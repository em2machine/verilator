// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Dependency graph for parameter/localparam/typedef resolution
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3LinkDotDepGraph.h"

#include "V3Ast.h"
#include "V3Const.h"
#include "V3Global.h"
#include "V3Width.h"

#include <algorithm>
#include <map>
#include <sstream>

VL_DEFINE_DEBUG_FUNCTIONS;

//======================================================================
// Static member definitions

V3LinkDotDepGraph::NodeMap V3LinkDotDepGraph::s_nodes;
std::vector<V3LinkDotDepGraph::DepNode*> V3LinkDotDepGraph::s_allNodes;
int V3LinkDotDepGraph::s_iterationCount = 0;
bool V3LinkDotDepGraph::s_enabled = false;
bool V3LinkDotDepGraph::s_preserveCapturedExprs = false;
bool V3LinkDotDepGraph::s_useInParam = false;
std::unordered_map<AstRefDType*, std::string> V3LinkDotDepGraph::s_refDTypeDotPathRegistry;
std::unordered_map<V3LinkDotDepGraph::TypedefClassKey, AstClass*,
                   V3LinkDotDepGraph::TypedefClassKeyHash> V3LinkDotDepGraph::s_typedefClassMap;

// Map from (module name, paramtype name) to cell name (captured during linkdot primary)
// We use names instead of pointers because nodes get cloned during V3Param
struct CellAssocKey {
    string moduleName;
    string paramTypeName;
    bool operator==(const CellAssocKey& o) const {
        return moduleName == o.moduleName && paramTypeName == o.paramTypeName;
    }
};
struct CellAssocKeyHash {
    size_t operator()(const CellAssocKey& k) const {
        return std::hash<string>()(k.moduleName) ^ (std::hash<string>()(k.paramTypeName) << 1);
    }
};
static std::unordered_map<CellAssocKey, string, CellAssocKeyHash> s_cellAssociations{};

//======================================================================
// Helper methods

AstNodeModule* V3LinkDotDepGraph::findOwnerModule(AstNode* nodep) {
    for (AstNode* curp = nodep; curp; curp = curp->backp()) {
        if (AstNodeModule* const modp = VN_CAST(curp, NodeModule)) return modp;
    }
    return nullptr;
}

string V3LinkDotDepGraph::nodeName(const DepNode* nodep) {
    if (!nodep || !nodep->nodep) return "<null>";
    if (const AstVar* const varp = VN_CAST(nodep->nodep, Var)) return varp->name();
    if (const AstTypedef* const tdp = VN_CAST(nodep->nodep, Typedef)) return tdp->name();
    if (const AstParamTypeDType* const ptdp = VN_CAST(nodep->nodep, ParamTypeDType))
        return ptdp->name();
    if (const AstRefDType* const rdp = VN_CAST(nodep->nodep, RefDType)) return rdp->name();
    return nodep->nodep->typeName();
}

string V3LinkDotDepGraph::nodeOwnerName(const DepNode* nodep) {
    if (!nodep || !nodep->ownerModp) return "<null>";
    return nodep->ownerModp->name();
}

static AstIfaceRefDType* findIfaceRefDType(AstNodeDType* dtypep) {
    if (!dtypep) return nullptr;
    if (AstIfaceRefDType* const ifaceRefp = VN_CAST(dtypep, IfaceRefDType)) return ifaceRefp;
    if (AstIfaceRefDType* const ifaceRefp = VN_CAST(dtypep->skipRefp(), IfaceRefDType)) return ifaceRefp;
    if (AstNodeDType* const subp = dtypep->subDTypep()) {
        if (AstIfaceRefDType* const ifaceRefp = findIfaceRefDType(subp)) return ifaceRefp;
    }
    return nullptr;
}

static AstNodeModule* findConnectedIfaceModpFromPort(AstNodeModule* modp,
                                                     const string& portName) {
    if (!modp || portName.empty()) return nullptr;
    AstNetlist* const rootp = v3Global.rootp();
    if (!rootp) return nullptr;
    for (AstNodeModule* topmodp = rootp->modulesp(); topmodp; topmodp = VN_AS(topmodp->nextp(), NodeModule)) {
        for (AstNode* stmtp = topmodp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            AstCell* const cellp = VN_CAST(stmtp, Cell);
            if (!cellp || cellp->modp() != modp) continue;
            for (AstPin* pinp = cellp->pinsp(); pinp; pinp = VN_CAST(pinp->nextp(), Pin)) {
                AstVar* const modVarp = pinp->modVarp();
                if (!modVarp || modVarp->name() != portName) continue;
                AstNode* exprp = pinp->exprp();
                if (!exprp) continue;
                while (AstNodePreSel* const preSelp = VN_CAST(exprp, NodePreSel)) exprp = preSelp->fromp();
                if (AstVarRef* const varRefp = VN_CAST(exprp, VarRef)) {
                    AstVar* const varp = varRefp->varp();
                    AstIfaceRefDType* ifaceRefp = findIfaceRefDType(varp->childDTypep());
                    if (!ifaceRefp) ifaceRefp = findIfaceRefDType(varp->subDTypep());
                    if (!ifaceRefp) ifaceRefp = findIfaceRefDType(varp->dtypep());
                    if (ifaceRefp && ifaceRefp->ifaceViaCellp()) return ifaceRefp->ifaceViaCellp();
                }
            }
        }
    }
    return nullptr;
}

const char* V3LinkDotDepGraph::nodeTypeName(NodeType type) {
    switch (type) {
    case NodeType::GPARAM: return "GPARAM";
    case NodeType::LPARAM: return "LPARAM";
    case NodeType::TYPEDEF: return "TYPEDEF";
    case NodeType::PARAMTYPEDTYPE: return "PARAMTYPE";
    case NodeType::REFDTYPE: return "REFDTYPE";
    case NodeType::STRUCTDTYPE: return "STRUCTDTYPE";
    case NodeType::UNIONDTYPE: return "UNIONDTYPE";
    }
    return "?";
}

V3LinkDotDepGraph::NodeType V3LinkDotDepGraph::classifyVar(const AstVar* varp) {
    if (!varp) return NodeType::GPARAM;
    if (varp->isGParam()) return NodeType::GPARAM;
    if (varp->isParam()) return NodeType::LPARAM;
    return NodeType::GPARAM;
}

//======================================================================
// Graph management

void V3LinkDotDepGraph::reset() {
    UINFO(5, "DEPGRAPH: reset() called, clearing graph nodes (keeping "
                  << s_cellAssociations.size() << " cell associations, "
                  << s_refDTypeDotPathRegistry.size() << " refdtype dotpath registrations)"
                  << endl);
    if (!s_preserveCapturedExprs) {
        for (DepNode* nodep : s_allNodes) {
            if (nodep && nodep->origExprp) {
                nodep->origExprp->deleteTree();
                nodep->origExprp = nullptr;
            }
            delete nodep;
        }
        s_allNodes.clear();
        s_nodes.clear();
    } else {
        std::vector<DepNode*> preserved;
        NodeMap preservedMap;
        preserved.reserve(s_allNodes.size());
        for (DepNode* nodep : s_allNodes) {
            if (nodep && nodep->origExprp
                && (nodep->nodeType == NodeType::GPARAM || nodep->nodeType == NodeType::LPARAM)) {
                // Drop preserved nodes whose AST node no longer maps to their owner module
                AstNodeModule* const currentOwnerp
                    = nodep->nodep ? findOwnerModule(nodep->nodep) : nullptr;
                if (!nodep->nodep || (nodep->ownerModp && currentOwnerp != nodep->ownerModp)) {
                    nodep->origExprp->deleteTree();
                    nodep->origExprp = nullptr;
                    delete nodep;
                    continue;
                }
                // Preserve captured exprs but clear stale dependency links
                nodep->dependsOn.clear();
                nodep->dependents.clear();
                preserved.push_back(nodep);
                preservedMap[nodep->nodep] = nodep;
            } else {
                if (nodep && nodep->origExprp) {
                    nodep->origExprp->deleteTree();
                    nodep->origExprp = nullptr;
                }
                delete nodep;
            }
        }
        s_allNodes.swap(preserved);
        s_nodes.swap(preservedMap);
    }
    // Note: Do NOT clear s_cellAssociations here - they are captured during linkdot primary
    // and need to persist until graph building which happens later
    // Note: Do NOT clear s_refDTypeDotPathRegistry here - populated during linkdot primary
    // and needed during graph build which occurs later.
    s_iterationCount = 0;
}

void V3LinkDotDepGraph::resetAll() {
    reset();
    s_cellAssociations.clear();
    s_refDTypeDotPathRegistry.clear();
    s_typedefClassMap.clear();
}

void V3LinkDotDepGraph::registerTypedefClass(AstTypedef* tdp, AstClass* classp,
                                              AstNodeModule* ownerModp) {
    if (!tdp || !classp || !ownerModp) return;
    TypedefClassKey key{ownerModp->name(), tdp->name()};
    auto it = s_typedefClassMap.find(key);
    if (it != s_typedefClassMap.end()) {
        // Already registered - update if different class
        if (it->second != classp) {
            UINFO(5, "DEPGRAPH: updating typedef-class mapping " << ownerModp->name()
                      << "::" << tdp->name() << " from " << it->second->name()
                      << " to " << classp->name() << endl);
            it->second = classp;
        }
        return;
    }
    s_typedefClassMap.emplace(key, classp);
    UINFO(5, "DEPGRAPH: registered typedef-class mapping " << ownerModp->name()
              << "::" << tdp->name() << " -> " << classp->name() << endl);
}

AstClass* V3LinkDotDepGraph::findTypedefClass(const string& ownerName, const string& typedefName) {
    TypedefClassKey key{ownerName, typedefName};
    auto it = s_typedefClassMap.find(key);
    if (it != s_typedefClassMap.end()) return it->second;
    return nullptr;
}

void V3LinkDotDepGraph::registerRefDTypeDotPath(AstRefDType* refp, const string& cellName,
                                                AstNodeModule* contextModp) {
    if (!refp || cellName.empty()) return;
    auto it = s_refDTypeDotPathRegistry.find(refp);
    if (it != s_refDTypeDotPathRegistry.end()) {
        UASSERT_OBJ(it->second == cellName, refp,
                    "Duplicate refdtype dotpath registry for '" << refp->name() << "' in "
                                                                  << (contextModp
                                                                          ? contextModp->name()
                                                                          : "<unknown>")
                                                                  << " old='" << it->second
                                                                  << "' new='" << cellName
                                                                  << "'");
        return;
    }
    s_refDTypeDotPathRegistry.emplace(refp, cellName);
    UINFO(5, "DEPGRAPH: registered refdtype dotpath '" << cellName << "' for '" << refp->name()
                  << "' in " << (contextModp ? contextModp->name() : "<unknown>") << endl);
}

void V3LinkDotDepGraph::registerCellAssociation(AstNode* nodep, AstCell* cellp,
                                                const string& typedefName,
                                                AstNodeModule* contextModp,
                                                const string& assocCellName) {
    UINFO(5, "DEPGRAPH: register assoc request typedef='" << typedefName
              << "' assocCell='" << assocCellName
              << "' context=" << (contextModp ? contextModp->name() : "<null>") << "\n");
    // Use contextModp if provided, otherwise find owner from node
    AstNodeModule* const ownerModp = contextModp ? contextModp : findOwnerModule(nodep);
    if (!ownerModp) return;

    // Get the paramtype name
    string paramTypeName;
    if (AstParamTypeDType* const ptdp = VN_CAST(nodep, ParamTypeDType)) {
        paramTypeName = ptdp->name();
    } else {
        return;  // Only handle PARAMTYPEDTYPEs for now
    }

    // Store as "cellName:typedefName"
    // The typedefName is passed from the caller who knows the actual typedef being referenced
    CellAssocKey key{ownerModp->name(), paramTypeName};
    string assocName = assocCellName;
    if (assocName.empty() && cellp) assocName = cellp->name();
    const size_t bra = assocName.find("__BRA__");
    if (bra != string::npos) assocName = assocName.substr(0, bra);
    if (assocName.empty()) return;
    string newAssoc = assocName + ":" + typedefName;
    s_cellAssociations[key] = newAssoc;
    UINFO(5, "DEPGRAPH: registered cell association for " << ownerModp->name()
              << "::" << paramTypeName << " -> cell '" << assocName
              << "' typedef '" << typedefName << "'" << endl);
}

const V3LinkDotDepGraph::DepNode* V3LinkDotDepGraph::find(AstNode* nodep) {
    const auto it = s_nodes.find(nodep);
    if (it == s_nodes.end()) return nullptr;
    return it->second;
}

V3LinkDotDepGraph::DepNode* V3LinkDotDepGraph::findOrCreateNode(AstNode* nodep, NodeType type,
                                                                 AstNodeModule* ownerModp) {
    if (!nodep) return nullptr;
    auto it = s_nodes.find(nodep);
    if (it != s_nodes.end()) return it->second;

    DepNode* const depNodep = new DepNode;
    depNodep->nodep = nodep;
    depNodep->nodeType = type;
    depNodep->ownerModp = ownerModp;
    s_nodes[nodep] = depNodep;
    s_allNodes.push_back(depNodep);

    UINFO(9, "DEPGRAPH: created " << nodeTypeName(type) << " node '" << nodeName(depNodep)
              << "' owner=" << nodeOwnerName(depNodep) << endl);
    return depNodep;
}

void V3LinkDotDepGraph::captureParamExpr(AstVar* varp, AstNodeModule* ownerModp) {
    if (!varp || !ownerModp) return;
    if (!varp->isGParam() && !varp->isParam()) return;
    if (!varp->valuep()) return;

    DepNode* const depNodep = findOrCreateNode(varp, classifyVar(varp), ownerModp);
    if (!depNodep || depNodep->origExprp) return;
    depNodep->origExprp = varp->valuep()->cloneTree(false);
    UINFO(5, "DEPGRAPH: captured default expr for param '" << varp->name()
              << "' in " << ownerModp->name() << endl);
}

void V3LinkDotDepGraph::captureParamExpr(AstVar* varp, AstNode* exprp,
                                         AstNodeModule* ownerModp) {
    if (!varp || !exprp || !ownerModp) return;
    if (!varp->isGParam() && !varp->isParam()) return;

    DepNode* const depNodep = findOrCreateNode(varp, classifyVar(varp), ownerModp);
    if (!depNodep || depNodep->origExprp) return;
    depNodep->origExprp = exprp->cloneTree(false);
    UINFO(5, "DEPGRAPH: captured override expr for param '" << varp->name()
              << "' in " << ownerModp->name() << endl);
}

void V3LinkDotDepGraph::captureParamTypeDType(AstParamTypeDType* ptdp, AstNodeDType* dtypep,
                                               AstNodeModule* ownerModp) {
    // Capture type parameter binding for specialized classes.
    // This ensures that when a class like my_pool#(T) is specialized with a concrete type,
    // the DepGraph has the binding information needed to resolve T inside the specialized class.
    if (!ptdp || !dtypep || !ownerModp) return;

    DepNode* const depNodep = findOrCreateNode(ptdp, NodeType::PARAMTYPEDTYPE, ownerModp);
    if (!depNodep) return;

    // Store the bound dtype as the origExprp (reusing this field for type params)
    if (!depNodep->origExprp) {
        depNodep->origExprp = dtypep->cloneTree(false);
        UINFO(5, "DEPGRAPH: captured type param binding for '" << ptdp->name()
                  << "' = " << dtypep->prettyDTypeName(true)
                  << " in " << ownerModp->name() << endl);
    }
}

void V3LinkDotDepGraph::addEdge(DepNode* from, DepNode* to) {
    if (!from || !to || from == to) return;
    from->dependsOn.insert(to);
    to->dependents.insert(from);
    UINFO(9, "DEPGRAPH: edge '" << nodeName(from) << "'@" << nodeOwnerName(from)
              << " --> '" << nodeName(to) << "'@" << nodeOwnerName(to) << endl);
}

void V3LinkDotDepGraph::forEach(const std::function<void(const DepNode&)>& fn) {
    for (const DepNode* nodep : s_allNodes) fn(*nodep);
}

//======================================================================
// Helper to recursively search for typedef/paramtype in nested interface cells

// Search for a typedef or paramtype named 'typedefName' in a cell named 'cellName'
// within the given module, recursively searching nested interface cells up to maxDepth
static void findTypedefInHierarchy(AstNodeModule* modp, const string& cellName,
                                   const string& typedefName, int maxDepth,
                                   AstTypedef*& targetTdp, AstParamTypeDType*& targetPtdp,
                                   AstNodeModule*& targetModp) {
    if (!modp || maxDepth <= 0 || targetTdp || targetPtdp) return;

    // Search cells in this module
    for (AstNode* stmtp = modp->stmtsp(); stmtp && !targetTdp && !targetPtdp; stmtp = stmtp->nextp()) {
        if (AstCell* const cellp = VN_CAST(stmtp, Cell)) {
            if (cellp->name() == cellName && cellp->modp()) {
                // Found the cell - look for typedef/paramtype in cell's module
                for (AstNode* childStmtp = cellp->modp()->stmtsp(); childStmtp; childStmtp = childStmtp->nextp()) {
                    if (AstTypedef* const tdp = VN_CAST(childStmtp, Typedef)) {
                        if (tdp->name() == typedefName) {
                            targetTdp = tdp;
                            targetModp = cellp->modp();
                            UINFO(5, "DEPGRAPH: found typedef '" << typedefName
                                      << "' in cell '" << cellName << "' at depth "
                                      << maxDepth << " in " << cellp->modp()->name() << endl);
                            return;
                        }
                    } else if (AstParamTypeDType* const ptdp = VN_CAST(childStmtp, ParamTypeDType)) {
                        if (ptdp->name() == typedefName) {
                            targetPtdp = ptdp;
                            targetModp = cellp->modp();
                            UINFO(5, "DEPGRAPH: found paramtype '" << typedefName
                                      << "' in cell '" << cellName << "' at depth "
                                      << maxDepth << " in " << cellp->modp()->name() << endl);
                            return;
                        }
                    }
                }
            }
            // Recursively search in interface cells
            if (cellp->modp() && VN_IS(cellp->modp(), Iface)) {
                findTypedefInHierarchy(cellp->modp(), cellName, typedefName, maxDepth - 1,
                                       targetTdp, targetPtdp, targetModp);
            }
        }
    }
}

static AstNodeModule* resolveCellPathModule(AstNodeModule* modp, const string& cellPath) {
    if (!modp) return nullptr;

    AstNodeModule* curModp = modp;
    size_t start = 0;
    while (start < cellPath.size()) {
        const size_t dotPos = cellPath.find('.', start);
        const string seg = (dotPos == string::npos)
                               ? cellPath.substr(start)
                               : cellPath.substr(start, dotPos - start);
        if (seg.empty()) return nullptr;

        AstNodeModule* nextModp = nullptr;

        for (AstNode* stmtp = curModp->stmtsp(); stmtp && !nextModp; stmtp = stmtp->nextp()) {
            if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                if (varp->name() != seg) continue;
                AstIfaceRefDType* ifaceRefp = findIfaceRefDType(varp->dtypep());
                if (!ifaceRefp) ifaceRefp = findIfaceRefDType(varp->subDTypep());
                if (!ifaceRefp) ifaceRefp = findIfaceRefDType(varp->childDTypep());
                if (!ifaceRefp) continue;
                if (AstNodeModule* const connected = findConnectedIfaceModpFromPort(curModp, seg)) {
                    nextModp = connected;
                } else if (ifaceRefp->cellp() && ifaceRefp->cellp()->modp()) {
                    nextModp = ifaceRefp->cellp()->modp();
                } else if (ifaceRefp->ifacep()) {
                    nextModp = ifaceRefp->ifacep();
                }
            }
        }

        for (AstNode* stmtp = curModp->stmtsp(); stmtp && !nextModp; stmtp = stmtp->nextp()) {
            if (AstCell* const cellp = VN_CAST(stmtp, Cell)) {
                if (cellp->name() == seg && cellp->modp()) nextModp = cellp->modp();
            }
        }

        if (!nextModp) return nullptr;
        curModp = nextModp;

        if (dotPos == string::npos) break;
        start = dotPos + 1;
    }

    return curModp;
}

//======================================================================
// Graph building

// Visitor to collect variable references in an expression
class DepExprVisitor final : public VNVisitorConst {
private:
    V3LinkDotDepGraph::DepNode* m_depNode;

    void visit(AstVarRef* nodep) override {
        if (AstVar* const varp = nodep->varp()) {
            AstNodeModule* const varOwnerp = V3LinkDotDepGraph::findOwnerModule(varp);
            V3LinkDotDepGraph::NodeType type = V3LinkDotDepGraph::classifyVar(varp);
            V3LinkDotDepGraph::DepNode* const targetp
                = V3LinkDotDepGraph::findOrCreateNode(varp, type, varOwnerp);
            V3LinkDotDepGraph::addEdge(m_depNode, targetp);
        }
    }
    void visit(AstVarXRef* nodep) override {
        // Hierarchical reference like io.types.ABits
        if (AstVar* const varp = nodep->varp()) {
            AstVar* targetVarp = varp;
            AstNodeModule* targetModp = V3LinkDotDepGraph::findOwnerModule(varp);
            if (m_depNode && m_depNode->ownerModp && !nodep->dotted().empty()) {
                const string dotted = nodep->dotted();
                const size_t firstDot = dotted.find('.');
                const string cellName = firstDot == string::npos
                                            ? dotted
                                            : dotted.substr(0, firstDot);
                const string rest = firstDot == string::npos ? "" : dotted.substr(firstDot + 1);
                if (!cellName.empty()) {
                    AstNodeModule* ifaceModp = findConnectedIfaceModpFromPort(m_depNode->ownerModp, cellName);
                    if (!ifaceModp) {
                        for (AstNode* stmtp = m_depNode->ownerModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                            if (AstCell* const cellp = VN_CAST(stmtp, Cell)) {
                                if (cellp->name() == cellName && cellp->modp()) {
                                    ifaceModp = cellp->modp();
                                    break;
                                }
                            }
                        }
                    }
                    if (ifaceModp) {
                        AstNodeModule* searchModp = ifaceModp;
                        if (!rest.empty()) {
                            const size_t nextDot = rest.find('.');
                            const string innerCell = nextDot == string::npos
                                                         ? rest
                                                         : rest.substr(0, nextDot);
                            for (AstNode* stmtp = ifaceModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                                if (AstCell* const cellp = VN_CAST(stmtp, Cell)) {
                                    if (cellp->name() == innerCell && cellp->modp()) {
                                        searchModp = cellp->modp();
                                        break;
                                    }
                                }
                            }
                        }
                        for (AstNode* stmtp = searchModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                            if (AstVar* const candp = VN_CAST(stmtp, Var)) {
                                if (candp->name() == nodep->name()) {
                                    targetVarp = candp;
                                    targetModp = searchModp;
                                    break;
                                }
                            }
                        }
                    }
                }
            }
            V3LinkDotDepGraph::NodeType type = V3LinkDotDepGraph::classifyVar(targetVarp);
            V3LinkDotDepGraph::DepNode* const targetp
                = V3LinkDotDepGraph::findOrCreateNode(targetVarp, type, targetModp);
            V3LinkDotDepGraph::addEdge(m_depNode, targetp);
            UINFO(5, "DEPGRAPH: xref '" << nodep->name() << "' dotted='" << nodep->dotted()
                      << "' -> " << V3LinkDotDepGraph::nodeName(targetp) << "@"
                      << (targetModp ? targetModp->name() : "<null>") << endl);
        }
    }
    void visit(AstRefDType* nodep) override {
        AstNodeModule* const ownerp = V3LinkDotDepGraph::findOwnerModule(nodep);
        if (!ownerp) return;
        V3LinkDotDepGraph::DepNode* const targetp
            = V3LinkDotDepGraph::findOrCreateNode(nodep, V3LinkDotDepGraph::NodeType::REFDTYPE, ownerp);
        // Skip edge if parent is PARAMTYPE with same name in same module (would create cycle)
        const bool isSelfRef = (m_depNode
                                && m_depNode->nodeType == V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE
                                && m_depNode->ownerModp == ownerp
                                && V3LinkDotDepGraph::nodeName(m_depNode) == nodep->name());
        if (!isSelfRef) V3LinkDotDepGraph::addEdge(m_depNode, targetp);
        if (AstTypedef* const tdp = nodep->typedefp()) {
            AstNodeModule* const tdOwnerp = V3LinkDotDepGraph::findOwnerModule(tdp);
            V3LinkDotDepGraph::DepNode* const tdNodep
                = V3LinkDotDepGraph::findOrCreateNode(
                    tdp, V3LinkDotDepGraph::NodeType::TYPEDEF, tdOwnerp);
            V3LinkDotDepGraph::addEdge(targetp, tdNodep);
            UINFO(5, "DEPGRAPH: refdtype '" << nodep->name() << "' -> typedef '"
                      << tdp->name() << "' in "
                      << (tdOwnerp ? tdOwnerp->name() : "<null>") << endl);
        } else if (AstParamTypeDType* const ptdp = VN_CAST(nodep->refDTypep(), ParamTypeDType)) {
            AstParamTypeDType* targetPtdp = ptdp;
            AstNodeModule* ptOwnerp = V3LinkDotDepGraph::findOwnerModule(ptdp);
            if (ptOwnerp && m_depNode && m_depNode->ownerModp
                && ptOwnerp->hasGParam() && ptOwnerp->name().find("__") == string::npos) {
                for (AstNode* stmtp = m_depNode->ownerModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                    if (AstParamTypeDType* const cellPtdp = VN_CAST(stmtp, ParamTypeDType)) {
                        if (cellPtdp->name() == ptdp->name()) {
                            targetPtdp = cellPtdp;
                            ptOwnerp = m_depNode->ownerModp;
                            break;
                        }
                    }
                }
            }
            V3LinkDotDepGraph::DepNode* const ptNodep
                = V3LinkDotDepGraph::findOrCreateNode(
                    targetPtdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, ptOwnerp);
            // Skip edge if REFDTYPE is child of the PARAMTYPE (would create cycle)
            const bool isSelfRef = (ptOwnerp == V3LinkDotDepGraph::findOwnerModule(nodep)
                                    && targetPtdp->name() == nodep->name());
            if (!isSelfRef) {
                V3LinkDotDepGraph::addEdge(targetp, ptNodep);
                UINFO(5, "DEPGRAPH: refdtype '" << nodep->name() << "' -> paramtype '"
                          << targetPtdp->name() << "' in "
                          << (ptOwnerp ? ptOwnerp->name() : "<null>")
                          << (targetPtdp != ptdp ? " (retargeted)" : "") << endl);
            }
        }
        iterateChildrenConst(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    DepExprVisitor(AstNode* exprp, V3LinkDotDepGraph::DepNode* depNode)
        : m_depNode(depNode) {
        if (exprp) iterateConst(exprp);
    }
};

void V3LinkDotDepGraph::collectExpressionDeps(AstNode* exprp, DepNode* depNode,
                                               AstNodeModule* /*scopeModp*/) {
    if (!exprp || !depNode) return;
    DepExprVisitor{exprp, depNode};
}

// Visitor to build the dependency graph from the AST
class DepGraphBuildVisitor final : public VNVisitorConst {
private:
    AstNodeModule* m_modp = nullptr;  // Current module/interface
    std::unordered_map<string, AstVar*> m_varsByName;  // Vars in current module

    void rebuildVarMap() {
        m_varsByName.clear();
        if (!m_modp) return;
        for (AstNode* stmtp = m_modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* const varp = VN_CAST(stmtp, Var)) m_varsByName[varp->name()] = varp;
        }
    }

    void visit(AstNodeModule* nodep) override {
        // Skip dead modules and template modules (unspecialized parameterized modules)
        // Template modules have GParams but no specialization suffix
        if (nodep->dead()) return;
        if (nodep->hasGParam() && nodep->name().find("__") == string::npos) {
            UINFO(9, "DEPGRAPH: skip template module " << nodep->name() << endl);
            return;
        }

        VL_RESTORER(m_modp);
        m_modp = nodep;
        rebuildVarMap();
        UINFO(9, "DEPGRAPH: visiting module " << nodep->name() << endl);
        iterateChildrenConst(nodep);
    }

    void visit(AstVar* nodep) override {
        if (!m_modp) return;
        // Only interested in parameters and localparams
        if (!nodep->isGParam() && !nodep->isParam()) return;

        V3LinkDotDepGraph::NodeType type = V3LinkDotDepGraph::classifyVar(nodep);
        V3LinkDotDepGraph::DepNode* const depNodep
            = V3LinkDotDepGraph::findOrCreateNode(nodep, type, m_modp);

        // If this is a specialized clone, inherit captured expression from original
        if (!depNodep->origExprp) {
            if (AstVar* const origVarp = nodep->clonep()) {
                if (const V3LinkDotDepGraph::DepNode* const origNodep
                    = V3LinkDotDepGraph::find(origVarp)) {
                    if (origNodep->origExprp) {
                        AstNode* const clonedExprp = origNodep->origExprp->cloneTree(false);
                        int relinkedRefs = 0;
                        clonedExprp->foreach([&](AstVarRef* refp) {
                            const auto it = m_varsByName.find(refp->varp()->name());
                            if (it != m_varsByName.end()) refp->varp(it->second);
                            if (it != m_varsByName.end()) ++relinkedRefs;
                        });
                        depNodep->origExprp = clonedExprp;
                        UINFO(5, "DEPGRAPH: inherited expr for param '" << nodep->name()
                                  << "' in " << m_modp->name() << " from template "
                                  << origNodep->ownerModp->name() << " (relinked "
                                  << relinkedRefs << " refs)" << endl);
                    }
                }
            }
        }
        if (!depNodep->origExprp && m_modp) {
            string baseModName = m_modp->name();
            const size_t suffixPos = baseModName.find("__");
            if (suffixPos != string::npos) baseModName = baseModName.substr(0, suffixPos);
            if (baseModName != m_modp->name()) {
                for (const V3LinkDotDepGraph::DepNode* const candp : V3LinkDotDepGraph::s_allNodes) {
                    if (!candp || !candp->origExprp) continue;
                    if (candp->nodeType != depNodep->nodeType) continue;
                    if (!candp->ownerModp || candp->ownerModp->name() != baseModName) continue;
                    if (V3LinkDotDepGraph::nodeName(candp) != V3LinkDotDepGraph::nodeName(depNodep)) {
                        continue;
                    }
                    AstNode* const clonedExprp = candp->origExprp->cloneTree(false);
                    int relinkedRefs = 0;
                    const auto resolveXRef = [&](AstVarXRef* xrefp) -> AstVar* {
                        if (!xrefp || !m_modp || xrefp->dotted().empty()) return nullptr;
                        const string dotted = xrefp->dotted();
                        const size_t firstDot = dotted.find('.');
                        const string cellName = firstDot == string::npos
                                                    ? dotted
                                                    : dotted.substr(0, firstDot);
                        const string rest = firstDot == string::npos ? "" : dotted.substr(firstDot + 1);
                        if (cellName.empty()) return nullptr;
                        AstNodeModule* ifaceModp = findConnectedIfaceModpFromPort(m_modp, cellName);
                        if (!ifaceModp) {
                            for (AstNode* stmtp = m_modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                                if (AstCell* const cellp = VN_CAST(stmtp, Cell)) {
                                    if (cellp->name() == cellName && cellp->modp()) {
                                        ifaceModp = cellp->modp();
                                        break;
                                    }
                                }
                            }
                        }
                        if (!ifaceModp) return nullptr;
                        AstNodeModule* searchModp = ifaceModp;
                        if (!rest.empty()) {
                            const size_t nextDot = rest.find('.');
                            const string innerCell = nextDot == string::npos
                                                         ? rest
                                                         : rest.substr(0, nextDot);
                            for (AstNode* stmtp = ifaceModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                                if (AstCell* const cellp = VN_CAST(stmtp, Cell)) {
                                    if (cellp->name() == innerCell && cellp->modp()) {
                                        searchModp = cellp->modp();
                                        break;
                                    }
                                }
                            }
                        }
                        for (AstNode* stmtp = searchModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                            if (AstVar* const candp = VN_CAST(stmtp, Var)) {
                                if (candp->name() == xrefp->name()) return candp;
                            }
                        }
                        return nullptr;
                    };
                    clonedExprp->foreach([&](AstVarRef* refp) {
                        const auto it = m_varsByName.find(refp->varp()->name());
                        if (it != m_varsByName.end()) refp->varp(it->second);
                        if (it != m_varsByName.end()) ++relinkedRefs;
                    });
                    clonedExprp->foreach([&](AstVarXRef* xrefp) {
                        if (AstVar* const resolvedp = resolveXRef(xrefp)) {
                            xrefp->varp(resolvedp);
                            ++relinkedRefs;
                        }
                    });
                    depNodep->origExprp = clonedExprp;
                    UINFO(5, "DEPGRAPH: inherited expr for param '" << nodep->name()
                              << "' in " << m_modp->name() << " from template "
                              << baseModName << " (name match, relinked "
                              << relinkedRefs << " refs)" << endl);
                    break;
                }
            }
        }

        // Collect dependencies from the value expression (prefer captured pre-constify)
        AstNode* exprp = depNodep->origExprp ? depNodep->origExprp : nodep->valuep();
        if (exprp) {
            V3LinkDotDepGraph::collectExpressionDeps(exprp, depNodep, m_modp);
            if (debug() >= 5) {
                std::ostringstream deps;
                bool first = true;
                for (V3LinkDotDepGraph::DepNode* const dep : depNodep->dependsOn) {
                    if (!dep) continue;
                    if (!first) deps << ", ";
                    first = false;
                    deps << V3LinkDotDepGraph::nodeName(dep)
                         << "@" << V3LinkDotDepGraph::nodeOwnerName(dep);
                }
                UINFO(5, "DEPGRAPH: deps for '" << nodep->name() << "'@" << m_modp->name()
                          << " = [" << deps.str() << "]" << endl);
            }
        }
    }

    void visit(AstTypedef* nodep) override {
        if (!m_modp) return;

        V3LinkDotDepGraph::DepNode* const depNodep
            = V3LinkDotDepGraph::findOrCreateNode(nodep, V3LinkDotDepGraph::NodeType::TYPEDEF, m_modp);

        // Collect dependencies from the subtype (e.g., width expressions)
        if (AstNodeDType* const dtypep = nodep->subDTypep()) {
            // For BasicDType, check the range expressions
            if (AstBasicDType* const bdtp = VN_CAST(dtypep, BasicDType)) {
                if (AstRange* const rangep = bdtp->rangep()) {
                    V3LinkDotDepGraph::collectExpressionDeps(rangep->leftp(), depNodep, m_modp);
                    V3LinkDotDepGraph::collectExpressionDeps(rangep->rightp(), depNodep, m_modp);
                }
            }
            // For RefDType pointing to another typedef (e.g., typedef c_inst.c_t b_t;)
            // Add edge from this typedef to the referenced typedef/paramtype
            if (AstRefDType* const rdtp = VN_CAST(dtypep, RefDType)) {
                if (AstTypedef* const refTdp = rdtp->typedefp()) {
                    AstNodeModule* const refOwnerp = V3LinkDotDepGraph::findOwnerModule(refTdp);
                    V3LinkDotDepGraph::DepNode* const refNodep
                        = V3LinkDotDepGraph::findOrCreateNode(refTdp, V3LinkDotDepGraph::NodeType::TYPEDEF, refOwnerp);
                    V3LinkDotDepGraph::addEdge(depNodep, refNodep);
                    UINFO(9, "DEPGRAPH: typedef '" << nodep->name() << "' depends on typedef '"
                              << refTdp->name() << "' in " << (refOwnerp ? refOwnerp->name() : "<null>") << endl);
                } else if (AstParamTypeDType* const refPtdp = VN_CAST(rdtp->refDTypep(), ParamTypeDType)) {
                    AstNodeModule* const refOwnerp = V3LinkDotDepGraph::findOwnerModule(refPtdp);
                    V3LinkDotDepGraph::DepNode* const refNodep
                        = V3LinkDotDepGraph::findOrCreateNode(
                            refPtdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, refOwnerp);
                    V3LinkDotDepGraph::addEdge(depNodep, refNodep);
                    UINFO(9, "DEPGRAPH: typedef '" << nodep->name() << "' depends on paramtype '"
                              << refPtdp->name() << "' in " << (refOwnerp ? refOwnerp->name() : "<null>") << endl);
                }
            }
            // For ClassRefDType (typedef to parameterized class like uvm_object_registry#(...))
            // Track the class dependency so we can resolve it correctly later
            if (AstClassRefDType* const crdtp = VN_CAST(dtypep, ClassRefDType)) {
                if (AstClass* const classp = crdtp->classp()) {
                    // Store the typedef -> class relationship for later resolution
                    // The class might be a specialized class (e.g., uvm_object_registry__Tz191)
                    UINFO(5, "DEPGRAPH: typedef '" << nodep->name() << "' points to class '"
                              << classp->name() << "' in " << m_modp->name() << endl);
                    // Register this typedef's target class for method resolution
                    V3LinkDotDepGraph::registerTypedefClass(nodep, classp, m_modp);
                }
            }
            // For struct/union types, create a DepNode and track member dependencies.
            // These may have been moved to TYPETABLE but are still referenced via subDTypep.
            if (AstNodeUOrStructDType* const usp = VN_CAST(dtypep, NodeUOrStructDType)) {
                V3LinkDotDepGraph::NodeType nodeType = VN_IS(usp, UnionDType)
                    ? V3LinkDotDepGraph::NodeType::UNIONDTYPE
                    : V3LinkDotDepGraph::NodeType::STRUCTDTYPE;
                V3LinkDotDepGraph::DepNode* const uspNodep
                    = V3LinkDotDepGraph::findOrCreateNode(usp, nodeType, m_modp);
                // Typedef depends on the struct/union
                V3LinkDotDepGraph::addEdge(depNodep, uspNodep);
                // Track member type dependencies (RefDType, PackArrayDType, etc.)
                for (AstMemberDType* memp = usp->membersp(); memp;
                     memp = VN_AS(memp->nextp(), MemberDType)) {
                    AstNodeDType* memDTypep = memp->subDTypep();
                    if (AstRefDType* const refp = VN_CAST(memDTypep, RefDType)) {
                        V3LinkDotDepGraph::DepNode* const refNodep
                            = V3LinkDotDepGraph::findOrCreateNode(
                                refp, V3LinkDotDepGraph::NodeType::REFDTYPE, m_modp);
                        V3LinkDotDepGraph::addEdge(uspNodep, refNodep);
                        AstNodeDType* const targetp = refp->refDTypep();
                        UINFO(5, "DEPGRAPH: typedef '" << nodep->name() << "' struct/union member '"
                                  << memp->name() << "' -> refdtype '" << refp->name() << "' -> "
                                  << (targetp ? targetp->prettyTypeName() : "<null>")
                                  << " w" << (targetp ? targetp->width() : 0) << endl);
                    } else if (AstPackArrayDType* const arrp = VN_CAST(memDTypep, PackArrayDType)) {
                        // Track array range dependencies (may use parameters)
                        if (AstRange* const rangep = arrp->rangep()) {
                            V3LinkDotDepGraph::collectExpressionDeps(rangep->leftp(), uspNodep, m_modp);
                            V3LinkDotDepGraph::collectExpressionDeps(rangep->rightp(), uspNodep, m_modp);
                            UINFO(5, "DEPGRAPH: typedef '" << nodep->name() << "' struct/union member '"
                                      << memp->name() << "' -> packarraydtype range deps collected" << endl);
                        }
                        // Also track the element type if it's a RefDType
                        if (AstRefDType* const elemRefp = VN_CAST(arrp->subDTypep(), RefDType)) {
                            V3LinkDotDepGraph::DepNode* const refNodep
                                = V3LinkDotDepGraph::findOrCreateNode(
                                    elemRefp, V3LinkDotDepGraph::NodeType::REFDTYPE, m_modp);
                            V3LinkDotDepGraph::addEdge(uspNodep, refNodep);
                            UINFO(5, "DEPGRAPH: typedef '" << nodep->name() << "' struct/union member '"
                                      << memp->name() << "' array element -> refdtype '"
                                      << elemRefp->name() << "'" << endl);
                        }
                    }
                }
                UINFO(5, "DEPGRAPH: typedef '" << nodep->name() << "' -> "
                          << (VN_IS(usp, UnionDType) ? "UNIONDTYPE" : "STRUCTDTYPE")
                          << " '" << usp->name() << "' w" << usp->width()
                          << " deps=" << uspNodep->dependsOn.size() << endl);
            }
            // For other types, iterate children
            V3LinkDotDepGraph::collectExpressionDeps(dtypep, depNodep, m_modp);
        }
    }

    void visit(AstParamTypeDType* nodep) override {
        if (!m_modp) return;

        V3LinkDotDepGraph::DepNode* const depNodep = V3LinkDotDepGraph::findOrCreateNode(
            nodep, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, m_modp);

        // Check for cell association registered during linkdot primary pass
        // The key uses the base module name (without specialization suffix) and paramtype name
        // For specialized modules like "sc__Cz1_Iz2", we need to check the original "sc" module
        string baseModName = m_modp->name();
        // Strip specialization suffix (everything after "__")
        const size_t suffixPos = baseModName.find("__");
        if (suffixPos != string::npos) baseModName = baseModName.substr(0, suffixPos);

        CellAssocKey key{baseModName, nodep->name()};
        auto it = s_cellAssociations.find(key);
        UINFO(5, "DEPGRAPH: lookup assoc key " << baseModName << "::" << nodep->name()
                  << (it != s_cellAssociations.end() ? " hit" : " miss") << "\n");
        if (it != s_cellAssociations.end()) {
            // Value is "cellName:typedefName"
            depNodep->cellName = it->second;
            UINFO(5, "DEPGRAPH: paramtype '" << nodep->name()
                      << "' in " << m_modp->name() << " (base=" << baseModName
                      << ") has registered cell:typedef '" << it->second << "'" << endl);

            // Parse cellName:typedefName and find the typedef node to add dependency edge
            // This ensures the PARAMTYPEDTYPE is resolved AFTER the typedef it references
            string cellName, typedefName;
            const size_t colonPos = it->second.find(':');
            if (colonPos != string::npos) {
                cellName = it->second.substr(0, colonPos);
                typedefName = it->second.substr(colonPos + 1);
            }

            AstNodeModule* const dottedModp =
                cellName.find('.') != string::npos ? resolveCellPathModule(m_modp, cellName) : nullptr;

            // Find the typedef or PARAMTYPEDTYPE in a cell with this name
            // We need to find the specialized interface's typedef or PARAMTYPEDTYPE
            // Search: 1) direct cells in this module, 2) cells in interfaces this module references
            if (!typedefName.empty()) {
                AstTypedef* targetTdp = nullptr;
                AstParamTypeDType* targetPtdp = nullptr;
                AstNodeModule* targetModp = nullptr;

                if (dottedModp) {
                    for (AstNode* childStmtp = dottedModp->stmtsp(); childStmtp;
                         childStmtp = childStmtp->nextp()) {
                        if (AstTypedef* const tdp = VN_CAST(childStmtp, Typedef)) {
                            if (tdp->name() == typedefName) {
                                targetTdp = tdp;
                                targetModp = dottedModp;
                                break;
                            }
                        } else if (AstParamTypeDType* const ptdp = VN_CAST(childStmtp, ParamTypeDType)) {
                            if (ptdp->name() == typedefName) {
                                targetPtdp = ptdp;
                                targetModp = dottedModp;
                                break;
                            }
                        }
                    }
                }

                // First, search for cells directly in this module
                for (AstNode* stmtp = m_modp->stmtsp(); stmtp && !targetTdp && !targetPtdp; stmtp = stmtp->nextp()) {
                    if (AstCell* const cellp = VN_CAST(stmtp, Cell)) {
                        if (cellp->name() == cellName && cellp->modp()) {
                            // Found the cell - look for typedef or PARAMTYPEDTYPE in cell's module
                            for (AstNode* childStmtp = cellp->modp()->stmtsp(); childStmtp;
                                 childStmtp = childStmtp->nextp()) {
                                if (AstTypedef* const tdp = VN_CAST(childStmtp, Typedef)) {
                                    if (tdp->name() == typedefName) {
                                        targetTdp = tdp;
                                        targetModp = cellp->modp();
                                        break;
                                    }
                                } else if (AstParamTypeDType* const ptdp = VN_CAST(childStmtp, ParamTypeDType)) {
                                    if (ptdp->name() == typedefName) {
                                        targetPtdp = ptdp;
                                        targetModp = cellp->modp();
                                        break;
                                    }
                                }
                            }
                        }
                    }
                }

                // If not found, search cells in interfaces this module references (via cells)
                if (!targetTdp && !targetPtdp) {
                    bool portNameMatch = false;
                    for (AstNode* stmtp = m_modp->stmtsp(); stmtp && !portNameMatch; stmtp = stmtp->nextp()) {
                        if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                            AstIfaceRefDType* ifaceRefp = VN_CAST(varp->dtypep(), IfaceRefDType);
                            if (!ifaceRefp && varp->dtypep()) {
                                ifaceRefp = VN_CAST(varp->dtypep()->skipRefp(), IfaceRefDType);
                            }
                            if (!ifaceRefp && varp->subDTypep()) {
                                ifaceRefp = VN_CAST(varp->subDTypep(), IfaceRefDType);
                            }
                            if (!ifaceRefp && varp->subDTypep()) {
                                ifaceRefp = VN_CAST(varp->subDTypep()->skipRefp(), IfaceRefDType);
                            }
                            if (!ifaceRefp && varp->isIfaceRef()) {
                                if (varp->childDTypep()) {
                                    ifaceRefp = VN_CAST(varp->childDTypep(), IfaceRefDType);
                                }
                            }
                            if (ifaceRefp && varp->name() == cellName) portNameMatch = true;
                        }
                    }
                    for (AstNode* stmtp = m_modp->stmtsp(); stmtp && !targetTdp && !targetPtdp; stmtp = stmtp->nextp()) {
                        if (AstCell* const ifaceCellp = VN_CAST(stmtp, Cell)) {
                            if (ifaceCellp->modp() && VN_IS(ifaceCellp->modp(), Iface)) {
                                // Search cells inside this interface
                                for (AstNode* ifaceStmtp = ifaceCellp->modp()->stmtsp();
                                     ifaceStmtp && !targetTdp && !targetPtdp; ifaceStmtp = ifaceStmtp->nextp()) {
                                    if (AstCell* const cellp = VN_CAST(ifaceStmtp, Cell)) {
                                        if (cellp->name() == cellName && cellp->modp()) {
                                            for (AstNode* childStmtp = cellp->modp()->stmtsp();
                                                 childStmtp; childStmtp = childStmtp->nextp()) {
                                                if (AstTypedef* const tdp = VN_CAST(childStmtp, Typedef)) {
                                                    if (tdp->name() == typedefName) {
                                                        targetTdp = tdp;
                                                        targetModp = cellp->modp();
                                                        break;
                                                    }
                                                } else if (AstParamTypeDType* const ptdp = VN_CAST(childStmtp, ParamTypeDType)) {
                                                    if (ptdp->name() == typedefName) {
                                                        targetPtdp = ptdp;
                                                        targetModp = cellp->modp();
                                                        break;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }

                // If not found, search interface PORTS (VAR with IFACEREF type)
                // This handles modules that take interfaces as ports rather than instantiating them
                if (!targetTdp && !targetPtdp) {
                    UINFO(9, "DEPGRAPH: searching iface ports in " << m_modp->name()
                              << " for cell '" << cellName << "' typedef '" << typedefName << "'" << endl);
                    bool portNameMatch = false;
                    for (AstNode* stmtp = m_modp->stmtsp(); stmtp && !portNameMatch; stmtp = stmtp->nextp()) {
                        if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                            AstIfaceRefDType* ifaceRefp = findIfaceRefDType(varp->dtypep());
                            if (!ifaceRefp) ifaceRefp = findIfaceRefDType(varp->subDTypep());
                            if (!ifaceRefp) ifaceRefp = findIfaceRefDType(varp->childDTypep());
                            if (ifaceRefp && varp->name() == cellName) portNameMatch = true;
                        }
                    }
                    for (AstNode* stmtp = m_modp->stmtsp(); stmtp && !targetTdp && !targetPtdp; stmtp = stmtp->nextp()) {
                        if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                            // Try to get IfaceRefDType - may be direct, via skipRefp, or via subDTypep
                            AstIfaceRefDType* ifaceRefp = findIfaceRefDType(varp->dtypep());
                            if (!ifaceRefp) ifaceRefp = findIfaceRefDType(varp->subDTypep());
                            if (!ifaceRefp) ifaceRefp = findIfaceRefDType(varp->childDTypep());
                            if (ifaceRefp) {
                                if (portNameMatch && varp->name() != cellName) continue;
                                UINFO(9, "DEPGRAPH: checking iface port '" << varp->name()
                                          << "' cellp=" << ifaceRefp->cellp()
                                          << " ifacep=" << ifaceRefp->ifacep() << endl);
                            }
                            // For interface ports, use ifacep() which points to the interface module
                            // For interface cells, use cellp()->modp()
                            AstNodeModule* ifaceModp = nullptr;
                            if (ifaceRefp && ifaceRefp->cellp() && ifaceRefp->cellp()->modp()
                                && VN_IS(ifaceRefp->cellp()->modp(), Iface)) {
                                ifaceModp = ifaceRefp->cellp()->modp();
                            } else if (ifaceRefp && ifaceRefp->ifacep()) {
                                ifaceModp = ifaceRefp->ifacep();
                            }
                            if (ifaceModp && varp->name() == cellName) {
                                if (AstNodeModule* const connectedIfaceModp
                                    = findConnectedIfaceModpFromPort(m_modp, cellName)) {
                                    ifaceModp = connectedIfaceModp;
                                    UINFO(5, "DEPGRAPH: resolved iface port '" << cellName
                                              << "' to connected interface " << ifaceModp->name()
                                              << " for typedef '" << typedefName << "' in "
                                              << m_modp->name() << endl);
                                }
                            }
                            if (ifaceModp) {
                                // First, look directly in the interface module for the typedef/paramtype
                                for (AstNode* ifaceStmtp = ifaceModp->stmtsp();
                                     ifaceStmtp && !targetTdp && !targetPtdp; ifaceStmtp = ifaceStmtp->nextp()) {
                                    if (AstTypedef* const tdp = VN_CAST(ifaceStmtp, Typedef)) {
                                        if (tdp->name() == typedefName) {
                                            targetTdp = tdp;
                                            targetModp = ifaceModp;
                                            UINFO(5, "DEPGRAPH: found typedef '" << typedefName
                                                      << "' via iface port '" << varp->name()
                                                      << "' in " << ifaceModp->name() << endl);
                                            break;
                                        }
                                    } else if (AstParamTypeDType* const ptdp = VN_CAST(ifaceStmtp, ParamTypeDType)) {
                                        if (ptdp->name() == typedefName) {
                                            targetPtdp = ptdp;
                                            targetModp = ifaceModp;
                                            UINFO(5, "DEPGRAPH: found paramtype '" << typedefName
                                                      << "' via iface port '" << varp->name()
                                                      << "' in " << ifaceModp->name() << endl);
                                            break;
                                        }
                                    }
                                }

                                // If not found, search cells inside this interface
                                for (AstNode* ifaceStmtp = ifaceModp->stmtsp();
                                     ifaceStmtp && !targetTdp && !targetPtdp; ifaceStmtp = ifaceStmtp->nextp()) {
                                    if (AstCell* const cellp = VN_CAST(ifaceStmtp, Cell)) {
                                        if (cellp->name() == cellName && cellp->modp()) {
                                            for (AstNode* childStmtp = cellp->modp()->stmtsp();
                                                 childStmtp; childStmtp = childStmtp->nextp()) {
                                                if (AstTypedef* const tdp = VN_CAST(childStmtp, Typedef)) {
                                                    if (tdp->name() == typedefName) {
                                                        targetTdp = tdp;
                                                        targetModp = cellp->modp();
                                                        UINFO(5, "DEPGRAPH: found typedef '" << typedefName
                                                                  << "' via iface port '" << varp->name()
                                                                  << "' cell '" << cellName
                                                                  << "' in " << cellp->modp()->name() << endl);
                                                        break;
                                                    }
                                                } else if (AstParamTypeDType* const ptdp = VN_CAST(childStmtp, ParamTypeDType)) {
                                                    if (ptdp->name() == typedefName) {
                                                        targetPtdp = ptdp;
                                                        targetModp = cellp->modp();
                                                        UINFO(5, "DEPGRAPH: found paramtype '" << typedefName
                                                                  << "' via iface port '" << varp->name()
                                                                  << "' cell '" << cellName
                                                                  << "' in " << cellp->modp()->name() << endl);
                                                        break;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }

                // If still not found, recursively search nested interface cells
                // This handles deeply nested paths like sc_io.types.a_if0.a_t
                if (!targetTdp && !targetPtdp) {
                    findTypedefInHierarchy(m_modp, cellName, typedefName, 5,
                                           targetTdp, targetPtdp, targetModp);
                }

                // If still not found, search all existing graph nodes for the typedef or paramtype
                // This handles cases where the typedef is in a deeply nested interface
                if (!targetTdp && !targetPtdp) {
                    for (auto& pair : V3LinkDotDepGraph::s_nodes) {
                        if (pair.second->nodeType == V3LinkDotDepGraph::NodeType::TYPEDEF
                            && pair.second->nodep) {
                            AstTypedef* const tdp = VN_CAST(pair.second->nodep, Typedef);
                            if (tdp && tdp->name() == typedefName) {
                                targetTdp = tdp;
                                targetModp = pair.second->ownerModp;
                                UINFO(9, "DEPGRAPH: found typedef '" << typedefName
                                          << "' via graph search in " << (targetModp ? targetModp->name() : "<null>") << endl);
                                break;
                            }
                        } else if (pair.second->nodeType == V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE
                                   && pair.second->nodep) {
                            AstParamTypeDType* const ptdp = VN_CAST(pair.second->nodep, ParamTypeDType);
                            if (ptdp && ptdp->name() == typedefName) {
                                targetPtdp = ptdp;
                                targetModp = pair.second->ownerModp;
                                UINFO(9, "DEPGRAPH: found paramtype '" << typedefName
                                          << "' via graph search in " << (targetModp ? targetModp->name() : "<null>") << endl);
                                break;
                            }
                        }
                    }
                }

                // Add dependency edge to the found typedef or paramtype
                if (targetTdp && targetModp) {
                    V3LinkDotDepGraph::DepNode* const tdNodep
                        = V3LinkDotDepGraph::findOrCreateNode(
                            targetTdp, V3LinkDotDepGraph::NodeType::TYPEDEF, targetModp);
                    depNodep->dependsOn.insert(tdNodep);
                    UINFO(5, "DEPGRAPH: added edge from paramtype '"
                              << nodep->name() << "' to typedef '"
                              << typedefName << "' in " << targetModp->name() << endl);
                } else if (targetPtdp && targetModp) {
                    V3LinkDotDepGraph::DepNode* const ptdNodep
                        = V3LinkDotDepGraph::findOrCreateNode(
                            targetPtdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, targetModp);
                    depNodep->dependsOn.insert(ptdNodep);
                    UINFO(5, "DEPGRAPH: added edge from paramtype '"
                              << nodep->name() << "' to paramtype '"
                              << typedefName << "' in " << targetModp->name() << endl);
                }
            }
        } else {
            UINFO(9, "DEPGRAPH: paramtype '" << nodep->name()
                      << "' in " << m_modp->name() << " (base=" << baseModName
                      << ") has NO registered cell (map size=" << s_cellAssociations.size() << ")" << endl);
        }

        // Collect dependencies from the subtype
        if (AstNodeDType* const dtypep = nodep->subDTypep()) {
            V3LinkDotDepGraph::collectExpressionDeps(dtypep, depNodep, m_modp);
        }
    }

    void visit(AstCell* nodep) override {
        if (!m_modp) return;
        // Handle cross-module edges: parameter pins connect parent expressions to child params
        AstNodeModule* const childModp = nodep->modp();
        if (!childModp) return;

        for (AstPin* pinp = nodep->pinsp(); pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            if (!pinp->modVarp()) continue;
            AstVar* const childVarp = pinp->modVarp();
            if (!childVarp->isGParam()) continue;

            // Create node for child parameter
            V3LinkDotDepGraph::NodeType childType = V3LinkDotDepGraph::classifyVar(childVarp);
            V3LinkDotDepGraph::DepNode* const childNodep
                = V3LinkDotDepGraph::findOrCreateNode(childVarp, childType, childModp);
            childNodep->cellp = nodep;

            // The child param depends on the pin expression (which may reference parent params/lparams)
            if (AstNode* const exprp = pinp->exprp()) {
                V3LinkDotDepGraph::collectExpressionDeps(exprp, childNodep, m_modp);
            }
        }

        iterateChildrenConst(nodep);
    }

    void visit(AstRefDType* nodep) override {
        if (!m_modp) return;

        V3LinkDotDepGraph::DepNode* const depNodep
            = V3LinkDotDepGraph::findOrCreateNode(nodep, V3LinkDotDepGraph::NodeType::REFDTYPE, m_modp);

        const auto regIt = V3LinkDotDepGraph::s_refDTypeDotPathRegistry.find(nodep);
        if (regIt != V3LinkDotDepGraph::s_refDTypeDotPathRegistry.end()) {
            depNodep->cellName = regIt->second;
        }

        // If the REFDTYPE is a child of a PARAMTYPEDTYPE, try to get the full dotpath from
        // the PARAMTYPE's cell association (which has the complete path like "cca_io.tlb_io")
        if (depNodep->cellName.empty() || depNodep->cellName.find('.') == string::npos) {
            for (AstNode* backp = nodep->backp(); backp; backp = backp->backp()) {
                if (AstParamTypeDType* const parentPtdp = VN_CAST(backp, ParamTypeDType)) {
                    string baseModName = m_modp->name();
                    const size_t suffixPos = baseModName.find("__");
                    if (suffixPos != string::npos) baseModName = baseModName.substr(0, suffixPos);
                    CellAssocKey key{baseModName, parentPtdp->name()};
                    auto assocIt = s_cellAssociations.find(key);
                    if (assocIt != s_cellAssociations.end()) {
                        const size_t colonPos = assocIt->second.find(':');
                        if (colonPos != string::npos) {
                            const string fullCellPath = assocIt->second.substr(0, colonPos);
                            if (!fullCellPath.empty() && fullCellPath.find('.') != string::npos) {
                                depNodep->cellName = fullCellPath;
                                UINFO(5, "DEPGRAPH: refdtype '" << nodep->name()
                                          << "' inherited full dotpath '" << fullCellPath
                                          << "' from parent paramtype '" << parentPtdp->name()
                                          << "'" << endl);
                            }
                        }
                    }
                    break;
                }
                if (VN_IS(backp, NodeModule)) break;
            }
        }

        // If this RefDType points to a typedef, add edge
        if (AstTypedef* const tdp = nodep->typedefp()) {
            AstTypedef* targetTdp = tdp;
            AstNodeModule* tdOwnerp = V3LinkDotDepGraph::findOwnerModule(tdp);
            if (m_modp && tdOwnerp && tdOwnerp->hasGParam()
                && tdOwnerp->name().find("__") == string::npos) {
                for (AstNode* stmtp = m_modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                    AstCell* const cellp = VN_CAST(stmtp, Cell);
                    if (!cellp || !cellp->modp()) continue;
                    if (!VN_IS(cellp->modp(), Iface)) continue;
                    string cellBase = cellp->modp()->name();
                    const size_t suffixPos = cellBase.find("__");
                    if (suffixPos != string::npos) cellBase = cellBase.substr(0, suffixPos);
                    if (cellBase != tdOwnerp->name()) continue;
                    for (AstNode* cellStmtp = cellp->modp()->stmtsp(); cellStmtp;
                         cellStmtp = cellStmtp->nextp()) {
                        if (AstTypedef* const cellTdp = VN_CAST(cellStmtp, Typedef)) {
                            if (cellTdp->name() == tdp->name()) {
                                targetTdp = cellTdp;
                                tdOwnerp = cellp->modp();
                                break;
                            }
                        }
                    }
                    if (targetTdp != tdp) break;
                }
            }
            V3LinkDotDepGraph::DepNode* const tdNodep
                = V3LinkDotDepGraph::findOrCreateNode(targetTdp, V3LinkDotDepGraph::NodeType::TYPEDEF,
                                                      tdOwnerp);
            V3LinkDotDepGraph::addEdge(depNodep, tdNodep);
        }

        // If this RefDType points to a ParamTypeDType, add edge
        if (AstParamTypeDType* const ptdp = VN_CAST(nodep->refDTypep(), ParamTypeDType)) {
            AstParamTypeDType* targetPtdp = ptdp;
            AstNodeModule* ptdOwnerp = V3LinkDotDepGraph::findOwnerModule(ptdp);

            // If the paramtype is defined in a template interface, retarget to a specialized instance
            // based on the dot-lhs cell name (when available).
            if (m_modp && ptdOwnerp && ptdOwnerp->hasGParam()
                && ptdOwnerp->name().find("__") == string::npos) {
                string dotCellName;
                if (!depNodep->cellName.empty()) {
                    dotCellName = depNodep->cellName;
                } else {
                    for (AstNode* backp = nodep->backp(); backp; backp = backp->backp()) {
                        if (AstDot* const dotp = VN_CAST(backp, Dot)) {
                            if (dotp->rhsp() == nodep) {
                                if (AstVarRef* const varrefp = VN_CAST(dotp->lhsp(), VarRef)) {
                                    dotCellName = varrefp->name();
                                    depNodep->cellName = dotCellName;
                                }
                                break;
                            }
                        }
                        if (VN_IS(backp, NodeModule)) break;
                    }
                }

                // Try to resolve dotted path using resolveCellPathModule (handles interface ports)
                if (!dotCellName.empty()) {
                    if (AstNodeModule* const resolvedModp = resolveCellPathModule(m_modp, dotCellName)) {
                        // Check if resolved module base name matches ptdOwnerp
                        string resolvedBase = resolvedModp->name();
                        const size_t suffixPos = resolvedBase.find("__");
                        if (suffixPos != string::npos) resolvedBase = resolvedBase.substr(0, suffixPos);
                        string ptdOwnerBase = ptdOwnerp->name();
                        const size_t ptdSuffixPos = ptdOwnerBase.find("__");
                        if (ptdSuffixPos != string::npos) ptdOwnerBase = ptdOwnerBase.substr(0, ptdSuffixPos);
                        if (resolvedBase == ptdOwnerBase) {
                            for (AstNode* cellStmtp = resolvedModp->stmtsp(); cellStmtp;
                                 cellStmtp = cellStmtp->nextp()) {
                                if (AstParamTypeDType* const cellPtdp = VN_CAST(cellStmtp, ParamTypeDType)) {
                                    if (cellPtdp->name() == ptdp->name()) {
                                        targetPtdp = cellPtdp;
                                        ptdOwnerp = resolvedModp;
                                        UINFO(5, "DEPGRAPH: refdtype '" << nodep->name()
                                                  << "' retargeted via resolveCellPathModule to "
                                                  << resolvedModp->name() << endl);
                                        break;
                                    }
                                }
                            }
                        }
                    }
                }

                // Fallback: search direct cells in current module
                if (targetPtdp == ptdp) {
                    for (AstNode* stmtp = m_modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                        AstCell* const cellp = VN_CAST(stmtp, Cell);
                        if (!cellp || !cellp->modp()) continue;
                        if (!VN_IS(cellp->modp(), Iface)) continue;
                        if (!dotCellName.empty() && cellp->name() != dotCellName) continue;
                        string cellBase = cellp->modp()->name();
                        const size_t suffixPos = cellBase.find("__");
                        if (suffixPos != string::npos) cellBase = cellBase.substr(0, suffixPos);
                        if (cellBase != ptdOwnerp->name()) continue;
                        for (AstNode* cellStmtp = cellp->modp()->stmtsp(); cellStmtp;
                             cellStmtp = cellStmtp->nextp()) {
                            if (AstParamTypeDType* const cellPtdp = VN_CAST(cellStmtp, ParamTypeDType)) {
                                if (cellPtdp->name() == ptdp->name()) {
                                    targetPtdp = cellPtdp;
                                    ptdOwnerp = cellp->modp();
                                    break;
                                }
                            }
                        }
                        if (targetPtdp != ptdp) break;
                    }
                }

                // Fallback: search interface ports in current module
                if (targetPtdp == ptdp && !dotCellName.empty()) {
                    for (AstNode* stmtp = m_modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                        if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                            if (varp->name() != dotCellName) continue;
                            AstIfaceRefDType* ifaceRefp = findIfaceRefDType(varp->dtypep());
                            if (!ifaceRefp) ifaceRefp = findIfaceRefDType(varp->subDTypep());
                            if (!ifaceRefp) ifaceRefp = findIfaceRefDType(varp->childDTypep());
                            if (!ifaceRefp) continue;
                            AstNodeModule* ifaceModp = findConnectedIfaceModpFromPort(m_modp, dotCellName);
                            if (!ifaceModp && ifaceRefp->cellp() && ifaceRefp->cellp()->modp()) {
                                ifaceModp = ifaceRefp->cellp()->modp();
                            }
                            if (!ifaceModp && ifaceRefp->ifacep()) {
                                ifaceModp = ifaceRefp->ifacep();
                            }
                            if (ifaceModp) {
                                string ifaceBase = ifaceModp->name();
                                const size_t suffixPos = ifaceBase.find("__");
                                if (suffixPos != string::npos) ifaceBase = ifaceBase.substr(0, suffixPos);
                                if (ifaceBase == ptdOwnerp->name()) {
                                    for (AstNode* ifaceStmtp = ifaceModp->stmtsp(); ifaceStmtp;
                                         ifaceStmtp = ifaceStmtp->nextp()) {
                                        if (AstParamTypeDType* const ifacePtdp = VN_CAST(ifaceStmtp, ParamTypeDType)) {
                                            if (ifacePtdp->name() == ptdp->name()) {
                                                targetPtdp = ifacePtdp;
                                                ptdOwnerp = ifaceModp;
                                                UINFO(5, "DEPGRAPH: refdtype '" << nodep->name()
                                                          << "' retargeted via iface port to "
                                                          << ifaceModp->name() << endl);
                                                break;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        if (targetPtdp != ptdp) break;
                    }
                }
            }

            V3LinkDotDepGraph::DepNode* const ptdNodep = V3LinkDotDepGraph::findOrCreateNode(
                targetPtdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, ptdOwnerp);
            V3LinkDotDepGraph::addEdge(depNodep, ptdNodep);
        }

        // If this RefDType has an explicit class/package scope, add edge to that typedef/paramtype
        if (AstNodeModule* const scopeModp = nodep->classOrPackagep()) {
            AstNodeModule* searchModp = scopeModp;
            if (AstClassPackage* const pkgp = VN_CAST(scopeModp, ClassPackage)) {
                if (pkgp->classp()) searchModp = pkgp->classp();
            }
            if (searchModp) {
                for (AstNode* stmtp = searchModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                    if (AstTypedef* const tdp = VN_CAST(stmtp, Typedef)) {
                        if (tdp->name() == nodep->name()) {
                            AstNodeModule* const tdOwnerp = V3LinkDotDepGraph::findOwnerModule(tdp);
                            V3LinkDotDepGraph::DepNode* const tdNodep
                                = V3LinkDotDepGraph::findOrCreateNode(
                                    tdp, V3LinkDotDepGraph::NodeType::TYPEDEF, tdOwnerp);
                            V3LinkDotDepGraph::addEdge(depNodep, tdNodep);
                            break;
                        }
                    } else if (AstParamTypeDType* const scopePtdp = VN_CAST(stmtp, ParamTypeDType)) {
                        if (scopePtdp->name() == nodep->name()) {
                            AstNodeModule* const ptdOwnerp = V3LinkDotDepGraph::findOwnerModule(scopePtdp);
                            V3LinkDotDepGraph::DepNode* const ptdNodep
                                = V3LinkDotDepGraph::findOrCreateNode(
                                    scopePtdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, ptdOwnerp);
                            V3LinkDotDepGraph::addEdge(depNodep, ptdNodep);
                            break;
                        }
                    }
                }
            }
        }
    }

    // Visit struct/union types to track their member RefDType dependencies
    void visit(AstStructDType* nodep) override {
        if (!m_modp) return;
        V3LinkDotDepGraph::DepNode* const depNodep = V3LinkDotDepGraph::findOrCreateNode(
            nodep, V3LinkDotDepGraph::NodeType::STRUCTDTYPE, m_modp);

        // Add dependency edges to member RefDTypes
        for (AstMemberDType* memp = nodep->membersp(); memp;
             memp = VN_AS(memp->nextp(), MemberDType)) {
            if (AstRefDType* const refp = VN_CAST(memp->subDTypep(), RefDType)) {
                AstNodeModule* const refOwnerp = V3LinkDotDepGraph::findOwnerModule(refp);
                V3LinkDotDepGraph::DepNode* const refNodep = V3LinkDotDepGraph::findOrCreateNode(
                    refp, V3LinkDotDepGraph::NodeType::REFDTYPE, refOwnerp ? refOwnerp : m_modp);
                V3LinkDotDepGraph::addEdge(depNodep, refNodep);
                // Debug: show what the RefDType points to
                AstNodeDType* const targetp = refp->refDTypep();
                UINFO(5, "DEPGRAPH: struct '" << nodep->name() << "' member '" << memp->name()
                          << "' -> refdtype '" << refp->name() << "' -> "
                          << (targetp ? targetp->prettyTypeName() : "<null>")
                          << " w" << (targetp ? targetp->width() : 0) << endl);
            }
        }
        UINFO(5, "DEPGRAPH: STRUCTDTYPE '" << nodep->name() << "' in " << m_modp->name()
                  << " w" << nodep->width() << " deps=" << depNodep->dependsOn.size() << endl);
        iterateChildrenConst(nodep);
    }

    void visit(AstUnionDType* nodep) override {
        if (!m_modp) return;
        V3LinkDotDepGraph::DepNode* const depNodep = V3LinkDotDepGraph::findOrCreateNode(
            nodep, V3LinkDotDepGraph::NodeType::UNIONDTYPE, m_modp);

        // Add dependency edges to member RefDTypes
        for (AstMemberDType* memp = nodep->membersp(); memp;
             memp = VN_AS(memp->nextp(), MemberDType)) {
            if (AstRefDType* const refp = VN_CAST(memp->subDTypep(), RefDType)) {
                AstNodeModule* const refOwnerp = V3LinkDotDepGraph::findOwnerModule(refp);
                V3LinkDotDepGraph::DepNode* const refNodep = V3LinkDotDepGraph::findOrCreateNode(
                    refp, V3LinkDotDepGraph::NodeType::REFDTYPE, refOwnerp ? refOwnerp : m_modp);
                V3LinkDotDepGraph::addEdge(depNodep, refNodep);
                // Debug: show what the RefDType points to
                AstNodeDType* const targetp = refp->refDTypep();
                UINFO(5, "DEPGRAPH: union '" << nodep->name() << "' member '" << memp->name()
                          << "' -> refdtype '" << refp->name() << "' -> "
                          << (targetp ? targetp->prettyTypeName() : "<null>")
                          << " w" << (targetp ? targetp->width() : 0) << endl);
            }
        }
        UINFO(5, "DEPGRAPH: UNIONDTYPE '" << nodep->name() << "' in " << m_modp->name()
                  << " w" << nodep->width() << " deps=" << depNodep->dependsOn.size() << endl);
        iterateChildrenConst(nodep);
    }

    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    explicit DepGraphBuildVisitor(AstNetlist* netlistp) {
        iterateConst(netlistp);
    }
};

void V3LinkDotDepGraph::build(AstNetlist* netlistp) {
    if (!s_enabled && !s_useInParam) return;
    UINFO(5, "DEPGRAPH: building dependency graph" << endl);
    reset();
    DepGraphBuildVisitor{netlistp};
    UINFO(5, "DEPGRAPH: built " << s_allNodes.size() << " nodes" << endl);
}

void V3LinkDotDepGraph::clearResolved() {
    for (DepNode* nodep : s_allNodes) {
        if (!nodep) continue;
        nodep->resolved = false;
        nodep->resolvedIteration = 0;
    }
}

//======================================================================
// Resolution - helper to re-evaluate a single node

void V3LinkDotDepGraph::reEvaluateNode(DepNode* nodep) {
    if (!nodep || !nodep->nodep) return;

    // Skip nodes in dead/template modules - only process specialized modules
    AstNodeModule* const ownerModp = nodep->ownerModp;
    if (ownerModp) {
        if (ownerModp->dead()) {
            UINFO(9, "DEPGRAPH: skip re-evaluate '" << nodeName(nodep)
                      << "' in dead module " << ownerModp->name() << endl);
            return;
        }
        // Skip template modules (unspecialized) - they have params but no __ suffix
        const bool hasSpecSuffix = ownerModp->name().find("__") != string::npos;
        if (!hasSpecSuffix && ownerModp->hasGParam()) {
            UINFO(9, "DEPGRAPH: skip re-evaluate '" << nodeName(nodep)
                      << "' in template module (GParam) " << ownerModp->name() << endl);
            return;
        }
    }

    if (nodep->nodeType == NodeType::TYPEDEF) {
        AstTypedef* const tdp = VN_CAST(nodep->nodep, Typedef);
        if (!tdp) return;

        if (AstRefDType* const refp = VN_CAST(tdp->subDTypep(), RefDType)) {
            if (!refp->subDTypep() && !refp->typedefp() && !refp->refDTypep()) {
                UINFO(5, "DEPGRAPH: skip re-evaluate typedef '" << tdp->name()
                          << "' in " << nodeOwnerName(nodep)
                          << " (unlinked refdtype)" << endl);
                return;
            }
        }

        // Relink VarRefs inside typedef's subDTypep to point to cloned parameters.
        // When an interface is cloned, VarRefs in struct member width expressions
        // (like $clog2(cfg.CCNumWaves) in pad0) still point to the template's parameter.
        // We need to relink them to the specialized module's parameter.
        if (ownerModp && tdp->subDTypep()) {
            // Build a map of parameter names to their Var nodes in the specialized module
            std::unordered_map<string, AstVar*> paramsByName;
            for (AstNode* stmtp = ownerModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                    if (varp->isGParam() || varp->isParam()) {
                        paramsByName[varp->name()] = varp;
                    }
                }
            }

            // Walk the typedef's subDTypep and relink VarRefs to cloned parameters
            tdp->subDTypep()->foreach([&](AstVarRef* refp) {
                AstVar* const oldVarp = refp->varp();
                if (!oldVarp) return;
                // Check if this VarRef points to a parameter in a different (template) module
                AstNodeModule* const varOwnerp = findOwnerModule(oldVarp);
                if (varOwnerp && varOwnerp != ownerModp
                    && (oldVarp->isGParam() || oldVarp->isParam())) {
                    // Try to find the corresponding parameter in the specialized module
                    auto it = paramsByName.find(oldVarp->name());
                    if (it != paramsByName.end() && it->second != oldVarp) {
                        UINFO(5, "DEPGRAPH: relink VarRef '" << oldVarp->name()
                                  << "' from template '" << varOwnerp->name()
                                  << "' to specialized '" << ownerModp->name()
                                  << "' in typedef '" << tdp->name() << "'" << endl);
                        refp->varp(it->second);
                    }
                }
            });
        }

        const int oldWidth = tdp->subDTypep() ? tdp->subDTypep()->width() : 0;

        // Clear the didWidth flag to force re-widthing
        tdp->didWidth(false);
        if (tdp->subDTypep()) tdp->subDTypep()->didWidth(false);

        // Re-run width calculation
        V3Width::widthParamsEdit(tdp);

        const int newWidth = tdp->subDTypep() ? tdp->subDTypep()->width() : 0;

        if (oldWidth != newWidth) {
            UINFO(5, "DEPGRAPH: re-evaluated typedef '" << tdp->name()
                      << "' width " << oldWidth << " -> " << newWidth
                      << " in " << nodeOwnerName(nodep) << endl);
        }

        // For ClassRefDType typedefs, ensure any references use the correct specialized class
        // This is the "update" phase of capture->resolve->update for class typedefs
        if (AstClassRefDType* const crdtp = VN_CAST(tdp->subDTypep(), ClassRefDType)) {
            if (AstClass* const classp = crdtp->classp()) {
                // Check if this matches our registered mapping
                AstClass* const registeredClassp = findTypedefClass(ownerModp->name(), tdp->name());
                if (registeredClassp && registeredClassp != classp) {
                    // Update the ClassRefDType to point to the registered class
                    UINFO(5, "DEPGRAPH: updating typedef '" << tdp->name()
                              << "' ClassRefDType from '" << classp->name()
                              << "' to '" << registeredClassp->name() << "'" << endl);
                    crdtp->classp(registeredClassp);
                }
                // Also update any RefDTypes in ownerModp that reference this typedef
                // to have the correct classOrPackagep
                if (ownerModp) {
                    AstClass* const targetClassp = registeredClassp ? registeredClassp : classp;
                    ownerModp->foreach([tdp, targetClassp](AstRefDType* refp) {
                        if (refp->typedefp() == tdp) {
                            if (refp->classOrPackagep() != targetClassp) {
                                UINFO(5, "DEPGRAPH: updating RefDType classOrPackagep for '"
                                          << refp->name() << "' to '" << targetClassp->name()
                                          << "'" << endl);
                                refp->classOrPackagep(targetClassp);
                            }
                        }
                    });
                    // Also update FUNCREFs that call methods through this typedef
                    // (e.g., type_id::get() where type_id is this typedef)
                    ownerModp->foreach([targetClassp](AstNodeFTaskRef* ftaskRefp) {
                        // Check if this FUNCREF's classOrPackagep points to a class
                        // that should be updated based on typedef
                        if (AstClass* const funcClassp
                            = VN_CAST(ftaskRefp->classOrPackagep(), Class)) {
                            // If the FUNCREF is calling a method in a parameterized class
                            // that matches our typedef's target, update it
                            if (funcClassp != targetClassp) {
                                // Check if funcClassp is the template version of targetClassp
                                const string funcName = funcClassp->name();
                                const string targetName = targetClassp->name();
                                // Strip specialization suffix to compare base names
                                const size_t funcSuffix = funcName.find("__");
                                const size_t targetSuffix = targetName.find("__");
                                const string funcBase
                                    = (funcSuffix != string::npos) ? funcName.substr(0, funcSuffix)
                                                                   : funcName;
                                const string targetBase = (targetSuffix != string::npos)
                                                              ? targetName.substr(0, targetSuffix)
                                                              : targetName;
                                if (funcBase == targetBase && funcSuffix != string::npos
                                    && targetSuffix != string::npos) {
                                    UINFO(5, "DEPGRAPH: updating FUNCREF classOrPackagep from '"
                                              << funcClassp->name() << "' to '"
                                              << targetClassp->name() << "'" << endl);
                                    ftaskRefp->classOrPackagep(targetClassp);
                                    // Also update taskp to point to method in new class
                                    if (AstNodeFTask* const oldTaskp = ftaskRefp->taskp()) {
                                        // Find matching function in target class by name
                                        for (AstNode* stmtp = targetClassp->stmtsp(); stmtp;
                                             stmtp = stmtp->nextp()) {
                                            if (AstNodeFTask* const newTaskp
                                                = VN_CAST(stmtp, NodeFTask)) {
                                                if (newTaskp->name() == oldTaskp->name()) {
                                                    ftaskRefp->taskp(newTaskp);
                                                    break;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    });
                }
            }
        }
    } else if (nodep->nodeType == NodeType::PARAMTYPEDTYPE) {
        AstParamTypeDType* const ptdp = VN_CAST(nodep->nodep, ParamTypeDType);
        if (!ptdp) return;

        // Find the typedef or resolved PARAMTYPEDTYPE from our dependency edges
        // This is critical for sibling instances with different parameters
        AstNodeDType* targetDTypep = nullptr;
        AstTypedef* targetTypedefp = nullptr;
        string targetName;
        for (DepNode* const depNodep : nodep->dependsOn) {
            if (depNodep->nodeType == NodeType::TYPEDEF) {
                AstTypedef* const tdp = VN_CAST(depNodep->nodep, Typedef);
                if (tdp && tdp->subDTypep()) {
                    targetDTypep = tdp->subDTypep();
                    targetTypedefp = tdp;
                    targetName = tdp->name();
                    UINFO(5, "DEPGRAPH: found typedef '" << targetName
                              << "' via dependency edge for paramtype '" << ptdp->name()
                              << "' in " << nodeOwnerName(nodep) << endl);
                    break;
                }
            } else if (depNodep->nodeType == NodeType::PARAMTYPEDTYPE) {
                // Follow PARAMTYPEDTYPE dependency - get its resolved dtype
                AstParamTypeDType* const depPtdp = VN_CAST(depNodep->nodep, ParamTypeDType);
                if (depPtdp && depPtdp->subDTypep() && depNodep->resolved) {
                    targetDTypep = depPtdp->subDTypep();
                    targetName = depPtdp->name();
                    UINFO(5, "DEPGRAPH: found paramtype '" << targetName
                              << "' via dependency edge for paramtype '" << ptdp->name()
                              << "' in " << nodeOwnerName(nodep) << endl);
                    break;
                }
            }
        }

        // If no dependency edge found, check for captured type binding from V3Param
        if (!targetDTypep && nodep->origExprp) {
            if (AstNodeDType* const boundDTypep = VN_CAST(nodep->origExprp, NodeDType)) {
                targetDTypep = boundDTypep;
                targetName = boundDTypep->prettyDTypeName(true);
                UINFO(5, "DEPGRAPH: found captured type binding '" << targetName
                          << "' for paramtype '" << ptdp->name()
                          << "' in " << nodeOwnerName(nodep) << endl);
            }
        }

        if (targetDTypep) {
            // Update the PARAMTYPEDTYPE to reference the resolved dtype
            ptdp->dtypep(targetDTypep);
            nodep->resolvedWidth = targetDTypep->width();
            UINFO(5, "DEPGRAPH: updated paramtype '" << ptdp->name()
                      << "' dtypep to '" << targetName
                      << "' (width=" << targetDTypep->width() << ")"
                      << " in " << nodeOwnerName(nodep) << endl);

            // If the paramtype has a required type RefDType, retarget it to the same typedef
            if (targetTypedefp) {
                if (AstRequireDType* const reqp
                    = VN_CAST(ptdp->getChildDTypep(), RequireDType)) {
                    if (AstRefDType* const refp = VN_CAST(reqp->lhsp(), RefDType)) {
                        if (refp->typedefp() != targetTypedefp) {
                            UINFO(5, "DEPGRAPH: updated paramtype '" << ptdp->name()
                                      << "' required-type RefDType typedefp to '"
                                      << targetTypedefp->name() << "' in "
                                      << nodeOwnerName(nodep) << endl);
                            refp->refDTypep(nullptr);
                            refp->typedefp(targetTypedefp);
                        }
                    }
                }
            }

            // The childDTypep (RequireDType) is normally removed after dtype resolution.
            // The RefDType inside it was already retargeted above, so safe to delete.
            if (AstNodeDType* const childp = ptdp->getChildDTypep()) {
                UINFO(5, "DEPGRAPH: removing paramtype childDTypep for '" << ptdp->name()
                          << "' in " << nodeOwnerName(nodep) << endl);
                childp->unlinkFrBack();
                ptdp->childDTypep(nullptr);
                VL_DO_DANGLING(childp->deleteTree(), childp);
            }
        } else {
            UINFO(9, "DEPGRAPH: no resolved dependency for paramtype '" << ptdp->name()
                      << "' in " << nodeOwnerName(nodep) << endl);
        }
    } else if (nodep->nodeType == NodeType::REFDTYPE) {
        AstRefDType* const rdp = VN_CAST(nodep->nodep, RefDType);
        if (!rdp) return;

        // Skip RefDTypes with null owner (e.g., in TYPETABLE).
        // These are global types that shouldn't be retargeted to module-local typedefs
        // which may be deleted when dead modules are removed.
        if (!nodep->ownerModp) {
            UINFO(5, "DEPGRAPH: skip retarget refdtype '" << rdp->name()
                      << "' - null owner module" << endl);
            return;
        }

        for (DepNode* const depNodep : nodep->dependsOn) {
            if (depNodep->nodeType == NodeType::TYPEDEF) {
                if (AstTypedef* const tdp = VN_CAST(depNodep->nodep, Typedef)) {
                    AstTypedef* targetTdp = tdp;
                    if (AstNodeModule* const tdOwnerp = findOwnerModule(tdp)) {
                        if (tdOwnerp->hasGParam() && tdOwnerp->name().find("__") == string::npos) {
                            AstNode* const cloneNodep = tdp->clonep();
                            if (AstTypedef* const cloneTdp = VN_CAST(cloneNodep, Typedef)) {
                                AstNodeModule* const cloneOwnerp = findOwnerModule(cloneTdp);
                                if (cloneOwnerp && cloneOwnerp != tdOwnerp) {
                                    UINFO(5, "DEPGRAPH: refdtype '" << rdp->name()
                                              << "' typedef target is template '" << tdOwnerp->name()
                                              << "', using clone in '" << cloneOwnerp->name() << "'" << endl);
                                    targetTdp = cloneTdp;
                                }
                            } else {
                                // clonep() failed, search graph for specialized typedef
                                for (const auto& entry : s_nodes) {
                                    DepNode* const searchNodep = entry.second;
                                    if (searchNodep->nodeType == NodeType::TYPEDEF
                                        && searchNodep != depNodep) {
                                        if (AstTypedef* const searchTdp
                                            = VN_CAST(searchNodep->nodep, Typedef)) {
                                            if (searchTdp->name() == tdp->name()) {
                                                AstNodeModule* const searchOwnerp
                                                    = findOwnerModule(searchTdp);
                                                if (searchOwnerp
                                                    && searchOwnerp->name().find(
                                                           tdOwnerp->name() + "__")
                                                           != string::npos) {
                                                    UINFO(5, "DEPGRAPH: refdtype '"
                                                              << rdp->name()
                                                              << "' typedef target is template '"
                                                              << tdOwnerp->name()
                                                              << "', found specialized clone in '"
                                                              << searchOwnerp->name() << "'"
                                                              << endl);
                                                    targetTdp = searchTdp;
                                                    break;
                                                }
                                            }
                                        }
                                    }
                                }
                                if (targetTdp == tdp) {
                                    UINFO(5, "DEPGRAPH: refdtype '" << rdp->name()
                                              << "' typedef target is template '"
                                              << tdOwnerp->name() << "' with no clone" << endl);
                                }
                            }
                        }
                    }
                    const bool needsUpdate = (rdp->typedefp() != targetTdp) || rdp->refDTypep();
                    if (needsUpdate) {
                        rdp->refDTypep(nullptr);
                        rdp->typedefp(targetTdp);
                        rdp->dtypep(nullptr);  // Clear stale dtypep to avoid broken link
                        rdp->didWidth(false);
                        // Update classOrPackagep to point to the specialized class
                        // (like IfaceCapture::replaceTypedef does for CLASS captures)
                        AstNodeModule* const targetOwnerp = findOwnerModule(targetTdp);
                        if (AstClass* const targetClassp = VN_CAST(targetOwnerp, Class)) {
                            rdp->classOrPackagep(targetClassp);
                            UINFO(5, "DEPGRAPH: retarget refdtype '" << rdp->name()
                                      << "' classOrPackagep to class '" << targetClassp->name()
                                      << "'" << endl);
                        }
                        UINFO(5, "DEPGRAPH: retarget refdtype '" << rdp->name()
                                  << "' typedefp to '" << targetTdp->name() << "' in "
                                  << nodeOwnerName(nodep) << endl);
                    }
                }
                break;
            } else if (depNodep->nodeType == NodeType::PARAMTYPEDTYPE) {
                if (AstParamTypeDType* const ptdp = VN_CAST(depNodep->nodep, ParamTypeDType)) {
                    AstParamTypeDType* targetPtdp = ptdp;
                    AstNodeModule* const ptdOwnerp = depNodep->ownerModp;

                    UINFO(5, "DEPGRAPH: REFDTYPE-RESOLVE '" << rdp->name()
                              << "'@" << nodeOwnerName(nodep)
                              << " dep->" << ptdp->name() << "@"
                              << (ptdOwnerp ? ptdOwnerp->name() : "<null>")
                              << " cellName='" << nodep->cellName << "'"
                              << " hasGParam=" << (ptdOwnerp ? ptdOwnerp->hasGParam() : false)
                              << " hasSuffix=" << (ptdOwnerp && ptdOwnerp->name().find("__") != string::npos)
                              << endl);

                    // If the dependency points to a template PARAMTYPEDTYPE, find the specialized one
                    // based on the REFDTYPE's context (its owner module and cell path)
                    if (ptdOwnerp && ptdOwnerp->hasGParam()
                        && ptdOwnerp->name().find("__") == string::npos) {
                        // The dependency is to a template - need to find specialized version
                        // Use the cellName from the REFDTYPE node to resolve the correct path
                        string cellPath = nodep->cellName;
                        UINFO(5, "DEPGRAPH: REFDTYPE-RESOLVE template detected, initial cellPath='"
                                  << cellPath << "'" << endl);
                        if (cellPath.empty()) {
                            // Try to get from parent PARAMTYPE's cell association
                            for (AstNode* backp = rdp->backp(); backp; backp = backp->backp()) {
                                UINFO(9, "DEPGRAPH: REFDTYPE-RESOLVE walking backp: "
                                          << backp->typeName() << endl);
                                if (AstParamTypeDType* const parentPtdp = VN_CAST(backp, ParamTypeDType)) {
                                    string baseModName = ownerModp ? ownerModp->name() : "";
                                    const size_t suffixPos = baseModName.find("__");
                                    if (suffixPos != string::npos) baseModName = baseModName.substr(0, suffixPos);
                                    CellAssocKey key{baseModName, parentPtdp->name()};
                                    auto assocIt = s_cellAssociations.find(key);
                                    UINFO(5, "DEPGRAPH: REFDTYPE-RESOLVE parent PARAMTYPE '"
                                              << parentPtdp->name() << "' baseModName='" << baseModName
                                              << "' assoc " << (assocIt != s_cellAssociations.end() ? "HIT" : "MISS")
                                              << (assocIt != s_cellAssociations.end() ? (" -> " + assocIt->second) : "")
                                              << endl);
                                    if (assocIt != s_cellAssociations.end()) {
                                        const size_t colonPos = assocIt->second.find(':');
                                        if (colonPos != string::npos) {
                                            cellPath = assocIt->second.substr(0, colonPos);
                                            UINFO(5, "DEPGRAPH: REFDTYPE-RESOLVE extracted cellPath='"
                                                      << cellPath << "'" << endl);
                                        }
                                    }
                                    break;
                                }
                                if (VN_IS(backp, NodeModule)) break;
                            }
                        }

                        UINFO(5, "DEPGRAPH: REFDTYPE-RESOLVE final cellPath='" << cellPath
                                  << "' ownerModp=" << (ownerModp ? ownerModp->name() : "<null>") << endl);

                        if (!cellPath.empty() && ownerModp) {
                            // Resolve the cell path to get the specialized interface module
                            AstNodeModule* const resolvedModp = resolveCellPathModule(ownerModp, cellPath);
                            UINFO(5, "DEPGRAPH: REFDTYPE-RESOLVE resolveCellPathModule('"
                                      << ownerModp->name() << "', '" << cellPath << "') -> "
                                      << (resolvedModp ? resolvedModp->name() : "<null>") << endl);
                            if (resolvedModp) {
                                // Check if resolved module is a specialization of ptdOwnerp
                                string resolvedBase = resolvedModp->name();
                                const size_t suffixPos = resolvedBase.find("__");
                                if (suffixPos != string::npos) resolvedBase = resolvedBase.substr(0, suffixPos);
                                UINFO(5, "DEPGRAPH: REFDTYPE-RESOLVE resolvedBase='" << resolvedBase
                                          << "' ptdOwnerp='" << ptdOwnerp->name() << "' match="
                                          << (resolvedBase == ptdOwnerp->name()) << endl);
                                if (resolvedBase == ptdOwnerp->name()) {
                                    // Found specialized interface - find the PARAMTYPEDTYPE in it
                                    for (AstNode* stmtp = resolvedModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                                        if (AstParamTypeDType* const specPtdp = VN_CAST(stmtp, ParamTypeDType)) {
                                            if (specPtdp->name() == ptdp->name()) {
                                                targetPtdp = specPtdp;
                                                UINFO(5, "DEPGRAPH: refdtype '" << rdp->name()
                                                          << "' paramtype target is template '"
                                                          << ptdOwnerp->name()
                                                          << "', resolved via cellPath '" << cellPath
                                                          << "' to specialized '" << resolvedModp->name()
                                                          << "'" << endl);
                                                break;
                                            }
                                        }
                                    }
                                }
                            }
                        }

                        // Fallback: search graph for specialized PARAMTYPEDTYPE
                        if (targetPtdp == ptdp) {
                            for (const auto& entry : s_nodes) {
                                DepNode* const searchNodep = entry.second;
                                if (searchNodep->nodeType == NodeType::PARAMTYPEDTYPE
                                    && searchNodep != depNodep) {
                                    if (AstParamTypeDType* const searchPtdp
                                        = VN_CAST(searchNodep->nodep, ParamTypeDType)) {
                                        if (searchPtdp->name() == ptdp->name()) {
                                            AstNodeModule* const searchOwnerp = searchNodep->ownerModp;
                                            if (searchOwnerp
                                                && searchOwnerp->name().find(ptdOwnerp->name() + "__")
                                                       != string::npos) {
                                                // Found a specialized version - but which one?
                                                // Need to match based on the owner module's suffix
                                                if (ownerModp) {
                                                    // Extract suffix from owner module
                                                    const size_t ownerSuffixPos = ownerModp->name().find("__");
                                                    if (ownerSuffixPos != string::npos) {
                                                        const string ownerSuffix = ownerModp->name().substr(ownerSuffixPos);
                                                        // Check if search owner has matching suffix components
                                                        if (searchOwnerp->name().find(ownerSuffix.substr(0, ownerSuffix.find('_', 2) + 1)) != string::npos
                                                            || ownerSuffix.find(searchOwnerp->name().substr(searchOwnerp->name().find("__"))) != string::npos) {
                                                            targetPtdp = searchPtdp;
                                                            UINFO(5, "DEPGRAPH: refdtype '" << rdp->name()
                                                                      << "' paramtype target is template '"
                                                                      << ptdOwnerp->name()
                                                                      << "', found specialized in '"
                                                                      << searchOwnerp->name() << "'" << endl);
                                                            break;
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }

                    const bool needsUpdate = (rdp->refDTypep() != targetPtdp) || rdp->typedefp();
                    if (needsUpdate) {
                        rdp->typedefp(nullptr);
                        rdp->refDTypep(targetPtdp);
                        rdp->dtypep(nullptr);  // Clear stale dtypep to avoid broken link
                        rdp->didWidth(false);
                        UINFO(5, "DEPGRAPH: retarget refdtype '" << rdp->name()
                                  << "' refDTypep to '" << targetPtdp->name() << "' in "
                                  << nodeOwnerName(nodep) << endl);
                    }
                }
                break;
            }
        }
    } else if (nodep->nodeType == NodeType::GPARAM || nodep->nodeType == NodeType::LPARAM) {
        AstVar* const varp = VN_CAST(nodep->nodep, Var);
        if (!varp) return;
        if (nodep->origExprp) {
            if (varp->valuep()) varp->valuep()->unlinkFrBack()->deleteTree();
            varp->valuep(nodep->origExprp->cloneTree(false));
        }
        if (!varp->valuep()) return;

        if (ownerModp) {
            const auto resolveXRef = [&](AstVarXRef* xrefp) -> AstVar* {
                if (!xrefp || xrefp->dotted().empty()) return nullptr;
                const string dotted = xrefp->dotted();
                const size_t firstDot = dotted.find('.');
                const string cellName = firstDot == string::npos
                                            ? dotted
                                            : dotted.substr(0, firstDot);
                const string rest = firstDot == string::npos ? "" : dotted.substr(firstDot + 1);
                if (cellName.empty()) return nullptr;
                AstNodeModule* ifaceModp = findConnectedIfaceModpFromPort(ownerModp, cellName);
                if (!ifaceModp) {
                    for (AstNode* stmtp = ownerModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                        if (AstCell* const cellp = VN_CAST(stmtp, Cell)) {
                            if (cellp->name() == cellName && cellp->modp()) {
                                ifaceModp = cellp->modp();
                                break;
                            }
                        }
                    }
                }
                if (!ifaceModp) return nullptr;
                AstNodeModule* searchModp = ifaceModp;
                if (!rest.empty()) {
                    const size_t nextDot = rest.find('.');
                    const string innerCell = nextDot == string::npos
                                                 ? rest
                                                 : rest.substr(0, nextDot);
                    for (AstNode* stmtp = ifaceModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                        if (AstCell* const cellp = VN_CAST(stmtp, Cell)) {
                            if (cellp->name() == innerCell && cellp->modp()) {
                                searchModp = cellp->modp();
                                break;
                            }
                        }
                    }
                }
                for (AstNode* stmtp = searchModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                    if (AstVar* const candp = VN_CAST(stmtp, Var)) {
                        if (candp->name() == xrefp->name()) return candp;
                    }
                }
                return nullptr;
            };
            varp->valuep()->foreach([&](AstVarXRef* xrefp) {
                if (AstVar* const resolvedp = resolveXRef(xrefp)) xrefp->varp(resolvedp);
            });
        }

        varp->didWidth(false);
        if (AstNode* const valuep = varp->valuep()) valuep->didWidth(false);
        V3Width::widthParamsEdit(varp);
        V3Const::constifyParamsEdit(varp);
    }
    // GPARAM and LPARAM values are already computed by V3Param, no need to re-evaluate
}

//======================================================================
// Resolution

int V3LinkDotDepGraph::resolve() {
    if (!s_enabled && !s_useInParam) return 0;
    UINFO(5, "DEPGRAPH: starting iterative resolution" << endl);

    s_iterationCount = 0;
    bool changed = true;

    while (changed) {
        changed = false;
        ++s_iterationCount;
        UINFO(9, "DEPGRAPH: iteration " << s_iterationCount << endl);

        for (DepNode* nodep : s_allNodes) {
            if (nodep->resolved) continue;

            // Check if all dependencies are resolved
            bool allDepsResolved = true;
            for (DepNode* depp : nodep->dependsOn) {
                if (!depp->resolved) {
                    allDepsResolved = false;
                    break;
                }
            }

            if (allDepsResolved) {
                // Re-evaluate this node now that its dependencies are resolved
                reEvaluateNode(nodep);

                // Mark as resolved
                nodep->resolved = true;
                nodep->resolvedIteration = s_iterationCount;
                changed = true;
                UINFO(9, "DEPGRAPH: resolved '" << nodeName(nodep) << "'@" << nodeOwnerName(nodep)
                          << " in iteration " << s_iterationCount << endl);
            }
        }

        // Safety check for cycles
        if (s_iterationCount > 1000) {
            v3warn(E_UNSUPPORTED, "Dependency graph resolution exceeded 1000 iterations - possible cycle");
            break;
        }
    }

    UINFO(5, "DEPGRAPH: resolution complete in " << s_iterationCount << " iterations" << endl);

    // Check for unresolved nodes
    int unresolvedCount = 0;
    for (DepNode* nodep : s_allNodes) {
        if (!nodep->resolved) {
            ++unresolvedCount;
            UINFO(9, "DEPGRAPH: unresolved node '" << nodeName(nodep) << "'@"
                      << nodeOwnerName(nodep) << endl);
        }
    }
    if (unresolvedCount > 0) {
        UINFO(5, "DEPGRAPH: " << unresolvedCount << " unresolved nodes (possible cycles)" << endl);
    }

    if (debug() >= 5) {
        UINFO(1, "DEPGRAPH: ========== REFDTYPE RESOLUTION SUMMARY ==========" << endl);
        for (DepNode* const nodep : s_allNodes) {
            if (!nodep || nodep->nodeType != NodeType::REFDTYPE) continue;
            if (!nodep->resolved) continue;
            AstRefDType* const rdp = VN_CAST(nodep->nodep, RefDType);
            if (!rdp) continue;
            string target;
            if (AstTypedef* const tdp = rdp->typedefp()) {
                AstNodeModule* const tdOwnerp = findOwnerModule(tdp);
                target = string{"typedef "} + tdp->name() + "@"
                         + (tdOwnerp ? tdOwnerp->name() : "<null>");
            } else if (AstParamTypeDType* const ptdp = VN_CAST(rdp->refDTypep(), ParamTypeDType)) {
                AstNodeModule* const ptOwnerp = findOwnerModule(ptdp);
                target = string{"paramtype "} + ptdp->name() + "@"
                         + (ptOwnerp ? ptOwnerp->name() : "<null>");
            }
            UINFO(1, "DEPGRAPH: RESOLVED REFDTYPE " << nodeName(nodep)
                      << "@" << nodeOwnerName(nodep) << " -> "
                      << (target.empty() ? "<unlinked>" : target) << endl);
            if (rdp->typedefp() && rdp->refDTypep()) {
                UINFO(1, "DEPGRAPH: WARNING refdtype has both typedefp and refDTypep set: "
                          << nodeName(nodep) << "@" << nodeOwnerName(nodep) << endl);
            }
        }
        UINFO(1, "DEPGRAPH: ========== END REFDTYPE SUMMARY ==========" << endl);
    }

    return s_iterationCount;
}

//======================================================================
// Apply - update RefDType pointers after resolution

int V3LinkDotDepGraph::apply() {
    if (!s_enabled && !s_useInParam) return 0;
    UINFO(5, "DEPGRAPH: applying - updating RefDType pointers" << endl);

    int updatedCount = 0;

    for (DepNode* const nodep : s_allNodes) {
        if (!nodep || nodep->resolved) continue;
        if (nodep->nodeType != NodeType::REFDTYPE) continue;
        if (nodep->dependsOn.empty()) continue;
        // Skip null-owner RefDTypes (TYPETABLE) to avoid dangling pointers
        if (!nodep->ownerModp) continue;
        AstRefDType* const rdp = VN_CAST(nodep->nodep, RefDType);
        if (!rdp) continue;

        // Find the correct typedef or paramtype from the dependencies
        for (DepNode* depp : nodep->dependsOn) {
            if (depp->nodeType == NodeType::TYPEDEF) {
                AstTypedef* const tdp = VN_CAST(depp->nodep, Typedef);
                if (tdp && rdp->typedefp() != tdp) {
                    UINFO(9, "DEPGRAPH: updating RefDType '" << rdp->name()
                              << "' typedefp from '"
                              << (rdp->typedefp() ? rdp->typedefp()->name() : "<null>")
                              << "' to '" << tdp->name() << "'" << endl);
                    rdp->typedefp(tdp);
                    ++updatedCount;
                }
            } else if (depp->nodeType == NodeType::PARAMTYPEDTYPE) {
                AstParamTypeDType* const ptdp = VN_CAST(depp->nodep, ParamTypeDType);
                if (ptdp && rdp->refDTypep() != ptdp) {
                    UINFO(9, "DEPGRAPH: updating RefDType '" << rdp->name()
                              << "' refDTypep from '"
                              << (rdp->refDTypep() ? rdp->refDTypep()->name() : "<null>")
                              << "' to '" << ptdp->name() << "'" << endl);
                    rdp->refDTypep(ptdp);
                    ++updatedCount;
                }
            }
        }
    }

    // First pass: clear stale refDTypep for RefDTypes inside specialized modules
    // that already have correct typedefp. During cloning, both pointers may get set,
    // but we only need typedefp when it points to a typedef in the same specialized module.
    int staleRefFixCount = 0;
    for (DepNode* const rdNodep : s_allNodes) {
        if (!rdNodep || rdNodep->nodeType != NodeType::REFDTYPE) continue;
        AstRefDType* const rdp = VN_CAST(rdNodep->nodep, RefDType);
        if (!rdp) continue;
        if (!rdp->typedefp() || !rdp->refDTypep()) continue;  // Only if both are set

        // Check if typedefp is in a specialized module
        AstNodeModule* const tdOwnerp = findOwnerModule(rdp->typedefp());
        if (tdOwnerp && tdOwnerp->name().find("__") != string::npos) {
            // typedefp is correct (in specialized module), clear stale refDTypep
            UINFO(5, "DEPGRAPH: clearing stale refDTypep for '" << rdp->name()
                      << "' in specialized module '" << tdOwnerp->name() << "'" << endl);
            rdp->refDTypep(nullptr);
            rdp->dtypep(nullptr);  // Force re-resolution
            rdp->didWidth(false);
            ++staleRefFixCount;
        }
    }

    // Fix RefDType nodes whose typedefp points to a template typedef.
    // Use PARAMTYPE nodes with the same name in the same owner module to find the correct
    // specialized typedef - PARAMTYPEs have correct edges based on cell associations.
    int cloneFixCount = 0;
    for (DepNode* const rdNodep : s_allNodes) {
        if (!rdNodep || rdNodep->nodeType != NodeType::REFDTYPE) continue;
        AstRefDType* const rdp = VN_CAST(rdNodep->nodep, RefDType);
        if (!rdp) continue;

        AstTypedef* const currentTdp = rdp->typedefp();
        if (!currentTdp) continue;

        // Check if current typedef is in a template (no __ suffix)
        AstNodeModule* const currentTdOwnerp = findOwnerModule(currentTdp);
        if (!currentTdOwnerp) continue;
        if (currentTdOwnerp->name().find("__") != string::npos) continue;  // Already specialized

        // Find a PARAMTYPE node in the same owner module with the same name
        // That PARAMTYPE's edge to TYPEDEF will have the correct specialized version
        AstTypedef* targetTdp = nullptr;
        AstNodeModule* targetOwnerp = nullptr;
        for (DepNode* const ptNodep : s_allNodes) {
            if (!ptNodep || ptNodep->nodeType != NodeType::PARAMTYPEDTYPE) continue;
            if (ptNodep->ownerModp != rdNodep->ownerModp) continue;  // Must be same owner
            if (nodeName(ptNodep) != rdp->name()) continue;  // Must have same name

            // Found matching PARAMTYPE - look for its edge to a specialized TYPEDEF
            for (DepNode* const depNodep : ptNodep->dependsOn) {
                if (!depNodep || depNodep->nodeType != NodeType::TYPEDEF) continue;
                AstTypedef* const candTdp = VN_CAST(depNodep->nodep, Typedef);
                if (!candTdp) continue;
                if (candTdp->name() != currentTdp->name()) continue;

                // Check if this typedef is in a specialized module
                if (depNodep->ownerModp
                    && depNodep->ownerModp->name().find("__") != string::npos) {
                    targetTdp = candTdp;
                    targetOwnerp = depNodep->ownerModp;
                    break;
                }
            }
            if (targetTdp) break;
        }

        if (targetTdp && targetTdp != currentTdp) {
            UINFO(5, "DEPGRAPH: fixing RefDType '" << rdp->name()
                      << "' typedefp from '" << currentTdOwnerp->name()
                      << "' to '" << targetOwnerp->name() << "'" << endl);
            rdp->typedefp(targetTdp);
            if (rdp->classOrPackagep() == currentTdOwnerp) {
                rdp->classOrPackagep(targetOwnerp);
            }
            ++cloneFixCount;
        }
    }

    // Safety pass: Fix pointers that point to template module nodes.
    // Template modules will be deleted by V3Dead, causing dangling pointers.
    // For typedefp: clear the pointer (it's optional)
    // For refDTypep: move the target type to TYPETABLE so it survives
    // Scan ALL modules and the TYPETABLE comprehensively.
    int templateTypedefpCleared = 0;
    int templateRefDTypepMoved = 0;

    auto fixRefDTypePointers = [&](AstRefDType* rdp) {
        // Fix typedefp - clear if pointing to template typedef
        if (AstTypedef* const tdp = rdp->typedefp()) {
            AstNodeModule* const tdOwnerp = findOwnerModule(tdp);
            if (tdOwnerp && tdOwnerp->hasGParam()
                && tdOwnerp->name().find("__") == string::npos) {
                UINFO(5, "DEPGRAPH: clearing typedefp to template typedef '" << tdp->name()
                          << "' in '" << tdOwnerp->name() << "' for RefDType '"
                          << rdp->name() << "'" << endl);
                rdp->typedefp(nullptr);
                ++templateTypedefpCleared;
            }
        }
        // Fix refDTypep - move target to TYPETABLE if in template module
        if (AstNodeDType* const subp = rdp->refDTypep()) {
            AstNodeModule* const subOwnerp = findOwnerModule(subp);
            if (subOwnerp && subOwnerp->hasGParam()
                && subOwnerp->name().find("__") == string::npos
                && subp->backp()) {  // Has a parent, so can be unlinked
                UINFO(5, "DEPGRAPH: moving refDTypep target '" << subp->prettyTypeName()
                          << "' from template '" << subOwnerp->name()
                          << "' to TYPETABLE for RefDType '" << rdp->name() << "'" << endl);
                subp->unlinkFrBack();
                v3Global.rootp()->typeTablep()->addTypesp(subp);
                ++templateRefDTypepMoved;
            }
        }
    };

    for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp;
         modp = VN_AS(modp->nextp(), NodeModule)) {
        modp->foreach([&](AstRefDType* rdp) { fixRefDTypePointers(rdp); });
    }
    // Also scan the type table
    if (v3Global.rootp()->typeTablep()) {
        v3Global.rootp()->typeTablep()->foreach([&](AstRefDType* rdp) {
            fixRefDTypePointers(rdp);
        });
    }
    if (templateTypedefpCleared > 0 || templateRefDTypepMoved > 0) {
        UINFO(5, "DEPGRAPH: fixed template pointers - cleared " << templateTypedefpCleared
                  << " typedefp, moved " << templateRefDTypepMoved
                  << " refDTypep targets to TYPETABLE" << endl);
    }

    // Retarget RefDTypes in TYPETABLE from template struct/union types to specialized versions.
    // Template types have unresolved parameter widths; specialized types have correct widths.
    // We identify the specialized version by finding a same-named type with different width
    // that was tracked by the depgraph (meaning it came from a specialized module).
    int templateStructRetargeted = 0;
    if (v3Global.rootp()->typeTablep()) {
        // First, collect all struct/union types that were tracked in the depgraph (specialized)
        std::unordered_map<string, AstNodeUOrStructDType*> specializedTypes;
        for (DepNode* const nodep : s_allNodes) {
            if (!nodep) continue;
            if (nodep->nodeType == NodeType::STRUCTDTYPE
                || nodep->nodeType == NodeType::UNIONDTYPE) {
                if (AstNodeUOrStructDType* const usp = VN_CAST(nodep->nodep, NodeUOrStructDType)) {
                    // Store by name - prefer the one from specialized module (has __ suffix)
                    if (nodep->ownerModp && nodep->ownerModp->name().find("__") != string::npos) {
                        specializedTypes[usp->name()] = usp;
                        UINFO(9, "DEPGRAPH: tracked specialized " << usp->prettyTypeName()
                                  << " '" << usp->name() << "' w" << usp->width()
                                  << " from " << nodep->ownerModp->name() << endl);
                    }
                }
            }
        }

        // Now retarget RefDTypes that point to template versions
        v3Global.rootp()->typeTablep()->foreach([&](AstRefDType* rdp) {
            AstNodeDType* const subp = rdp->refDTypep();
            if (!subp) return;
            if (AstNodeUOrStructDType* const usp = VN_CAST(subp, NodeUOrStructDType)) {
                auto it = specializedTypes.find(usp->name());
                if (it != specializedTypes.end() && it->second != usp) {
                    AstNodeUOrStructDType* const specializedp = it->second;
                    if (specializedp->width() != usp->width()) {
                        UINFO(5, "DEPGRAPH: retargeting RefDType '" << rdp->name()
                                  << "' from " << usp->prettyTypeName() << " w" << usp->width()
                                  << " to specialized w" << specializedp->width() << endl);
                        rdp->refDTypep(specializedp);
                        ++templateStructRetargeted;
                    }
                }
            }
        });
    }
    if (templateStructRetargeted > 0) {
        UINFO(5, "DEPGRAPH: retargeted " << templateStructRetargeted
                  << " RefDTypes from template to specialized struct/union types" << endl);
    }

    // Retarget RefDTypes from template PARAMTYPEDTYPEs to specialized versions.
    // Template PARAMTYPEDTYPEs have wrong widths; specialized ones have correct widths.
    // NOTE: Use subDTypep()->width() to get the resolved width, not width() which may be stale.
    int templateParamTypeRetargeted = 0;
    if (v3Global.rootp()->typeTablep()) {
        // Collect specialized PARAMTYPEDTYPEs by name (from specialized modules)
        std::unordered_map<string, AstParamTypeDType*> specializedParamTypes;
        for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp;
             modp = VN_AS(modp->nextp(), NodeModule)) {
            if (modp->name().find("__") != string::npos) {
                // Specialized module
                modp->foreach([&](AstParamTypeDType* ptdp) {
                    AstNodeDType* const subp = ptdp->subDTypep();
                    int resolvedWidth = subp ? subp->width() : ptdp->width();
                    if (resolvedWidth > 0) {
                        auto it = specializedParamTypes.find(ptdp->name());
                        // Prefer larger resolved width
                        if (it == specializedParamTypes.end()) {
                            specializedParamTypes[ptdp->name()] = ptdp;
                        } else {
                            AstNodeDType* const existingSubp = it->second->subDTypep();
                            int existingWidth = existingSubp ? existingSubp->width() : it->second->width();
                            if (resolvedWidth > existingWidth) {
                                specializedParamTypes[ptdp->name()] = ptdp;
                            }
                        }
                        UINFO(9, "DEPGRAPH: tracked specialized PARAMTYPEDTYPE '"
                                  << ptdp->name() << "' resolvedW=" << resolvedWidth
                                  << " from " << modp->name() << endl);
                    }
                });
            }
        }

        // Helper to get resolved width of PARAMTYPEDTYPE
        auto getResolvedWidth = [](AstParamTypeDType* ptdp) -> int {
            AstNodeDType* const subp = ptdp->subDTypep();
            return subp ? subp->width() : ptdp->width();
        };

        // Retarget RefDTypes that point to template PARAMTYPEDTYPEs
        v3Global.rootp()->typeTablep()->foreach([&](AstRefDType* rdp) {
            if (AstParamTypeDType* const ptdp = VN_CAST(rdp->refDTypep(), ParamTypeDType)) {
                auto it = specializedParamTypes.find(ptdp->name());
                if (it != specializedParamTypes.end() && it->second != ptdp) {
                    int specWidth = getResolvedWidth(it->second);
                    int templWidth = getResolvedWidth(ptdp);
                    if (specWidth > templWidth) {
                        UINFO(5, "DEPGRAPH: retargeting RefDType '" << rdp->name()
                                  << "' from PARAMTYPEDTYPE resolvedW=" << templWidth
                                  << " to specialized resolvedW=" << specWidth << endl);
                        rdp->refDTypep(it->second);
                        ++templateParamTypeRetargeted;
                    }
                }
            }
        });
        // Also in modules
        for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp;
             modp = VN_AS(modp->nextp(), NodeModule)) {
            modp->foreach([&](AstRefDType* rdp) {
                if (AstParamTypeDType* const ptdp = VN_CAST(rdp->refDTypep(), ParamTypeDType)) {
                    auto it = specializedParamTypes.find(ptdp->name());
                    if (it != specializedParamTypes.end() && it->second != ptdp) {
                        int specWidth = getResolvedWidth(it->second);
                        int templWidth = getResolvedWidth(ptdp);
                        if (specWidth > templWidth) {
                            UINFO(5, "DEPGRAPH: retargeting RefDType '" << rdp->name()
                                      << "' in " << modp->name()
                                      << " from PARAMTYPEDTYPE resolvedW=" << templWidth
                                      << " to specialized resolvedW=" << specWidth << endl);
                            rdp->refDTypep(it->second);
                            ++templateParamTypeRetargeted;
                        }
                    }
                }
            });
        }
    }
    if (templateParamTypeRetargeted > 0) {
        UINFO(5, "DEPGRAPH: retargeted " << templateParamTypeRetargeted
                  << " RefDTypes from template to specialized PARAMTYPEDTYPEs" << endl);
    }

    // Retarget PackArrayDTypes in TYPETABLE from template to specialized versions.
    // Template PackArrayDTypes have unresolved parameter ranges (e.g., [-1:0]).
    // Find specialized versions by matching fileline and preferring larger widths.
    int templateArrayRetargeted = 0;
    if (v3Global.rootp()->typeTablep()) {
        // Collect all PackArrayDTypes by fileline
        std::unordered_map<string, AstPackArrayDType*> specializedArrays;
        v3Global.rootp()->typeTablep()->foreach([&](AstPackArrayDType* arrp) {
            const string key = arrp->fileline()->ascii();
            auto it = specializedArrays.find(key);
            if (it == specializedArrays.end() || arrp->width() > it->second->width()) {
                specializedArrays[key] = arrp;
            }
        });

        // Retarget MemberDTypes that reference template PackArrayDTypes
        v3Global.rootp()->typeTablep()->foreach([&](AstMemberDType* memp) {
            if (AstPackArrayDType* const arrp = VN_CAST(memp->subDTypep(), PackArrayDType)) {
                const string key = arrp->fileline()->ascii();
                auto it = specializedArrays.find(key);
                if (it != specializedArrays.end() && it->second != arrp
                    && it->second->width() > arrp->width()) {
                    UINFO(5, "DEPGRAPH: retargeting MemberDType '" << memp->name()
                              << "' from PackArrayDType w" << arrp->width()
                              << " to specialized w" << it->second->width() << endl);
                    memp->refDTypep(it->second);
                    ++templateArrayRetargeted;
                }
            }
        });

        // Mark template PackArrayDType ranges to suppress ASCRANGE warning.
        // Template arrays have unresolved parameter ranges that will be checked
        // correctly in the specialized version. Use warnOff to suppress.
        v3Global.rootp()->typeTablep()->foreach([&](AstPackArrayDType* arrp) {
            const string key = arrp->fileline()->ascii();
            auto it = specializedArrays.find(key);
            if (it != specializedArrays.end() && it->second != arrp
                && arrp->width() < it->second->width()) {
                // This is a template version - suppress ASCRANGE warning
                if (AstRange* const rangep = arrp->rangep()) {
                    rangep->fileline()->warnOff(V3ErrorCode::ASCRANGE, true);
                    UINFO(5, "DEPGRAPH: suppressed ASCRANGE for template PackArrayDType w"
                              << arrp->width() << " at " << key << endl);
                }
            }
        });
    }
    if (templateArrayRetargeted > 0) {
        UINFO(5, "DEPGRAPH: retargeted " << templateArrayRetargeted
                  << " MemberDTypes from template to specialized PackArrayDTypes" << endl);
    }

    // Sync RefDType widths with their refDTypep targets.
    // After retargeting, the cached width may be stale even if dtypep is correct.
    // Update both dtypep and the cached width.
    int refDTypeSynced = 0;
    auto syncRefDType = [&](AstRefDType* rdp) {
        AstNodeDType* const refp = rdp->refDTypep();
        if (!refp) return;
        if (refp->width() > 0 && refp->width() != rdp->width()) {
            UINFO(5, "DEPGRAPH: syncing RefDType '" << rdp->name()
                      << "' w" << rdp->width()
                      << " to match refDTypep w" << refp->width() << endl);
            rdp->dtypep(refp);
            rdp->widthForce(refp->width(), refp->widthMin());
            ++refDTypeSynced;
        }
    };
    if (v3Global.rootp()->typeTablep()) {
        v3Global.rootp()->typeTablep()->foreach([&](AstRefDType* rdp) {
            syncRefDType(rdp);
        });
    }
    for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp;
         modp = VN_AS(modp->nextp(), NodeModule)) {
        modp->foreach([&](AstRefDType* rdp) { syncRefDType(rdp); });
    }
    if (refDTypeSynced > 0) {
        UINFO(5, "DEPGRAPH: synced " << refDTypeSynced
                  << " RefDType widths to match refDTypep" << endl);
    }

    int nullSubCount = 0;
    if (debug() >= 5) {
        for (DepNode* const nodep : s_allNodes) {
            if (!nodep || nodep->nodeType != NodeType::REFDTYPE) continue;
            AstRefDType* const rdp = VN_CAST(nodep->nodep, RefDType);
            if (!rdp) continue;
            if (!rdp->subDTypep()) {
                ++nullSubCount;
                UINFO(5, "DEPGRAPH: refdtype has null subDTypep: " << nodeName(nodep)
                          << "@" << nodeOwnerName(nodep) << endl);
            }
        }
    }
    UINFO(5, "DEPGRAPH: apply complete - updated " << updatedCount << " RefDType pointers, fixed "
              << cloneFixCount << " cloned RefDTypes, cleared " << staleRefFixCount
              << " stale refDTypep" << endl);
    if (debug() >= 5) {
        UINFO(5, "DEPGRAPH: apply complete - " << nullSubCount
                  << " refdtype nodes with null subDTypep" << endl);
    }

    // Mark template module types as "widthed" to prevent V3Width from checking them.
    // Template modules have unresolved parameters, so their types may have incorrect
    // parameter-dependent widths. The specialized clones have correct widths and will
    // be properly checked by V3Width.
    int templateTypesMarked = 0;
    int templateModulesFound = 0;
    for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp;
         modp = VN_AS(modp->nextp(), NodeModule)) {
        // Template modules have hasGParam() but no __ suffix (not specialized)
        const bool isTemplate = modp->hasGParam() && modp->name().find("__") == string::npos;
        UINFO(9, "DEPGRAPH: checking module '" << modp->name()
                  << "' hasGParam=" << modp->hasGParam()
                  << " isTemplate=" << isTemplate << endl);
        if (isTemplate) {
            ++templateModulesFound;
            modp->foreach([&](AstNodeUOrStructDType* dtypep) {
                UINFO(9, "DEPGRAPH: found type '" << dtypep->name()
                          << "' didWidth=" << dtypep->didWidth() << endl);
                if (!dtypep->didWidth()) {
                    dtypep->didWidth(true);
                    ++templateTypesMarked;
                }
            });
        }
    }
    UINFO(5, "DEPGRAPH: found " << templateModulesFound << " template modules, marked "
              << templateTypesMarked << " types as widthed" << endl);

    return updatedCount + staleRefFixCount + cloneFixCount + templateTypedefpCleared
           + templateRefDTypepMoved + templateStructRetargeted + templateParamTypeRetargeted
           + templateArrayRetargeted + refDTypeSynced + templateTypesMarked;
}

//======================================================================
// Mark template types BEFORE V3Param

void V3LinkDotDepGraph::markTemplateTypes(AstNetlist* netlistp) {
    // Mark template module types as "widthed" to prevent V3Width errors during V3Param.
    // Template modules have unresolved parameters, so their struct/union types may have
    // incorrect parameter-dependent widths. Marking them as didWidth(true) prevents
    // V3Width from checking them and triggering spurious errors.
    // The specialized clones will be properly checked after V3Param creates them.
    int templateTypesMarked = 0;
    int templateModulesFound = 0;
    for (AstNodeModule* modp = netlistp->modulesp(); modp;
         modp = VN_AS(modp->nextp(), NodeModule)) {
        // Template modules have hasGParam() but no __ suffix (not specialized)
        const bool isTemplate = modp->hasGParam() && modp->name().find("__") == string::npos;
        if (isTemplate) {
            ++templateModulesFound;
            modp->foreach([&](AstNodeUOrStructDType* dtypep) {
                if (!dtypep->didWidth()) {
                    dtypep->didWidth(true);
                    ++templateTypesMarked;
                }
            });
        }
    }
    UINFO(5, "DEPGRAPH: markTemplateTypes - found " << templateModulesFound
              << " template modules, marked " << templateTypesMarked
              << " types as widthed" << endl);
}

//======================================================================
// Per-module resolution with widthing - call DURING V3Param before constification

void V3LinkDotDepGraph::syncRefDTypeWidths(AstNodeModule* modp) {
    // Resolve RefDType widths by following the type chain and widthing as needed.
    // This ensures $bits() expressions get correct values during widthParamsEdit.
    //
    // The key is to follow: RefDType -> ParamTypeDType -> RefDType -> StructDType
    // and width each type in the chain, then propagate widths back up.
    if (!modp) return;

    UINFO(5, "DEPGRAPH: syncRefDTypeWidths for " << modp->name() << endl);

    // Iterate until no progress (handles nested dependencies)
    int iteration = 0;
    bool progress = true;
    while (progress && iteration < 100) {
        progress = false;
        ++iteration;

        modp->foreach([&](AstRefDType* rdp) {
            // Follow the type chain to find the ultimate type
            AstNodeDType* ultimateTypep = rdp;
            int depth = 0;
            while (ultimateTypep && depth < 50) {
                ++depth;
                if (AstRefDType* const rp = VN_CAST(ultimateTypep, RefDType)) {
                    if (rp->refDTypep()) {
                        ultimateTypep = rp->refDTypep();
                        continue;
                    }
                }
                if (AstParamTypeDType* const ptp = VN_CAST(ultimateTypep, ParamTypeDType)) {
                    if (ptp->subDTypep()) {
                        ultimateTypep = ptp->subDTypep();
                        continue;
                    }
                }
                break;  // Reached a concrete type
            }

            if (!ultimateTypep) return;

            // If the ultimate type has width but RefDType doesn't, width the RefDType
            const int ultimateWidth = ultimateTypep->width();
            if (ultimateWidth > 0 && ultimateWidth != rdp->width()) {
                UINFO(5, "DEPGRAPH: syncRefDTypeWidths iter=" << iteration
                          << " '" << rdp->name() << "' in " << modp->name()
                          << " w" << rdp->width() << " -> w" << ultimateWidth
                          << " (via " << ultimateTypep->prettyTypeName() << ")" << endl);

                // Update the RefDType's width
                if (AstNodeDType* const refp = rdp->refDTypep()) {
                    rdp->dtypep(refp);
                }
                rdp->widthForce(ultimateWidth, ultimateWidth);
                progress = true;
            }

            // Also try to width ParamTypeDTypes in the chain
            if (AstParamTypeDType* const ptdp = VN_CAST(rdp->refDTypep(), ParamTypeDType)) {
                if (ptdp->width() != ultimateWidth && ultimateWidth > 0) {
                    UINFO(5, "DEPGRAPH: syncRefDTypeWidths widthing PARAMTYPEDTYPE '"
                              << ptdp->name() << "' w" << ptdp->width()
                              << " -> w" << ultimateWidth << endl);
                    ptdp->widthForce(ultimateWidth, ultimateWidth);
                    progress = true;
                }
            }
        });
    }

    UINFO(5, "DEPGRAPH: syncRefDTypeWidths completed in " << iteration
              << " iterations for " << modp->name() << endl);
}

//======================================================================
// Debugging

void V3LinkDotDepGraph::dumpGraph() {
    UINFO(1, "DEPGRAPH: ========== DEPENDENCY GRAPH DUMP ==========" << endl);
    UINFO(1, "DEPGRAPH: Total nodes: " << s_allNodes.size()
              << "  Iterations: " << s_iterationCount << endl);

    // Group nodes by owner module for clearer output
    std::map<string, std::vector<const DepNode*>> byOwner;
    for (const DepNode* nodep : s_allNodes) {
        byOwner[nodeOwnerName(nodep)].push_back(nodep);
    }

    for (const auto& kv : byOwner) {
        UINFO(1, "DEPGRAPH: --- Module: " << kv.first << " ---" << endl);
        for (const DepNode* nodep : kv.second) {
            dumpNode(nodep);
        }
    }

    UINFO(1, "DEPGRAPH: ========== END GRAPH DUMP ==========" << endl);
}

void V3LinkDotDepGraph::dumpNode(const DepNode* nodep) {
    if (!nodep) return;

    std::ostringstream deps;
    for (const DepNode* depp : nodep->dependsOn) {
        if (deps.tellp() > 0) deps << ", ";
        deps << "'" << nodeName(depp) << "'@" << nodeOwnerName(depp);
    }

    string extra;
    if (nodep->nodeType == NodeType::REFDTYPE && !nodep->cellName.empty()) {
        extra = " cell=" + nodep->cellName;
    }

    UINFO(1, "DEPGRAPH:   " << nodeTypeName(nodep->nodeType) << " '" << nodeName(nodep) << "'"
              << " resolved=" << (nodep->resolved ? "Y" : "N")
              << " iter=" << nodep->resolvedIteration
              << extra
              << " deps=[" << deps.str() << "]"
              << endl);
}

//======================================================================
// Hierarchical tree dump

void V3LinkDotDepGraph::dumpModuleTree(AstNodeModule* modp, const string& prefix, bool isLast) {
    if (!modp || modp->dead()) return;

    const auto formatConstValue = [](const AstConst* constp) -> string {
        if (!constp) return "";
        const V3Number& num = constp->num();
        if (num.isNumber()) {
            return string{" = "} + (constp->isSigned() ? num.toDecimalS() : num.toDecimalU());
        }
        return string{" = "} + num.toString();
    };

    const auto formatParamTypeResolution = [](const AstParamTypeDType* ptdp,
                                              const DepNode* dnp) -> string {
        if (!ptdp || !dnp || !dnp->resolved) return "";
        AstNodeDType* const dtypep = ptdp->dtypep();
        if (!dtypep) return "";
        string widthStr;
        if (dnp->resolvedWidth > 0) widthStr = " [w" + std::to_string(dnp->resolvedWidth) + "]";
        else if (dtypep->width() > 0) widthStr = " [w" + std::to_string(dtypep->width()) + "]";
        string cellStr;
        string cellName;
        if (!dnp->cellName.empty()) {
            cellName = dnp->cellName;
            const size_t colonPos = cellName.find(':');
            if (colonPos != string::npos) cellName = cellName.substr(0, colonPos);
        }
        if (!cellName.empty()) {
            string targetName;
            for (DepNode* const depNodep : dnp->dependsOn) {
                if ((depNodep->nodeType == NodeType::TYPEDEF
                     || depNodep->nodeType == NodeType::PARAMTYPEDTYPE)
                    && depNodep->ownerModp) {
                    targetName = depNodep->ownerModp->name();
                    break;
                }
            }
            if (!targetName.empty()) cellStr = " via " + targetName + " (" + cellName + ")";
            else cellStr = " via " + cellName;
        }
        return string{" -> "} + dtypep->prettyDTypeName(false) + widthStr + cellStr;
    };

    const auto formatRefDTypeResolution = [](const DepNode* dnp) -> string {
        if (!dnp) return "";
        string cellStr;
        if (!dnp->cellName.empty()) cellStr = " cell=" + dnp->cellName;
        string targetStr;
        for (DepNode* const depNodep : dnp->dependsOn) {
            if ((depNodep->nodeType == NodeType::TYPEDEF
                 || depNodep->nodeType == NodeType::PARAMTYPEDTYPE)
                && depNodep->ownerModp) {
                targetStr = " -> " + depNodep->ownerModp->name();
                break;
            }
        }
        return cellStr + targetStr;
    };

    const string connector = isLast ? "└── " : "├── ";
    const string extension = isLast ? "    " : "│   ";

    // Print module header
    string modType = "MODULE";
    if (VN_IS(modp, Iface)) modType = "IFACE";
    else if (VN_IS(modp, Class)) modType = "CLASS";
    else if (VN_IS(modp, Package)) modType = "PACKAGE";

    UINFO(1, "DEPGRAPH: " << prefix << connector << modp->name() << " : " << modType << endl);

    const string childPrefix = prefix + extension;

    // Collect items to print
    std::vector<std::pair<string, string>> items;  // (connector, description)

    // Print parameters and localparams in this module
    for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
        if (AstVar* const varp = VN_CAST(stmtp, Var)) {
            if (varp->isGParam()) {
                const DepNode* const dnp = find(varp);
                string resolved = dnp ? (dnp->resolved ? " [resolved]" : " [pending]") : "";
                string valStr;
                if (varp->valuep()) {
                    if (AstConst* const constp = VN_CAST(varp->valuep(), Const)) {
                        valStr = formatConstValue(constp);
                    }
                }
                items.push_back({"", "GPARAM " + varp->name() + valStr + resolved});
            } else if (varp->isParam()) {
                const DepNode* const dnp = find(varp);
                string resolved = dnp ? (dnp->resolved ? " [resolved]" : " [pending]") : "";
                // Show value if available
                string valStr;
                if (varp->valuep()) {
                    if (AstConst* const constp = VN_CAST(varp->valuep(), Const)) {
                        valStr = formatConstValue(constp);
                    }
                }
                items.push_back({"", "LPARAM " + varp->name() + valStr + resolved});
            }
        } else if (AstTypedef* const tdp = VN_CAST(stmtp, Typedef)) {
            const DepNode* const dnp = find(tdp);
            string resolved = dnp ? (dnp->resolved ? " [resolved]" : " [pending]") : "";
            // Try to get width info
            string widthStr;
            if (AstNodeDType* const dtypep = tdp->subDTypep()) {
                if (dtypep->width() > 0) {
                    widthStr = " [w" + std::to_string(dtypep->width()) + "]";
                }
            }
            items.push_back({"", "TYPEDEF " + tdp->name() + widthStr + resolved});
        } else if (AstParamTypeDType* const ptdp = VN_CAST(stmtp, ParamTypeDType)) {
            const DepNode* const dnp = find(ptdp);
            string resolved = dnp ? (dnp->resolved ? " [resolved]" : " [pending]") : "";
            string targetStr = formatParamTypeResolution(ptdp, dnp);
            items.push_back({"", "PARAMTYPE " + ptdp->name() + resolved + targetStr});
        }
    }

    // Include module-level REFDTYPE nodes to surface instance context in tree
    for (DepNode* const dnp : s_allNodes) {
        if (!dnp || dnp->nodeType != NodeType::REFDTYPE) continue;
        if (dnp->ownerModp != modp) continue;
        string suffix = formatRefDTypeResolution(dnp);
        items.push_back({"", "REFDTYPE " + nodeName(dnp) + suffix});
    }

    // Print items
    for (size_t i = 0; i < items.size(); ++i) {
        bool itemIsLast = (i == items.size() - 1);
        // Check if there are child cells after this
        bool hasChildCells = false;
        for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (VN_IS(stmtp, Cell)) { hasChildCells = true; break; }
        }
        if (hasChildCells) itemIsLast = false;

        const string itemConnector = itemIsLast ? "└── " : "├── ";
        UINFO(1, "DEPGRAPH: " << childPrefix << itemConnector << items[i].second << endl);
    }

    // Collect and print child cells
    std::vector<AstCell*> cells;
    for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
        if (AstCell* const cellp = VN_CAST(stmtp, Cell)) {
            cells.push_back(cellp);
        }
    }

    for (size_t i = 0; i < cells.size(); ++i) {
        AstCell* const cellp = cells[i];
        bool cellIsLast = (i == cells.size() - 1);
        const string cellConnector = cellIsLast ? "└── " : "├── ";
        const string cellExtension = cellIsLast ? "    " : "│   ";

        AstNodeModule* const childModp = cellp->modp();
        string childModName = childModp ? childModp->name() : "<unlinked>";

        UINFO(1, "DEPGRAPH: " << childPrefix << cellConnector
                  << cellp->name() << " : " << childModName << endl);

        // Recursively dump child module contents (but not the full tree to avoid duplication)
        if (childModp && !childModp->dead()) {
            const string grandchildPrefix = childPrefix + cellExtension;
            // Print params/typedefs of child inline
            std::vector<string> childItems;
            for (AstNode* cstmtp = childModp->stmtsp(); cstmtp; cstmtp = cstmtp->nextp()) {
                if (AstVar* const varp = VN_CAST(cstmtp, Var)) {
                    if (varp->isGParam()) {
                        const DepNode* const dnp = find(varp);
                        string resolved = dnp ? (dnp->resolved ? " [R]" : " [P]") : "";
                        string valStr;
                        if (varp->valuep()) {
                            if (AstConst* const constp = VN_CAST(varp->valuep(), Const)) {
                                valStr = formatConstValue(constp);
                            }
                        }
                        childItems.push_back("GPARAM " + varp->name() + valStr + resolved);
                    } else if (varp->isParam()) {
                        const DepNode* const dnp = find(varp);
                        string resolved = dnp ? (dnp->resolved ? " [R]" : " [P]") : "";
                        string valStr;
                        if (varp->valuep()) {
                            if (AstConst* const constp = VN_CAST(varp->valuep(), Const)) {
                                valStr = formatConstValue(constp);
                            }
                        }
                        childItems.push_back("LPARAM " + varp->name() + valStr + resolved);
                    }
                } else if (AstTypedef* const tdp = VN_CAST(cstmtp, Typedef)) {
                    const DepNode* const dnp = find(tdp);
                    string resolved = dnp ? (dnp->resolved ? " [R]" : " [P]") : "";
                    string widthStr;
                    if (AstNodeDType* const dtypep = tdp->subDTypep()) {
                        if (dtypep->width() > 0) {
                            widthStr = "[w" + std::to_string(dtypep->width()) + "]";
                        }
                    }
                    childItems.push_back("TYPEDEF " + tdp->name() + widthStr + resolved);
                } else if (AstParamTypeDType* const ptdp = VN_CAST(cstmtp, ParamTypeDType)) {
                    const DepNode* const dnp = find(ptdp);
                    string resolved = dnp ? (dnp->resolved ? " [R]" : " [P]") : "";
                    string targetStr = formatParamTypeResolution(ptdp, dnp);
                    childItems.push_back("PARAMTYPE " + ptdp->name() + resolved + targetStr);
                }
            }
            for (size_t j = 0; j < childItems.size(); ++j) {
                bool jIsLast = (j == childItems.size() - 1);
                // Check for nested cells
                bool hasNestedCells = false;
                for (AstNode* cstmtp = childModp->stmtsp(); cstmtp; cstmtp = cstmtp->nextp()) {
                    if (VN_IS(cstmtp, Cell)) { hasNestedCells = true; break; }
                }
                if (hasNestedCells) jIsLast = false;
                const string jConnector = jIsLast ? "└── " : "├── ";
                UINFO(1, "DEPGRAPH: " << grandchildPrefix << jConnector << childItems[j] << endl);
            }
            // Recurse for nested cells
            std::vector<AstCell*> nestedCells;
            for (AstNode* cstmtp = childModp->stmtsp(); cstmtp; cstmtp = cstmtp->nextp()) {
                if (AstCell* const ncellp = VN_CAST(cstmtp, Cell)) {
                    nestedCells.push_back(ncellp);
                }
            }
            for (size_t k = 0; k < nestedCells.size(); ++k) {
                AstCell* const ncellp = nestedCells[k];
                bool kIsLast = (k == nestedCells.size() - 1);
                dumpModuleTree(ncellp->modp(), grandchildPrefix, kIsLast);
            }
        }
    }
}

void V3LinkDotDepGraph::dumpGraphDepsTree() {
    UINFO(1, "DEPGRAPH: ========== DEPENDENCY EDGE TREE ==========" << endl);
    UINFO(1, "DEPGRAPH: Total nodes: " << s_allNodes.size()
              << "  Iterations: " << s_iterationCount << endl);

    auto nodeLabel = [](const DepNode* nodep) {
        std::ostringstream label;
        label << nodeTypeName(nodep->nodeType) << " " << nodeName(nodep)
              << "@" << nodeOwnerName(nodep);
        if (nodep->resolved) label << " [R]";
        return label.str();
    };

    std::map<string, std::vector<const DepNode*>> byOwner;
    for (const DepNode* nodep : s_allNodes) {
        if (!nodep) continue;
        byOwner[nodeOwnerName(nodep)].push_back(nodep);
    }

    for (const auto& kv : byOwner) {
        UINFO(1, "DEPGRAPH: " << kv.first << endl);
        const auto& nodes = kv.second;
        for (size_t i = 0; i < nodes.size(); ++i) {
            const DepNode* const nodep = nodes[i];
            if (!nodep) continue;
            const bool isLastNode = (i + 1 == nodes.size());
            const string nodeConnector = isLastNode ? "└── " : "├── ";
            const string nodePrefix = isLastNode ? "    " : "│   ";
            UINFO(1, "DEPGRAPH: " << nodeConnector << nodeLabel(nodep) << endl);
            if (nodep->dependsOn.empty()) {
                UINFO(1, "DEPGRAPH: " << nodePrefix << "(no deps)" << endl);
                continue;
            }
            size_t depIdx = 0;
            for (const DepNode* dep : nodep->dependsOn) {
                if (!dep) continue;
                const bool isLastDep = (++depIdx == nodep->dependsOn.size());
                const string depConnector = isLastDep ? "└── " : "├── ";
                UINFO(1, "DEPGRAPH: " << nodePrefix << depConnector
                          << nodeLabel(dep) << endl);
            }
        }
    }

    UINFO(1, "DEPGRAPH: ========== END EDGE TREE ==========" << endl);
}

void V3LinkDotDepGraph::dumpGraphTree(AstNetlist* netlistp) {
    UINFO(1, "DEPGRAPH: ========== HIERARCHY TREE ==========" << endl);
    UINFO(1, "DEPGRAPH: Total nodes: " << s_allNodes.size()
              << "  Iterations: " << s_iterationCount << endl);

    // Find top module
    AstNodeModule* topp = nullptr;
    for (AstNodeModule* modp = netlistp->modulesp(); modp;
         modp = VN_AS(modp->nextp(), NodeModule)) {
        if (modp->isTop() && !modp->dead()) {
            topp = modp;
            break;
        }
    }

    if (topp) {
        UINFO(1, "DEPGRAPH: " << topp->name() << " (top)" << endl);
        // Print top module contents
        std::vector<AstCell*> topCells;
        for (AstNode* stmtp = topp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstCell* const cellp = VN_CAST(stmtp, Cell)) {
                topCells.push_back(cellp);
            }
        }
        for (size_t i = 0; i < topCells.size(); ++i) {
            bool isLast = (i == topCells.size() - 1);
            dumpModuleTree(topCells[i]->modp(), "", isLast);
        }
    } else {
        UINFO(1, "DEPGRAPH: <no top module found>" << endl);
    }

    UINFO(1, "DEPGRAPH: ========== END TREE ==========" << endl);
}
