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
std::unordered_map<AstRefDType*, std::string> V3LinkDotDepGraph::s_refDTypeDotPathRegistry;

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
    for (DepNode* nodep : s_allNodes) delete nodep;
    s_allNodes.clear();
    s_nodes.clear();
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

        // Collect dependencies from the value expression
        if (AstNode* const valuep = nodep->valuep()) {
            V3LinkDotDepGraph::collectExpressionDeps(valuep, depNodep, m_modp);
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

            // Find the typedef or PARAMTYPEDTYPE in a cell with this name
            // We need to find the specialized interface's typedef or PARAMTYPEDTYPE
            // Search: 1) direct cells in this module, 2) cells in interfaces this module references
            if (!typedefName.empty()) {
                AstTypedef* targetTdp = nullptr;
                AstParamTypeDType* targetPtdp = nullptr;
                AstNodeModule* targetModp = nullptr;

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

    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    explicit DepGraphBuildVisitor(AstNetlist* netlistp) {
        iterateConst(netlistp);
    }
};

void V3LinkDotDepGraph::build(AstNetlist* netlistp) {
    if (!s_enabled) return;
    UINFO(5, "DEPGRAPH: building dependency graph" << endl);
    reset();
    DepGraphBuildVisitor{netlistp};
    UINFO(5, "DEPGRAPH: built " << s_allNodes.size() << " nodes" << endl);
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
                            refp->typedefp(targetTypedefp);
                        }
                    }
                }
            }

            // The childDTypep (RequireDType) should be removed after dtype resolution
            if (AstNodeDType* const childp = ptdp->getChildDTypep()) {
                childp->unlinkFrBack();
                ptdp->childDTypep(nullptr);
                VL_DO_DANGLING(childp->deleteTree(), childp);
            }
        } else {
            UINFO(9, "DEPGRAPH: no resolved dependency for paramtype '" << ptdp->name()
                      << "' in " << nodeOwnerName(nodep) << endl);
        }
    }
    // GPARAM and LPARAM values are already computed by V3Param, no need to re-evaluate
}

//======================================================================
// Resolution

int V3LinkDotDepGraph::resolve() {
    if (!s_enabled) return 0;
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

    return s_iterationCount;
}

//======================================================================
// Apply - update RefDType pointers after resolution

void V3LinkDotDepGraph::apply() {
    if (!s_enabled) return;
    UINFO(5, "DEPGRAPH: applying - updating RefDType pointers" << endl);

    int updatedCount = 0;

    for (DepNode* nodep : s_allNodes) {
        if (!nodep->resolved) continue;

        // Update RefDType pointers to point to correct specialized typedefs
        if (nodep->nodeType == NodeType::REFDTYPE) {
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
    }

    UINFO(5, "DEPGRAPH: apply complete - updated " << updatedCount << " RefDType pointers" << endl);
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

void V3LinkDotDepGraph::dumpGraphTree(AstNetlist* netlistp) {
    UINFO(1, "DEPGRAPH: ========== DEPENDENCY TREE ==========" << endl);
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
