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

V3LinkDotDepGraph::NodeMap V3LinkDotDepGraph::s_nodes{};
std::vector<V3LinkDotDepGraph::DepNode*> V3LinkDotDepGraph::s_allNodes{};
int V3LinkDotDepGraph::s_iterationCount = 0;
bool V3LinkDotDepGraph::s_enabled = false;

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
    for (DepNode* nodep : s_allNodes) delete nodep;
    s_allNodes.clear();
    s_nodes.clear();
    s_iterationCount = 0;
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
        // Skip dead modules
        if (nodep->dead()) return;

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
            // Add edge from this typedef to the referenced typedef
            if (AstRefDType* const rdtp = VN_CAST(dtypep, RefDType)) {
                if (AstTypedef* const refTdp = rdtp->typedefp()) {
                    AstNodeModule* const refOwnerp = V3LinkDotDepGraph::findOwnerModule(refTdp);
                    V3LinkDotDepGraph::DepNode* const refNodep
                        = V3LinkDotDepGraph::findOrCreateNode(refTdp, V3LinkDotDepGraph::NodeType::TYPEDEF, refOwnerp);
                    V3LinkDotDepGraph::addEdge(depNodep, refNodep);
                    UINFO(9, "DEPGRAPH: typedef '" << nodep->name() << "' depends on typedef '"
                              << refTdp->name() << "' in " << (refOwnerp ? refOwnerp->name() : "<null>") << endl);
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

        // If this RefDType points to a typedef, add edge
        if (AstTypedef* const tdp = nodep->typedefp()) {
            AstNodeModule* const tdOwnerp = V3LinkDotDepGraph::findOwnerModule(tdp);
            V3LinkDotDepGraph::DepNode* const tdNodep
                = V3LinkDotDepGraph::findOrCreateNode(tdp, V3LinkDotDepGraph::NodeType::TYPEDEF, tdOwnerp);
            V3LinkDotDepGraph::addEdge(depNodep, tdNodep);
        }

        // If this RefDType points to a ParamTypeDType, add edge
        if (AstParamTypeDType* const ptdp = VN_CAST(nodep->refDTypep(), ParamTypeDType)) {
            AstNodeModule* const ptdOwnerp = V3LinkDotDepGraph::findOwnerModule(ptdp);
            V3LinkDotDepGraph::DepNode* const ptdNodep = V3LinkDotDepGraph::findOrCreateNode(
                ptdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, ptdOwnerp);
            V3LinkDotDepGraph::addEdge(depNodep, ptdNodep);
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

    if (nodep->nodeType == NodeType::TYPEDEF) {
        AstTypedef* const tdp = VN_CAST(nodep->nodep, Typedef);
        if (!tdp) return;

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

        const int oldWidth = ptdp->subDTypep() ? ptdp->subDTypep()->width() : 0;

        ptdp->didWidth(false);
        if (ptdp->subDTypep()) ptdp->subDTypep()->didWidth(false);

        V3Width::widthParamsEdit(ptdp);

        const int newWidth = ptdp->subDTypep() ? ptdp->subDTypep()->width() : 0;

        if (oldWidth != newWidth) {
            UINFO(5, "DEPGRAPH: re-evaluated paramtype '" << ptdp->name()
                      << "' width " << oldWidth << " -> " << newWidth
                      << " in " << nodeOwnerName(nodep) << endl);
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

            // Find the correct typedef from the dependencies
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

    UINFO(1, "DEPGRAPH:   " << nodeTypeName(nodep->nodeType) << " '" << nodeName(nodep) << "'"
              << " resolved=" << (nodep->resolved ? "Y" : "N")
              << " iter=" << nodep->resolvedIteration
              << " deps=[" << deps.str() << "]"
              << endl);
}

//======================================================================
// Hierarchical tree dump

void V3LinkDotDepGraph::dumpModuleTree(AstNodeModule* modp, const string& prefix, bool isLast) {
    if (!modp || modp->dead()) return;

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
                items.push_back({"", "GPARAM " + varp->name() + resolved});
            } else if (varp->isParam()) {
                const DepNode* const dnp = find(varp);
                string resolved = dnp ? (dnp->resolved ? " [resolved]" : " [pending]") : "";
                // Show value if available
                string valStr;
                if (varp->valuep()) {
                    if (AstConst* const constp = VN_CAST(varp->valuep(), Const)) {
                        valStr = " = " + constp->num().ascii();
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
            items.push_back({"", "PARAMTYPE " + ptdp->name() + resolved});
        }
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
                                valStr = "=" + constp->num().ascii();
                            }
                        }
                        childItems.push_back("GPARAM " + varp->name() + valStr + resolved);
                    } else if (varp->isParam()) {
                        const DepNode* const dnp = find(varp);
                        string resolved = dnp ? (dnp->resolved ? " [R]" : " [P]") : "";
                        string valStr;
                        if (varp->valuep()) {
                            if (AstConst* const constp = VN_CAST(varp->valuep(), Const)) {
                                valStr = "=" + constp->num().ascii();
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
