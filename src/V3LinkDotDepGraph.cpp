//*************************************************************************
// DESCRIPTION: Verilator: Interface typedef capture with path-based keys
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
#include "V3LinkDotIfaceCapture.h"
#include "V3SymTable.h"
#include "V3Width.h"

#include <algorithm>
#include <iomanip>
#include <map>
#include <sstream>

VL_DEFINE_DEBUG_FUNCTIONS;

//======================================================================
// Static member definitions

V3LinkDotDepGraph::NodeMap V3LinkDotDepGraph::s_nodes;
std::vector<V3LinkDotDepGraph::DepNode*> V3LinkDotDepGraph::s_allNodes;
int V3LinkDotDepGraph::s_iterationCount = 0;
bool V3LinkDotDepGraph::s_enabled = false;
bool V3LinkDotDepGraph::s_executing = false;
std::unordered_map<AstRefDType*, std::string> V3LinkDotDepGraph::s_refDTypeDotPathRegistry;
std::unordered_set<AstNodeModule*> V3LinkDotDepGraph::s_builtModules;
std::unordered_set<AstNodeModule*> V3LinkDotDepGraph::s_parameterizedModules;
static std::unordered_map<AstRefDType*, AstTypedef*> s_refDTypeScopedTypedefs;
static std::unordered_map<AstTypedef*, AstTypedef*> s_typedefScopedTypedefs;

// Pool of cloned types created during DepGraph execution.
// This pool OWNS all cloned types - DepNodes just reference them via resolvedTypep.
// Multiple DepNodes may share the same resolvedTypep via propagation along dependency chains.
// Cleanup happens here (once per type) rather than in DepNodes (which would cause double-free).
static std::vector<AstNodeDType*> s_clonedTypes;

// Map from hierarchical port path to connected interface instance cell path
// e.g., "t.u_subA.io" -> "t.subA_io"
static std::unordered_map<string, string> s_cellAssociations{};

//======================================================================
// Helper methods

AstNodeModule* V3LinkDotDepGraph::findOwnerModule(AstNode* nodep) {
    if (reinterpret_cast<uintptr_t>(nodep) < 4096) return nullptr;
    for (AstNode* curp = nodep; curp; curp = curp->backp()) {
        if (reinterpret_cast<uintptr_t>(curp) < 4096) return nullptr;
        if (AstNodeModule* const modp = VN_CAST(curp, NodeModule)) return modp;
    }
    return nullptr;
}

// Check if a module is a specialized clone (has been renamed by V3Param)
static bool isSpecializedModule(const AstNodeModule* modp) {
    if (!modp) return false;
    // Specialized modules have name() != origName() because V3Param renames them
    return modp->name() != modp->origName();
}

// Check if a module is a template (has parameters but not yet specialized)
static bool isTemplateModule(const AstNodeModule* modp) {
    if (!modp) return false;
    if (modp->isTop()) return false;
    // A module is a template if it has parameters AND has not been specialized (renamed)
    return modp->hasGParam() && !isSpecializedModule(modp);
}

// ParamSubstVisitor - Substitutes parameter references with resolved values
// Used during TYPEDEF execution to replace VarRefs with constants from DepNode::resolvedValuep

class ParamSubstVisitor final : public VNVisitor {
    // Map from parameter name to resolved value
    std::map<string, AstNode*> m_paramValues;
    // Map from typedef name to resolved type
    std::map<string, AstNodeDType*> m_typedefTypes;
    // Map from ATTROF key (attrType + operand type name) to resolved constant value
    // This allows us to match cloned ATTROF nodes to their resolved values
    // Key format: "DIM_BITS:data_t" for $bits(data_t)
    std::map<string, AstConst*> m_attrOfValues;

public:
    // Add a parameter value substitution
    void addParam(const string& name, AstNode* valuep) {
        if (valuep) m_paramValues[name] = valuep;
    }
    // Add a typedef type substitution
    void addTypedef(const string& name, AstNodeDType* typep) {
        if (typep) m_typedefTypes[name] = typep;
    }
    // Add an ATTROF ($bits, etc.) value substitution
    // Key format: "attrType:typeName" (e.g., "DIM_BITS:data_t")
    void addAttrOf(VAttrType attrType, const string& typeName, AstConst* valuep) {
        if (!typeName.empty() && valuep) {
            const string key = VAttrType{attrType}.ascii() + string(":") + typeName;
            m_attrOfValues[key] = valuep;
        }
    }

    // Run substitution on a cloned dtype tree
    void substitute(AstNode* nodep) {
        if (nodep) iterate(nodep);
    }

private:
    void visit(AstVarRef* nodep) override {
        // Check if this VarRef points to a parameter we have a value for
        if (!nodep->varp()) return;
        const string& name = nodep->varp()->name();
        auto it = m_paramValues.find(name);
        if (it != m_paramValues.end() && it->second) {
            // Clone the resolved value
            AstNode* newp = it->second->cloneTree(false);

            // If it's a Const, we can use it directly
            // If it's a PATTERN or ConsPackUOrStruct, we need to handle member selection specially
            // For now, just substitute and let V3Const handle it

            UINFO(5, "DEPGRAPH: ParamSubstVisitor replacing VarRef '" << name << "' with "
                                                                      << newp->typeName() << endl);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }

    // Handle member selection from struct parameters
    // When we see cfg.p_a where cfg is a struct parameter, extract the member value
    void visit(AstMemberSel* nodep) override {
        // First iterate children to substitute any VarRefs
        iterateChildren(nodep);

        // Check if the fromp is now a PATTERN (after VarRef substitution)
        if (AstPattern* const patp = VN_CAST(nodep->fromp(), Pattern)) {
            const string& memberName = nodep->name();
            // Extract the member value from the PATTERN
            for (AstPatMember* memp = VN_CAST(patp->itemsp(), PatMember); memp;
                 memp = VN_AS(memp->nextp(), PatMember)) {
                // Check if this member matches
                string keyName;
                if (AstText* const keyTextp = VN_CAST(memp->keyp(), Text)) {
                    keyName = keyTextp->text();
                } else if (AstVarRef* const keyVrp = VN_CAST(memp->keyp(), VarRef)) {
                    keyName = keyVrp->name();
                }
                if (keyName == memberName && memp->lhssp()) {
                    // Found the member - replace MemberSel with the member value
                    AstNode* const valuep = memp->lhssp()->cloneTree(false);
                    UINFO(5, "DEPGRAPH: ParamSubstVisitor extracting member '"
                                 << memberName << "' from PATTERN" << endl);
                    nodep->replaceWith(valuep);
                    VL_DO_DANGLING(nodep->deleteTree(), nodep);
                    return;
                }
            }
        }

        // Also check for ConsPackUOrStruct (what PATTERN becomes after V3Width/V3Const)
        if (AstConsPackUOrStruct* const consp = VN_CAST(nodep->fromp(), ConsPackUOrStruct)) {
            const string& memberName = nodep->name();
            // Extract the member value from the ConsPackUOrStruct
            // membersp() is a list of AstConsPackMember
            for (AstConsPackMember* memp = consp->membersp(); memp;
                 memp = VN_AS(memp->nextp(), ConsPackMember)) {
                if (memp->name() == memberName && memp->rhsp()) {
                    // Found the member - replace MemberSel with the member value
                    AstNode* const valuep = memp->rhsp()->cloneTree(false);
                    UINFO(5, "DEPGRAPH: ParamSubstVisitor extracting member '"
                                 << memberName << "' from ConsPackUOrStruct" << endl);
                    nodep->replaceWith(valuep);
                    VL_DO_DANGLING(nodep->deleteTree(), nodep);
                    return;
                }
            }
        }
    }

    void visit(AstRefDType* nodep) override {
        // Check if this RefDType points to a typedef we have a resolved type for
        const string& name = nodep->name();
        auto it = m_typedefTypes.find(name);
        if (it != m_typedefTypes.end() && it->second) {
            // Get the resolved type
            AstNodeDType* const resolvedTypep = it->second;
            const int resolvedWidth = resolvedTypep->width();
            UINFO(5, "DEPGRAPH: ParamSubstVisitor updating RefDType '"
                         << name << "' width to " << resolvedWidth
                         << " resolvedTypep=" << cvtToHex(resolvedTypep) << " "
                         << resolvedTypep->prettyTypeName() << " typedefp="
                         << (nodep->typedefp() ? nodep->typedefp()->name() : "<null>")
                         << " refDTypep=" << cvtToHex(nodep->refDTypep()) << endl);
            // Clear typedefp so V3Width doesn't follow it to the template typedef
            nodep->typedefp(nullptr);
            // Set refDTypep to the resolved type (a clone)
            nodep->refDTypep(resolvedTypep);
            // Set the width
            if (resolvedWidth > 0) { nodep->widthForce(resolvedWidth, resolvedWidth); }
            UINFO(5, "DEPGRAPH: ParamSubstVisitor AFTER: RefDType '"
                         << name << "' typedefp="
                         << (nodep->typedefp() ? nodep->typedefp()->name() : "<null>")
                         << " refDTypep=" << cvtToHex(nodep->refDTypep())
                         << " width=" << nodep->width() << endl);
        }
        // Still iterate children
        iterateChildren(nodep);
    }

    void visit(AstMemberDType* nodep) override {
        // First iterate children to update any RefDType widths
        iterateChildren(nodep);
        // Then update member's width from its subDTypep
        if (nodep->subDTypep() && nodep->subDTypep()->width() > 0) {
            UINFO(5, "DEPGRAPH: ParamSubstVisitor updating MemberDType '"
                         << nodep->name() << "' width from " << nodep->width() << " to "
                         << nodep->subDTypep()->width() << endl);
            nodep->widthForce(nodep->subDTypep()->width(), nodep->subDTypep()->widthMin());
        }
    }

    void visit(AstAttrOf* nodep) override {
        // Handle $bits(type), $dimensions(type), etc.
        // If we have a resolved value for this ATTROF, replace the entire
        // ATTROF node with the constant value.
        // First, iterate children in case there are nested substitutions
        iterateChildren(nodep);

        // Build the key: attrType:typeName
        string typeName;
        if (nodep->fromp()) {
            if (AstRefDType* const rdtp = VN_CAST(nodep->fromp(), RefDType)) {
                typeName = rdtp->name();
            } else if (AstNodeDType* const dtypep = VN_CAST(nodep->fromp(), NodeDType)) {
                typeName = dtypep->name();
            }
        }

        if (!typeName.empty()) {
            const string key = nodep->attrType().ascii() + string(":") + typeName;
            auto it = m_attrOfValues.find(key);
            if (it != m_attrOfValues.end() && it->second) {
                AstConst* const newp = it->second->cloneTree(false);
                UINFO(5, "DEPGRAPH: ParamSubstVisitor replacing AttrOf("
                             << key << ") with CONST value=" << newp->num().toUInt() << endl);
                nodep->replaceWith(newp);
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
                return;
            }
        }
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }
};

bool V3LinkDotDepGraph::inTemplateModule(const AstNode* nodep) {
    const AstNodeModule* const modp = findOwnerModule(const_cast<AstNode*>(nodep));
    // Null owner means compilation unit - treat as template to prevent certain operations
    // (this preserves the original behavior that other code depends on)
    if (!modp) return true;
    return isTemplateModule(modp);
}

string V3LinkDotDepGraph::nodeName(const DepNode* nodep) {
    if (!nodep || !nodep->nodep) return "<null>";
    if (const AstVar* const varp = VN_CAST(nodep->nodep, Var)) return varp->name();
    if (const AstTypedef* const tdp = VN_CAST(nodep->nodep, Typedef)) return tdp->name();
    if (const AstParamTypeDType* const ptdp = VN_CAST(nodep->nodep, ParamTypeDType))
        return ptdp->name();
    if (const AstRefDType* const rdp = VN_CAST(nodep->nodep, RefDType)) return rdp->name();
    if (const AstAttrOf* const attrp = VN_CAST(nodep->nodep, AttrOf)) {
        // For ATTROF, use the attribute type name (e.g., "DIM_BITS")
        return attrp->attrType().ascii();
    }
    return nodep->nodep->typeName();
}

string V3LinkDotDepGraph::nodeOwnerName(const DepNode* nodep) {
    if (!nodep || !nodep->ownerModp) return "<null>";
    return nodep->ownerModp->name();
}

//======================================================================
// Debug: Dump dependency graph tree view

// File-scope helper for node type name (needed by static helper functions)
static const char* nodeTypeName(V3LinkDotDepGraph::NodeType type) {
    switch (type) {
    case V3LinkDotDepGraph::NodeType::GPARAM: return "GPARAM";
    case V3LinkDotDepGraph::NodeType::LPARAM: return "LPARAM";
    case V3LinkDotDepGraph::NodeType::TYPEDEF: return "TYPEDEF";
    case V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE: return "PARAMTYPE";
    case V3LinkDotDepGraph::NodeType::REFDTYPE: return "REFDTYPE";
    case V3LinkDotDepGraph::NodeType::STRUCTDTYPE: return "STRUCTDTYPE";
    case V3LinkDotDepGraph::NodeType::UNIONDTYPE: return "UNIONDTYPE";
    case V3LinkDotDepGraph::NodeType::ATTROF: return "ATTROF";
    case V3LinkDotDepGraph::NodeType::FUNC: return "FUNC";
    }
    // LCOV_EXCL_START
    UASSERT(false, "nodeTypeName: unhandled NodeType");
    return "?";  // Unreachable
    // LCOV_EXCL_STOP
}

void V3LinkDotDepGraph::dumpGraph(const char* stageName) {
    if (!debug()) return;

    UINFO(3, "DEPGRAPH: \n");
    UINFO(3, "DEPGRAPH: ========== DUMP: " << stageName << " ==========" << endl);
    UINFO(3, "DEPGRAPH: Total nodes: " << s_allNodes.size() << endl);
    UINFO(3, "DEPGRAPH: \n");

    // Group nodes by owner module for cleaner output
    std::map<string, std::vector<DepNode*>> nodesByModule;
    for (DepNode* nodep : s_allNodes) {
        if (!nodep) continue;
        const string ownerName = nodep->ownerModp ? nodep->ownerModp->name() : "<global>";
        nodesByModule[ownerName].push_back(nodep);
    }

    for (const auto& pair : nodesByModule) {
        UINFO(3, "DEPGRAPH: --- Module: " << pair.first << " (" << pair.second.size()
                                          << " nodes) ---" << endl);
        for (DepNode* nodep : pair.second) {
            // Node identity
            UINFO(3, "DEPGRAPH:   [" << nodeTypeName(nodep->nodeType) << "] " << nodeName(nodep)
                                     << endl);

            // Initial state (inputs from AST at build time)
            UINFO(3, "DEPGRAPH:     initial: width=" << nodep->initialWidth);
            if (nodep->initialValuep) { UINFO(3, " valuep=" << nodep->initialValuep); }
            if (nodep->initialTypep) { UINFO(3, " typep=" << nodep->initialTypep); }
            UINFO(3, endl);

            // Resolved state (outputs after execution)
            UINFO(3, "DEPGRAPH:     resolved: " << (nodep->resolved ? "YES" : "NO")
                                                << " width=" << nodep->resolvedWidth);
            if (nodep->resolvedTypep) { UINFO(3, " typep=" << nodep->resolvedTypep); }
            if (nodep->resolvedValuep) { UINFO(3, " valuep=" << nodep->resolvedValuep); }
            UINFO(3, endl);

            // Execution state
            UINFO(3, "DEPGRAPH:     exec: pendingDeps=" << nodep->pendingDeps << " iteration="
                                                        << nodep->resolvedIteration << endl);

            // Dependencies (inputs - what this node reads from)
            if (!nodep->dependsOn.empty()) {
                UINFO(3, "DEPGRAPH:     dependsOn (" << nodep->dependsOn.size() << "):" << endl);
                for (DepNode* const depp : nodep->dependsOn) {
                    if (!depp) continue;
                    UINFO(3, "DEPGRAPH:       <- [" << nodeTypeName(depp->nodeType) << "] "
                                                    << nodeName(depp) << "@" << nodeOwnerName(depp)
                                                    << " resolved=" << (depp->resolved ? "Y" : "N")
                                                    << " width=" << depp->resolvedWidth << endl);
                }
            }

            // Dependents (outputs - what nodes read from this)
            if (!nodep->dependents.empty()) {
                UINFO(3, "DEPGRAPH:     dependents (" << nodep->dependents.size() << "):" << endl);
                for (DepNode* const depp : nodep->dependents) {
                    if (!depp) continue;
                    UINFO(3, "DEPGRAPH:       -> [" << nodeTypeName(depp->nodeType) << "] "
                                                    << nodeName(depp) << "@" << nodeOwnerName(depp)
                                                    << " pending=" << depp->pendingDeps << endl);
                }
            }
        }
        UINFO(3, "DEPGRAPH: \n");
    }

    // Summary statistics
    int resolvedCount = 0;
    int unresolvedCount = 0;
    int readyCount = 0;
    for (DepNode* nodep : s_allNodes) {
        if (!nodep) continue;
        if (nodep->resolved) {
            ++resolvedCount;
        } else {
            ++unresolvedCount;
            if (nodep->pendingDeps == 0) ++readyCount;
        }
    }
    UINFO(3, "DEPGRAPH: Summary: resolved=" << resolvedCount << " unresolved=" << unresolvedCount
                                            << " ready=" << readyCount << endl);
    UINFO(3, "DEPGRAPH: ========== END DUMP ==========" << endl);
    UINFO(3, "DEPGRAPH: \n");
}

// Helper for dumpGraphDepsTree - recursively print dependency tree
// visited: tracks current path for cycle detection (cleared when backtracking)
// printedLines: maps nodes to the line number where they were first printed
// lineNum: current line number counter (passed by reference to track across calls)
static void dumpDepsTreeNode(V3LinkDotDepGraph::DepNode* nodep, const string& prefix, bool isLast,
                             std::set<V3LinkDotDepGraph::DepNode*>& visited,
                             std::map<V3LinkDotDepGraph::DepNode*, int>& printedLines,
                             int& lineNum) {
    if (!nodep) return;

    // Check if this node was already printed in another branch (converging paths)
    const auto it = printedLines.find(nodep);
    const bool alreadyPrinted = (it != printedLines.end());
    string convergeAnnotation;
    if (alreadyPrinted) { convergeAnnotation = " (see line #" + std::to_string(it->second) + ")"; }

    // Record current line number for this node
    const int thisLine = ++lineNum;

    // Print this node with cellPath qualifier if present
    const string connector = isLast ? "+-- " : "|-- ";
    const string cellQualifier = nodep->cellPath.empty() ? "" : ("[" + nodep->cellPath + "]");
    const string addrStr = nodep->nodep ? (" <" + AstNode::nodeAddr(nodep->nodep) + ">") : "";
    UINFO(3, "DEPGRAPH: " << std::setw(4) << thisLine << ": " << prefix << connector << "["
                          << nodeTypeName(nodep->nodeType) << "] "
                          << V3LinkDotDepGraph::nodeName(nodep) << "@"
                          << V3LinkDotDepGraph::nodeOwnerName(nodep) << addrStr << cellQualifier
                          << " (pending=" << nodep->pendingDeps << " resolved="
                          << (nodep->resolved ? "Y" : "N") << " width=" << nodep->resolvedWidth
                          << ")" << convergeAnnotation << endl);

    // If already printed, don't repeat the subtree
    if (alreadyPrinted) return;

    // Check for cycles (node in current path)
    if (visited.count(nodep)) {
        ++lineNum;
        UINFO(3, "DEPGRAPH: " << std::setw(4) << lineNum << ": " << prefix
                              << (isLast ? "    " : "|   ") << "+-- (cycle)" << endl);
        return;
    }
    visited.insert(nodep);

    // Print dependencies (what this node depends on)
    const string childPrefix = prefix + (isLast ? "    " : "|   ");
    std::vector<V3LinkDotDepGraph::DepNode*> deps(nodep->dependsOn.begin(),
                                                  nodep->dependsOn.end());
    for (size_t i = 0; i < deps.size(); ++i) {
        dumpDepsTreeNode(deps[i], childPrefix, i == deps.size() - 1, visited, printedLines,
                         lineNum);
    }

    visited.erase(nodep);
    printedLines[nodep] = thisLine;  // Record line number where this node was printed
}

void V3LinkDotDepGraph::dumpGraphDepsTree(const char* stageName) {
    if (!debug()) return;

    UINFO(3, "DEPGRAPH: \n");
    UINFO(3, "DEPGRAPH: ========== DEPS TREE: " << stageName << " ==========" << endl);
    UINFO(3, "DEPGRAPH: (shows what each node DEPENDS ON - arrows point to dependencies)" << endl);
    UINFO(3, "DEPGRAPH: \n");

    // Find root nodes (nodes with dependents but no one depends on them, i.e., leaf consumers)
    // Actually, for a "what depends on what" tree, we want to start from nodes that
    // have dependents (are depended upon) - these are the "roots" of the dependency tree
    std::set<DepNode*> rootNodes;
    for (DepNode* nodep : s_allNodes) {
        if (!nodep) continue;
        // A root is a node with no dependsOn (boundary condition)
        if (nodep->dependsOn.empty()) { rootNodes.insert(nodep); }
    }

    UINFO(3, "DEPGRAPH: Boundary nodes (no dependencies - ready to execute):" << endl);
    for (DepNode* rootp : rootNodes) {
        const string cellQualifier = rootp->cellPath.empty() ? "" : ("[" + rootp->cellPath + "]");
        UINFO(3, "DEPGRAPH:   [" << nodeTypeName(rootp->nodeType) << "] " << nodeName(rootp) << "@"
                                 << nodeOwnerName(rootp) << cellQualifier << endl);
    }
    UINFO(3, "DEPGRAPH: \n");

    // Now print the tree from each leaf node (nodes with no dependents)
    UINFO(3, "DEPGRAPH: Dependency chains (leaf -> ... -> root):" << endl);
    std::map<DepNode*, int> printedLines;  // Track nodes and their line numbers
    int lineNum = 0;
    for (DepNode* nodep : s_allNodes) {
        if (!nodep) continue;
        // Leaf nodes have no dependents (nothing depends on them)
        if (nodep->dependents.empty() && !nodep->dependsOn.empty()) {
            std::set<DepNode*> visited;
            dumpDepsTreeNode(nodep, "", true, visited, printedLines, lineNum);
            UINFO(3, "DEPGRAPH: \n");
        }
    }

    UINFO(3, "DEPGRAPH: ========== END DEPS TREE ==========" << endl);
    UINFO(3, "DEPGRAPH: \n");
}

// Helper to format resolved value for display
static string formatResolvedValue(V3LinkDotDepGraph::DepNode* nodep) {
    if (!nodep->resolved) return "";
    std::ostringstream oss;
    // Show width for types/dtypes
    if (nodep->resolvedWidth > 0) { oss << " width=" << nodep->resolvedWidth; }
    // Show value for parameters
    if (nodep->resolvedValuep) {
        if (AstConst* const constp = VN_CAST(nodep->resolvedValuep, Const)) {
            if (constp->num().isFourState()) {
                oss << " val=4'state";
            } else if (constp->num().isString()) {
                oss << " val=\"" << constp->num().toString() << "\"";
            } else {
                oss << " val=" << constp->num().toUInt();
            }
        } else {
            // Show the node type for non-const expressions (e.g., PATTERN for structs)
            oss << " val=<" << nodep->resolvedValuep->typeName() << ">";
        }
    }
    // Show type for type parameters
    if (nodep->resolvedTypep) { oss << " type=" << nodep->resolvedTypep->prettyTypeName(); }
    return oss.str();
}

// Helper for dumpGraphDependentsTree - recursively print dependents tree (reverse direction)
// visited: tracks current path for cycle detection (cleared when backtracking)
// printedLines: maps nodes to the line number where they were first printed
// lineNum: current line number counter (passed by reference to track across calls)
static void dumpDependentsTreeNode(V3LinkDotDepGraph::DepNode* nodep, const string& prefix,
                                   bool isLast, std::set<V3LinkDotDepGraph::DepNode*>& visited,
                                   std::map<V3LinkDotDepGraph::DepNode*, int>& printedLines,
                                   int& lineNum) {
    if (!nodep) return;

    // Check if this node was already printed in another branch (converging paths)
    const auto it = printedLines.find(nodep);
    const bool alreadyPrinted = (it != printedLines.end());
    string convergeAnnotation;
    if (alreadyPrinted) { convergeAnnotation = " (see line #" + std::to_string(it->second) + ")"; }

    // Record current line number for this node
    const int thisLine = ++lineNum;

    // Print this node with cellPath qualifier if present
    const string connector = isLast ? "+-- " : "|-- ";
    const string cellQualifier = nodep->cellPath.empty() ? "" : ("[" + nodep->cellPath + "]");
    const string resolvedInfo = formatResolvedValue(nodep);
    UINFO(3, "DEPGRAPH: " << std::setw(4) << thisLine << ": " << prefix << connector << "["
                          << nodeTypeName(nodep->nodeType) << "] "
                          << V3LinkDotDepGraph::nodeName(nodep) << "@"
                          << V3LinkDotDepGraph::nodeOwnerName(nodep) << cellQualifier
                          << " (pending=" << nodep->pendingDeps
                          << " resolved=" << (nodep->resolved ? "Y" : "N") << resolvedInfo << ")"
                          << convergeAnnotation << endl);

    // If already printed, don't repeat the subtree
    if (alreadyPrinted) return;

    // Check for cycles (node in current path)
    if (visited.count(nodep)) {
        ++lineNum;
        UINFO(3, "DEPGRAPH: " << std::setw(4) << lineNum << ": " << prefix
                              << (isLast ? "    " : "|   ") << "+-- (cycle)" << endl);
        return;
    }
    visited.insert(nodep);

    // Print dependents (what depends on this node) - reverse direction
    const string childPrefix = prefix + (isLast ? "    " : "|   ");
    std::vector<V3LinkDotDepGraph::DepNode*> deps(nodep->dependents.begin(),
                                                  nodep->dependents.end());
    for (size_t i = 0; i < deps.size(); ++i) {
        dumpDependentsTreeNode(deps[i], childPrefix, i == deps.size() - 1, visited, printedLines,
                               lineNum);
    }

    visited.erase(nodep);
    printedLines[nodep] = thisLine;  // Record line number where this node was printed
}

void V3LinkDotDepGraph::dumpGraphDependentsTree(const char* stageName) {
    if (!debug()) return;

    UINFO(3, "DEPGRAPH: \n");
    UINFO(3, "DEPGRAPH: ========== DEPENDENTS TREE: " << stageName << " ==========" << endl);
    UINFO(3, "DEPGRAPH: (shows what DEPENDS ON each node - execution order view)" << endl);
    UINFO(3, "DEPGRAPH: \n");

    // Find leaf nodes (nodes with no dependents - final consumers)
    std::set<DepNode*> leafNodes;
    for (DepNode* nodep : s_allNodes) {
        if (!nodep) continue;
        if (nodep->dependents.empty()) { leafNodes.insert(nodep); }
    }

    UINFO(3, "DEPGRAPH: Leaf nodes (no dependents - final consumers):" << endl);
    for (DepNode* leafp : leafNodes) {
        UINFO(3, "DEPGRAPH:   [" << nodeTypeName(leafp->nodeType) << "] " << nodeName(leafp) << "@"
                                 << nodeOwnerName(leafp)
                                 << (leafp->cellPath.empty() ? "" : "[" + leafp->cellPath + "]")
                                 << endl);
    }
    UINFO(3, "DEPGRAPH: \n");

    // Print the tree from each root node (nodes with no dependencies - boundary conditions)
    UINFO(3, "DEPGRAPH: Execution chains (root -> ... -> leaf):" << endl);
    std::map<DepNode*, int> printedLines;  // Track nodes and their line numbers
    int lineNum = 0;
    for (DepNode* nodep : s_allNodes) {
        if (!nodep) continue;
        // Root nodes have no dependencies (boundary conditions)
        if (nodep->dependsOn.empty() && !nodep->dependents.empty()) {
            std::set<DepNode*> visited;
            dumpDependentsTreeNode(nodep, "", true, visited, printedLines, lineNum);
            UINFO(3, "DEPGRAPH: \n");
        }
    }

    UINFO(3, "DEPGRAPH: ========== END DEPENDENTS TREE ==========" << endl);
    UINFO(3, "DEPGRAPH: \n");
}

static AstIfaceRefDType* findIfaceRefDType(AstNodeDType* dtypep) {
    if (!dtypep) return nullptr;
    if (AstIfaceRefDType* const ifaceRefp = VN_CAST(dtypep, IfaceRefDType)) return ifaceRefp;
    if (AstIfaceRefDType* const ifaceRefp = VN_CAST(dtypep->skipRefp(), IfaceRefDType))
        return ifaceRefp;
    if (AstNodeDType* const subp = dtypep->subDTypep()) {
        if (AstIfaceRefDType* const ifaceRefp = findIfaceRefDType(subp)) return ifaceRefp;
    }
    return nullptr;
}

static AstNodeModule* findConnectedIfaceModpFromPort(AstNodeModule* modp, const string& portName) {
    if (!modp || portName.empty()) return nullptr;
    AstNetlist* const rootp = v3Global.rootp();
    if (!rootp) return nullptr;
    for (AstNodeModule* topmodp = rootp->modulesp(); topmodp;
         topmodp = VN_AS(topmodp->nextp(), NodeModule)) {
        for (AstNode* stmtp = topmodp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            AstCell* const cellp = VN_CAST(stmtp, Cell);
            if (!cellp || cellp->modp() != modp) continue;
            for (AstPin* pinp = cellp->pinsp(); pinp; pinp = VN_CAST(pinp->nextp(), Pin)) {
                AstVar* const modVarp = pinp->modVarp();
                if (!modVarp || modVarp->name() != portName) continue;
                AstNode* exprp = pinp->exprp();
                if (!exprp) continue;
                while (AstNodePreSel* const preSelp = VN_CAST(exprp, NodePreSel))
                    exprp = preSelp->fromp();
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

// Find connected interface cell name and parent cellPath for an interface port
// Returns true if found, with connectedCellName and parentCellPath set
static bool findConnectedIfaceCellPath(AstNodeModule* modp, const string& portName,
                                       const string& currentCellPath, string& connectedCellName,
                                       string& parentCellPath) {
    if (!modp || portName.empty() || currentCellPath.empty()) return false;
    // Get parent cellPath by removing last component
    const size_t lastDot = currentCellPath.rfind('.');
    if (lastDot == string::npos) return false;
    parentCellPath = currentCellPath.substr(0, lastDot);
    const string cellInstanceName = currentCellPath.substr(lastDot + 1);

    AstNetlist* const rootp = v3Global.rootp();
    if (!rootp) return false;
    for (AstNodeModule* topmodp = rootp->modulesp(); topmodp;
         topmodp = VN_AS(topmodp->nextp(), NodeModule)) {
        for (AstNode* stmtp = topmodp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            AstCell* const cellp = VN_CAST(stmtp, Cell);
            if (!cellp || cellp->modp() != modp) continue;
            if (cellp->name() != cellInstanceName) continue;
            for (AstPin* pinp = cellp->pinsp(); pinp; pinp = VN_CAST(pinp->nextp(), Pin)) {
                AstVar* const modVarp = pinp->modVarp();
                if (!modVarp || modVarp->name() != portName) continue;
                AstNode* exprp = pinp->exprp();
                if (!exprp) continue;
                while (AstNodePreSel* const preSelp = VN_CAST(exprp, NodePreSel))
                    exprp = preSelp->fromp();
                if (AstVarRef* const varRefp = VN_CAST(exprp, VarRef)) {
                    connectedCellName = varRefp->name();
                    // Strip __Viftop suffix if present
                    const size_t viftopPos = connectedCellName.find("__Viftop");
                    if (viftopPos != string::npos)
                        connectedCellName = connectedCellName.substr(0, viftopPos);
                    return true;
                }
            }
        }
    }
    return false;
}

// Resolve a cellPath (potentially with dots) to a module, traversing interface ports
static AstNodeModule* resolveCellPathModule(AstNodeModule* modp, const string& cellPath) {
    if (!modp) return nullptr;

    AstNodeModule* curModp = modp;
    size_t start = 0;
    while (start < cellPath.size()) {
        const size_t dotPos = cellPath.find('.', start);
        const string seg = (dotPos == string::npos) ? cellPath.substr(start)
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
                if (AstNodeModule* const connected
                    = findConnectedIfaceModpFromPort(curModp, seg)) {
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

const char* V3LinkDotDepGraph::nodeTypeName(NodeType type) {
    switch (type) {
    case NodeType::GPARAM: return "GPARAM";
    case NodeType::LPARAM: return "LPARAM";
    case NodeType::TYPEDEF: return "TYPEDEF";
    case NodeType::PARAMTYPEDTYPE: return "PARAMTYPE";
    case NodeType::REFDTYPE: return "REFDTYPE";
    case NodeType::STRUCTDTYPE: return "STRUCTDTYPE";
    case NodeType::UNIONDTYPE: return "UNIONDTYPE";
    case NodeType::ATTROF: return "ATTROF";
    case NodeType::FUNC: return "FUNC";
    }
    // LCOV_EXCL_START
    UASSERT(false, "nodeTypeName: unhandled NodeType");
    return "?";  // Unreachable
    // LCOV_EXCL_STOP
}

V3LinkDotDepGraph::NodeType V3LinkDotDepGraph::classifyVar(const AstVar* varp) {
    UASSERT(varp, "classifyVar called with null varp");
    if (varp->isGParam()) return NodeType::GPARAM;
    if (varp->isParam()) return NodeType::LPARAM;
    // Non-parameter variables should not be classified - caller should check first
    UASSERT_OBJ(false, varp,
                "classifyVar called on non-parameter variable '" << varp->name() << "'");
    return NodeType::GPARAM;  // Unreachable, but needed for compiler
}

//======================================================================
// Helper to normalize cellNames by stripping __BRA__??__KET__ placeholder
// This is needed because interface arrays like subA_io[0] are registered
// with __BRA__??__KET__ before the index is resolved, but all array elements
// share the same type definition, so we use the base cell name for lookup.

static string normalizeCellName(const string& cellName) {
    const size_t pos = cellName.find("__BRA__??__KET__");
    if (pos != string::npos) { return cellName.substr(0, pos); }
    return cellName;
}

//======================================================================
// Graph management

void V3LinkDotDepGraph::reset() {
    UINFO(5, "DEPGRAPH: reset() called, clearing graph nodes (keeping "
                 << s_cellAssociations.size() << " cell associations, "
                 << s_refDTypeDotPathRegistry.size() << " refdtype dotpath registrations)"
                 << endl);
    for (DepNode* nodep : s_allNodes) {
        if (nodep) {
            // Clean up cloned initial state
            if (nodep->initialValuep) {
                nodep->initialValuep->deleteTree();
                nodep->initialValuep = nullptr;
            }
            if (nodep->initialTypep) {
                nodep->initialTypep->deleteTree();
                nodep->initialTypep = nullptr;
            }
        }
        delete nodep;
    }
    s_allNodes.clear();
    s_nodes.clear();
    // Note: Do NOT clear s_cellAssociations here - they are captured during linkdot primary
    // and need to persist until graph building which happens later
    // Note: Do NOT clear s_refDTypeDotPathRegistry here - populated during linkdot primary
    // and needed during graph build which occurs later.
    // Note: Do NOT clear s_refDTypeScopedTypedefs here - populated during linkdot primary
    // and needed during graph build which occurs later.
    // Note: s_clonedTypes should already be empty (cleaned up by cleanupClonedTypes)
    // but clear it here for safety in case reset() is called without cleanup
    s_clonedTypes.clear();
    s_iterationCount = 0;
    s_builtModules.clear();
    s_parameterizedModules.clear();
}

void V3LinkDotDepGraph::resetAll() {
    reset();
    s_cellAssociations.clear();
    s_refDTypeDotPathRegistry.clear();
    s_refDTypeScopedTypedefs.clear();
    s_typedefScopedTypedefs.clear();
}

void V3LinkDotDepGraph::registerRefDTypeDotPath(AstRefDType* refp, const string& cellName,
                                                AstNodeModule* contextModp) {
    UASSERT(refp, "registerRefDTypeDotPath called with null refdtype");
    UASSERT_OBJ(!cellName.empty(), refp,
                "registerRefDTypeDotPath called with empty cellName for '" << refp->name() << "'");
    auto it = s_refDTypeDotPathRegistry.find(refp);
    if (it != s_refDTypeDotPathRegistry.end()) {
        UASSERT_OBJ(it->second == cellName, refp,
                    "Duplicate refdtype dotpath registry for '"
                        << refp->name() << "' in "
                        << (contextModp ? contextModp->name() : "<unknown>") << " old='"
                        << it->second << "' new='" << cellName << "'");
        return;
    }
    s_refDTypeDotPathRegistry.emplace(refp, cellName);
    UINFO(5, "DEPGRAPH: registered refdtype dotpath '"
                 << cellName << "' for '" << refp->name() << "' in "
                 << (contextModp ? contextModp->name() : "<unknown>") << " ptr=" << cvtToHex(refp)
                 << endl);
}

void V3LinkDotDepGraph::registerRefDTypeScopedTypedef(AstRefDType* refp, AstTypedef* tdp) {
    UASSERT(refp, "registerRefDTypeScopedTypedef called with null refdtype");
    UASSERT(tdp,
            "registerRefDTypeScopedTypedef called with null typedef for '" << refp->name() << "'");
    s_refDTypeScopedTypedefs[refp] = tdp;
    UINFO(5, "DEPGRAPH: registered refdtype scoped typedef '" << refp->name() << "' -> '"
                                                              << tdp->name() << "'" << endl);
}

void V3LinkDotDepGraph::registerTypedefScopedTypedef(AstTypedef* typedefp, AstTypedef* scopedp) {
    UASSERT(typedefp, "registerTypedefScopedTypedef called with null typedef");
    UASSERT(scopedp, "registerTypedefScopedTypedef called with null scoped typedef for '"
                         << typedefp->name() << "'");
    s_typedefScopedTypedefs[typedefp] = scopedp;
    UINFO(5, "DEPGRAPH: registered typedef scoped typedef '" << typedefp->name() << "' -> '"
                                                             << scopedp->name() << "'" << endl);
}

void V3LinkDotDepGraph::registerCellAssociation(const string& portPath,
                                                const string& ifaceCellPath) {
    UINFO(5, "DEPGRAPH: register cell assoc portPath='" << portPath << "' -> ifaceCellPath='"
                                                        << ifaceCellPath << "'" << endl);
    UASSERT(!portPath.empty(), "registerCellAssociation called with empty portPath");
    UASSERT(!ifaceCellPath.empty(), "registerCellAssociation called with empty ifaceCellPath");
    s_cellAssociations[portPath] = ifaceCellPath;
}

void V3LinkDotDepGraph::registerIfaceTypedefContext(
    AstRefDType* refp, const char* stageLabel, int dotPos, bool dotIsFinal,
    const std::string& dotText, VSymEnt* dotSymp, VSymEnt* curSymp, AstNodeModule* modp,
    AstNode* nodep, const std::function<bool(AstVar*, AstRefDType*)>& promoteVarCb,
    const std::function<std::string()>& indentFn) {

    if (!refp) return;

    // Single check: is this an interface cell reference?
    AstCell* ifaceCellp = nullptr;
    if (dotSymp && VN_IS(dotSymp->nodep(), Cell)) {
        AstCell* const cellp = VN_AS(dotSymp->nodep(), Cell);
        if (cellp->modp() && VN_IS(cellp->modp(), Iface)) { ifaceCellp = cellp; }
    }

    // Determine the cell name for DepGraph registration
    // Use dotText (the identifier text) instead of cellp->name() because
    // cellp may be shared between template modules and have wrong name
    string cellName;
    if (ifaceCellp) {
        cellName = dotText.empty() ? ifaceCellp->name() : dotText;
    } else if (!dotText.empty()) {
        cellName = dotText;
    }

    // Register with DepGraph if we have a cell name
    if (enabled() && !cellName.empty()) {
        UINFO(5, indentFn() << "DEPGRAPH: registerIfaceTypedefContext " << stageLabel
                            << ": refp=" << cvtToHex(refp) << " cellName=" << cellName
                            << " ifaceCellp=" << (ifaceCellp ? cvtToHex(ifaceCellp) : "<null>")
                            << " mod=" << (modp ? modp->name() : "<null>") << "\n");
        registerRefDTypeDotPath(refp, cellName, modp);
    }

    // Register with IfaceCapture (it has its own enabled check internally)
    V3LinkDotIfaceCapture::captureTypedefContext(refp, stageLabel, dotPos, dotIsFinal, dotText,
                                                 dotSymp, curSymp, modp, nodep, promoteVarCb,
                                                 indentFn);
}

const V3LinkDotDepGraph::DepNode* V3LinkDotDepGraph::find(AstNode* nodep, const string& cellPath) {
    const NodeKey key{nodep, cellPath};
    const auto it = s_nodes.find(key);
    if (it == s_nodes.end()) return nullptr;
    return it->second;
}

V3LinkDotDepGraph::DepNode* V3LinkDotDepGraph::findMutable(AstNode* nodep,
                                                           const string& cellPath) {
    const NodeKey key{nodep, cellPath};
    const auto it = s_nodes.find(key);
    if (it == s_nodes.end()) return nullptr;
    return it->second;
}

AstTypedef* V3LinkDotDepGraph::findSpecializedTypedef(const std::string& name,
                                                      AstNodeModule** ownerp) {
    for (DepNode* const candNodep : s_allNodes) {
        if (!candNodep || candNodep->nodeType != NodeType::TYPEDEF) continue;
        AstTypedef* const candTdp = VN_CAST(candNodep->nodep, Typedef);
        if (!candTdp || candTdp->name() != name) continue;
        if (isSpecializedModule(candNodep->ownerModp)) {
            if (ownerp) *ownerp = candNodep->ownerModp;
            return candTdp;
        }
    }
    return nullptr;
}

V3LinkDotDepGraph::DepNode* V3LinkDotDepGraph::findOrCreateNode(AstNode* nodep, NodeType type,
                                                                AstNodeModule* ownerModp,
                                                                const string& cellPath) {
    if (!nodep) return nullptr;
    const NodeKey key{nodep, cellPath};
    auto it = s_nodes.find(key);
    if (it != s_nodes.end()) return it->second;

    if (type == NodeType::PARAMTYPEDTYPE) {
        UASSERT_OBJ(ownerModp, nodep,
                    "DEPGRAPH: PARAMTYPEDTYPE node created with null owner module");
        // For PARAMTYPEDTYPE, check if a node with the same name and owner already exists
        // This handles the case where captureParamExpr creates a node before build() runs
        // with a different AST pointer but the same logical identity
        if (AstParamTypeDType* const ptdp = VN_CAST(nodep, ParamTypeDType)) {
            DepNode* existingp = findByNameAndOwner(ptdp->name(), ownerModp, type, cellPath);
            if (existingp) {
                // Register this AST pointer to map to the existing node
                s_nodes[key] = existingp;
                UINFO(5, "DEPGRAPH: PARAMTYPEDTYPE '"
                             << ptdp->name() << "' reusing existing node in " << ownerModp->name()
                             << " cellPath='" << cellPath << "'" << endl);
                return existingp;
            }
        }
    }

    DepNode* const depNodep = new DepNode;
    depNodep->nodep = nodep;
    depNodep->nodeType = type;
    depNodep->ownerModp = ownerModp;
    depNodep->cellPath = cellPath;

    // Track parameterized modules: any module with a cell-context DepNode
    // (non-empty cellPath) is instantiated with specific parameter values
    // and will be cloned by V3Param.
    if (!cellPath.empty() && ownerModp) {
        const bool inserted = s_parameterizedModules.insert(ownerModp).second;
        UINFO(9, "DEPGRAPH: parameterized-mark "
                     << (inserted ? "insert" : "seen") << " mod='" << ownerModp->name() << "'"
                     << " someInstanceName='" << ownerModp->someInstanceName() << "'"
                     << " cellPath='" << cellPath << "'" << " nodeType=" << static_cast<int>(type)
                     << endl);
    }

    // Capture initial width from AST during build phase
    // This is the only time we read from AST - resolution uses only DepNode state
    switch (type) {
    case NodeType::TYPEDEF: {
        AstTypedef* const tdp = VN_CAST(nodep, Typedef);
        if (tdp && tdp->subDTypep()) depNodep->initialWidth = tdp->subDTypep()->width();
        break;
    }
    case NodeType::PARAMTYPEDTYPE: {
        AstParamTypeDType* const ptdp = VN_CAST(nodep, ParamTypeDType);
        if (ptdp) {
            if (ptdp->dtypep())
                depNodep->initialWidth = ptdp->dtypep()->width();
            else if (ptdp->subDTypep())
                depNodep->initialWidth = ptdp->subDTypep()->width();
        }
        break;
    }
    case NodeType::REFDTYPE: {
        AstRefDType* const rdp = VN_CAST(nodep, RefDType);
        if (rdp) depNodep->initialWidth = rdp->width();
        break;
    }
    case NodeType::STRUCTDTYPE:
    case NodeType::UNIONDTYPE: {
        AstNodeUOrStructDType* const usp = VN_CAST(nodep, NodeUOrStructDType);
        if (usp) depNodep->initialWidth = usp->width();
        break;
    }
    case NodeType::GPARAM:
    case NodeType::LPARAM: {
        AstVar* const varp = VN_CAST(nodep, Var);
        if (varp) {
            depNodep->initialWidth = varp->width();
            // Capture default value from AST - this is the "boundary condition" for ready nodes
            // Two scenarios:
            //   1. Constant override - captured later via captureParamExpr()
            //   2. Default value - captured here from varp->valuep()
            // Ready nodes (pendingDeps=0) use these initial values to seed graph execution
            if (varp->valuep() && !depNodep->initialValuep) {
                depNodep->initialValuep = varp->valuep()->cloneTree(false);
                if (AstConst* const constp = VN_CAST(varp->valuep(), Const)) {
                    depNodep->initialWidth = constp->width();
                    UINFO(5, "DEPGRAPH: captured default const width="
                                 << constp->width() << " for param '" << varp->name() << "'"
                                 << endl);
                }
            }
        }
        break;
    }
    case NodeType::ATTROF:
        // ATTROF nodes ($bits, etc.) have no initial width - computed during resolution
        break;
    case NodeType::FUNC:
        // FUNC nodes have no initial width - they track return type dependencies
        break;
    }

    s_nodes[key] = depNodep;
    s_allNodes.push_back(depNodep);

    UINFO(9, "DEPGRAPH: created " << nodeTypeName(type) << " node '" << nodeName(depNodep)
                                  << "' owner=" << nodeOwnerName(depNodep) << " cellPath='"
                                  << cellPath << "'" << " initialWidth=" << depNodep->initialWidth
                                  << endl);

    // Extra debug for PARAMTYPE nodes to trace template node creation
    if (type == NodeType::PARAMTYPEDTYPE && cellPath.empty()) {
        UINFO(5, "DEPGRAPH: WARNING: Created PARAMTYPE '"
                     << nodeName(depNodep)
                     << "' with EMPTY cellPath (template node) - check call stack" << endl);
        v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("paramtype_template_debug"));
    }

    // For REFDTYPE nodes, look up cellName from the registry
    if (type == NodeType::REFDTYPE) {
        if (AstRefDType* const rdp = VN_CAST(nodep, RefDType)) {
            const auto regIt = s_refDTypeDotPathRegistry.find(rdp);
            if (regIt != s_refDTypeDotPathRegistry.end()) {
                depNodep->cellName = regIt->second;
                UINFO(5, "DEPGRAPH: REFDTYPE '" << rdp->name() << "' cellName='"
                                                << depNodep->cellName << "' from registry in "
                                                << (ownerModp ? ownerModp->name() : "<unknown>")
                                                << endl);
            } else if (AstRefDType* const origRefp = rdp->clonep()) {
                const auto origIt = s_refDTypeDotPathRegistry.find(origRefp);
                if (origIt != s_refDTypeDotPathRegistry.end()) {
                    depNodep->cellName = origIt->second;
                    UINFO(5, "DEPGRAPH: REFDTYPE '"
                                 << rdp->name() << "' cellName='" << depNodep->cellName
                                 << "' inherited from clone in "
                                 << (ownerModp ? ownerModp->name() : "<unknown>") << endl);
                }
            }
        }
    }
    return depNodep;
}

V3LinkDotDepGraph::DepNode* V3LinkDotDepGraph::findByNameAndOwner(const string& name,
                                                                  AstNodeModule* ownerModp,
                                                                  NodeType type,
                                                                  const string& cellPath) {
    // Search for an existing node with the given name, owner, type, and cellPath
    for (DepNode* const nodep : s_allNodes) {
        if (!nodep || nodep->nodeType != type) continue;
        if (nodep->ownerModp != ownerModp) continue;
        if (nodep->cellPath != cellPath) continue;
        if (nodeName(nodep) == name) return nodep;
    }
    return nullptr;
}

void V3LinkDotDepGraph::addEdge(DepNode* from, DepNode* to) {
    UASSERT(from, "addEdge called with null 'from' node");
    UASSERT(to, "addEdge called with null 'to' node");
    if (from == to) {
        UINFO(5, "DEPGRAPH: skip self-edge '"
                     << nodeName(from) << "'@" << nodeOwnerName(from)
                     << " type=" << nodeTypeName(from->nodeType)
                     << " nodep=" << (from->nodep ? cvtToHex(from->nodep) : "<nullptr>") << endl);
        return;
    }
    // Check if this is a new edge (not already present)
    const bool isNewEdge = (from->dependsOn.find(to) == from->dependsOn.end());
    from->dependsOn.insert(to);
    to->dependents.insert(from);
    // If adding a new edge and the target isn't resolved, increment pendingDeps
    // This ensures nodes added after build() still have correct dependency counts
    if (isNewEdge && !to->resolved) {
        ++from->pendingDeps;
        UINFO(5, "DEPGRAPH: addEdge incremented pendingDeps for '"
                     << nodeName(from) << "'@" << nodeOwnerName(from) << " = " << from->pendingDeps
                     << endl);
    }
    UINFO(9, "DEPGRAPH: edge '" << nodeName(from) << "'@" << nodeOwnerName(from)
                                << " type=" << nodeTypeName(from->nodeType)
                                << " nodep=" << (from->nodep ? cvtToHex(from->nodep) : "<nullptr>")
                                << " --> '" << nodeName(to) << "'@" << nodeOwnerName(to)
                                << " type=" << nodeTypeName(to->nodeType) << " nodep="
                                << (to->nodep ? cvtToHex(to->nodep) : "<nullptr>") << endl);
    if (from->nodeType == NodeType::PARAMTYPEDTYPE
        && (to->nodeType == NodeType::PARAMTYPEDTYPE || to->nodeType == NodeType::TYPEDEF)) {
        UINFO(5, "DEPGRAPH: paramtype edge '"
                     << nodeName(from) << "'@" << nodeOwnerName(from) << " cell='"
                     << from->cellName << "' -> '" << nodeName(to) << "'@" << nodeOwnerName(to)
                     << " type=" << nodeTypeName(to->nodeType) << " cell='" << to->cellName << "'"
                     << endl);
    }
}

//======================================================================
// Graph building

// Visitor to collect variable references in an expression
class DepExprVisitor final : public VNVisitorConst {
private:
    V3LinkDotDepGraph::DepNode* m_depNode;
    string m_cellPathOverride;  // Override cellPath for pin expressions (use parent's context)
    bool m_hasCellPathOverride = false;  // True if cellPathOverride was explicitly provided

    // Get the effective cellPath - use override if set, else depNode's cellPath
    // IMPORTANT: For cross-module references (e.g., nested interface referencing parent's param),
    // the caller MUST provide cellPathOverride. Returning empty string for cross-module refs
    // creates template nodes that cause incorrect dependency resolution.
    string effectiveCellPath(AstNodeModule* targetOwnerp) const {
        // If caller explicitly provided a cellPathOverride, use it.
        // Note: empty string IS a valid override (top-level context).
        if (m_hasCellPathOverride) return m_cellPathOverride;
        if (!m_depNode) return "";
        if (targetOwnerp == m_depNode->ownerModp) return m_depNode->cellPath;

        // Cross-module reference without cellPathOverride.
        // Handle known legitimate cases:

        // Case 1: Target owner is null (compilation unit) - empty cellPath is correct.
        if (!targetOwnerp) {
            UINFO(9, "DEPGRAPH: cross-module ref to null owner (compilation unit)"
                         << " returning empty cellPath" << endl);
            return "";
        }

        // Case 2: Target is top module or package - empty cellPath is correct.
        // These are global/shared and don't have per-instance context.
        if (targetOwnerp->isTop() || VN_IS(targetOwnerp, Package)) {
            UINFO(9, "DEPGRAPH: cross-module ref to top/package "
                         << targetOwnerp->name() << " returning empty cellPath" << endl);
            return "";
        }

        // Case 3: Target is a parent interface in the hierarchy.
        // Strip the last component of the depNode's cellPath to get the parent context.
        // This is only safe for interfaces because the parent cellPath directly maps
        // to the interface instance. For regular modules, the mapping may not hold.
        if (!m_depNode->cellPath.empty() && VN_IS(targetOwnerp, Iface)) {
            const size_t lastDot = m_depNode->cellPath.rfind('.');
            if (lastDot != string::npos) {
                const string parentPath = m_depNode->cellPath.substr(0, lastDot);
                UINFO(5, "DEPGRAPH: cross-module ref to interface "
                             << targetOwnerp->name() << " using parent cellPath='" << parentPath
                             << "' (depNode cellPath='" << m_depNode->cellPath << "')" << endl);
                return parentPath;
            }
        }

        // Unhandled cross-module ref to a non-top, non-package, non-interface module.
        // This indicates a bug: either the caller should have provided cellPathOverride,
        // or deps were collected redundantly without the correct context.
        UASSERT_OBJ(false, m_depNode->nodep,
                    "effectiveCellPath: unhandled cross-module ref"
                        << " target=" << targetOwnerp->name()
                        << " targetType=" << targetOwnerp->typeName()
                        << " depNode=" << V3LinkDotDepGraph::nodeName(m_depNode) << " cellPath='"
                        << m_depNode->cellPath << "'");
        return "";  // Unreachable, but needed for compiler
    }

    void visit(AstVarRef* nodep) override {
        if (AstVar* const varp = nodep->varp()) {
            // Only create dependency nodes for parameters (GPARAM, LPARAM)
            // Regular variables (logic, wire, etc.) are not part of the dependency graph
            if (!varp->isGParam() && !varp->isParam()) {
                UINFO(9, "DEPGRAPH: DepExprVisitor skipping non-param var '"
                             << varp->name() << "' (not GPARAM/LPARAM)" << endl);
                return;
            }
            AstNodeModule* const varOwnerp = V3LinkDotDepGraph::findOwnerModule(varp);
            V3LinkDotDepGraph::NodeType type = V3LinkDotDepGraph::classifyVar(varp);
            const string cellPath = effectiveCellPath(varOwnerp);
            V3LinkDotDepGraph::DepNode* const targetp
                = V3LinkDotDepGraph::findOrCreateNode(varp, type, varOwnerp, cellPath);
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
                const string cellName
                    = firstDot == string::npos ? dotted : dotted.substr(0, firstDot);
                const string rest = firstDot == string::npos ? "" : dotted.substr(firstDot + 1);
                if (!cellName.empty()) {
                    AstNodeModule* ifaceModp
                        = findConnectedIfaceModpFromPort(m_depNode->ownerModp, cellName);
                    if (!ifaceModp) {
                        for (AstNode* stmtp = m_depNode->ownerModp->stmtsp(); stmtp;
                             stmtp = stmtp->nextp()) {
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
                            const string innerCell
                                = nextDot == string::npos ? rest : rest.substr(0, nextDot);
                            for (AstNode* stmtp = ifaceModp->stmtsp(); stmtp;
                                 stmtp = stmtp->nextp()) {
                                if (AstCell* const cellp = VN_CAST(stmtp, Cell)) {
                                    if (cellp->name() == innerCell && cellp->modp()) {
                                        searchModp = cellp->modp();
                                        break;
                                    }
                                }
                            }
                        }
                        for (AstNode* stmtp = searchModp->stmtsp(); stmtp;
                             stmtp = stmtp->nextp()) {
                            if (AstVar* const candp = VN_CAST(stmtp, Var)) {
                                if (candp->name() == nodep->name()) {
                                    targetVarp = candp;
                                    targetModp = searchModp;
                                    break;
                                }
                            }
                        }
                    } else {
                        // Expected for port-based VarXRefs (e.g., io.cfg where io is a port
                        // of the parent module, not a cell in the current interface).
                        // The cellAssociations lookup below will resolve the correct cellPath.
                        UINFO(5, "DEPGRAPH: VarXRef dotted='"
                                     << dotted << "' cellName='" << cellName << "' not a cell in "
                                     << m_depNode->ownerModp->name()
                                     << " - will resolve via cellAssociations" << endl);
                    }
                }
            }
            // Only create dependency nodes for parameters (GPARAM, LPARAM)
            // Regular variables (logic, wire, etc.) are not part of the dependency graph
            if (!targetVarp->isGParam() && !targetVarp->isParam()) {
                UINFO(9, "DEPGRAPH: DepExprVisitor skipping non-param var '"
                             << targetVarp->name() << "' (not GPARAM/LPARAM)" << endl);
                return;
            }
            V3LinkDotDepGraph::NodeType type = V3LinkDotDepGraph::classifyVar(targetVarp);

            // For VarXRef through interface ports (e.g., io.cfg), use s_cellAssociations
            // to resolve the port reference to the actual interface instance cellPath.
            // e.g., dotted='io' in child at top.u0 -> portPath='top.u0.io' -> 'top.bus0'
            string cellPath;
            if (m_depNode && !nodep->dotted().empty()) {
                const string dotted = nodep->dotted();
                const size_t firstDot = dotted.find('.');
                const string cellName
                    = firstDot == string::npos ? dotted : dotted.substr(0, firstDot);

                // Build the parent cellPath (strip last component from depNode's cellPath)
                string parentCellPath;
                if (!m_depNode->cellPath.empty()) {
                    const size_t lastDot = m_depNode->cellPath.rfind('.');
                    if (lastDot != string::npos) {
                        parentCellPath = m_depNode->cellPath.substr(0, lastDot);
                    }
                }
                // If caller provided cellPathOverride, use that as parent context
                if (m_hasCellPathOverride) parentCellPath = m_cellPathOverride;

                if (!cellName.empty() && !parentCellPath.empty()) {
                    const string portPath = parentCellPath + "." + cellName;
                    const auto assocIt = s_cellAssociations.find(portPath);
                    if (assocIt != s_cellAssociations.end()) {
                        cellPath = assocIt->second;
                        UINFO(5, "DEPGRAPH: xref resolved via cellAssoc: portPath='"
                                     << portPath << "' -> ifaceCellPath='" << cellPath << "'"
                                     << endl);
                    }
                }
            }
            // Fallback to effectiveCellPath if cellAssoc didn't resolve
            if (cellPath.empty()) { cellPath = effectiveCellPath(targetModp); }

            V3LinkDotDepGraph::DepNode* const targetp
                = V3LinkDotDepGraph::findOrCreateNode(targetVarp, type, targetModp, cellPath);
            V3LinkDotDepGraph::addEdge(m_depNode, targetp);
            UINFO(5, "DEPGRAPH: xref '" << nodep->name() << "' dotted='" << nodep->dotted()
                                        << "' -> " << V3LinkDotDepGraph::nodeName(targetp) << "@"
                                        << (targetModp ? targetModp->name() : "<null>")
                                        << " cellPath='" << cellPath << "'" << endl);
        }
    }
    void visit(AstRefDType* nodep) override {
        AstNodeModule* ownerp = V3LinkDotDepGraph::findOwnerModule(nodep);
        // For cloned RefDTypes (not attached to AST), use depNode's owner as fallback.
        // But only if the node is truly detached (no backp). If backp exists but owner is null,
        // the node is in the compilation unit and should stay that way.
        const bool isDetached = !nodep->backp();
        if (!ownerp && isDetached && m_depNode && m_depNode->ownerModp) {
            ownerp = m_depNode->ownerModp;
        }
        // Use cellPath override if set (for pin expressions), else depNode's cellPath
        const string cellPath = effectiveCellPath(ownerp);
        // Null owner means compilation unit - that's valid, don't skip
        V3LinkDotDepGraph::DepNode* const targetp = V3LinkDotDepGraph::findOrCreateNode(
            nodep, V3LinkDotDepGraph::NodeType::REFDTYPE, ownerp, cellPath);
        // Skip edge if parent is PARAMTYPE and this REFDTYPE points back to the same PARAMTYPE
        // (would create a cycle). But if the REFDTYPE points to a DIFFERENT PARAMTYPE (e.g., in
        // a parent module), we DO need the edge to ensure proper resolution order.
        const bool isSelfRef
            = (m_depNode && m_depNode->nodeType == V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE
               && m_depNode->nodep == nodep->refDTypep());
        if (!isSelfRef) V3LinkDotDepGraph::addEdge(m_depNode, targetp);
        if (AstTypedef* const tdp = nodep->typedefp()) {
            AstNodeModule* const tdOwnerp = V3LinkDotDepGraph::findOwnerModule(tdp);
            // If typedef is in an interface, compute interface cellPath from dotted reference
            string tdCellPath = cellPath;
            UINFO(5, "DEPGRAPH: REFDTYPE->TYPEDEF check: refdtype='"
                         << nodep->name() << "' typedef='" << tdp->name()
                         << "' tdOwnerp=" << (tdOwnerp ? tdOwnerp->name() : "<null>")
                         << " isIface=" << (tdOwnerp && VN_IS(tdOwnerp, Iface)) << " cellPath='"
                         << cellPath << "'" << " targetp->cellName='" << targetp->cellName << "'"
                         << " ownerp=" << (ownerp ? ownerp->name() : "<null>") << endl);
            if (tdOwnerp && VN_IS(tdOwnerp, Iface)) {
                // Check if targetp has a cellName from dotted access (e.g., "io" from "io.data_t")
                if (!targetp->cellName.empty()) {
                    // The cellName is the interface PORT name (e.g., "io").
                    // We need to find which interface INSTANCE is connected to this port.
                    // Use m_depNode->cellPath for the current cell context (e.g., "t.u_subA")
                    // Build portPath: cellContext + "." + portName = "t.u_subA.io"
                    // Look up in s_cellAssociations to get the connected interface instance path

                    string cellContext;
                    if (m_depNode && !m_depNode->cellPath.empty()) {
                        cellContext = m_depNode->cellPath;
                    } else if (!cellPath.empty()) {
                        cellContext = cellPath;
                    } else if (ownerp) {
                        cellContext = ownerp->name();
                    }

                    // Normalize cellName by stripping __BRA__??__KET__ placeholder.
                    // Interface arrays like subA_io[0] are registered with __BRA__??__KET__
                    // before the index is resolved, but all array elements share the same
                    // type definition, so we use the base cell name for lookup.
                    const string normalizedCellName = normalizeCellName(targetp->cellName);
                    const string portPath = cellContext.empty()
                                                ? normalizedCellName
                                                : cellContext + "." + normalizedCellName;
                    UINFO(5, "DEPGRAPH: REFDTYPE->TYPEDEF looking up portPath='"
                                 << portPath << "'" << " (original cellName='" << targetp->cellName
                                 << "')" << endl);

                    // Look up the connected interface instance cellPath
                    const auto assocIt = s_cellAssociations.find(portPath);
                    if (assocIt != s_cellAssociations.end()) {
                        tdCellPath = assocIt->second;
                        UINFO(5, "DEPGRAPH: REFDTYPE->TYPEDEF found cell association: portPath='"
                                     << portPath << "' -> ifaceCellPath='" << tdCellPath << "'"
                                     << endl);
                    } else {
                        // Try prefix-based rewrite: if portPath is "t.c.wif.a_inst" and
                        // cell association has "t.c.wif" -> "t.wif", rewrite to "t.wif.a_inst".
                        // This handles nested interface access through ports (e.g., accessing
                        // a sub-cell within an interface passed via a port).
                        // Use longest-prefix match to avoid ambiguity when multiple associations
                        // could match different prefixes of the same path.
                        bool foundPrefix = false;
                        size_t bestLen = 0;
                        string bestTarget;
                        string bestPrefix;
                        for (const auto& assoc : s_cellAssociations) {
                            const string& pfx = assoc.first;
                            if (pfx.size() > bestLen && portPath.size() > pfx.size()
                                && portPath[pfx.size()] == '.'
                                && portPath.compare(0, pfx.size(), pfx) == 0) {
                                bestLen = pfx.size();
                                bestTarget = assoc.second;
                                bestPrefix = pfx;
                            }
                        }
                        if (bestLen > 0) {
                            const string suffix = portPath.substr(bestLen);
                            tdCellPath = bestTarget + suffix;
                            UINFO(5,
                                  "DEPGRAPH: REFDTYPE->TYPEDEF prefix cell association: portPath='"
                                      << portPath << "' prefix='" << bestPrefix << "' -> '"
                                      << tdCellPath << "'" << endl);
                            foundPrefix = true;
                        }
                        if (!foundPrefix) {
                            // Fallback: use cellContext + normalizedCellName directly
                            tdCellPath = cellContext.empty()
                                             ? normalizedCellName
                                             : cellContext + "." + normalizedCellName;
                            UINFO(5,
                                  "DEPGRAPH: REFDTYPE->TYPEDEF no cell association for portPath='"
                                      << portPath << "', using fallback tdCellPath='" << tdCellPath
                                      << "'" << endl);
                        }
                    }
                } else if (!cellPath.empty()) {
                    // Try to find interface cell/port in current module that matches the typedef
                    // owner
                    if (m_depNode && m_depNode->ownerModp) {
                        bool found = false;
                        // First, look for interface instances (cells)
                        for (AstNode* stmtp = m_depNode->ownerModp->stmtsp(); stmtp && !found;
                             stmtp = stmtp->nextp()) {
                            if (AstCell* const cellp = VN_CAST(stmtp, Cell)) {
                                if (cellp->modp() && VN_IS(cellp->modp(), Iface)) {
                                    string cellModBase = cellp->modp()->name();
                                    const size_t sp = cellModBase.find("__");
                                    if (sp != string::npos)
                                        cellModBase = cellModBase.substr(0, sp);
                                    string tdOwnerBase = tdOwnerp->name();
                                    const size_t tp = tdOwnerBase.find("__");
                                    if (tp != string::npos)
                                        tdOwnerBase = tdOwnerBase.substr(0, tp);
                                    if (cellModBase == tdOwnerBase) {
                                        tdCellPath = cellPath + "." + cellp->name();
                                        UINFO(5, "DEPGRAPH: REFDTYPE->TYPEDEF using interface "
                                                 "cellPath '"
                                                     << tdCellPath << "' from cell '"
                                                     << cellp->name() << "'" << endl);
                                        found = true;
                                    }
                                }
                            }
                        }
                        // If not found, look for interface ports and trace through connection
                        if (!found) {
                            for (AstNode* stmtp = m_depNode->ownerModp->stmtsp(); stmtp && !found;
                                 stmtp = stmtp->nextp()) {
                                if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                                    if (!varp->isIfaceRef()) continue;
                                    AstIfaceRefDType* ifaceRefp
                                        = findIfaceRefDType(varp->dtypep());
                                    if (!ifaceRefp)
                                        ifaceRefp = findIfaceRefDType(varp->subDTypep());
                                    if (!ifaceRefp)
                                        ifaceRefp = findIfaceRefDType(varp->childDTypep());
                                    if (!ifaceRefp) continue;
                                    AstNodeModule* ifaceModp = nullptr;
                                    if (ifaceRefp->ifacep())
                                        ifaceModp = ifaceRefp->ifacep();
                                    else if (ifaceRefp->cellp() && ifaceRefp->cellp()->modp())
                                        ifaceModp = ifaceRefp->cellp()->modp();
                                    if (!ifaceModp) continue;
                                    string ifaceModBase = ifaceModp->name();
                                    const size_t sp = ifaceModBase.find("__");
                                    if (sp != string::npos)
                                        ifaceModBase = ifaceModBase.substr(0, sp);
                                    string tdOwnerBase = tdOwnerp->name();
                                    const size_t tp = tdOwnerBase.find("__");
                                    if (tp != string::npos)
                                        tdOwnerBase = tdOwnerBase.substr(0, tp);
                                    if (ifaceModBase == tdOwnerBase) {
                                        // Found matching interface port - trace through connection
                                        string connectedCellName, parentCellPath;
                                        if (findConnectedIfaceCellPath(
                                                m_depNode->ownerModp, varp->name(), cellPath,
                                                connectedCellName, parentCellPath)) {
                                            tdCellPath = parentCellPath + "." + connectedCellName;
                                            UINFO(5, "DEPGRAPH: REFDTYPE->TYPEDEF using interface "
                                                     "cellPath '"
                                                         << tdCellPath << "' from port '"
                                                         << varp->name() << "' connected to '"
                                                         << connectedCellName << "'" << endl);
                                            found = true;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            // For modules with interface port references, find the correct instantiated typedef
            // The tdCellPath was already computed above from targetp->cellName (the resolved
            // interface instance name like 'subA_io'). We use findByNameAndOwner to find an
            // existing TYPEDEF node at that cellPath, or fall back to findOrCreateNode.
            V3LinkDotDepGraph::DepNode* tdNodep = nullptr;

            // If the typedef is in an interface and we have a cellName (dotted reference),
            // look for the instantiated typedef at the computed tdCellPath
            const bool isIfaceRef
                = (tdOwnerp && VN_IS(tdOwnerp, Iface) && !targetp->cellName.empty());

            if (isIfaceRef) {
                // tdCellPath was computed above as the full path to the interface instance
                // e.g., "t.subA_io" for typedef io.data_t in subA connected to subA_io
                UINFO(5, "DEPGRAPH: Looking for interface typedef at tdCellPath='" << tdCellPath
                                                                                   << "'" << endl);

                // First try to find an existing TYPEDEF node at this cellPath
                tdNodep = V3LinkDotDepGraph::findByNameAndOwner(
                    tdp->name(), tdOwnerp, V3LinkDotDepGraph::NodeType::TYPEDEF, tdCellPath);
                UINFO(5, "DEPGRAPH: findByNameAndOwner('"
                             << tdp->name() << "', " << tdOwnerp->name() << ", TYPEDEF, '"
                             << tdCellPath << "') -> "
                             << (tdNodep ? ("found cellPath='" + tdNodep->cellPath + "'")
                                         : "NOT FOUND")
                             << endl);

                if (!tdNodep) {
                    // Node doesn't exist yet, create it
                    tdNodep = V3LinkDotDepGraph::findOrCreateNode(
                        tdp, V3LinkDotDepGraph::NodeType::TYPEDEF, tdOwnerp, tdCellPath);
                }
                UINFO(5, "DEPGRAPH: Found/created interface typedef node at '"
                             << tdCellPath << "' nodep=" << cvtToHex(tdNodep) << " cellPath='"
                             << tdNodep->cellPath << "'" << endl);
            } else {
                // For non-interface-typedef refs, create/find the node normally
                tdNodep = V3LinkDotDepGraph::findOrCreateNode(
                    tdp, V3LinkDotDepGraph::NodeType::TYPEDEF, tdOwnerp, tdCellPath);
            }

            UASSERT(tdNodep, "tdNodep is null for refdtype '" << nodep->name() << "'");

            V3LinkDotDepGraph::addEdge(targetp, tdNodep);
            UINFO(5, "DEPGRAPH: refdtype '" << nodep->name() << "' -> typedef '" << tdp->name()
                                            << "' in " << (tdOwnerp ? tdOwnerp->name() : "<null>")
                                            << " cellPath=" << tdCellPath << endl);
        } else if (AstParamTypeDType* const ptdp = VN_CAST(nodep->refDTypep(), ParamTypeDType)) {
            AstParamTypeDType* targetPtdp = ptdp;
            AstNodeModule* ptOwnerp = V3LinkDotDepGraph::findOwnerModule(ptdp);

            // Compute the cellPath for the PARAMTYPE target
            // If this REFDTYPE has a cellName (from dotted access like io.data_t),
            // use cell association to find the correct cellPath for the interface
            string ptCellPath = cellPath;
            bool usedCellAssociation = false;
            if (!targetp->cellName.empty() && ptOwnerp && VN_IS(ptOwnerp, Iface)) {
                // Build portPath: currentCellPath + "." + cellName
                // Normalize cellName to strip __BRA__??__KET__ placeholder for interface arrays
                const string normalizedCellName = normalizeCellName(targetp->cellName);
                string cellContext;
                if (m_depNode && !m_depNode->cellPath.empty()) {
                    cellContext = m_depNode->cellPath;
                } else if (!cellPath.empty()) {
                    cellContext = cellPath;
                } else if (ownerp) {
                    // Use owner module name when cellContext is empty (e.g., top module)
                    cellContext = ownerp->name();
                }
                const string portPath = cellContext.empty()
                                            ? normalizedCellName
                                            : cellContext + "." + normalizedCellName;
                UINFO(5, "DEPGRAPH: REFDTYPE->PARAMTYPE looking up portPath='" << portPath << "'"
                                                                               << endl);

                // Look up the connected interface instance cellPath
                const auto assocIt = s_cellAssociations.find(portPath);
                if (assocIt != s_cellAssociations.end()) {
                    ptCellPath = assocIt->second;
                    usedCellAssociation = true;
                    UINFO(5, "DEPGRAPH: REFDTYPE->PARAMTYPE found cell association: portPath='"
                                 << portPath << "' -> ifaceCellPath='" << ptCellPath << "'"
                                 << endl);
                } else {
                    // Fallback: use cellContext + normalizedCellName directly
                    ptCellPath = cellContext.empty() ? normalizedCellName
                                                     : cellContext + "." + normalizedCellName;
                    UINFO(5, "DEPGRAPH: REFDTYPE->PARAMTYPE no cell association for portPath='"
                                 << portPath << "', using fallback ptCellPath='" << ptCellPath
                                 << "'" << endl);
                }
            }

            // Only retarget to current module's PARAMTYPE if:
            // 1. We didn't use cell association AND
            // 2. There's no cellName (not a dotted access like subA_io.data_t)
            // When we have a cellName, we want to connect to the interface's PARAMTYPE
            if (!usedCellAssociation && targetp->cellName.empty() && m_depNode
                && m_depNode->ownerModp) {
                const bool isTemplateOwner = isTemplateModule(ptOwnerp);
                if (!ptOwnerp || isTemplateOwner) {
                    for (AstNode* stmtp = m_depNode->ownerModp->stmtsp(); stmtp;
                         stmtp = stmtp->nextp()) {
                        if (AstParamTypeDType* const cellPtdp = VN_CAST(stmtp, ParamTypeDType)) {
                            if (cellPtdp->name() == ptdp->name()) {
                                targetPtdp = cellPtdp;
                                ptOwnerp = m_depNode->ownerModp;
                                break;
                            }
                        }
                    }
                }
            }
            if (!ptOwnerp) {
                UINFO(5, "DEPGRAPH: refdtype '" << nodep->name()
                                                << "' skip paramtype edge (null owner)" << endl);
            } else {
                UINFO(5, "DEPGRAPH: refdtype '"
                             << nodep->name() << "' -> paramtype '" << targetPtdp->name()
                             << "' in " << ptOwnerp->name() << " using ptCellPath='" << ptCellPath
                             << "'" << " m_cellPathOverride='" << m_cellPathOverride << "'"
                             << endl);
                V3LinkDotDepGraph::DepNode* const ptNodep = V3LinkDotDepGraph::findOrCreateNode(
                    targetPtdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, ptOwnerp, ptCellPath);
                // Skip edge if REFDTYPE is child of the PARAMTYPE (would create cycle)
                const bool isSelfRef = (m_depNode && m_depNode->nodep == targetPtdp);
                if (!isSelfRef) {
                    V3LinkDotDepGraph::addEdge(targetp, ptNodep);
                    UINFO(5, "DEPGRAPH: refdtype '"
                                 << nodep->name() << "' -> paramtype '" << targetPtdp->name()
                                 << "' in " << (ptOwnerp ? ptOwnerp->name() : "<null>")
                                 << (targetPtdp != ptdp ? " (retargeted)" : "") << endl);
                }
            }
        }
        iterateChildrenConst(nodep);
    }
    void visit(AstAttrOf* nodep) override {
        // For ATTROF nodes (like $bits), add dependency on the ATTROF node itself
        // The ATTROF node will have its own dependencies on the source type
        AstNodeModule* ownerp = V3LinkDotDepGraph::findOwnerModule(nodep);
        if (!ownerp && m_depNode && m_depNode->ownerModp) ownerp = m_depNode->ownerModp;
        // Use cellPath from m_depNode for per-cell-context
        const string& cellPath = m_depNode ? m_depNode->cellPath : "";
        if (ownerp) {
            V3LinkDotDepGraph::DepNode* const attrNodep = V3LinkDotDepGraph::findOrCreateNode(
                nodep, V3LinkDotDepGraph::NodeType::ATTROF, ownerp, cellPath);
            V3LinkDotDepGraph::addEdge(m_depNode, attrNodep);
            UINFO(5, "DEPGRAPH: expr depends on ATTROF '"
                         << nodep->attrType().ascii() << "' in " << ownerp->name() << " fromp="
                         << (nodep->fromp() ? nodep->fromp()->typeName() : "<null>") << endl);

            // Also add edge from ATTROF to its source type
            // Handle different cases:
            // 1. $bits(type) - fromp is RefDType
            // 2. $bits(var) - fromp is VarRef or ParseRef, need to follow to var's dtype
            if (AstRefDType* const rdp = VN_CAST(nodep->fromp(), RefDType)) {
                AstNodeModule* rdpOwnerp = V3LinkDotDepGraph::findOwnerModule(rdp);
                if (!rdpOwnerp) rdpOwnerp = ownerp;
                V3LinkDotDepGraph::DepNode* const rdpNodep = V3LinkDotDepGraph::findOrCreateNode(
                    rdp, V3LinkDotDepGraph::NodeType::REFDTYPE, rdpOwnerp, cellPath);
                V3LinkDotDepGraph::addEdge(attrNodep, rdpNodep);
                UINFO(5, "DEPGRAPH: ATTROF '" << nodep->attrType().ascii()
                                              << "' depends on REFDTYPE '" << rdp->name()
                                              << "' in " << rdpOwnerp->name() << endl);

                // Add edge from REFDTYPE to TYPEDEF if applicable
                if (AstTypedef* const tdp = rdp->typedefp()) {
                    AstNodeModule* tdOwnerp = V3LinkDotDepGraph::findOwnerModule(tdp);
                    if (!tdOwnerp) tdOwnerp = rdpOwnerp;
                    V3LinkDotDepGraph::DepNode* tdNodep = V3LinkDotDepGraph::findByNameAndOwner(
                        tdp->name(), tdOwnerp, V3LinkDotDepGraph::NodeType::TYPEDEF, cellPath);
                    if (!tdNodep) {
                        tdNodep = V3LinkDotDepGraph::findOrCreateNode(
                            tdp, V3LinkDotDepGraph::NodeType::TYPEDEF, tdOwnerp, cellPath);
                    }
                    V3LinkDotDepGraph::addEdge(rdpNodep, tdNodep);
                    UINFO(5, "DEPGRAPH: REFDTYPE '" << rdp->name() << "' depends on TYPEDEF '"
                                                    << tdp->name() << "' in " << tdOwnerp->name()
                                                    << endl);
                }

                // Also add edge from REFDTYPE to PARAMTYPEDTYPE if applicable
                if (AstParamTypeDType* const ptdp = VN_CAST(rdp->refDTypep(), ParamTypeDType)) {
                    AstNodeModule* ptdOwnerp = V3LinkDotDepGraph::findOwnerModule(ptdp);
                    if (!ptdOwnerp) ptdOwnerp = rdpOwnerp;
                    // First try to find an existing PARAMTYPEDTYPE node with the same name
                    // This handles the case where the expression contains a different AST node
                    // than the one that was already added to the DepGraph
                    V3LinkDotDepGraph::DepNode* ptdNodep = V3LinkDotDepGraph::findByNameAndOwner(
                        ptdp->name(), ptdOwnerp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE,
                        cellPath);
                    if (!ptdNodep) {
                        // No existing node found, create one
                        ptdNodep = V3LinkDotDepGraph::findOrCreateNode(
                            ptdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, ptdOwnerp,
                            cellPath);
                    } else {
                        UINFO(5, "DEPGRAPH: ATTROF using existing PARAMTYPEDTYPE node '"
                                     << ptdp->name() << "' in " << ptdOwnerp->name()
                                     << " resolved=" << ptdNodep->resolved << endl);
                    }
                    V3LinkDotDepGraph::addEdge(rdpNodep, ptdNodep);
                    UINFO(5, "DEPGRAPH: REFDTYPE '"
                                 << rdp->name() << "' depends on PARAMTYPEDTYPE '" << ptdp->name()
                                 << "' in " << ptdOwnerp->name() << endl);
                }
            } else if (AstVarRef* const vrp = VN_CAST(nodep->fromp(), VarRef)) {
                // $bits(var) - follow through to the variable's dtype
                if (AstVar* const varp = vrp->varp()) {
                    // Try dtypep() first, then childDTypep() (before linkdot resolves types)
                    AstNodeDType* dtypep = varp->dtypep();
                    if (!dtypep) dtypep = varp->childDTypep();
                    if (AstRefDType* const rdp = VN_CAST(dtypep, RefDType)) {
                        AstNodeModule* rdpOwnerp = V3LinkDotDepGraph::findOwnerModule(rdp);
                        if (!rdpOwnerp) rdpOwnerp = ownerp;
                        V3LinkDotDepGraph::DepNode* const rdpNodep
                            = V3LinkDotDepGraph::findOrCreateNode(
                                rdp, V3LinkDotDepGraph::NodeType::REFDTYPE, rdpOwnerp, cellPath);
                        V3LinkDotDepGraph::addEdge(attrNodep, rdpNodep);
                        UINFO(5, "DEPGRAPH: ATTROF '"
                                     << nodep->attrType().ascii() << "' (via var '" << varp->name()
                                     << "') depends on REFDTYPE '" << rdp->name() << "' in "
                                     << rdpOwnerp->name() << endl);

                        // Add edge from REFDTYPE to TYPEDEF if applicable
                        if (AstTypedef* const tdp = rdp->typedefp()) {
                            AstNodeModule* tdOwnerp = V3LinkDotDepGraph::findOwnerModule(tdp);
                            if (!tdOwnerp) tdOwnerp = rdpOwnerp;
                            V3LinkDotDepGraph::DepNode* tdNodep
                                = V3LinkDotDepGraph::findOrCreateNode(
                                    tdp, V3LinkDotDepGraph::NodeType::TYPEDEF, tdOwnerp, cellPath);
                            V3LinkDotDepGraph::addEdge(rdpNodep, tdNodep);
                            UINFO(5, "DEPGRAPH: REFDTYPE '"
                                         << rdp->name()
                                         << "' (from ATTROF var) depends on TYPEDEF '"
                                         << tdp->name() << "' in " << tdOwnerp->name() << endl);
                        }
                        // Add edge from REFDTYPE to PARAMTYPE if applicable
                        // This ensures the dependency chain is complete
                        else if (AstParamTypeDType* const ptdp
                                 = VN_CAST(rdp->refDTypep(), ParamTypeDType)) {
                            AstNodeModule* ptdOwnerp = V3LinkDotDepGraph::findOwnerModule(ptdp);
                            if (!ptdOwnerp) ptdOwnerp = rdpOwnerp;
                            V3LinkDotDepGraph::DepNode* ptdNodep
                                = V3LinkDotDepGraph::findOrCreateNode(
                                    ptdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, ptdOwnerp,
                                    cellPath);
                            V3LinkDotDepGraph::addEdge(rdpNodep, ptdNodep);
                            UINFO(5, "DEPGRAPH: REFDTYPE '"
                                         << rdp->name()
                                         << "' (from ATTROF var) depends on PARAMTYPE '"
                                         << ptdp->name() << "' in " << ptdOwnerp->name() << endl);
                        }
                    }
                }
            }
        }
        // Don't iterate children - the ATTROF node handles its own dependencies
    }
    void visit(AstMemberSel* nodep) override {
        // Struct member access like cfg.AddrBits - depends on the base variable being resolved
        // The base variable (e.g., cfg) must be a parameter for us to resolve the member value
        if (AstVarRef* const vrp = VN_CAST(nodep->fromp(), VarRef)) {
            if (AstVar* const varp = vrp->varp()) {
                // Only create dependency if the base is a parameter
                if (varp->isGParam() || varp->isParam()) {
                    AstNodeModule* const varOwnerp = V3LinkDotDepGraph::findOwnerModule(varp);
                    V3LinkDotDepGraph::NodeType type = V3LinkDotDepGraph::classifyVar(varp);
                    const string cellPath = effectiveCellPath(varOwnerp);
                    V3LinkDotDepGraph::DepNode* const targetp
                        = V3LinkDotDepGraph::findOrCreateNode(varp, type, varOwnerp, cellPath);
                    V3LinkDotDepGraph::addEdge(m_depNode, targetp);
                    UINFO(5, "DEPGRAPH: MemberSel '" << nodep->name() << "' depends on param '"
                                                     << varp->name() << "'" << endl);
                }
            }
        }
        // Continue iterating children (in case there are nested expressions)
        iterateChildrenConst(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    DepExprVisitor(AstNode* exprp, V3LinkDotDepGraph::DepNode* depNode,
                   const string& cellPathOverride = "", bool hasCellPathOverride = false)
        : m_depNode{depNode}
        , m_cellPathOverride{cellPathOverride}
        , m_hasCellPathOverride{hasCellPathOverride} {
        if (exprp) iterateConst(exprp);
    }
};

void V3LinkDotDepGraph::collectExpressionDeps(AstNode* exprp, DepNode* depNode,
                                              AstNodeModule* /*scopeModp*/,
                                              const string& cellPathOverride,
                                              bool hasCellPathOverride) {
    if (!exprp || !depNode) return;
    DepExprVisitor{exprp, depNode, cellPathOverride, hasCellPathOverride};
}

//======================================================================
// CellAssocDiscoveryVisitor - Discovers and registers interface port ->
// interface instance associations BEFORE the main DepGraph build.
// This ensures s_cellAssociations is fully populated for lookups during
// DepGraphBuildVisitor::visit(AstRefDType*).

class CellAssocDiscoveryVisitor final : public VNVisitorConst {
private:
    AstNodeModule* m_modp = nullptr;  // Current module
    string m_cellPath;  // Current hierarchical cell path

    void visit(AstNodeModule* nodep) override {
        if (nodep->dead()) return;
        if (m_cellPath.empty()) {
            // At top-level, only process top module and packages
            const bool isTop = nodep->isTop();
            const bool isPackage = VN_IS(nodep, Package);
            if (!isTop && !isPackage) return;
        }

        VL_RESTORER(m_modp);
        m_modp = nodep;
        iterateChildrenConst(nodep);
    }

    void visit(AstCell* nodep) override {
        if (!m_modp) return;
        AstNodeModule* const childModp = nodep->modp();
        if (!childModp) return;

        // Build the cellPath for this instantiation
        const string parentCellPath = m_cellPath;
        const string childCellPath = parentCellPath.empty()
                                         ? (m_modp->name() + "." + nodep->name())
                                         : (parentCellPath + "." + nodep->name());

        // Process port pins (pinsp) - these contain interface port connections
        for (AstPin* pinp = nodep->pinsp(); pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            if (!pinp->modVarp()) continue;
            AstVar* const childVarp = pinp->modVarp();

            // Check if this is an interface port (not a regular port)
            // Interface ports have isIfaceRef() or have IfaceRefDType
            bool isIfacePort = childVarp->isIfaceRef();
            if (!isIfacePort) {
                AstIfaceRefDType* ifaceRefp = findIfaceRefDType(childVarp->dtypep());
                if (!ifaceRefp) ifaceRefp = findIfaceRefDType(childVarp->subDTypep());
                if (!ifaceRefp) ifaceRefp = findIfaceRefDType(childVarp->childDTypep());
                isIfacePort = (ifaceRefp != nullptr);
            }

            if (!isIfacePort) continue;

            // Get the port name (the interface port in the child module)
            const string& portName = childVarp->name();

            // Find the connected interface instance from the parent module
            if (AstNode* exprp = pinp->exprp()) {
                // Strip through NodePreSel if present
                while (AstNodePreSel* const preSelp = VN_CAST(exprp, NodePreSel)) {
                    exprp = preSelp->fromp();
                }

                if (AstVarRef* const vrp = VN_CAST(exprp, VarRef)) {
                    // The connected interface instance name
                    string ifaceName = vrp->name();
                    // Strip __Viftop suffix if present (Verilator internal naming)
                    const size_t viftopPos = ifaceName.find("__Viftop");
                    if (viftopPos != string::npos) { ifaceName = ifaceName.substr(0, viftopPos); }

                    // Build the hierarchical port path and interface cell path
                    // portPath: "t.u_subA.io" (cellPath + "." + portName)
                    // ifaceCellPath: "t.subA_io" (parentCellPath + "." + ifaceName, or
                    // m_modp->name() + "." + ifaceName at top)
                    const string portPath = childCellPath + "." + portName;
                    const string ifaceCellPath = parentCellPath.empty()
                                                     ? (m_modp->name() + "." + ifaceName)
                                                     : (parentCellPath + "." + ifaceName);

                    // Register the association
                    V3LinkDotDepGraph::registerCellAssociation(portPath, ifaceCellPath);
                } else {
                    UINFO(1, "DEPGRAPH: WARNING: CellAssocDiscovery: interface port '"
                                 << portName << "' on cell '" << nodep->name()
                                 << "' has non-VarRef expression type=" << exprp->typeName()
                                 << " - skipping association" << endl);
                }
            }
        }

        // Recursively visit the child module's contents
        {
            VL_RESTORER(m_modp);
            VL_RESTORER(m_cellPath);
            m_modp = childModp;
            m_cellPath = childCellPath;
            iterateChildrenConst(childModp);
        }

        iterateChildrenConst(nodep);
    }

    void visit(AstGenBlock* nodep) override {
        // Named generate blocks are part of the instance hierarchy.
        // V3Param includes them via m_generateHierName (V3Param.cpp:2718-2719).
        // We must include them in cellPaths to match.
        if (!nodep->name().empty()) {
            VL_RESTORER(m_cellPath);
            if (m_cellPath.empty()) {
                m_cellPath = m_modp->name() + "." + nodep->prettyName();
            } else {
                m_cellPath = m_cellPath + "." + nodep->prettyName();
            }
            UINFO(9, "DEPGRAPH: CellAssocDiscovery entering generate block '"
                         << nodep->prettyName() << "' cellPath='" << m_cellPath << "'" << endl);
            iterateChildrenConst(nodep);
        } else {
            iterateChildrenConst(nodep);
        }
    }

    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    explicit CellAssocDiscoveryVisitor(AstNetlist* netlistp) { iterateConst(netlistp); }
};

// Visitor to build the dependency graph from the AST
class DepGraphBuildVisitor final : public VNVisitorConst {
private:
    AstNodeModule* m_modp = nullptr;  // Current module/interface
    string m_cellPath;  // Current hierarchical cell path (e.g., "t.u_sub.u_inner")
    std::unordered_map<string, AstVar*> m_varsByName;  // Vars in current module

    void rebuildVarMap() {
        m_varsByName.clear();
        if (!m_modp) return;
        for (AstNode* stmtp = m_modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* const varp = VN_CAST(stmtp, Var)) m_varsByName[varp->name()] = varp;
        }
    }

    void visit(AstNodeModule* nodep) override {
        // NEW ARCHITECTURE: Instantiated modules are visited in cell context (with cellPath).
        // At top-level (empty cellPath), only visit:
        // - Top module (entry point)
        // - Packages (not instantiated, imported)
        // Skip all other modules - they'll be visited when we encounter the Cell that
        // instantiates them, giving us the correct cellPath.
        if (nodep->dead()) return;
        if (m_cellPath.empty()) {
            // At top-level, only process top module and packages
            const bool isTop = nodep->isTop();
            const bool isPackage = VN_IS(nodep, Package);
            if (!isTop && !isPackage) {
                UINFO(9, "DEPGRAPH: skipping module "
                             << nodep->name()
                             << " in top-level iteration (will visit in cell context)" << endl);
                return;
            }
        }

        VL_RESTORER(m_modp);
        m_modp = nodep;
        rebuildVarMap();
        UINFO(9, "DEPGRAPH: visiting module " << nodep->name() << " cellPath='" << m_cellPath
                                              << "'" << endl);

        iterateChildrenConst(nodep);
    }

    void visit(AstVar* nodep) override {
        if (!m_modp) return;
        // Only interested in parameters and localparams
        if (!nodep->isGParam() && !nodep->isParam()) return;

        V3LinkDotDepGraph::NodeType type = V3LinkDotDepGraph::classifyVar(nodep);
        V3LinkDotDepGraph::DepNode* const depNodep
            = V3LinkDotDepGraph::findOrCreateNode(nodep, type, m_modp, m_cellPath);

        // If this is a specialized clone, inherit captured expression from original
        if (!depNodep->initialValuep) {
            if (AstVar* const origVarp = nodep->clonep()) {
                if (const V3LinkDotDepGraph::DepNode* const origNodep
                    = V3LinkDotDepGraph::find(origVarp)) {
                    if (origNodep->initialValuep) {
                        AstNode* const clonedExprp = origNodep->initialValuep->cloneTree(false);
                        int relinkedRefs = 0;
                        clonedExprp->foreach([&](AstVarRef* refp) {
                            UASSERT_OBJ(refp->varp(), refp,
                                        "VarRef has null varp in cloned initialValuep");
                            const auto it = m_varsByName.find(refp->varp()->name());
                            if (it != m_varsByName.end()) refp->varp(it->second);
                            if (it != m_varsByName.end()) ++relinkedRefs;
                        });
                        // Relink RefDTypes to PARAMTYPEDTYPEs in the specialized module
                        clonedExprp->foreach([&](AstRefDType* rdp) {
                            for (AstNode* stmtp = m_modp->stmtsp(); stmtp;
                                 stmtp = stmtp->nextp()) {
                                if (AstParamTypeDType* const ptdp
                                    = VN_CAST(stmtp, ParamTypeDType)) {
                                    if (ptdp->name() == rdp->name()) {
                                        UINFO(5, "DEPGRAPH: relinked RefDType '"
                                                     << rdp->name() << "' to PARAMTYPEDTYPE in "
                                                     << m_modp->name() << endl);
                                        rdp->refDTypep(ptdp);
                                        rdp->typedefp(nullptr);
                                        ++relinkedRefs;
                                        break;
                                    }
                                }
                            }
                        });
                        depNodep->initialValuep = clonedExprp;
                        UINFO(5, "DEPGRAPH: inherited expr for param '"
                                     << nodep->name() << "' in " << m_modp->name()
                                     << " from template " << origNodep->ownerModp->name()
                                     << " (relinked " << relinkedRefs << " refs)" << endl);
                    }
                }
            }
        }
        if (!depNodep->initialValuep && m_modp) {
            string baseModName = m_modp->name();
            const size_t suffixPos = baseModName.find("__");
            if (suffixPos != string::npos) baseModName = baseModName.substr(0, suffixPos);
            if (baseModName != m_modp->name()) {
                for (const V3LinkDotDepGraph::DepNode* const candp :
                     V3LinkDotDepGraph::s_allNodes) {
                    if (!candp || !candp->initialValuep) continue;
                    if (candp->nodeType != depNodep->nodeType) continue;
                    if (!candp->ownerModp || candp->ownerModp->name() != baseModName) continue;
                    if (V3LinkDotDepGraph::nodeName(candp)
                        != V3LinkDotDepGraph::nodeName(depNodep)) {
                        continue;
                    }
                    AstNode* const clonedExprp = candp->initialValuep->cloneTree(false);
                    int relinkedRefs = 0;
                    const auto resolveXRef = [&](AstVarXRef* xrefp) -> AstVar* {
                        if (!xrefp || !m_modp || xrefp->dotted().empty()) return nullptr;
                        const string dotted = xrefp->dotted();
                        const size_t firstDot = dotted.find('.');
                        const string cellName
                            = firstDot == string::npos ? dotted : dotted.substr(0, firstDot);
                        const string rest
                            = firstDot == string::npos ? "" : dotted.substr(firstDot + 1);
                        if (cellName.empty()) return nullptr;
                        AstNodeModule* ifaceModp
                            = findConnectedIfaceModpFromPort(m_modp, cellName);
                        if (!ifaceModp) {
                            for (AstNode* stmtp = m_modp->stmtsp(); stmtp;
                                 stmtp = stmtp->nextp()) {
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
                            const string innerCell
                                = nextDot == string::npos ? rest : rest.substr(0, nextDot);
                            for (AstNode* stmtp = ifaceModp->stmtsp(); stmtp;
                                 stmtp = stmtp->nextp()) {
                                if (AstCell* const cellp = VN_CAST(stmtp, Cell)) {
                                    if (cellp->name() == innerCell && cellp->modp()) {
                                        searchModp = cellp->modp();
                                        break;
                                    }
                                }
                            }
                        }
                        for (AstNode* stmtp = searchModp->stmtsp(); stmtp;
                             stmtp = stmtp->nextp()) {
                            if (AstVar* const candp = VN_CAST(stmtp, Var)) {
                                if (candp->name() == xrefp->name()) return candp;
                            }
                        }
                        return nullptr;
                    };
                    clonedExprp->foreach([&](AstVarRef* refp) {
                        UASSERT_OBJ(refp->varp(), refp,
                                    "VarRef has null varp in cloned initialValuep");
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
                    // Relink RefDTypes to PARAMTYPEDTYPEs in the specialized module
                    clonedExprp->foreach([&](AstRefDType* rdp) {
                        // Look for PARAMTYPEDTYPE with matching name in specialized module
                        for (AstNode* stmtp = m_modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                            if (AstParamTypeDType* const ptdp = VN_CAST(stmtp, ParamTypeDType)) {
                                if (ptdp->name() == rdp->name()) {
                                    UINFO(5, "DEPGRAPH: relinked RefDType '"
                                                 << rdp->name() << "' to PARAMTYPEDTYPE in "
                                                 << m_modp->name() << endl);
                                    rdp->refDTypep(ptdp);
                                    rdp->typedefp(nullptr);
                                    ++relinkedRefs;
                                    break;
                                }
                            }
                        }
                    });
                    depNodep->initialValuep = clonedExprp;
                    UINFO(5, "DEPGRAPH: inherited expr for param '"
                                 << nodep->name() << "' in " << m_modp->name() << " from template "
                                 << baseModName << " (name match, relinked " << relinkedRefs
                                 << " refs)" << endl);
                    break;
                }
            }
        }

        // Collect dependencies from the value expression (prefer captured pre-constify)
        // IMPORTANT: If the node already has dependencies, they were set by pin processing
        // in visit(AstCell*) with the correct parentCellPath context. Don't re-collect here
        // without cellPathOverride - that would create duplicate edges with wrong context
        // (empty cellPath -> template-level nodes instead of cell-context nodes).
        if (depNodep->dependsOn.empty()) {
            AstNode* exprp = depNodep->initialValuep ? depNodep->initialValuep : nodep->valuep();
            if (exprp) { V3LinkDotDepGraph::collectExpressionDeps(exprp, depNodep, m_modp); }
        }

        // Also collect dependencies from the dtype (e.g., localparam tm_region_t foo = ...)
        // The localparam depends on the PARAMTYPEDTYPE for its type.
        if (AstNodeDType* const dtypep = nodep->dtypep()) {
            if (AstRefDType* const rdtp = VN_CAST(dtypep, RefDType)) {
                if (AstParamTypeDType* const ptdp = VN_CAST(rdtp->refDTypep(), ParamTypeDType)) {
                    AstNodeModule* const ptdOwnerp = V3LinkDotDepGraph::findOwnerModule(ptdp);
                    V3LinkDotDepGraph::DepNode* const ptdNodep
                        = V3LinkDotDepGraph::findOrCreateNode(
                            ptdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, ptdOwnerp,
                            m_cellPath);
                    V3LinkDotDepGraph::addEdge(depNodep, ptdNodep);
                    UINFO(5, "DEPGRAPH: param '"
                                 << nodep->name() << "' depends on paramtype '" << ptdp->name()
                                 << "' in " << (ptdOwnerp ? ptdOwnerp->name() : "<null>") << endl);
                }
            }
        }

        if (debug() >= 5) {
            std::ostringstream deps;
            bool first = true;
            for (V3LinkDotDepGraph::DepNode* const dep : depNodep->dependsOn) {
                if (!dep) continue;
                if (!first) deps << ", ";
                first = false;
                deps << V3LinkDotDepGraph::nodeName(dep) << "@"
                     << V3LinkDotDepGraph::nodeOwnerName(dep);
            }
            UINFO(5, "DEPGRAPH: deps for '" << nodep->name() << "'@" << m_modp->name() << " = ["
                                            << deps.str() << "]" << endl);
        }
    }

    void visit(AstTypedef* nodep) override {
        if (!m_modp) return;

        V3LinkDotDepGraph::DepNode* const depNodep = V3LinkDotDepGraph::findOrCreateNode(
            nodep, V3LinkDotDepGraph::NodeType::TYPEDEF, m_modp, m_cellPath);

        if (nodep->name() == "type_id") {
            AstRefDType* const childRefp = VN_CAST(nodep->subDTypep(), RefDType);
            const bool scopedHit
                = childRefp
                  && s_refDTypeScopedTypedefs.find(childRefp) != s_refDTypeScopedTypedefs.end();
            UINFO(5, "DEPGRAPH: typedef type_id in "
                         << (m_modp ? m_modp->name() : "<null>")
                         << " child_ref=" << (childRefp ? childRefp->name() : "<none>")
                         << " scoped_hit=" << (scopedHit ? "yes" : "no") << endl);
            const auto tdIt = s_typedefScopedTypedefs.find(nodep);
            if (tdIt != s_typedefScopedTypedefs.end()) {
                AstTypedef* const scopeTdp = tdIt->second;
                AstNodeModule* const tdOwnerp = V3LinkDotDepGraph::findOwnerModule(scopeTdp);
                V3LinkDotDepGraph::DepNode* const tdNodep = V3LinkDotDepGraph::findOrCreateNode(
                    scopeTdp, V3LinkDotDepGraph::NodeType::TYPEDEF, tdOwnerp, m_cellPath);
                V3LinkDotDepGraph::addEdge(depNodep, tdNodep);
                UINFO(5, "DEPGRAPH: typedef type_id edge to scoped typedef '"
                             << scopeTdp->name() << "' in "
                             << (tdOwnerp ? tdOwnerp->name() : "<null>") << endl);
            }
        }

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
                        = V3LinkDotDepGraph::findOrCreateNode(
                            refTdp, V3LinkDotDepGraph::NodeType::TYPEDEF, refOwnerp, m_cellPath);
                    V3LinkDotDepGraph::addEdge(depNodep, refNodep);
                    UINFO(9, "DEPGRAPH: typedef '"
                                 << nodep->name() << "' depends on typedef '" << refTdp->name()
                                 << "' in " << (refOwnerp ? refOwnerp->name() : "<null>") << endl);
                } else if (AstParamTypeDType* const refPtdp
                           = VN_CAST(rdtp->refDTypep(), ParamTypeDType)) {
                    AstNodeModule* const refOwnerp = V3LinkDotDepGraph::findOwnerModule(refPtdp);
                    V3LinkDotDepGraph::DepNode* const refNodep
                        = V3LinkDotDepGraph::findOrCreateNode(
                            refPtdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, refOwnerp,
                            m_cellPath);
                    V3LinkDotDepGraph::addEdge(depNodep, refNodep);
                    UINFO(9, "DEPGRAPH: typedef '"
                                 << nodep->name() << "' depends on paramtype '" << refPtdp->name()
                                 << "' in " << (refOwnerp ? refOwnerp->name() : "<null>") << endl);
                }
            }
            // For ClassRefDType (typedef to parameterized class like uvm_object_registry#(...))
            // Track the class dependency so we can resolve it correctly later
            if (AstClassRefDType* const crdtp = VN_CAST(dtypep, ClassRefDType)) {
                if (AstClass* const classp = crdtp->classp()) {
                    UINFO(5, "DEPGRAPH: typedef '" << nodep->name() << "' points to class '"
                                                   << classp->name() << "' in " << m_modp->name()
                                                   << endl);
                }
            }
            // For struct/union types, create a DepNode and track member dependencies.
            // These may have been moved to TYPETABLE but are still referenced via subDTypep.
            UINFO(5, "DEPGRAPH: typedef '"
                         << nodep->name()
                         << "' subDTypep=" << (dtypep ? dtypep->prettyTypeName() : "<null>")
                         << " type=" << (dtypep ? dtypep->typeName() : "<null>") << endl);
            if (AstNodeUOrStructDType* const usp = VN_CAST(dtypep, NodeUOrStructDType)) {
                V3LinkDotDepGraph::NodeType nodeType
                    = VN_IS(usp, UnionDType) ? V3LinkDotDepGraph::NodeType::UNIONDTYPE
                                             : V3LinkDotDepGraph::NodeType::STRUCTDTYPE;
                V3LinkDotDepGraph::DepNode* const uspNodep
                    = V3LinkDotDepGraph::findOrCreateNode(usp, nodeType, m_modp, m_cellPath);
                // Typedef depends on the struct/union
                V3LinkDotDepGraph::addEdge(depNodep, uspNodep);
                // Track member type dependencies (RefDType, PackArrayDType, etc.)
                for (AstMemberDType* memp = usp->membersp(); memp;
                     memp = VN_AS(memp->nextp(), MemberDType)) {
                    AstNodeDType* memDTypep = memp->subDTypep();
                    UINFO(5, "DEPGRAPH: typedef '"
                                 << nodep->name() << "' checking member '" << memp->name()
                                 << "' subDTypep="
                                 << (memDTypep ? memDTypep->prettyTypeName() : "<null>") << endl);
                    if (AstRefDType* const refp = VN_CAST(memDTypep, RefDType)) {
                        V3LinkDotDepGraph::DepNode* const refNodep
                            = V3LinkDotDepGraph::findOrCreateNode(
                                refp, V3LinkDotDepGraph::NodeType::REFDTYPE, m_modp, m_cellPath);
                        V3LinkDotDepGraph::addEdge(uspNodep, refNodep);

                        // If the RefDType points to a PARAMTYPEDTYPE, add direct edge to it.
                        // This ensures the struct waits for the PARAMTYPEDTYPE to be resolved.
                        AstNodeDType* const targetp = refp->refDTypep();
                        UINFO(5,
                              "DEPGRAPH: typedef '"
                                  << nodep->name() << "' member '" << memp->name() << "' targetp="
                                  << (targetp ? targetp->prettyTypeName() : "<null>") << " type="
                                  << (targetp ? targetp->typeName() : "<null>") << endl);
                        if (AstParamTypeDType* const ptdp = VN_CAST(targetp, ParamTypeDType)) {
                            AstNodeModule* const ptdOwnerp
                                = V3LinkDotDepGraph::findOwnerModule(ptdp);
                            V3LinkDotDepGraph::DepNode* const ptdNodep
                                = V3LinkDotDepGraph::findOrCreateNode(
                                    ptdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE,
                                    ptdOwnerp ? ptdOwnerp : m_modp, m_cellPath);
                            V3LinkDotDepGraph::addEdge(uspNodep, ptdNodep);
                            UINFO(5, "DEPGRAPH: typedef '"
                                         << nodep->name() << "' struct member '" << memp->name()
                                         << "' -> PARAMTYPEDTYPE '" << ptdp->name() << "'"
                                         << endl);
                        }

                        UINFO(5, "DEPGRAPH: typedef '"
                                     << nodep->name() << "' struct/union member '" << memp->name()
                                     << "' -> refdtype '" << refp->name() << "' -> "
                                     << (targetp ? targetp->prettyTypeName() : "<null>") << " w"
                                     << (targetp ? targetp->width() : 0) << endl);
                    } else if (AstPackArrayDType* const arrp
                               = VN_CAST(memDTypep, PackArrayDType)) {
                        // Track array range dependencies (may use parameters)
                        if (AstRange* const rangep = arrp->rangep()) {
                            V3LinkDotDepGraph::collectExpressionDeps(rangep->leftp(), uspNodep,
                                                                     m_modp);
                            V3LinkDotDepGraph::collectExpressionDeps(rangep->rightp(), uspNodep,
                                                                     m_modp);
                            UINFO(5, "DEPGRAPH: typedef '"
                                         << nodep->name() << "' struct/union member '"
                                         << memp->name()
                                         << "' -> packarraydtype range deps collected" << endl);
                        }
                        // Also track the element type if it's a RefDType
                        if (AstRefDType* const elemRefp = VN_CAST(arrp->subDTypep(), RefDType)) {
                            V3LinkDotDepGraph::DepNode* const refNodep
                                = V3LinkDotDepGraph::findOrCreateNode(
                                    elemRefp, V3LinkDotDepGraph::NodeType::REFDTYPE, m_modp,
                                    m_cellPath);
                            V3LinkDotDepGraph::addEdge(uspNodep, refNodep);
                            UINFO(5, "DEPGRAPH: typedef '"
                                         << nodep->name() << "' struct/union member '"
                                         << memp->name() << "' array element -> refdtype '"
                                         << elemRefp->name() << "'" << endl);
                        }
                    }
                }
                UINFO(5, "DEPGRAPH: typedef '"
                             << nodep->name() << "' -> "
                             << (VN_IS(usp, UnionDType) ? "UNIONDTYPE" : "STRUCTDTYPE") << " '"
                             << usp->name() << "' w" << usp->width()
                             << " deps=" << uspNodep->dependsOn.size() << endl);
                // Collect expression deps from struct members onto STRUCTDTYPE node (not TYPEDEF)
                // This ensures WIDTH dependency goes to struct, not typedef
                V3LinkDotDepGraph::collectExpressionDeps(dtypep, uspNodep, m_modp);
            } else {
                // For other types (not struct/union), collect deps onto TYPEDEF node
                V3LinkDotDepGraph::collectExpressionDeps(dtypep, depNodep, m_modp);
            }
        }
    }

    void visit(AstParamTypeDType* nodep) override {
        if (!m_modp) return;

        V3LinkDotDepGraph::DepNode* const depNodep = V3LinkDotDepGraph::findOrCreateNode(
            nodep, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, m_modp, m_cellPath);

        // Traverse the default type to collect dependencies (e.g. ranges using other params)
        // BUT: If this PARAMTYPE already has dependencies (from a pin override), skip this.
        // The pin override already provides the correct dependency edge.
        // Use m_cellPath as override so cross-module refs use correct context
        if (nodep->subDTypep() && depNodep->dependsOn.empty()) {
            if (nodep->name() == "T") {
                UINFO(5, "DEPGRAPH: DEBUG: visit ParamTypeDType 'T' in "
                             << m_modp->name() << " collecting deps from subDTypep with cellPath='"
                             << m_cellPath << "'\n");
            }
            V3LinkDotDepGraph::collectExpressionDeps(nodep->subDTypep(), depNodep, m_modp,
                                                     m_cellPath, /*hasCellPathOverride=*/true);
        } else {
            if (nodep->name() == "T") {
                UINFO(5, "DEPGRAPH: DEBUG: visit ParamTypeDType 'T' in "
                             << m_modp->name()
                             << (depNodep->dependsOn.empty()
                                     ? " has NO subDTypep"
                                     : " SKIP - already has deps from pin override")
                             << "\n");
            }
        }

        // NOTE: Dependencies from subDTypep are already collected at the top of this function
        // with the correct cellPath override. Do NOT call collectExpressionDeps again here
        // as it would create template nodes without cellPath context.
    }

    void visit(AstCell* nodep) override {
        if (!m_modp) return;
        // Handle cross-module edges: parameter pins connect parent expressions to child params
        AstNodeModule* const childModp = nodep->modp();
        if (!childModp) return;

        // Build the cellPath for this instantiation context
        // e.g., if we're in "t" visiting cell "u_sub", cellPath becomes "t.u_sub"
        const string parentCellPath = m_cellPath;
        const string childCellPath = parentCellPath.empty()
                                         ? (m_modp->name() + "." + nodep->name())
                                         : (parentCellPath + "." + nodep->name());

        UINFO(9, "DEPGRAPH: visit Cell '" << nodep->name() << "' in " << m_modp->name()
                                          << " childModp=" << childModp->name() << " cellPath='"
                                          << childCellPath << "'" << endl);

        // Process parameter pins (paramsp) - these contain parameter overrides like #($bits(var))
        // This is CRITICAL: we must capture these BEFORE V3Param processes them
        for (AstPin* pinp = nodep->paramsp(); pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            // Handle VALUE parameter pins (modVarp points to AstVar with isGParam)
            if (pinp->modVarp()) {
                AstVar* const childVarp = pinp->modVarp();
                if (!childVarp->isGParam()) continue;

                UINFO(9, "DEPGRAPH: Cell '" << nodep->name() << "' value param pin '"
                                            << pinp->name() << "' -> " << childVarp->name()
                                            << " in " << childModp->name() << " cellPath='"
                                            << childCellPath << "'" << endl);

                // Create node for child parameter (the GPARAM being overridden) with cellPath
                // context
                V3LinkDotDepGraph::NodeType childType = V3LinkDotDepGraph::classifyVar(childVarp);
                V3LinkDotDepGraph::DepNode* const childNodep = V3LinkDotDepGraph::findOrCreateNode(
                    childVarp, childType, childModp, childCellPath);
                childNodep->cellp = nodep;
                childNodep->pinp = pinp;  // Track the pin for FinalizeAST to update

                // The child param depends on the pin expression (which may reference parent
                // params/lparams) This creates the cross-module dependency edge IMPORTANT: Use
                // parentCellPath for expression deps - the expression is in the parent module's
                // scope, not the child's
                if (AstNode* const exprp = pinp->exprp()) {
                    UINFO(9, "DEPGRAPH: Collecting deps from param override expr for "
                                 << childVarp->name() << " using parentCellPath='"
                                 << parentCellPath << "'" << endl);
                    V3LinkDotDepGraph::collectExpressionDeps(
                        exprp, childNodep, m_modp, parentCellPath, /*hasCellPathOverride=*/true);

                    // Capture override expression - override REPLACES default as boundary
                    // condition
                    if (childNodep->initialValuep) { childNodep->initialValuep->deleteTree(); }
                    childNodep->initialValuep = exprp->cloneTree(false);
                    if (AstConst* const constp = VN_CAST(exprp, Const)) {
                        childNodep->initialWidth = constp->width();
                        UINFO(5, "DEPGRAPH: Cell override const width="
                                     << constp->width() << " for param '" << childVarp->name()
                                     << "'" << " cellPath='" << childCellPath << "'" << endl);
                    }
                    UINFO(9, "DEPGRAPH: Captured override expr for " << childVarp->name() << endl);
                }
            }
            // Handle TYPE parameter pins (modPTypep points to AstParamTypeDType)
            else if (pinp->modPTypep()) {
                AstParamTypeDType* const childPtdp = pinp->modPTypep();


                // Create node for child type parameter with cellPath context
                V3LinkDotDepGraph::DepNode* const childNodep = V3LinkDotDepGraph::findOrCreateNode(
                    childPtdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, childModp,
                    childCellPath);
                childNodep->cellp = nodep;
                childNodep->pinp = pinp;
                // The child type param depends on the pin expression (which is a type reference)
                // e.g., tflop #(.T(local_data_t)) - T depends on local_data_t
                // IMPORTANT: Use parentCellPath for expression deps - the expression is in the
                // parent module's scope, not the child's
                if (AstNode* const exprp = pinp->exprp()) {
                    UINFO(9, "DEPGRAPH: Collecting deps from type param override for "
                                 << childPtdp->name() << " using parentCellPath='"
                                 << parentCellPath << "'" << endl);
                    V3LinkDotDepGraph::collectExpressionDeps(
                        exprp, childNodep, m_modp, parentCellPath, /*hasCellPathOverride=*/true);
                }

                // For type parameter pins, capture the override type's width as initial state
                // This handles cases like #(logic) where the type is a simple basic type
                // with no dependencies - it's a boundary condition
                // exprp() can be an AstNodeDType for type parameters
                if (AstNodeDType* const dtypep = VN_CAST(pinp->exprp(), NodeDType)) {
                    int width = dtypep->width();
                    if (width <= 0) {
                        // Try to get width from basic type keyword
                        if (AstBasicDType* const bdtp = VN_CAST(dtypep, BasicDType)) {
                            if (bdtp->keyword() == VBasicDTypeKwd::LOGIC
                                || bdtp->keyword() == VBasicDTypeKwd::BIT) {
                                width = 1;
                            }
                        }
                    }
                    if (width > 0 && childNodep->initialWidth <= 0) {
                        childNodep->initialWidth = width;
                        UINFO(5, "DEPGRAPH: type param pin '" << pinp->name()
                                                              << "' captured width=" << width
                                                              << " from exprp dtype" << endl);
                    }
                }
            }
        }

        // Process port pins (pinsp) - these contain port connections
        for (AstPin* pinp = nodep->pinsp(); pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            if (!pinp->modVarp()) continue;
            AstVar* const childVarp = pinp->modVarp();
            if (!childVarp->isGParam()) continue;

            // Create node for child parameter with cellPath context
            V3LinkDotDepGraph::NodeType childType = V3LinkDotDepGraph::classifyVar(childVarp);
            V3LinkDotDepGraph::DepNode* const childNodep = V3LinkDotDepGraph::findOrCreateNode(
                childVarp, childType, childModp, childCellPath);
            childNodep->cellp = nodep;
            childNodep->pinp = pinp;

            // The child param depends on the pin expression (which may reference parent
            // params/lparams) IMPORTANT: Use parentCellPath for expression deps - the expression
            // is in the parent module's scope, not the child's (same as parameter pins above)
            if (AstNode* const exprp = pinp->exprp()) {
                V3LinkDotDepGraph::collectExpressionDeps(exprp, childNodep, m_modp, parentCellPath,
                                                         /*hasCellPathOverride=*/true);
            }
        }

        // Now visit the child module's contents in this cell's context
        // This creates per-cell-context nodes for typedefs, structs, localparams, etc.
        {
            VL_RESTORER(m_modp);
            VL_RESTORER(m_cellPath);
            m_modp = childModp;
            m_cellPath = childCellPath;
            rebuildVarMap();
            UINFO(9, "DEPGRAPH: entering child module " << childModp->name() << " with cellPath='"
                                                        << m_cellPath << "'" << endl);
            iterateChildrenConst(childModp);
        }

        iterateChildrenConst(nodep);
    }

    void visit(AstGenBlock* nodep) override {
        // Named generate blocks are part of the instance hierarchy.
        // V3Param includes them via m_generateHierName (V3Param.cpp:2718-2719).
        // We must include them in cellPaths to match.
        if (!nodep->name().empty()) {
            VL_RESTORER(m_cellPath);
            if (m_cellPath.empty()) {
                m_cellPath = m_modp->name() + "." + nodep->prettyName();
            } else {
                m_cellPath = m_cellPath + "." + nodep->prettyName();
            }
            UINFO(9, "DEPGRAPH: entering generate block '" << nodep->prettyName() << "' cellPath='"
                                                           << m_cellPath << "'" << endl);
            iterateChildrenConst(nodep);
        } else {
            iterateChildrenConst(nodep);
        }
    }

    void visit(AstRefDType* nodep) override {
        if (!m_modp) return;

        // findOrCreateNode handles registry lookup for cellName
        V3LinkDotDepGraph::DepNode* const depNodep = V3LinkDotDepGraph::findOrCreateNode(
            nodep, V3LinkDotDepGraph::NodeType::REFDTYPE, m_modp, m_cellPath);

        // If this RefDType points to a typedef, add edge
        if (AstTypedef* const tdp = nodep->typedefp()) {
            AstTypedef* targetTdp = tdp;
            AstNodeModule* tdOwnerp = V3LinkDotDepGraph::findOwnerModule(tdp);
            string ifaceCellPath;  // cellPath for interface typedef
            if (m_modp && isTemplateModule(tdOwnerp)) {
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
            // Compute interface cellPath if we're in a cell context and the typedef is in an
            // interface
            if (!m_cellPath.empty() && VN_IS(tdOwnerp, Iface)) {
                // Find the connected interface instance from the parent module
                const size_t lastDot = m_cellPath.rfind('.');
                if (lastDot != string::npos) {
                    const string parentPath = m_cellPath.substr(0, lastDot);
                    const string cellInstanceName = m_cellPath.substr(lastDot + 1);
                    // Find parent module
                    const size_t parentLastDot = parentPath.rfind('.');
                    const string parentModName = parentLastDot != string::npos
                                                     ? parentPath.substr(parentLastDot + 1)
                                                     : parentPath;
                    AstNodeModule* parentModp = nullptr;
                    for (const auto& pair : V3LinkDotDepGraph::s_nodes) {
                        if (pair.second->ownerModp
                            && pair.second->ownerModp->name() == parentModName) {
                            parentModp = pair.second->ownerModp;
                            break;
                        }
                    }
                    if (parentModp) {
                        // Find the cell and its interface port connection
                        for (AstNode* stmtp = parentModp->stmtsp(); stmtp;
                             stmtp = stmtp->nextp()) {
                            if (AstCell* const cellp = VN_CAST(stmtp, Cell)) {
                                if (cellp->name() == cellInstanceName && cellp->modp() == m_modp) {
                                    // Look at pins to find interface connections
                                    for (AstPin* pinp = cellp->pinsp(); pinp;
                                         pinp = VN_AS(pinp->nextp(), Pin)) {
                                        // Check if this pin connects to an interface of the right
                                        // type
                                        if (AstVarRef* const vrp
                                            = VN_CAST(pinp->exprp(), VarRef)) {
                                            // Check if the connected var is the interface we're
                                            // looking for
                                            if (AstVar* const connVarp = vrp->varp()) {
                                                AstIfaceRefDType* ifaceRefp
                                                    = findIfaceRefDType(connVarp->dtypep());
                                                if (!ifaceRefp)
                                                    ifaceRefp
                                                        = findIfaceRefDType(connVarp->subDTypep());
                                                if (!ifaceRefp)
                                                    ifaceRefp = findIfaceRefDType(
                                                        connVarp->childDTypep());
                                                if (ifaceRefp) {
                                                    AstNodeModule* connIfaceModp = nullptr;
                                                    if (ifaceRefp->cellp()
                                                        && ifaceRefp->cellp()->modp()) {
                                                        connIfaceModp = ifaceRefp->cellp()->modp();
                                                    } else if (ifaceRefp->ifacep()) {
                                                        connIfaceModp = ifaceRefp->ifacep();
                                                    }
                                                    // Check if this interface matches the
                                                    // typedef's owner
                                                    if (connIfaceModp) {
                                                        string connBase = connIfaceModp->name();
                                                        const size_t sp = connBase.find("__");
                                                        if (sp != string::npos)
                                                            connBase = connBase.substr(0, sp);
                                                        string tdBase = tdOwnerp->name();
                                                        const size_t tp = tdBase.find("__");
                                                        if (tp != string::npos)
                                                            tdBase = tdBase.substr(0, tp);
                                                        if (connBase == tdBase) {
                                                            // Strip __Viftop suffix
                                                            string ifaceName = vrp->name();
                                                            const size_t viftopPos
                                                                = ifaceName.find("__Viftop");
                                                            if (viftopPos != string::npos) {
                                                                ifaceName = ifaceName.substr(
                                                                    0, viftopPos);
                                                            }
                                                            ifaceCellPath
                                                                = parentPath + "." + ifaceName;
                                                            UINFO(5, "DEPGRAPH: REFDTYPE->TYPEDEF "
                                                                     "using interface cellPath '"
                                                                         << ifaceCellPath
                                                                         << "' for typedef '"
                                                                         << tdp->name() << "'"
                                                                         << endl);
                                                            break;
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    break;
                                }
                            }
                        }
                    }
                }
            }
            V3LinkDotDepGraph::DepNode* const tdNodep = V3LinkDotDepGraph::findOrCreateNode(
                targetTdp, V3LinkDotDepGraph::NodeType::TYPEDEF, tdOwnerp, ifaceCellPath);
            V3LinkDotDepGraph::addEdge(depNodep, tdNodep);
        }

        // If this RefDType points to a ParamTypeDType, add edge
        if (AstParamTypeDType* const ptdp = VN_CAST(nodep->refDTypep(), ParamTypeDType)) {
            AstParamTypeDType* targetPtdp = ptdp;
            AstNodeModule* ptdOwnerp = V3LinkDotDepGraph::findOwnerModule(ptdp);

            // If the paramtype is defined in a template interface, retarget to a specialized
            // instance based on the dot-lhs cell name (when available).
            if (m_modp && isTemplateModule(ptdOwnerp)) {
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
                    if (AstNodeModule* const resolvedModp
                        = resolveCellPathModule(m_modp, dotCellName)) {
                        // Check if resolved module base name matches ptdOwnerp
                        string resolvedBase = resolvedModp->name();
                        const size_t suffixPos = resolvedBase.find("__");
                        if (suffixPos != string::npos)
                            resolvedBase = resolvedBase.substr(0, suffixPos);
                        string ptdOwnerBase = ptdOwnerp->name();
                        const size_t ptdSuffixPos = ptdOwnerBase.find("__");
                        if (ptdSuffixPos != string::npos)
                            ptdOwnerBase = ptdOwnerBase.substr(0, ptdSuffixPos);
                        if (resolvedBase == ptdOwnerBase) {
                            for (AstNode* cellStmtp = resolvedModp->stmtsp(); cellStmtp;
                                 cellStmtp = cellStmtp->nextp()) {
                                if (AstParamTypeDType* const cellPtdp
                                    = VN_CAST(cellStmtp, ParamTypeDType)) {
                                    if (cellPtdp->name() == ptdp->name()) {
                                        targetPtdp = cellPtdp;
                                        ptdOwnerp = resolvedModp;
                                        UINFO(5,
                                              "DEPGRAPH: refdtype '"
                                                  << nodep->name()
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
                            if (AstParamTypeDType* const cellPtdp
                                = VN_CAST(cellStmtp, ParamTypeDType)) {
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
                            AstNodeModule* ifaceModp
                                = findConnectedIfaceModpFromPort(m_modp, dotCellName);
                            if (!ifaceModp && ifaceRefp->cellp() && ifaceRefp->cellp()->modp()) {
                                ifaceModp = ifaceRefp->cellp()->modp();
                            }
                            if (!ifaceModp && ifaceRefp->ifacep()) {
                                ifaceModp = ifaceRefp->ifacep();
                            }
                            if (ifaceModp) {
                                string ifaceBase = ifaceModp->name();
                                const size_t suffixPos = ifaceBase.find("__");
                                if (suffixPos != string::npos)
                                    ifaceBase = ifaceBase.substr(0, suffixPos);
                                if (ifaceBase == ptdOwnerp->name()) {
                                    for (AstNode* cellStmtp = ifaceModp->stmtsp(); cellStmtp;
                                         cellStmtp = cellStmtp->nextp()) {
                                        if (AstParamTypeDType* const cellPtdp
                                            = VN_CAST(cellStmtp, ParamTypeDType)) {
                                            if (cellPtdp->name() == ptdp->name()) {
                                                targetPtdp = cellPtdp;
                                                ptdOwnerp = ifaceModp;
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

            // Use m_cellPath for the PARAMTYPE node - for cross-module refs, we need to
            // compute the correct cellPath based on the parent module's context
            string ptdCellPath;
            if (!m_cellPath.empty() && ptdOwnerp != m_modp) {
                // Cross-module reference - use parent's cellPath (strip the current cell name)
                const size_t lastDot = m_cellPath.rfind('.');
                if (lastDot != string::npos) { ptdCellPath = m_cellPath.substr(0, lastDot); }
            } else {
                ptdCellPath = m_cellPath;
            }
            V3LinkDotDepGraph::DepNode* const ptdNodep = V3LinkDotDepGraph::findOrCreateNode(
                targetPtdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, ptdOwnerp, ptdCellPath);
            V3LinkDotDepGraph::addEdge(depNodep, ptdNodep);
        }

        // If this RefDType has an explicit class/package scope, add edge to that typedef/paramtype
        if (AstClassOrPackageRef* const scopeRefp
            = VN_CAST(nodep->classOrPackageOpp(), ClassOrPackageRef)) {
            if (AstTypedef* const scopeTdp = VN_CAST(scopeRefp->classOrPackageNodep(), Typedef)) {
                AstNodeModule* const tdOwnerp = V3LinkDotDepGraph::findOwnerModule(scopeTdp);
                V3LinkDotDepGraph::DepNode* const tdNodep = V3LinkDotDepGraph::findOrCreateNode(
                    scopeTdp, V3LinkDotDepGraph::NodeType::TYPEDEF, tdOwnerp, m_cellPath);
                V3LinkDotDepGraph::addEdge(depNodep, tdNodep);
                UINFO(5, "DEPGRAPH: refdtype '"
                             << nodep->name() << "' scoped by typedef '" << scopeTdp->name()
                             << "' in " << (tdOwnerp ? tdOwnerp->name() : "<null>") << endl);
            } else if (AstClass* const scopeClassp
                       = VN_CAST(scopeRefp->classOrPackageSkipp(), Class)) {
                for (AstNode* stmtp = scopeClassp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                    if (AstTypedef* const candTdp = VN_CAST(stmtp, Typedef)) {
                        if (candTdp->name() == nodep->name()) {
                            AstNodeModule* const tdOwnerp
                                = V3LinkDotDepGraph::findOwnerModule(candTdp);
                            V3LinkDotDepGraph::DepNode* const tdNodep
                                = V3LinkDotDepGraph::findOrCreateNode(
                                    candTdp, V3LinkDotDepGraph::NodeType::TYPEDEF, tdOwnerp,
                                    m_cellPath);
                            V3LinkDotDepGraph::addEdge(depNodep, tdNodep);
                            UINFO(5, "DEPGRAPH: refdtype '"
                                         << nodep->name() << "' scoped by class '"
                                         << scopeClassp->name() << "' typedef '" << candTdp->name()
                                         << "'" << endl);
                            break;
                        }
                    }
                }
            }
        }

        {
            auto it = s_refDTypeScopedTypedefs.find(nodep);
            AstTypedef* parentTdp = nullptr;
            for (AstNode* backp = nodep->backp(); backp; backp = backp->backp()) {
                if (AstTypedef* const tdp = VN_CAST(backp, Typedef)) {
                    parentTdp = tdp;
                    break;
                }
                if (VN_IS(backp, NodeModule)) break;
            }
            if (nodep->name() == "uvm_object_registry") {
                UINFO(5, "DEPGRAPH: refdtype '"
                             << nodep->name()
                             << "' parent typedef=" << (parentTdp ? parentTdp->name() : "<none>")
                             << " in " << (m_modp ? m_modp->name() : "<null>") << endl);
            }
            if (parentTdp && parentTdp->name() == "type_id") {
                const bool directHit = it != s_refDTypeScopedTypedefs.end();
                bool cloneHit = false;
                AstRefDType* origRefp = nullptr;
                if (!directHit) {
                    origRefp = nodep->clonep();
                    if (origRefp) {
                        cloneHit = s_refDTypeScopedTypedefs.find(origRefp)
                                   != s_refDTypeScopedTypedefs.end();
                    }
                }
                UINFO(5, "DEPGRAPH: scoped typedef lookup for type_id in "
                             << (m_modp ? m_modp->name() : "<null>") << " refdtype='"
                             << nodep->name() << "'" << " parent='" << parentTdp->name() << "'"
                             << " direct=" << (directHit ? "yes" : "no")
                             << " clone=" << (cloneHit ? "yes" : "no")
                             << " has_clone=" << (origRefp ? "yes" : "no") << endl);
            }
            if (it == s_refDTypeScopedTypedefs.end()) {
                if (AstRefDType* const origRefp = nodep->clonep()) {
                    it = s_refDTypeScopedTypedefs.find(origRefp);
                }
            }
            if (it != s_refDTypeScopedTypedefs.end()) {
                AstTypedef* const scopeTdp = it->second;
                AstNodeModule* const tdOwnerp = V3LinkDotDepGraph::findOwnerModule(scopeTdp);
                V3LinkDotDepGraph::DepNode* const tdNodep = V3LinkDotDepGraph::findOrCreateNode(
                    scopeTdp, V3LinkDotDepGraph::NodeType::TYPEDEF, tdOwnerp, m_cellPath);
                V3LinkDotDepGraph::addEdge(depNodep, tdNodep);
                UINFO(5, "DEPGRAPH: refdtype '"
                             << nodep->name() << "' scoped by registered typedef '"
                             << scopeTdp->name() << "' in "
                             << (tdOwnerp ? tdOwnerp->name() : "<null>") << endl);
            }
        }

        if (AstNodeModule* const scopeModp = nodep->classOrPackagep()) {
            AstNodeModule* searchModp = scopeModp;
            if (AstClassPackage* const pkgp = VN_CAST(scopeModp, ClassPackage)) {
                if (pkgp->classp()) searchModp = pkgp->classp();
            }
            if (searchModp) {
                for (AstNode* stmtp = searchModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                    if (AstTypedef* const tdp = VN_CAST(stmtp, Typedef)) {
                        if (tdp->name() == nodep->name()) {
                            AstNodeModule* const tdOwnerp
                                = V3LinkDotDepGraph::findOwnerModule(tdp);
                            V3LinkDotDepGraph::DepNode* const tdNodep
                                = V3LinkDotDepGraph::findOrCreateNode(
                                    tdp, V3LinkDotDepGraph::NodeType::TYPEDEF, tdOwnerp,
                                    m_cellPath);
                            V3LinkDotDepGraph::addEdge(depNodep, tdNodep);
                            break;
                        }
                    } else if (AstParamTypeDType* const scopePtdp
                               = VN_CAST(stmtp, ParamTypeDType)) {
                        if (scopePtdp->name() == nodep->name()) {
                            AstNodeModule* const ptdOwnerp
                                = V3LinkDotDepGraph::findOwnerModule(scopePtdp);
                            V3LinkDotDepGraph::DepNode* const ptdNodep
                                = V3LinkDotDepGraph::findOrCreateNode(
                                    scopePtdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE,
                                    ptdOwnerp, m_cellPath);
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
            nodep, V3LinkDotDepGraph::NodeType::STRUCTDTYPE, m_modp, m_cellPath);

        // Add dependency edges to member types.
        // The struct's width depends on its members' widths, so we need edges to:
        // 1. Member's RefDType
        // 2. Member's PARAMTYPEDTYPE (if the RefDType points to one)
        for (AstMemberDType* memp = nodep->membersp(); memp;
             memp = VN_AS(memp->nextp(), MemberDType)) {
            if (AstRefDType* const refp = VN_CAST(memp->subDTypep(), RefDType)) {
                AstNodeModule* const refOwnerp = V3LinkDotDepGraph::findOwnerModule(refp);
                V3LinkDotDepGraph::DepNode* const refNodep = V3LinkDotDepGraph::findOrCreateNode(
                    refp, V3LinkDotDepGraph::NodeType::REFDTYPE, refOwnerp ? refOwnerp : m_modp,
                    m_cellPath);
                V3LinkDotDepGraph::addEdge(depNodep, refNodep);

                // If the RefDType points to a PARAMTYPEDTYPE, add direct edge to it.
                // This ensures the struct waits for the PARAMTYPEDTYPE to be resolved.
                AstNodeDType* const targetp = refp->refDTypep();
                if (AstParamTypeDType* const ptdp = VN_CAST(targetp, ParamTypeDType)) {
                    AstNodeModule* const ptdOwnerp = V3LinkDotDepGraph::findOwnerModule(ptdp);
                    V3LinkDotDepGraph::DepNode* const ptdNodep
                        = V3LinkDotDepGraph::findOrCreateNode(
                            ptdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE,
                            ptdOwnerp ? ptdOwnerp : m_modp, m_cellPath);
                    V3LinkDotDepGraph::addEdge(depNodep, ptdNodep);
                    UINFO(5, "DEPGRAPH: struct '" << nodep->name() << "' member '" << memp->name()
                                                  << "' -> PARAMTYPEDTYPE '" << ptdp->name() << "'"
                                                  << endl);
                }

                UINFO(5, "DEPGRAPH: struct '" << nodep->name() << "' member '" << memp->name()
                                              << "' -> refdtype '" << refp->name() << "' -> "
                                              << (targetp ? targetp->prettyTypeName() : "<null>")
                                              << " w" << (targetp ? targetp->width() : 0) << endl);
            }
        }
        UINFO(5, "DEPGRAPH: STRUCTDTYPE '" << nodep->name() << "' in " << m_modp->name() << " w"
                                           << nodep->width()
                                           << " deps=" << depNodep->dependsOn.size() << endl);
        iterateChildrenConst(nodep);
    }

    void visit(AstUnionDType* nodep) override {
        if (!m_modp) return;
        V3LinkDotDepGraph::DepNode* const depNodep = V3LinkDotDepGraph::findOrCreateNode(
            nodep, V3LinkDotDepGraph::NodeType::UNIONDTYPE, m_modp);

        // Add dependency edges to member types (same as struct)
        for (AstMemberDType* memp = nodep->membersp(); memp;
             memp = VN_AS(memp->nextp(), MemberDType)) {
            if (AstRefDType* const refp = VN_CAST(memp->subDTypep(), RefDType)) {
                AstNodeModule* const refOwnerp = V3LinkDotDepGraph::findOwnerModule(refp);
                V3LinkDotDepGraph::DepNode* const refNodep = V3LinkDotDepGraph::findOrCreateNode(
                    refp, V3LinkDotDepGraph::NodeType::REFDTYPE, refOwnerp ? refOwnerp : m_modp);
                V3LinkDotDepGraph::addEdge(depNodep, refNodep);

                // If the RefDType points to a PARAMTYPEDTYPE, add direct edge to it.
                AstNodeDType* const targetp = refp->refDTypep();
                if (AstParamTypeDType* const ptdp = VN_CAST(targetp, ParamTypeDType)) {
                    AstNodeModule* const ptdOwnerp = V3LinkDotDepGraph::findOwnerModule(ptdp);
                    V3LinkDotDepGraph::DepNode* const ptdNodep
                        = V3LinkDotDepGraph::findOrCreateNode(
                            ptdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE,
                            ptdOwnerp ? ptdOwnerp : m_modp);
                    V3LinkDotDepGraph::addEdge(depNodep, ptdNodep);
                    UINFO(5, "DEPGRAPH: union '" << nodep->name() << "' member '" << memp->name()
                                                 << "' -> PARAMTYPEDTYPE '" << ptdp->name() << "'"
                                                 << endl);
                }

                UINFO(5, "DEPGRAPH: union '" << nodep->name() << "' member '" << memp->name()
                                             << "' -> refdtype '" << refp->name() << "' -> "
                                             << (targetp ? targetp->prettyTypeName() : "<null>")
                                             << " w" << (targetp ? targetp->width() : 0) << endl);
            }
        }
        UINFO(5, "DEPGRAPH: UNIONDTYPE '" << nodep->name() << "' in " << m_modp->name() << " w"
                                          << nodep->width()
                                          << " deps=" << depNodep->dependsOn.size() << endl);
        iterateChildrenConst(nodep);
    }

    // Helper to add dependency from ATTROF to a variable's dtype
    void addAttrOfVarDep(V3LinkDotDepGraph::DepNode* depNodep, AstAttrOf* nodep, AstVar* varp) {
        AstNodeDType* dtypep = varp->dtypep();
        // Skip through to the actual type
        while (dtypep) {
            if (AstRefDType* const rdp = VN_CAST(dtypep, RefDType)) {
                // Variable's type is a RefDType (e.g., data_t d;)
                AstNodeModule* rdpOwnerp = V3LinkDotDepGraph::findOwnerModule(rdp);
                if (!rdpOwnerp) rdpOwnerp = m_modp;
                V3LinkDotDepGraph::DepNode* const rdpNodep = V3LinkDotDepGraph::findOrCreateNode(
                    rdp, V3LinkDotDepGraph::NodeType::REFDTYPE, rdpOwnerp, m_cellPath);
                V3LinkDotDepGraph::addEdge(depNodep, rdpNodep);
                UINFO(5, "DEPGRAPH: ATTROF '" << nodep->attrType().ascii() << "' (via var '"
                                              << varp->name() << "') depends on REFDTYPE '"
                                              << rdp->name() << "' in " << m_modp->name() << endl);

                // Also add edge to PARAMTYPEDTYPE if applicable
                if (AstParamTypeDType* const ptdp = VN_CAST(rdp->refDTypep(), ParamTypeDType)) {
                    AstNodeModule* ptdOwnerp = V3LinkDotDepGraph::findOwnerModule(ptdp);
                    if (!ptdOwnerp) ptdOwnerp = rdpOwnerp;
                    V3LinkDotDepGraph::DepNode* const ptdNodep
                        = V3LinkDotDepGraph::findOrCreateNode(
                            ptdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, ptdOwnerp,
                            m_cellPath);
                    V3LinkDotDepGraph::addEdge(depNodep, ptdNodep);
                    UINFO(5, "DEPGRAPH: ATTROF '"
                                 << nodep->attrType().ascii() << "' (via var '" << varp->name()
                                 << "') depends on PARAMTYPEDTYPE '" << ptdp->name() << "' in "
                                 << m_modp->name() << endl);
                }
                break;
            } else if (AstNodeUOrStructDType* const usp = VN_CAST(dtypep, NodeUOrStructDType)) {
                // Variable's type is a struct/union
                AstNodeModule* uspOwnerp = V3LinkDotDepGraph::findOwnerModule(usp);
                if (!uspOwnerp) uspOwnerp = m_modp;
                V3LinkDotDepGraph::DepNode* const uspNodep = V3LinkDotDepGraph::findOrCreateNode(
                    usp,
                    VN_IS(usp, StructDType) ? V3LinkDotDepGraph::NodeType::STRUCTDTYPE
                                            : V3LinkDotDepGraph::NodeType::UNIONDTYPE,
                    uspOwnerp, m_cellPath);
                V3LinkDotDepGraph::addEdge(depNodep, uspNodep);
                UINFO(5, "DEPGRAPH: ATTROF '" << nodep->attrType().ascii() << "' (via var '"
                                              << varp->name() << "') depends on STRUCTDTYPE in "
                                              << m_modp->name() << endl);
                break;
            } else if (VN_IS(dtypep, BasicDType) || VN_IS(dtypep, ConstDType)
                       || VN_IS(dtypep, PackArrayDType) || VN_IS(dtypep, UnpackArrayDType)) {
                // Known non-parameterized types - no dependency needed
                // BasicDType: logic [N:0], int, etc.
                // ConstDType: const wrapper
                // PackArrayDType/UnpackArrayDType: arrays of basic types
                UINFO(9, "DEPGRAPH: ATTROF '" << nodep->attrType().ascii() << "' (via var '"
                                              << varp->name() << "') has non-parameterized dtype "
                                              << dtypep->typeName() << " - no dependency needed"
                                              << endl);
                break;
            } else {
                // Unknown dtype - warn so we can add handling if needed
                UINFO(1, "DEPGRAPH: WARNING: ATTROF '"
                             << nodep->attrType().ascii() << "' (via var '" << varp->name()
                             << "') has unhandled dtype " << dtypep->typeName() << " in "
                             << m_modp->name() << endl);
                break;
            }
        }
    }

    void visit(AstAttrOf* nodep) override {
        if (!m_modp) return;
        // Only interested in dimension/bits attributes that depend on types
        if (nodep->attrType() != VAttrType::DIM_BITS
            && nodep->attrType() != VAttrType::DIM_DIMENSIONS
            && nodep->attrType() != VAttrType::DIM_HIGH && nodep->attrType() != VAttrType::DIM_LEFT
            && nodep->attrType() != VAttrType::DIM_LOW && nodep->attrType() != VAttrType::DIM_RIGHT
            && nodep->attrType() != VAttrType::DIM_SIZE
            && nodep->attrType() != VAttrType::DIM_UNPK_DIMENSIONS) {
            return;
        }

        // Create ATTROF node in the graph
        V3LinkDotDepGraph::DepNode* const depNodep = V3LinkDotDepGraph::findOrCreateNode(
            nodep, V3LinkDotDepGraph::NodeType::ATTROF, m_modp, m_cellPath);

        UINFO(5, "DEPGRAPH: ATTROF '" << nodep->attrType().ascii() << "' fromp type="
                                      << (nodep->fromp() ? nodep->fromp()->typeName() : "<null>")
                                      << " in " << m_modp->name() << endl);

        // Add dependency on the fromp - handle different cases:
        // 1. $bits(type) - fromp is RefDType
        // 2. $bits(var) - fromp is VarRef, need to follow to var's dtype
        if (AstRefDType* const rdp = VN_CAST(nodep->fromp(), RefDType)) {
            AstNodeModule* rdpOwnerp = V3LinkDotDepGraph::findOwnerModule(rdp);
            if (!rdpOwnerp) rdpOwnerp = m_modp;
            V3LinkDotDepGraph::DepNode* const rdpNodep = V3LinkDotDepGraph::findOrCreateNode(
                rdp, V3LinkDotDepGraph::NodeType::REFDTYPE, rdpOwnerp, m_cellPath);
            V3LinkDotDepGraph::addEdge(depNodep, rdpNodep);
            UINFO(5, "DEPGRAPH: ATTROF '" << nodep->attrType().ascii() << "' depends on REFDTYPE '"
                                          << rdp->name() << "' in " << m_modp->name() << endl);
            // Do NOT add REFDTYPE->PARAMTYPEDTYPE edge here.  The REFDTYPE's
            // own visit() creates the correct instance-specific edge with
            // proper cellPath resolution.  Adding it here with m_cellPath
            // (which is the ATTROF owner's path, not the interface instance
            // path) creates a spurious template node with empty cellPath.
        } else if (AstVarRef* const vrp = VN_CAST(nodep->fromp(), VarRef)) {
            // $bits(var) - follow through to the variable's dtype
            if (AstVar* const varp = vrp->varp()) { addAttrOfVarDep(depNodep, nodep, varp); }
        } else if (AstParseRef* const prp = VN_CAST(nodep->fromp(), ParseRef)) {
            // $bits(var) where var is still a PARSEREF (not yet resolved to VarRef)
            // Look up the variable by name in the current module
            const string& varName = prp->name();
            AstVar* varp = nullptr;
            for (AstNode* stmtp = m_modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                if (AstVar* const candp = VN_CAST(stmtp, Var)) {
                    if (candp->name() == varName) {
                        varp = candp;
                        break;
                    }
                }
            }
            if (varp) {
                addAttrOfVarDep(depNodep, nodep, varp);
            } else {
                UINFO(5, "DEPGRAPH: ATTROF '" << nodep->attrType().ascii() << "' PARSEREF '"
                                              << varName << "' not found in " << m_modp->name()
                                              << endl);
            }
        }

        // Also collect any expression dependencies from fromp/dimp
        V3LinkDotDepGraph::collectExpressionDeps(nodep->fromp(), depNodep, m_modp);
        V3LinkDotDepGraph::collectExpressionDeps(nodep->dimp(), depNodep, m_modp);
    }

    void visit(AstNodeFTask* nodep) override {
        if (!m_modp) return;

        // Add function/task to dependency graph to track return type dependencies
        V3LinkDotDepGraph::DepNode* const depNodep = V3LinkDotDepGraph::findOrCreateNode(
            nodep, V3LinkDotDepGraph::NodeType::FUNC, m_modp, m_cellPath);

        // If function has a return type, add dependency edge
        if (nodep->isFunction() && nodep->fvarp()) {
            if (AstVar* const fvarp = VN_CAST(nodep->fvarp(), Var)) {
                V3LinkDotDepGraph::collectExpressionDeps(fvarp->dtypep(), depNodep, m_modp);
            }
        }

        // Visit function body for dependencies
        iterateChildrenConst(nodep);
    }

    // Helper to create edges for REFDTYPEs inside a dtype that reference PARAMTYPEDTYPEs
    void createEdgesForDtypeRefDTypes(AstNodeDType* dtypep) {
        if (!dtypep || !m_modp) return;
        dtypep->foreach([&](AstRefDType* rdp) {
            if (AstParamTypeDType* const ptdp = VN_CAST(rdp->refDTypep(), ParamTypeDType)) {
                AstNodeModule* rdpOwnerp = V3LinkDotDepGraph::findOwnerModule(rdp);
                if (!rdpOwnerp) rdpOwnerp = m_modp;
                AstNodeModule* ptdOwnerp = V3LinkDotDepGraph::findOwnerModule(ptdp);
                if (!ptdOwnerp) ptdOwnerp = rdpOwnerp;
                V3LinkDotDepGraph::DepNode* const rdpNodep = V3LinkDotDepGraph::findOrCreateNode(
                    rdp, V3LinkDotDepGraph::NodeType::REFDTYPE, rdpOwnerp);
                V3LinkDotDepGraph::DepNode* const ptdNodep = V3LinkDotDepGraph::findOrCreateNode(
                    ptdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, ptdOwnerp);
                V3LinkDotDepGraph::addEdge(rdpNodep, ptdNodep);
                UINFO(5, "DEPGRAPH: VAR dtype REFDTYPE '"
                             << rdp->name() << "' depends on PARAMTYPEDTYPE '" << ptdp->name()
                             << "' in " << m_modp->name() << endl);
            }
        });
    }

    void visit(AstNode* nodep) override {
        // For non-parameter VAR nodes, traverse their dtypes to find REFDTYPEs
        // that reference PARAMTYPEDTYPEs and create dependency edges
        if (AstVar* const varp = VN_CAST(nodep, Var)) {
            if (!varp->isGParam() && !varp->isParam()) {
                createEdgesForDtypeRefDTypes(varp->dtypep());
            }
        }
        iterateChildrenConst(nodep);
    }

public:
    explicit DepGraphBuildVisitor(AstNetlist* netlistp) { iterateConst(netlistp); }
};

void V3LinkDotDepGraph::build(AstNetlist* netlistp) {
    UINFO(3, "\n");
    UINFO(3, "========== DEPGRAPH PHASE: BUILD ==========" << endl);

    // NEW ARCHITECTURE: Build runs once before V3Param, capturing all nodes and edges
    // Old architecture had incremental builds during V3Param iterations - no longer needed
    if (s_allNodes.empty()) {
        reset();
    } else {
        // NEW ARCHITECTURE: build should only run once with empty graph
        UASSERT(false, "DEPGRAPH: build() called with "
                           << s_allNodes.size()
                           << " existing nodes - build should only be called once");
    }

    // PHASE 1: Discover and register cell associations for interface ports
    // This populates s_cellAssociations with mappings like "t.u_subA.io" -> "t.subA_io"
    // These associations are then used during DepGraphBuildVisitor::visit(AstRefDType*)
    // to correctly resolve typedefs that reference interface types through ports.
    UINFO(3, "DEPGRAPH: Phase 1 - Cell Association Discovery" << endl);
    CellAssocDiscoveryVisitor{netlistp};
    UINFO(3, "DEPGRAPH: Discovered " << s_cellAssociations.size() << " cell associations" << endl);

    // PHASE 2: Build the dependency graph
    // Now that s_cellAssociations is populated, DepGraphBuildVisitor can correctly
    // create dependency edges for REFDTYPE nodes that reference interface typedefs.
    UINFO(3, "DEPGRAPH: Phase 2 - Graph Build" << endl);
    DepGraphBuildVisitor{netlistp};

    for (AstNodeModule* modp = netlistp->modulesp(); modp;
         modp = VN_AS(modp->nextp(), NodeModule)) {
        s_builtModules.insert(modp);
    }
    auto recomputePendingDeps = []() {
        for (DepNode* nodep : s_allNodes) {
            if (!nodep) continue;
            if (nodep->resolved) {
                nodep->pendingDeps = 0;
                continue;
            }
            int pending = 0;
            for (DepNode* const depp : nodep->dependsOn) {
                if (depp && !depp->resolved) ++pending;
            }
            // Keep the higher value - addEdge may have incremented pendingDeps for edges
            // added after the initial build, and those edges may point to nodes that
            // are now resolved but haven't yet decremented this node's pendingDeps
            if (pending > nodep->pendingDeps) nodep->pendingDeps = pending;
            UINFO(9, "DEPGRAPH: pendingDeps '" << nodeName(nodep) << "'@" << nodeOwnerName(nodep)
                                               << " = " << nodep->pendingDeps << endl);
        }
    };
    recomputePendingDeps();
    UINFO(5, "DEPGRAPH: built " << s_allNodes.size() << " nodes" << endl);
    UINFO(5, "DEPGRAPH: parameterized module set size=" << s_parameterizedModules.size() << endl);
    for (AstNodeModule* const modp : s_parameterizedModules) {
        if (!modp) continue;
        UINFO(9, "DEPGRAPH: parameterized module in set mod='"
                     << modp->name() << "' someInstanceName='" << modp->someInstanceName() << "'"
                     << endl);
    }
    dumpGraph("after-build");
    dumpGraphDepsTree("after-build");
    dumpGraphDependentsTree("after-build");
}

//======================================================================
// Resolution - helper to sanitize cloned dtype trees

// After cloneTree(), cross-links like refDTypep, typedefp, classOrPackagep still point
// to nodes in the original/template tree. When V3Width processes the clone, it may
// follow these links and modify the template tree, causing broken pointers when
// the template is later deleted by V3Dead.
//
// This helper walks the cloned tree and clears any cross-links that point outside
// the clone. The ParamSubstVisitor will later set refDTypep to our resolved types.
static void sanitizeClonedDType(AstNodeDType* cloneDTypep) {
    if (!cloneDTypep) return;

    // Walk all nodes in the cloned tree and clear cross-links to the original AST.
    // For ALL dtype nodes: clear virtRefDTypep so V3Width uses childDTypep
    // (the cloned child) instead of refDTypep (which points to the original AST).
    // For RefDType specifically: also clear typedefp and classOrPackagep.
    cloneDTypep->foreach([](AstNode* nodep) {
        if (AstRefDType* const rdp = VN_CAST(nodep, RefDType)) {
            if (rdp->typedefp()) {
                UINFO(9, "DEPGRAPH: sanitize clearing typedefp on RefDType '" << rdp->name() << "'"
                                                                              << endl);
                rdp->typedefp(nullptr);
            }
            if (rdp->classOrPackagep()) {
                UINFO(9, "DEPGRAPH: sanitize clearing classOrPackagep on RefDType '"
                             << rdp->name() << "'" << endl);
                rdp->classOrPackagep(nullptr);
            }
            if (rdp->refDTypep()) {
                UINFO(9, "DEPGRAPH: sanitize clearing refDTypep on RefDType '"
                             << rdp->name() << "' was pointing to "
                             << rdp->refDTypep()->prettyTypeName() << endl);
                rdp->refDTypep(nullptr);
            }
            return;
        }
        // For all other dtype nodes: clear virtRefDTypep if set.
        // After cloneTree, refDTypep cross-references point to the original AST.
        // V3Width would follow these and corrupt the original by setting refDTypep
        // on nodes that still have childDTypep (violating the XOR invariant).
        // Clearing forces V3Width to use childDTypep (the cloned child) instead.
        if (AstNodeDType* const dtp = VN_CAST(nodep, NodeDType)) {
            if (dtp->virtRefDTypep()) {
                UINFO(9, "DEPGRAPH: sanitize clearing virtRefDTypep on "
                             << dtp->prettyTypeName() << " '" << dtp->name() << "'" << endl);
                dtp->virtRefDTypep(nullptr);
            }
        }
    });
}

//======================================================================
// Resolution - helper to evaluate LPARAM expressions

// Helper to evaluate an LPARAM expression by substituting resolved param values
// from dependencies and folding to a constant.
// Returns the folded AstConst, or nullptr if evaluation failed.
// Handles arbitrary expressions like: cfg.Width * cfg.Depth, $bits(data_t) + $bits(data2_t), etc.
//
// Algorithm:
// 1. Collect all dependency nodes that have resolved constant values
// 2. Clone the expression - cloneTree() sets clonep() on original nodes pointing to clones
// 3. For each dependency, use clonep() to find the cloned node and replace it with the value
// 4. Run V3Width and V3Const to fold the expression
static AstConst* evaluateLparamExpression(AstNode* exprp, V3LinkDotDepGraph::DepNode* nodep,
                                          const string& debugName) {
    using DepNode = V3LinkDotDepGraph::DepNode;

    if (!exprp || !nodep) return nullptr;

    // Skip if expression is already a constant
    if (AstConst* const constp = VN_CAST(exprp, Const)) { return constp->cloneTree(false); }

    // Skip if expression is a PATTERN - those are struct params, not expressions to evaluate
    if (VN_IS(exprp, Pattern)) return nullptr;

    UINFO(5, "DEPGRAPH: " << debugName << " evaluating expression: " << exprp->typeName() << endl);

    // 1. Collect all dependencies with resolved values (including transitive)
    // We need to collect before cloning so we can use clonep() after
    std::vector<std::pair<AstNode*, AstNode*>> substitutions;  // (origNodep, resolvedValuep)
    std::set<DepNode*> visited;
    std::function<void(DepNode*)> collectDeps = [&](DepNode* depp) {
        if (!depp || !depp->resolved || visited.count(depp)) return;
        visited.insert(depp);

        if (depp->resolvedValuep && depp->nodep) {
            AstNode* valuep = depp->resolvedValuep;

            // For PATTERN values, convert to ConsPackUOrStruct
            if (AstPattern* const patp = VN_CAST(valuep, Pattern)) {
                AstVar* const varp = VN_CAST(depp->nodep, Var);
                if (varp && varp->dtypep()) {
                    AstPattern* const clonePatp = patp->cloneTree(false);
                    clonePatp->dtypep(varp->dtypep());
                    V3Width::widthParamsEdit(clonePatp);
                    V3Const::constifyParamsEdit(clonePatp);
                    valuep = clonePatp;
                    UINFO(5, "DEPGRAPH: " << debugName << " processed PATTERN for "
                                          << V3LinkDotDepGraph::nodeName(depp) << " -> "
                                          << valuep->typeName() << endl);
                }
            }

            substitutions.push_back({depp->nodep, valuep});
            UINFO(5, "DEPGRAPH: " << debugName
                                  << " collected substitution: " << depp->nodep->typeName()
                                  << " -> " << valuep->typeName() << endl);
        }

        // Recurse into transitive dependencies
        for (DepNode* const transDepp : depp->dependsOn) { collectDeps(transDepp); }
    };
    for (DepNode* const depp : nodep->dependsOn) { collectDeps(depp); }

    // 2. Clone the expression - this sets clonep() on original nodes
    AstNode* clonedExprp = exprp->cloneTree(false);

    // 3. For each substitution, find the cloned node via clonep() and replace it
    // We need to wrap in a container first so replaceWith() works
    FileLine* const fl = exprp->fileline();
    AstBegin* const wrapperp = new AstBegin{fl, "[LparamEval]", clonedExprp, true /*implied*/};

    for (const auto& subst : substitutions) {
        AstNode* const origNodep = subst.first;
        AstNode* const valuep = subst.second;

        // clonep() points from original to its clone (set during cloneTree)
        AstNode* const clonedNodep = origNodep->clonep();
        if (clonedNodep) {
            // Clone the value and replace the cloned node
            AstNode* const newValuep = valuep->cloneTree(false);
            UINFO(5, "DEPGRAPH: " << debugName << " replacing cloned " << clonedNodep->typeName()
                                  << " with " << newValuep->typeName() << endl);
            clonedNodep->replaceWith(newValuep);
            VL_DO_DANGLING(clonedNodep->deleteTree(), clonedNodep);
        }
    }

    // Also run ParamSubstVisitor for VarRef and MemberSel substitutions
    // (these are matched by name, not by clonep())
    ParamSubstVisitor substVisitor;
    for (const auto& subst : substitutions) {
        // For VarRef substitutions, we need the parameter name
        if (AstVar* const varp = VN_CAST(subst.first, Var)) {
            substVisitor.addParam(varp->name(), subst.second);
        }
    }
    substVisitor.substitute(wrapperp);

    // 4. Extract the (possibly replaced) expression from the wrapper
    AstNode* resultExprp = wrapperp->stmtsp();
    if (resultExprp) { resultExprp->unlinkFrBack(); }

    // Clean up the wrapper
    VL_DO_DANGLING(wrapperp->deleteTree(), wrapperp);

    if (!resultExprp) {
        UINFO(5, "DEPGRAPH: " << debugName << " substitution produced null expression" << endl);
        return nullptr;
    }

    UINFO(5,
          "DEPGRAPH: " << debugName << " after substitution: " << resultExprp->typeName() << endl);

    // 5. Width and fold the expression
    resultExprp = V3Width::widthParamsEdit(resultExprp);
    resultExprp = V3Const::constifyEdit(resultExprp);

    UINFO(5, "DEPGRAPH: " << debugName << " after constify: " << resultExprp->typeName() << endl);

    // 6. Check if we got a constant
    if (AstConst* const constp = VN_CAST(resultExprp, Const)) {
        UINFO(5, "DEPGRAPH: " << debugName << " evaluated to const value="
                              << constp->num().toUInt() << " width=" << constp->width() << endl);
        return constp;
    }

    UINFO(5, "DEPGRAPH: " << debugName << " failed to evaluate to constant, result="
                          << resultExprp->typeName() << endl);
    return nullptr;
}

//======================================================================
// Resolution - helper to clone, substitute, and width a parameterized dtype

// Helper to clone a dtype, substitute resolved params/typedefs from dependencies,
// and compute width via V3Width/V3Const. Used by both TYPEDEF and STRUCTDTYPE execution.
// Returns the resolved dtype with computed width, or nullptr on failure.
static AstNodeDType* resolveParameterizedDType(AstNodeDType* dtypep,
                                               V3LinkDotDepGraph::DepNode* nodep,
                                               const string& debugName) {
    using DepNode = V3LinkDotDepGraph::DepNode;
    using NodeType = V3LinkDotDepGraph::NodeType;

    if (!dtypep || !nodep) return nullptr;

    // 1. Clone the dtype - get self-contained copy of entire type tree
    AstNodeDType* const cloneDTypep = dtypep->cloneTree(false);

    // Add to cloned types pool for centralized cleanup
    // The pool owns this type - DepNodes just reference it via resolvedTypep
    s_clonedTypes.push_back(cloneDTypep);

    // 2. Sanitize the clone - clear cross-links that point to template tree
    // This prevents V3Width from following pointers back to the template and modifying it
    sanitizeClonedDType(cloneDTypep);

    // Debug: Check if clone RefDType is same object as original
    if (AstStructDType* const origSdtp = VN_CAST(dtypep, StructDType)) {
        if (AstStructDType* const cloneSdtp = VN_CAST(cloneDTypep, StructDType)) {
            AstMemberDType* origMemp = origSdtp->membersp();
            AstMemberDType* cloneMemp = cloneSdtp->membersp();
            while (origMemp && cloneMemp) {
                if (AstRefDType* const origRdtp = VN_CAST(origMemp->subDTypep(), RefDType)) {
                    if (AstRefDType* const cloneRdtp = VN_CAST(cloneMemp->subDTypep(), RefDType)) {
                        if (origRdtp == cloneRdtp) {
                            UINFO(0, "DEPGRAPH: FATAL clone RefDType '"
                                         << origRdtp->name()
                                         << "' is SAME OBJECT as original! ptr="
                                         << cvtToHex(origRdtp) << endl);
                        }
                    }
                }
                origMemp = VN_CAST(origMemp->nextp(), MemberDType);
                cloneMemp = VN_CAST(cloneMemp->nextp(), MemberDType);
            }
        }
    }

    // Debug: Check if clone shares nodes with original (indicates incomplete clone)
    if (AstStructDType* const origSdtp = VN_CAST(dtypep, StructDType)) {
        if (AstStructDType* const cloneSdtp = VN_CAST(cloneDTypep, StructDType)) {
            AstMemberDType* origMemp = origSdtp->membersp();
            AstMemberDType* cloneMemp = cloneSdtp->membersp();
            while (origMemp && cloneMemp) {
                if (origMemp->subDTypep() && cloneMemp->subDTypep()) {
                    if (origMemp->subDTypep() == cloneMemp->subDTypep()) {
                        UINFO(0, "DEPGRAPH: WARNING member '"
                                     << origMemp->name() << "' shares subDTypep with original! "
                                     << "ptr=" << cvtToHex(origMemp->subDTypep()) << endl);
                    }
                }
                origMemp = VN_CAST(origMemp->nextp(), MemberDType);
                cloneMemp = VN_CAST(cloneMemp->nextp(), MemberDType);
            }
        }
    }

    // Debug: Check if clone RefDType points to original typedef
    if (AstStructDType* const cloneSdtp = VN_CAST(cloneDTypep, StructDType)) {
        for (AstMemberDType* memp = cloneSdtp->membersp(); memp;
             memp = VN_AS(memp->nextp(), MemberDType)) {
            if (AstRefDType* const rdtp = VN_CAST(memp->subDTypep(), RefDType)) {
                UINFO(0, "DEPGRAPH: clone RefDType '"
                             << rdtp->name() << "' typedefp="
                             << (rdtp->typedefp() ? rdtp->typedefp()->name() : "<null>")
                             << " typedefpBackp="
                             << (rdtp->typedefp() && rdtp->typedefp()->backp() ? "Y" : "N")
                             << endl);
            }
        }
    }
    // We need to collect from TRANSITIVE dependencies, not just direct ones,
    // because struct members reference typedefs through REFDTYPE nodes
    ParamSubstVisitor substVisitor;
    std::set<DepNode*> visited;
    std::function<void(DepNode*)> collectSubstitutions = [&](DepNode* depp) {
        if (!depp || !depp->resolved || visited.count(depp)) return;
        visited.insert(depp);

        // Add parameter values (GPARAM, LPARAM)
        if ((depp->nodeType == NodeType::GPARAM || depp->nodeType == NodeType::LPARAM)
            && depp->resolvedValuep) {
            const string paramName = V3LinkDotDepGraph::nodeName(depp);
            AstNode* valuep = depp->resolvedValuep;

            // If it's a PATTERN, we need to process it through V3Width
            // to convert it to ConsPackUOrStruct
            if (AstPattern* const patp = VN_CAST(valuep, Pattern)) {
                // Get the dtype from the parameter variable
                AstVar* const varp = VN_CAST(depp->nodep, Var);
                if (varp && varp->dtypep()) {
                    // Clone the pattern and set its dtype
                    AstPattern* const clonePatp = patp->cloneTree(false);
                    clonePatp->dtypep(varp->dtypep());
                    // Process through V3Width to convert PATTERN -> ConsPackUOrStruct
                    V3Width::widthParamsEdit(clonePatp);
                    V3Const::constifyParamsEdit(clonePatp);
                    // Use the processed value
                    valuep = clonePatp;
                    UINFO(5, "DEPGRAPH: " << debugName << " processed PATTERN for param "
                                          << paramName << " -> " << valuep->typeName() << endl);
                }
            }

            substVisitor.addParam(paramName, valuep);
            UINFO(5, "DEPGRAPH: " << debugName << " adding param substitution: " << paramName
                                  << endl);
        }

        // Add typedef types (from TYPEDEF or REFDTYPE nodes)
        // REFDTYPE nodes that reference typedefs also have resolvedTypep
        if ((depp->nodeType == NodeType::TYPEDEF || depp->nodeType == NodeType::REFDTYPE)
            && depp->resolvedTypep) {
            const string typedefName = V3LinkDotDepGraph::nodeName(depp);
            substVisitor.addTypedef(typedefName, depp->resolvedTypep);
            UINFO(5, "DEPGRAPH: " << debugName << " adding typedef substitution: " << typedefName
                                  << " from "
                                  << (depp->nodeType == NodeType::TYPEDEF ? "TYPEDEF" : "REFDTYPE")
                                  << " resolvedTypep=" << depp->resolvedTypep->prettyTypeName()
                                  << " width=" << depp->resolvedTypep->width() << endl);
        }

        // Recurse into transitive dependencies
        for (DepNode* const transDepp : depp->dependsOn) { collectSubstitutions(transDepp); }
    };
    for (DepNode* const depp : nodep->dependsOn) { collectSubstitutions(depp); }

    // 3. Run substitution on the cloned type tree
    UINFO(5, "DEPGRAPH: " << debugName
                          << " before substitution, cloneDTypep=" << cloneDTypep->prettyTypeName()
                          << " width=" << cloneDTypep->width() << endl);
    substVisitor.substitute(cloneDTypep);
    UINFO(5, "DEPGRAPH: " << debugName
                          << " after substitution, cloneDTypep=" << cloneDTypep->prettyTypeName()
                          << " width=" << cloneDTypep->width() << endl);

    // Debug: dump struct members after substitution
    if (AstStructDType* const sdtp = VN_CAST(cloneDTypep, StructDType)) {
        for (AstMemberDType* memp = sdtp->membersp(); memp;
             memp = VN_AS(memp->nextp(), MemberDType)) {
            UINFO(5, "DEPGRAPH: " << debugName << " member '" << memp->name()
                                  << "' width=" << memp->width() << " subDTypep="
                                  << (memp->subDTypep() ? memp->subDTypep()->prettyTypeName()
                                                        : "<null>")
                                  << " subWidth="
                                  << (memp->subDTypep() ? memp->subDTypep()->width() : 0) << endl);
        }
    }

    // 4. Call V3Width and V3Const to evaluate the parameterized expressions
    // This computes widths and folds constants
    V3Width::widthParamsEdit(cloneDTypep);

    // Sanitize AGAIN after V3Width - V3Width may have set refDTypep to template nodes
    // This is critical because V3Width follows type chains and may set refDTypep
    // to BasicDType nodes that exist in the template tree
    sanitizeClonedDType(cloneDTypep);

    UINFO(5, "DEPGRAPH: " << debugName
                          << " after V3Width, cloneDTypep=" << cloneDTypep->prettyTypeName()
                          << " width=" << cloneDTypep->width() << endl);
    V3Const::constifyParamsEdit(cloneDTypep);
    UINFO(5, "DEPGRAPH: " << debugName
                          << " after V3Const, cloneDTypep=" << cloneDTypep->prettyTypeName()
                          << " width=" << cloneDTypep->width() << endl);

    // Debug: dump struct members after V3Width
    if (AstStructDType* const sdtp = VN_CAST(cloneDTypep, StructDType)) {
        for (AstMemberDType* memp = sdtp->membersp(); memp;
             memp = VN_AS(memp->nextp(), MemberDType)) {
            UINFO(5, "DEPGRAPH: " << debugName << " FINAL member '" << memp->name()
                                  << "' width=" << memp->width() << " subDTypep="
                                  << (memp->subDTypep() ? memp->subDTypep()->prettyTypeName()
                                                        : "<null>")
                                  << " subWidth="
                                  << (memp->subDTypep() ? memp->subDTypep()->width() : 0) << endl);
        }
    }

    UINFO(5,
          "DEPGRAPH: " << debugName << " resolved dtype width=" << cloneDTypep->width() << endl);

    return cloneDTypep;
}

//======================================================================
// Resolution - helper to re-evaluate a single node

void V3LinkDotDepGraph::reEvaluateNode(DepNode* nodep) {
    // NEW ARCHITECTURE: reEvaluateNode computes resolved state purely from dependency DepNodes.
    // No AST reads or writes here - DepGraph is a shadow data structure.
    // Initial values are captured during build phase into DepNode fields.
    // Final values are applied to AST in finalizeAST() after all nodes are resolved.
    //
    // Execution model:
    //   1. Read resolved state from parent DepNodes (dependsOn)
    //   2. Compute this node's resolved state
    //   3. Store result in this node (resolvedWidth, resolvedTypep, resolvedValuep)
    //   4. Caller will wake up children (dependents)
    if (!nodep) return;

    // Skip nodes in dead modules
    AstNodeModule* const ownerModp = nodep->ownerModp;
    if (ownerModp && ownerModp->dead()) {
        UINFO(9, "DEPGRAPH: skip re-evaluate '" << nodeName(nodep) << "' in dead module "
                                                << ownerModp->name() << endl);
        return;
    }

    // Initialize resolved state from initial state (boundary conditions)
    // This is important for nodes with no dependencies (roots of the graph)
    // For boundary nodes (no dependsOn), the "input edge" is the AST node itself
    // We read from the AST during execution, not just from cached initialWidth
    if (nodep->dependsOn.empty()) {
        // Boundary node - read current state from AST (the "input edge")
        switch (nodep->nodeType) {
        case NodeType::PARAMTYPEDTYPE: {
            AstParamTypeDType* const ptdp = VN_CAST(nodep->nodep, ParamTypeDType);
            if (ptdp) {
                int width = 0;
                // Try dtypep first (the resolved type)
                if (ptdp->dtypep()) {
                    width = ptdp->dtypep()->width();
                    UINFO(5, "DEPGRAPH: PARAMTYPE '"
                                 << ptdp->name() << "' dtypep=" << ptdp->dtypep()->prettyTypeName()
                                 << " width=" << width << endl);
                }
                // Then try subDTypep (the default type)
                if (width <= 0 && ptdp->subDTypep()) {
                    width = ptdp->subDTypep()->width();
                    UINFO(5, "DEPGRAPH: PARAMTYPE '" << ptdp->name() << "' subDTypep="
                                                     << ptdp->subDTypep()->prettyTypeName()
                                                     << " width=" << width << endl);
                    // For basic types like 'logic', width might be 0 but we know it's 1
                    if (width <= 0) {
                        if (AstBasicDType* const bdtp = VN_CAST(ptdp->subDTypep(), BasicDType)) {
                            // Basic types have known widths even if not set
                            if (bdtp->keyword() == VBasicDTypeKwd::LOGIC
                                || bdtp->keyword() == VBasicDTypeKwd::BIT) {
                                width = 1;  // Single-bit basic type
                                UINFO(5, "DEPGRAPH: PARAMTYPE '"
                                             << ptdp->name()
                                             << "' using default width=1 for basic type" << endl);
                            }
                        }
                    }
                }
                if (width > 0) nodep->resolvedWidth = width;
            }
            break;
        }
        case NodeType::GPARAM:
        case NodeType::LPARAM: {
            // For GPARAMs, the value comes from the pin override (captured in initialValuep)
            // For LPARAMs with no dependencies, use initialValuep if it's a constant
            // Do NOT read from varp->valuep() as that's the default, not the override
            if (nodep->initialWidth > 0 && nodep->resolvedWidth <= 0) {
                nodep->resolvedWidth = nodep->initialWidth;
            }
            if (nodep->initialValuep && !nodep->resolvedValuep) {
                if (VN_IS(nodep->initialValuep, Const)) {
                    nodep->resolvedValuep = nodep->initialValuep;
                }
            }
            break;
        }
        default:
            // For other types, use cached initialWidth
            if (nodep->initialWidth > 0 && nodep->resolvedWidth <= 0) {
                nodep->resolvedWidth = nodep->initialWidth;
            }
            break;
        }
    } else if (nodep->initialWidth > 0 && nodep->resolvedWidth <= 0) {
        // Non-boundary node - use cached initialWidth as fallback
        nodep->resolvedWidth = nodep->initialWidth;
    }
    // Only copy initialValuep for boundary nodes (no dependencies)
    // Nodes with dependencies should get their value from the dependency chain
    if (nodep->initialValuep && !nodep->resolvedValuep && nodep->dependsOn.empty()) {
        // Only use initialValuep if it's a constant - expressions like $bits()
        // need to be computed from the dependency chain
        if (VN_IS(nodep->initialValuep, Const)) { nodep->resolvedValuep = nodep->initialValuep; }
    }
    // NOTE: Do NOT copy initialTypep to resolvedTypep - initialTypep points to
    // the original AST node which may be modified/deleted. resolvedTypep should
    // only be set to cloned nodes created during resolution.

    // Special handling for STRUCTDTYPE/UNIONDTYPE - use helper to properly compute width
    // This must happen BEFORE the general propagation loop since we need all dependencies resolved
    if ((nodep->nodeType == NodeType::STRUCTDTYPE || nodep->nodeType == NodeType::UNIONDTYPE)
        && !nodep->resolvedTypep) {
        AstNodeDType* const sdtp = VN_CAST(nodep->nodep, NodeDType);
        if (sdtp) {
            AstNodeDType* const resolvedDTypep
                = resolveParameterizedDType(sdtp, nodep, "STRUCTDTYPE '" + nodeName(nodep) + "'");
            if (resolvedDTypep) {
                nodep->resolvedTypep = resolvedDTypep;
                nodep->resolvedWidth = resolvedDTypep->width();
                UINFO(5, "DEPGRAPH: STRUCTDTYPE '" << nodeName(nodep) << "' resolved width="
                                                   << nodep->resolvedWidth << endl);
            }
        }
    }

    // Read resolved state from parent DepNodes
    for (DepNode* const depp : nodep->dependsOn) {
        if (!depp || !depp->resolved) continue;

        // For other nodes, propagate resolvedWidth normally
        if (depp->resolvedWidth > 0 && nodep->resolvedWidth <= 0) {
            nodep->resolvedWidth = depp->resolvedWidth;
            UINFO(5, "DEPGRAPH: propagate resolvedWidth " << depp->resolvedWidth << " from '"
                                                          << nodeName(depp) << "' to '"
                                                          << nodeName(nodep) << "'" << endl);
        }

        // Propagate resolvedTypep for type parameters
        if (depp->resolvedTypep && !nodep->resolvedTypep) {
            nodep->resolvedTypep = depp->resolvedTypep;
            UINFO(5, "DEPGRAPH: propagate resolvedTypep from '" << nodeName(depp) << "' to '"
                                                                << nodeName(nodep) << "'" << endl);
        }

        // Propagate resolvedValuep only to nodes that should have values
        // (GPARAM, LPARAM, ATTROF) - NOT to type nodes (TYPEDEF, STRUCTDTYPE, REFDTYPE, etc.)
        if (depp->resolvedValuep && !nodep->resolvedValuep
            && (nodep->nodeType == NodeType::GPARAM || nodep->nodeType == NodeType::LPARAM
                || nodep->nodeType == NodeType::ATTROF)) {
            nodep->resolvedValuep = depp->resolvedValuep;
            UINFO(5, "DEPGRAPH: propagate resolvedValuep from '"
                         << nodeName(depp) << "' to '" << nodeName(nodep) << "'" << endl);
        }
    }

    // Special handling for TYPEDEF nodes - clone, substitute, and build the type
    // This handles arbitrarily complex parameterized types like:
    //   typedef logic [cfg.p_a-1:0] data_t;
    //   typedef struct packed { logic [cfg.CCNumWaveThreads*64-1:0] raw; } tb_data_t;
    if (nodep->nodeType == NodeType::TYPEDEF && !nodep->resolvedTypep) {
        AstTypedef* const tdp = VN_CAST(nodep->nodep, Typedef);
        if (tdp && tdp->subDTypep()) {
            // Check if direct dependency is a STRUCTDTYPE/UNIONDTYPE with resolved type
            // If so, use that type directly - the struct execution already computed it
            bool usedStructType = false;
            for (DepNode* const depp : nodep->dependsOn) {
                if (!depp || !depp->resolved) continue;
                if ((depp->nodeType == NodeType::STRUCTDTYPE
                     || depp->nodeType == NodeType::UNIONDTYPE)
                    && depp->resolvedTypep && depp->resolvedWidth > 0) {
                    // Use the struct's resolved width and type directly
                    nodep->resolvedWidth = depp->resolvedWidth;
                    nodep->resolvedTypep = depp->resolvedTypep;
                    UINFO(5, "DEPGRAPH: TYPEDEF '" << tdp->name()
                                                   << "' using STRUCTDTYPE resolved width="
                                                   << nodep->resolvedWidth << endl);
                    usedStructType = true;
                    break;
                }
            }

            if (!usedStructType) {
                // Use helper to clone, substitute, and width the typedef's subDTypep
                AstNodeDType* const resolvedDTypep = resolveParameterizedDType(
                    tdp->subDTypep(), nodep, "TYPEDEF '" + tdp->name() + "'");
                if (resolvedDTypep) {
                    nodep->resolvedTypep = resolvedDTypep;
                    nodep->resolvedWidth = resolvedDTypep->width();
                    UINFO(5, "DEPGRAPH: TYPEDEF '" << tdp->name() << "' built type with width="
                                                   << nodep->resolvedWidth << endl);
                }
            }
        }
    }

    // If no dependency provided a width, use the initial width captured during build
    if (nodep->resolvedWidth <= 0 && nodep->initialWidth > 0) {
        nodep->resolvedWidth = nodep->initialWidth;
        UINFO(5, "DEPGRAPH: use initialWidth " << nodep->initialWidth << " for '"
                                               << nodeName(nodep) << "'" << endl);
    }

    // Special handling for LPARAM nodes - ALWAYS evaluate the expression
    // The initialValuep is always an expression tree that may contain:
    //   - Simple CONST (already evaluated)
    //   - VARREF to another param
    //   - MemberSel for struct params (cfg.Width)
    //   - Complex expressions ($bits(data_t) * cfg.Width - 2 + $clog2(param_B))
    //   - PATTERN (struct literal like '{8})
    // We substitute all dependencies and fold to a constant.
    if (nodep->nodeType == NodeType::LPARAM && nodep->initialValuep) {
        // Special case: PATTERN values need dtype set before V3Width can process them
        if (AstPattern* const patp = VN_CAST(nodep->initialValuep, Pattern)) {
            AstVar* const varp = VN_CAST(nodep->nodep, Var);
            // Use subDTypep() - m_dtypep may be null while childDTypep
            // (the REFDTYPE child) is already linked by LinkDot.
            AstNodeDType* const varDTypep = varp ? varp->subDTypep() : nullptr;
            if (varp && varDTypep) {
                // 1. Collect resolved values from dependencies for substitution
                std::vector<std::pair<AstNode*, AstNode*>> substitutions;
                std::set<DepNode*> visited;
                std::function<void(DepNode*)> collectDeps = [&](DepNode* depp) {
                    if (!depp || !depp->resolved || visited.count(depp)) return;
                    visited.insert(depp);
                    if (depp->resolvedValuep && depp->nodep) {
                        substitutions.push_back({depp->nodep, depp->resolvedValuep});
                    }
                    for (DepNode* const transDepp : depp->dependsOn) { collectDeps(transDepp); }
                };
                for (DepNode* const depp : nodep->dependsOn) { collectDeps(depp); }

                // Only constify PATTERNs that have actual resolved dependencies
                // to substitute. PATTERNs with only literal constants (no deps)
                // don't need DepGraph intervention - V3Param handles them.
                // Calling widthParamsEdit during DepGraph execution on such
                // PATTERNs produces wrong results (AST not fully set up).
                if (!substitutions.empty()) {
                    // 2. Clone the pattern (sets clonep() on all original nodes)
                    AstPattern* const clonePatp = patp->cloneTree(false);

                    // 3. Substitute resolved dependency values into the clone
                    // This replaces e.g. ATTROF($bits(cmd_beat_t)) with CONST(512)
                    for (const auto& subst : substitutions) {
                        AstNode* const clonedNodep = subst.first->clonep();
                        if (clonedNodep) {
                            AstNode* const newValuep = subst.second->cloneTree(false);
                            UINFO(9, "DEPGRAPH: LPARAM '" << nodeName(nodep)
                                                          << "' PATTERN substituting "
                                                          << clonedNodep->typeName() << " -> "
                                                          << newValuep->typeName() << endl);
                            clonedNodep->replaceWith(newValuep);
                            VL_DO_DANGLING(clonedNodep->deleteTree(), clonedNodep);
                        }
                    }

                    // 4. Set dtype and process through V3Width/V3Const
                    // widthParamsEdit/constifyParamsEdit may replace the node
                    // (e.g. PATTERN -> ConsPackUOrStruct), so capture returns.
                    clonePatp->dtypep(varDTypep);
                    AstNode* resultExprp = V3Width::widthParamsEdit(clonePatp);
                    V3Const::constifyParamsEdit(resultExprp);

                    // Only store if constification produced a proper constant.
                    // If widthParamsEdit produced something unexpected (e.g. CONCAT),
                    // discard and fall back to original PATTERN.
                    if (VN_IS(resultExprp, Const) || VN_IS(resultExprp, ConsPackUOrStruct)) {
                        nodep->resolvedValuep = resultExprp;
                        if (resultExprp->dtypep()) {
                            nodep->resolvedWidth = resultExprp->dtypep()->width();
                        }
                        UINFO(5, "DEPGRAPH: LPARAM '" << nodeName(nodep)
                                                      << "' processed PATTERN -> "
                                                      << resultExprp->typeName() << endl);
                    } else {
                        UINFO(5, "DEPGRAPH: LPARAM '"
                                     << nodeName(nodep) << "' PATTERN constification produced "
                                     << resultExprp->typeName() << ", falling back to as-is"
                                     << endl);
                        resultExprp->deleteTree();
                        nodep->resolvedValuep = nodep->initialValuep;
                    }
                } else {
                    // No substitutions needed - use original PATTERN as-is.
                    // V3Param will constify it with fully available types.
                    nodep->resolvedValuep = nodep->initialValuep;
                    UINFO(5, "DEPGRAPH: LPARAM '"
                                 << nodeName(nodep)
                                 << "' PATTERN has no deps to substitute, using as-is" << endl);
                }
            } else {
                // No dtype available - use as-is
                nodep->resolvedValuep = nodep->initialValuep;
                UINFO(5, "DEPGRAPH: LPARAM '" << nodeName(nodep)
                                              << "' PATTERN has no dtype, using as-is" << endl);
            }
        } else {
            // Not a PATTERN - evaluate as expression
            AstConst* const constp = evaluateLparamExpression(nodep->initialValuep, nodep,
                                                              "LPARAM '" + nodeName(nodep) + "'");
            if (constp) {
                nodep->resolvedValuep = constp;
                nodep->resolvedWidth = constp->width();
            } else {
                // Evaluation failed - use initialValuep as fallback
                // This may happen if dependencies aren't fully resolved yet
                if (!nodep->resolvedValuep) {
                    nodep->resolvedValuep = nodep->initialValuep;
                    UINFO(1, "DEPGRAPH: WARNING: LPARAM '"
                                 << nodeName(nodep) << "'@" << nodeOwnerName(nodep)
                                 << " cellPath='" << nodep->cellPath
                                 << "' evaluation failed, using initialValuep as fallback"
                                 << " (result type="
                                 << (nodep->initialValuep ? nodep->initialValuep->typeName()
                                                          : "<null>")
                                 << ")" << endl);
                }
            }
        }
    } else if (!nodep->resolvedValuep && nodep->initialValuep) {
        // For non-LPARAM nodes, use initialValuep if no value was propagated
        nodep->resolvedValuep = nodep->initialValuep;
        UINFO(5, "DEPGRAPH: use initialValuep for '" << nodeName(nodep) << "'" << endl);
    }

    // Special handling for ATTROF nodes ($bits, $dimensions, etc.)
    // These need to COMPUTE a value based on the operand's type, not just propagate width
    if (nodep->nodeType == NodeType::ATTROF) {
        AstAttrOf* const attrp = VN_CAST(nodep->nodep, AttrOf);
        if (attrp && attrp->attrType() == VAttrType::DIM_BITS) {
            // $bits() returns the width of the operand type as an integer VALUE
            // The resolvedWidth we propagated is the width of the operand type
            // We need to create a CONST node with that value
            int bitsValue = 0;
            for (DepNode* const depp : nodep->dependsOn) {
                if (!depp || !depp->resolved) continue;
                if (depp->resolvedWidth > 0) {
                    bitsValue = depp->resolvedWidth;
                    break;
                }
            }
            if (bitsValue > 0) {
                // Create a constant with the $bits() result
                // Note: We create a new AstConst here - it will be used in finalizeAST
                FileLine* const fl = attrp->fileline();
                AstConst* const constp
                    = new AstConst{fl, AstConst::Unsized32{}, static_cast<uint32_t>(bitsValue)};
                nodep->resolvedValuep = constp;
                nodep->resolvedWidth = 32;  // $bits() returns a 32-bit integer
                UINFO(5, "DEPGRAPH: ATTROF $bits() computed value="
                             << bitsValue << " for '" << nodeName(nodep) << "'" << endl);
            }
        }
    }

    UINFO(9, "DEPGRAPH: reEvaluateNode '" << nodeName(nodep) << "'@" << nodeOwnerName(nodep)
                                          << " resolvedWidth=" << nodep->resolvedWidth
                                          << " resolvedTypep=" << nodep->resolvedTypep
                                          << " resolvedValuep=" << nodep->resolvedValuep << endl);
}

//======================================================================
// Resolution

int V3LinkDotDepGraph::resolve() {
    UINFO(3, "\n");
    UINFO(3, "========== DEPGRAPH PHASE: RESOLVE ==========" << endl);

    // NEW ARCHITECTURE: Single-pass OOO resolution
    // - Ready nodes (pendingDeps=0) are boundary conditions with initial values
    // - Each node executes: read from parents, compute, store in self, wake children
    // - All nodes must resolve before finalizeAST

    s_iterationCount = 0;
    std::deque<DepNode*> ready;

    // Identify boundary conditions - nodes with no unresolved dependencies
    UINFO(3, "DEPGRAPH BOUNDARY CONDITIONS (ready nodes):" << endl);
    for (DepNode* nodep : s_allNodes) {
        if (!nodep || nodep->resolved) continue;
        if (nodep->pendingDeps == 0) {
            ready.push_back(nodep);
            UINFO(3, "  [" << nodeTypeName(nodep->nodeType) << "] " << nodeName(nodep) << "@"
                           << nodeOwnerName(nodep) << " initial={width=" << nodep->initialWidth
                           << (nodep->initialValuep ? " hasValue" : "")
                           << (nodep->initialTypep ? " hasType" : "") << "}" << endl);
        }
    }
    UINFO(3, "Total boundary nodes: " << ready.size() << endl);
    UINFO(3, endl);

    while (!ready.empty()) {
        DepNode* nodep = ready.front();
        ready.pop_front();
        if (!nodep || nodep->resolved) continue;
        if (nodep->pendingDeps > 0) continue;

        // Skip template nodes (empty cellPath with interface owner)
        // Template nodes are just templates - actual work happens on cell-context nodes
        // This prevents crashes when trying to resolve template TYPEDEFs that have no
        // valid dependencies (they depend on template params that are never instantiated)
        if (nodep->cellPath.empty() && nodep->ownerModp && VN_IS(nodep->ownerModp, Iface)) {
            // Mark as resolved but don't actually process - just propagate initial values
            nodep->resolved = true;
            nodep->resolvedIteration = ++s_iterationCount;
            nodep->resolvedWidth = nodep->initialWidth;
            if (nodep->initialValuep) nodep->resolvedValuep = nodep->initialValuep;
            if (nodep->initialTypep) nodep->resolvedTypep = nodep->initialTypep;
            UINFO(3, "\n");
            UINFO(3, "DEPGRAPH SKIP-TEMPLATE[" << s_iterationCount << "]: " << "["
                                               << nodeTypeName(nodep->nodeType) << "] "
                                               << nodeName(nodep) << "@" << nodeOwnerName(nodep)
                                               << " (template interface node)" << endl);
            // Still wake up dependents
            for (DepNode* const depNodep : nodep->dependents) {
                if (!depNodep || depNodep->resolved) continue;
                if (depNodep->pendingDeps > 0) --depNodep->pendingDeps;
                if (depNodep->pendingDeps == 0) ready.push_back(depNodep);
            }
            continue;
        }

        // === EXECUTION TRACE: Before ===
        UINFO(3, "\n");
        UINFO(3, "DEPGRAPH EXEC[" << (s_iterationCount + 1) << "]: " << "["
                                  << nodeTypeName(nodep->nodeType) << "] " << nodeName(nodep)
                                  << "@" << nodeOwnerName(nodep) << endl);

        // Input surfaces: what we read from parent DepNodes
        UINFO(3, "  INPUTS:" << endl);
        UINFO(3, "    initial: width=" << nodep->initialWidth);
        if (nodep->initialValuep) UINFO(3, " valuep=" << nodep->initialValuep);
        if (nodep->initialTypep) UINFO(3, " typep=" << nodep->initialTypep);
        UINFO(3, endl);
        for (DepNode* const depp : nodep->dependsOn) {
            if (!depp) continue;
            UINFO(3, "    <- [" << nodeTypeName(depp->nodeType) << "] " << nodeName(depp) << "@"
                                << nodeOwnerName(depp)
                                << " resolved=" << (depp->resolved ? "Y" : "N")
                                << " width=" << depp->resolvedWidth);
            if (depp->resolvedTypep) UINFO(3, " typep=" << depp->resolvedTypep);
            if (depp->resolvedValuep) UINFO(3, " valuep=" << depp->resolvedValuep);
            UINFO(3, endl);
        }

        reEvaluateNode(nodep);

        // Always mark as resolved - if commit skipped replacement (e.g., width=0),
        // the guards in V3Width/V3Const will handle it later.
        nodep->resolved = true;
        nodep->resolvedIteration = ++s_iterationCount;

        // === EXECUTION TRACE: After ===
        UINFO(3, "  OUTPUTS:" << endl);
        UINFO(3, "    resolved: width=" << nodep->resolvedWidth);
        if (nodep->resolvedTypep) UINFO(3, " typep=" << nodep->resolvedTypep);
        if (nodep->resolvedValuep) UINFO(3, " valuep=" << nodep->resolvedValuep);
        UINFO(3, endl);

        // Wake up dependent nodes (children read from parents during their own execution)
        int wokenCount = 0;
        UINFO(3, "  WAKE:" << endl);
        for (DepNode* const depNodep : nodep->dependents) {
            if (!depNodep || depNodep->resolved) continue;
            if (depNodep->pendingDeps > 0) --depNodep->pendingDeps;
            const bool nowReady = (depNodep->pendingDeps == 0);
            UINFO(3, "    -> [" << nodeTypeName(depNodep->nodeType) << "] " << nodeName(depNodep)
                                << "@" << nodeOwnerName(depNodep) << " pending="
                                << depNodep->pendingDeps << (nowReady ? " READY" : "") << endl);
            if (nowReady) {
                ready.push_back(depNodep);
                ++wokenCount;
            }
        }
        if (nodep->dependents.empty()) { UINFO(3, "    (no dependents)" << endl); }
        UINFO(3, "  SUMMARY: step=" << s_iterationCount << " woken=" << wokenCount
                                    << " queueSize=" << ready.size() << endl);
    }

    UINFO(5, "DEPGRAPH: resolution complete in " << s_iterationCount << " steps" << endl);

    // Check for unresolved nodes
    int unresolvedCount = 0;
    for (DepNode* nodep : s_allNodes) {
        if (!nodep->resolved) {
            ++unresolvedCount;
            UINFO(9, "DEPGRAPH: unresolved node '"
                         << nodeName(nodep) << "'@" << nodeOwnerName(nodep)
                         << " type=" << nodeTypeName(nodep->nodeType) << " nodep="
                         << (nodep->nodep ? cvtToHex(nodep->nodep) : "<nullptr>") << endl);
            for (DepNode* const depp : nodep->dependsOn) {
                if (!depp || depp->resolved) continue;
                UINFO(9, "DEPGRAPH:   pending dep -> '"
                             << nodeName(depp) << "'@" << nodeOwnerName(depp)
                             << " type=" << nodeTypeName(depp->nodeType) << " nodep="
                             << (depp->nodep ? cvtToHex(depp->nodep) : "<nullptr>") << endl);
            }
        }
    }
    if (unresolvedCount > 0) {
        UINFO(1, "DEPGRAPH: WARNING: "
                     << unresolvedCount
                     << " unresolved nodes after resolution (possible dependency cycle)" << endl);
        for (DepNode* nodep : s_allNodes) {
            if (!nodep || nodep->resolved) continue;
            UINFO(1, "DEPGRAPH:   UNRESOLVED: [" << nodeTypeName(nodep->nodeType) << "] "
                                                 << nodeName(nodep) << "@" << nodeOwnerName(nodep)
                                                 << " cellPath='" << nodep->cellPath << "'"
                                                 << " pendingDeps=" << nodep->pendingDeps << endl);
        }
    }

    if (debug() >= 5) {
        UINFO(5, "DEPGRAPH: ========== REFDTYPE RESOLUTION SUMMARY ==========" << endl);
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
            UINFO(5, "DEPGRAPH: RESOLVED REFDTYPE "
                         << nodeName(nodep) << "@" << nodeOwnerName(nodep) << " -> "
                         << (target.empty() ? "<unlinked>" : target) << endl);
            if (rdp->typedefp() && rdp->refDTypep()) {
                AstTypedef* const curTdp = rdp->typedefp();
                AstNodeDType* const curRefp = rdp->refDTypep();
                AstNodeModule* const tOwnerp = curTdp ? findOwnerModule(curTdp) : nullptr;
                AstNodeModule* const rOwnerp = curRefp ? findOwnerModule(curRefp) : nullptr;
                UINFO(5, "DEPGRAPH: WARNING refdtype has both typedefp and refDTypep set: "
                             << nodeName(nodep) << "@" << nodeOwnerName(nodep) << " typedef='"
                             << (curTdp ? curTdp->name() : "<null>") << "' typedefp=" << curTdp
                             << "' typedefBackp=" << (curTdp ? curTdp->backp() : nullptr)
                             << "' typedefOwner='" << (tOwnerp ? tOwnerp->name() : "<null>")
                             << "' refDType='" << (curRefp ? curRefp->prettyTypeName() : "<null>")
                             << "' refDTypep=" << curRefp
                             << "' refBackp=" << (curRefp ? curRefp->backp() : nullptr)
                             << "' refOwner='" << (rOwnerp ? rOwnerp->name() : "<null>")
                             << "' dtypep=" << rdp->dtypep() << endl);
            }
        }
        UINFO(5, "DEPGRAPH: ========== END REFDTYPE SUMMARY ==========" << endl);
    }

    // Dump the dependents tree after execution to verify resolved values
    dumpGraphDependentsTree("after-resolve");

    return s_iterationCount;
}

//======================================================================
// Finalize AST - apply all deferred mutations in a single pass

static void finalizeParamType(V3LinkDotDepGraph::DepNode* nodep) {
    AstParamTypeDType* const ptdp = VN_CAST(nodep->nodep, ParamTypeDType);
    if (!ptdp) return;

    UINFO(5, "DEPGRAPH: finalizeParamType '" << ptdp->name()
                                             << "' resolvedWidth=" << nodep->resolvedWidth
                                             << " resolvedTypep=" << nodep->resolvedTypep << endl);

    // Option B (Moderate): Do NOT replace dtypep with our built type.
    // We only force widths here. V3Param will rebuild the types from
    // the parameter constants we've already set.
    // The resolvedTypep is kept in DepNode for internal use (e.g., propagating
    // widths to downstream nodes) but not inserted into the AST.

    // Apply resolved width from DepNode - only if different
    if (nodep->resolvedWidth > 0 && ptdp->width() != nodep->resolvedWidth) {
        UINFO(5, "DEPGRAPH: finalizeParamType '" << ptdp->name() << "' width " << ptdp->width()
                                                 << " -> " << nodep->resolvedWidth << endl);
        ptdp->widthForce(nodep->resolvedWidth, nodep->resolvedWidth);
    }
}

static void finalizeRefDType(V3LinkDotDepGraph::DepNode* nodep) {
    AstRefDType* const rdp = VN_CAST(nodep->nodep, RefDType);
    if (!rdp) return;

    UINFO(5, "DEPGRAPH: finalizeRefDType '" << rdp->name()
                                            << "' resolvedWidth=" << nodep->resolvedWidth
                                            << " (clonedTypep not inserted into AST)" << endl);

    // Option B (Moderate): Do NOT replace refDTypep/typedefp with our built type.
    // We only force widths here. V3Param will rebuild the types from
    // the parameter constants we've already set.
    // The resolvedTypep is kept in DepNode for internal use (e.g., propagating
    // widths to downstream nodes) but not inserted into the AST.

    // Apply resolved owner module from DepNode
    if (nodep->resolvedOwnerModp && rdp->classOrPackagep() != nodep->resolvedOwnerModp) {
        rdp->classOrPackagep(nodep->resolvedOwnerModp);
    }

    // Apply resolved width from DepNode - only if different
    if (nodep->resolvedWidth > 0 && rdp->width() != nodep->resolvedWidth) {
        UINFO(5, "DEPGRAPH: finalizeRefDType '" << rdp->name() << "' width " << rdp->width()
                                                << " -> " << nodep->resolvedWidth << endl);
        rdp->widthForce(nodep->resolvedWidth, nodep->resolvedWidth);
    }
}

static void finalizeTypedef(V3LinkDotDepGraph::DepNode* nodep) {
    AstTypedef* const tdp = VN_CAST(nodep->nodep, Typedef);
    if (!tdp) return;

    UINFO(5, "DEPGRAPH: finalizeTypedef '" << tdp->name()
                                           << "' resolvedWidth=" << nodep->resolvedWidth
                                           << " (clonedTypep not inserted into AST)" << endl);

    // Option 2 (Moderate): Do NOT replace dtypep with our built type.
    // We only force widths here. V3Param will rebuild the types from
    // the parameter constants we've already set.
    // The resolvedTypep is kept in DepNode for internal use (e.g., propagating
    // widths to downstream nodes) but not inserted into the AST.

    // Apply resolved width from DepNode - only if different and dtypep exists
    if (nodep->resolvedWidth > 0 && tdp->dtypep() && tdp->width() != nodep->resolvedWidth) {
        UINFO(5, "DEPGRAPH: finalizeTypedef '" << tdp->name() << "' width " << tdp->width()
                                               << " -> " << nodep->resolvedWidth << endl);
        tdp->dtypep()->widthForce(nodep->resolvedWidth, nodep->resolvedWidth);
    }
}

static void finalizeParam(V3LinkDotDepGraph::DepNode* nodep) {
    AstVar* const varp = VN_CAST(nodep->nodep, Var);
    if (!varp) return;

    UINFO(5, "DEPGRAPH: finalizeParam '" << varp->name()
                                         << "' resolvedWidth=" << nodep->resolvedWidth
                                         << " resolvedValuep=" << nodep->resolvedValuep << endl);

    // Apply resolved value from DepNode - should already be a constant
    if (nodep->resolvedValuep) {
        AstConst* const resolvedConstp = VN_CAST(nodep->resolvedValuep, Const);
        AstConst* const astConstp = varp->valuep() ? VN_CAST(varp->valuep(), Const) : nullptr;

        // Only update if AST doesn't already have the correct constant value
        bool needsUpdate = false;
        if (!astConstp) {
            // AST has no constant value (or non-const expression)
            needsUpdate = true;
        } else if (resolvedConstp && !astConstp->num().isCaseEq(resolvedConstp->num())) {
            // AST has a different constant value
            needsUpdate = true;
        }

        if (needsUpdate) {
            UINFO(5, "DEPGRAPH: finalizeParam '" << varp->name() << "' updating value" << endl);
            if (varp->valuep()) { varp->valuep()->unlinkFrBack()->deleteTree(); }
            varp->valuep(nodep->resolvedValuep->cloneTree(false));
            // NOTE: Do NOT modify varp->dtypep() here - that sets childDTypep
            // which violates V3Broken invariants. The dtype is managed by V3Width.
        }
    }
    // NOTE: Do NOT modify varp->dtypep()->widthForce() here - V3Width handles this
}

//======================================================================
// Public query APIs

bool V3LinkDotDepGraph::isParameterized(const AstNodeModule* modp) {
    if (!s_enabled || !modp) return false;
    const bool result = s_parameterizedModules.count(const_cast<AstNodeModule*>(modp)) > 0;
    UINFO(9, "DEPGRAPH: isParameterized mod='" << modp->name() << "' someInstanceName='"
                                               << modp->someInstanceName() << "' -> "
                                               << (result ? "true" : "false") << endl);
    return result;
}

const V3LinkDotDepGraph::DepNode* V3LinkDotDepGraph::lookupResolved(const std::string& name,
                                                                    AstNodeModule* ownerModp,
                                                                    NodeType nodeType,
                                                                    const std::string& cellPath) {
    if (!s_enabled) return nullptr;
    DepNode* const dnp = findByNameAndOwner(name, ownerModp, nodeType, cellPath);
    if (!dnp || !dnp->resolved) return nullptr;
    return dnp;
}

// NOTE: We intentionally do NOT replace AstAttrOf nodes in finalizeAST.
// The AstAttrOf's fromp() child (AstRefDType) may be referenced by the
// IfaceCapture ledger.  Deleting the tree would leave dangling pointers.
// Instead, V3Width calls getResolvedAttrOf() to get the pre-computed value.

AstConst* V3LinkDotDepGraph::getResolvedAttrOf(const AstAttrOf* nodep) {
    if (!s_enabled || !nodep) return nullptr;
    // Search all DepNodes for an ATTROF node matching this AstAttrOf pointer.
    // ATTROF nodes have unique AstAttrOf* pointers (one per $bits() expression).
    for (const DepNode* dnp : s_allNodes) {
        if (!dnp) continue;
        if (dnp->nodeType != NodeType::ATTROF) continue;
        if (dnp->nodep != nodep) continue;
        if (!dnp->resolved) return nullptr;
        return VN_CAST(dnp->resolvedValuep, Const);
    }
    return nullptr;
}

void V3LinkDotDepGraph::finalizeAST() {
    if (!s_enabled) return;

    UINFO(3, "\n");
    UINFO(3, "========== DEPGRAPH finalizeAST ==========" << endl);

    int resolvedCount = 0;
    int unresolvedCount = 0;
    int paramTypeCount = 0;
    int refDTypeCount = 0;
    int typedefCount = 0;
    int paramCount = 0;

    // Single pass: apply resolved state to AST by node type
    for (DepNode* nodep : s_allNodes) {
        if (!nodep) continue;
        if (!nodep->resolved) {
            ++unresolvedCount;
            UINFO(5, "DEPGRAPH: finalizeAST UNRESOLVED: ["
                         << nodeTypeName(nodep->nodeType) << "] " << nodeName(nodep) << "@"
                         << nodeOwnerName(nodep) << " cellPath='" << nodep->cellPath << "'"
                         << " pendingDeps=" << nodep->pendingDeps << endl);
            continue;
        }
        ++resolvedCount;

        switch (nodep->nodeType) {
        case NodeType::PARAMTYPEDTYPE:
            // Only finalize template-level (empty cellPath).
            // Cell-context instances have different resolved widths for the same
            // template AST node - writing all of them lets the last writer win,
            // corrupting the template that V3Param clones from.
            // V3Width re-evaluates typedef widths on each clone using the clone's
            // correctly-set GPARAM values.
            if (nodep->cellPath.empty()) {
                finalizeParamType(nodep);
                ++paramTypeCount;
            }
            break;
        case NodeType::REFDTYPE:
            if (nodep->cellPath.empty()) {
                finalizeRefDType(nodep);
                ++refDTypeCount;
            }
            break;
        case NodeType::TYPEDEF:
            if (nodep->cellPath.empty()) {
                finalizeTypedef(nodep);
                ++typedefCount;
            }
            break;
        case NodeType::GPARAM:
            // Only finalize template-level GPARAMs (empty cellPath).
            // Cell-context GPARAMs carry override values that must NOT be written
            // to the template AST - V3Param compares pin overrides against the
            // template's default to decide whether cloning is needed.
            if (nodep->cellPath.empty()) {
                finalizeParam(nodep);
                ++paramCount;
            }
            break;
        case NodeType::LPARAM:
            // LPARAMs with cell-context must be applied per-clone by V3Param
            // Only finalize template LPARAMs (empty cellPath) here
            if (nodep->cellPath.empty()) {
                finalizeParam(nodep);
                ++paramCount;
            }
            break;
        case NodeType::STRUCTDTYPE:
        case NodeType::UNIONDTYPE:
            // Struct/union widths - don't modify AST here, V3Width handles this
            break;
        case NodeType::ATTROF:
            // ATTROF ($bits) - do NOT replace here; the fromp child may be
            // referenced by the IfaceCapture ledger.  The resolved value is
            // available via getResolvedAttrOf() for V3Width to query.
            break;
        case NodeType::FUNC:
            // FUNC nodes - no AST finalization needed
            break;
        }
    }

    UINFO(3, "DEPGRAPH: finalizeAST complete - resolved="
                 << resolvedCount << " unresolved=" << unresolvedCount
                 << " PARAMTYPE=" << paramTypeCount << " REFDTYPE=" << refDTypeCount
                 << " TYPEDEF=" << typedefCount << " PARAM=" << paramCount << endl);

    // Clean up cloned types before V3Param runs to avoid polluting type table
    cleanupClonedTypes();
}

//======================================================================
// Cleanup cloned types - removes from type table and deletes

void V3LinkDotDepGraph::cleanupClonedTypes() {
    if (!s_enabled) return;

    // Clear resolvedTypep pointers in all DepNodes first
    // These are just references - the pool owns the actual types
    for (DepNode* nodep : s_allNodes) {
        if (nodep) nodep->resolvedTypep = nullptr;
    }

    // Delete cloned types from the centralized pool
    // This pool owns all cloned types created during DepGraph execution.
    // Multiple DepNodes may have shared the same resolvedTypep via propagation,
    // but each type is only in the pool once, so we delete exactly once.
    int deletedCount = 0;
    for (AstNodeDType* typep : s_clonedTypes) {
        if (!typep) continue;
        // Only delete if not attached to AST (cloned nodes have no backp)
        if (!typep->backp()) {
            VL_DO_DANGLING(typep->deleteTree(), typep);
            ++deletedCount;
        }
    }
    s_clonedTypes.clear();

    UINFO(3, "DEPGRAPH: cleaned up " << deletedCount << " cloned type nodes from pool" << endl);
}

//======================================================================
// Apply resolved values to cloned module (called by V3Param after cloning)

void V3LinkDotDepGraph::applyResolvedToClone(AstNodeModule* srcModp, AstNodeModule* newModp,
                                             const std::string& cellPath) {
    if (!s_enabled) return;
    UASSERT(srcModp, "applyResolvedToClone called with null srcModp");
    UASSERT(newModp, "applyResolvedToClone called with null newModp");
    if (cellPath.empty()) return;

    UINFO(5, "DEPGRAPH: applyResolvedToClone srcMod=" << srcModp->name()
                                                      << " newMod=" << newModp->name()
                                                      << " cellPath=" << cellPath << endl);

    // Build a map from var name to cloned var in newModp
    std::unordered_map<std::string, AstVar*> clonedVarsByName;
    for (AstNode* stmtp = newModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
        if (AstVar* const varp = VN_CAST(stmtp, Var)) { clonedVarsByName[varp->name()] = varp; }
    }

    // Determine which cellPath to use for matching DepNodes.
    // V3Param may pass a cellPath that doesn't match DepGraph's cellPath
    // (e.g., for nested interface instances where someInstanceName() is stale).
    // In that case, fall back to matching by GPARAM values on the cloned module.
    // This is safe because identical GPARAMs produce identical LPARAMs, and
    // V3Param deduplicates clones with identical parameters.
    std::string matchCellPath = cellPath;

    // Check if any resolved DepNode exists with exact cellPath match for this srcModp
    bool hasExactMatch = false;
    for (DepNode* dnp : s_allNodes) {
        if (!dnp || !dnp->resolved) continue;
        if (dnp->ownerModp != srcModp) continue;
        if (dnp->cellPath == cellPath) {
            hasExactMatch = true;
            break;
        }
    }
    if (!hasExactMatch) {
        UINFO(5,
              "DEPGRAPH: applyResolvedToClone no exact cellPath match, trying fallbacks" << endl);

        // Collect GPARAM values from the cloned module (already set by V3Param pin assignment)
        std::unordered_map<std::string, AstNode*> cloneGParamValues;
        for (AstNode* stmtp = newModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                if (varp->isGParam() && varp->valuep()) {
                    cloneGParamValues[varp->name()] = varp->valuep();
                    UINFO(5, "DEPGRAPH:   clone GPARAM '" << varp->name() << "' type="
                                                          << varp->valuep()->typeName() << endl);
                }
            }
        }

        // Collect all distinct cellPaths for this srcModp that have resolved GPARAM nodes
        std::set<std::string> candidatePaths;
        for (DepNode* dnp : s_allNodes) {
            if (!dnp || !dnp->resolved) continue;
            if (dnp->ownerModp != srcModp) continue;
            if (dnp->nodeType == NodeType::GPARAM && !dnp->cellPath.empty()) {
                candidatePaths.insert(dnp->cellPath);
            }
        }

        UINFO(5, "DEPGRAPH:   candidate cellPaths: " << candidatePaths.size() << endl);
        for (const auto& cp : candidatePaths) {
            UINFO(5, "DEPGRAPH:     candidate: '" << cp << "'" << endl);
        }

        // Try to match by GPARAM values first (using sameTree - works when both
        // sides are the same AST node type, e.g., both CONST)
        bool foundByGParam = false;
        for (const auto& candPath : candidatePaths) {
            bool allMatch = true;
            bool anyChecked = false;
            for (DepNode* dnp : s_allNodes) {
                if (!dnp || !dnp->resolved) continue;
                if (dnp->ownerModp != srcModp) continue;
                if (dnp->cellPath != candPath) continue;
                if (dnp->nodeType != NodeType::GPARAM) continue;

                AstVar* const gvarp = VN_CAST(dnp->nodep, Var);
                if (!gvarp || !dnp->resolvedValuep) continue;

                const auto it = cloneGParamValues.find(gvarp->name());
                if (it == cloneGParamValues.end()) {
                    allMatch = false;
                    break;
                }

                if (!it->second->sameTree(dnp->resolvedValuep)) {
                    allMatch = false;
                    break;
                }
                anyChecked = true;
            }
            if (allMatch && anyChecked) {
                UINFO(5, "DEPGRAPH: applyResolvedToClone cellPath fallback (GPARAM match): '"
                             << cellPath << "' -> '" << candPath << "'" << endl);
                matchCellPath = candPath;
                foundByGParam = true;
                break;
            }
        }

        // If GPARAM value comparison failed (e.g., CONST vs PATTERN type mismatch),
        // try rewriting V3Param's cellPath using s_cellAssociations.
        //
        // V3Param builds paths through module cells: t.u_subA.sub_types
        //   (t -> u_subA cell -> skips interface port 'io' -> sub_types cell)
        // DepGraph builds paths through interface cells: t.subA_io.sub_types
        //   (t -> subA_io interface cell -> sub_types cell)
        //
        // s_cellAssociations maps: "t.u_subA.io" -> "t.subA_io"
        //
        // Algorithm: split V3Param's path at each dot from the right.
        // For each prefix, check if any s_cellAssociations key starts with
        // that prefix + "." (meaning the module at that prefix has an interface
        // port). If found, the association value gives the interface cell path.
        // Append the suffix to get the DepGraph-style path.
        if (!foundByGParam && !candidatePaths.empty()) {
            std::string rewrittenPath;
            bool foundRewrite = false;

            // Split cellPath into prefix and suffix at each dot from the right
            // e.g., "t.u_subA.sub_types" -> prefix="t.u_subA", suffix="sub_types"
            size_t splitPos = cellPath.rfind('.');
            while (splitPos != std::string::npos && !foundRewrite) {
                const std::string prefix = cellPath.substr(0, splitPos);
                const std::string suffix = cellPath.substr(splitPos + 1);
                const std::string prefixDot = prefix + ".";

                // Find any s_cellAssociations key that starts with this prefix + "."
                // e.g., key="t.u_subA.io" starts with "t.u_subA."
                for (const auto& assoc : s_cellAssociations) {
                    const std::string& portPath = assoc.first;  // e.g., "t.u_subA.io"
                    const std::string& ifacePath = assoc.second;  // e.g., "t.subA_io"

                    if (portPath.size() > prefixDot.size()
                        && portPath.compare(0, prefixDot.size(), prefixDot) == 0) {
                        // Found: portPath starts with prefix + "."
                        // Rewrite: ifacePath + "." + suffix
                        rewrittenPath = ifacePath + "." + suffix;
                        UINFO(5, "DEPGRAPH:   trying rewrite via assoc: prefix='"
                                     << prefix << "' portPath='" << portPath << "' -> '"
                                     << ifacePath << "' + '." << suffix << "' = '" << rewrittenPath
                                     << "'" << endl);
                        if (candidatePaths.count(rewrittenPath)) {
                            foundRewrite = true;
                            break;
                        }
                    }
                }

                // Try next split point (further left)
                if (splitPos > 0) {
                    splitPos = cellPath.rfind('.', splitPos - 1);
                } else {
                    break;
                }
            }

            if (foundRewrite) {
                UINFO(5, "DEPGRAPH: applyResolvedToClone cellPath fallback "
                         "(cellAssoc rewrite): '"
                             << cellPath << "' -> '" << rewrittenPath << "'" << endl);
                matchCellPath = rewrittenPath;
            } else {
                UASSERT_OBJ(false, srcModp,
                            "applyResolvedToClone: no cellPath match found for '"
                                << cellPath << "' srcMod=" << srcModp->name()
                                << " candidates=" << candidatePaths.size());
            }
        }
    }

    // Apply resolved LPARAM values in two passes:
    // 1. Instance-specific (matching cellPath) - these take priority
    // 2. Template-level (empty cellPath) - only for LPARAMs not already set
    std::set<std::string> appliedNames;  // Track which LPARAMs were set by instance match
    int appliedCount = 0;

    // Pass 1: Instance-specific matches
    for (DepNode* nodep : s_allNodes) {
        if (!nodep || !nodep->resolved) continue;
        if (nodep->ownerModp != srcModp) continue;
        if (nodep->cellPath != matchCellPath) continue;
        if (nodep->nodeType != NodeType::LPARAM) continue;

        AstVar* const srcVarp = VN_CAST(nodep->nodep, Var);
        UASSERT(srcVarp, "LPARAM DepNode has non-Var nodep");
        if (!nodep->resolvedValuep) continue;

        // Only apply fully constant values. Non-constant resolved values
        // (e.g., unprocessed PATTERNs) may contain broken references.
        // ConsPackUOrStruct is what V3Width produces from a PATTERN and is
        // fully constant, so accept it alongside Const.
        if (!VN_IS(nodep->resolvedValuep, Const)
            && !VN_IS(nodep->resolvedValuep, ConsPackUOrStruct)) {
            UINFO(5, "DEPGRAPH: applyResolvedToClone LPARAM '"
                         << srcVarp->name() << "' (instance) SKIPPED non-const type="
                         << nodep->resolvedValuep->typeName() << endl);
            continue;
        }

        const auto it = clonedVarsByName.find(srcVarp->name());
        UASSERT_OBJ(it != clonedVarsByName.end(), srcVarp,
                    "LPARAM '" << srcVarp->name() << "' not found in cloned module "
                               << newModp->name());
        AstVar* const clonedVarp = it->second;

        UINFO(5, "DEPGRAPH: applyResolvedToClone LPARAM '"
                     << srcVarp->name() << "' (instance) val=" << nodep->resolvedValuep << endl);
        if (clonedVarp->valuep()) clonedVarp->valuep()->unlinkFrBack()->deleteTree();
        clonedVarp->valuep(nodep->resolvedValuep->cloneTree(false));
        appliedNames.insert(srcVarp->name());
        ++appliedCount;
    }

    // Pass 2: Template-level (empty cellPath) - only for LPARAMs not already set
    for (DepNode* nodep : s_allNodes) {
        if (!nodep || !nodep->resolved) continue;
        if (nodep->ownerModp != srcModp) continue;
        if (!nodep->cellPath.empty()) continue;  // Only template-level
        if (nodep->nodeType != NodeType::LPARAM) continue;

        AstVar* const srcVarp = VN_CAST(nodep->nodep, Var);
        UASSERT(srcVarp, "LPARAM DepNode has non-Var nodep");
        if (!nodep->resolvedValuep) continue;
        if (appliedNames.count(srcVarp->name())) continue;  // Already set by instance match

        // Only apply fully constant values (same reason as pass 1)
        if (!VN_IS(nodep->resolvedValuep, Const)
            && !VN_IS(nodep->resolvedValuep, ConsPackUOrStruct)) {
            UINFO(5, "DEPGRAPH: applyResolvedToClone LPARAM '"
                         << srcVarp->name() << "' (template) SKIPPED non-const type="
                         << nodep->resolvedValuep->typeName() << endl);
            continue;
        }

        const auto it = clonedVarsByName.find(srcVarp->name());
        UASSERT_OBJ(it != clonedVarsByName.end(), srcVarp,
                    "LPARAM '" << srcVarp->name() << "' not found in cloned module "
                               << newModp->name());
        AstVar* const clonedVarp = it->second;

        UINFO(5, "DEPGRAPH: applyResolvedToClone LPARAM '"
                     << srcVarp->name() << "' (template) val=" << nodep->resolvedValuep << endl);
        if (clonedVarp->valuep()) clonedVarp->valuep()->unlinkFrBack()->deleteTree();
        clonedVarp->valuep(nodep->resolvedValuep->cloneTree(false));
        ++appliedCount;
    }

    UINFO(5,
          "DEPGRAPH: applyResolvedToClone applied " << appliedCount << " LPARAM values" << endl);

    // Pass 3: Fold parameter expressions inside the clone's typedef subtrees.
    // After Pass 1/2 set GPARAM/LPARAM values on the clone, expressions like
    // cfg.DDNumStuffThreads-1 inside RANGE nodes can be folded to constants.
    // Without this, V3Width's widthParamsEdit moves PACKARRAYDTYPEs to the
    // type table with unresolved RANGE expressions (e.g., [-1:0] instead of
    // [7:0]), causing spurious ASCRANGE warnings.
    //
    // We substitute parameter values into the clone's typedef subtrees using
    // ParamSubstVisitor (same mechanism as DepGraph resolution), then fold
    // with V3Const.  This uses only the clone's own parameter values - we
    // NEVER clone or copy nodes from the DepGraph shadow AST.
    int typedefApplied = 0;

    // Build a ParamSubstVisitor with the clone's resolved GPARAM values
    ParamSubstVisitor substVisitor;
    for (AstNode* stmtp = newModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
        if (AstVar* const varp = VN_CAST(stmtp, Var)) {
            if (varp->isGParam() && varp->valuep()) {
                substVisitor.addParam(varp->name(), varp->valuep());
                UINFO(5, "DEPGRAPH: applyResolvedToClone Pass 3 param '"
                             << varp->name() << "' = " << varp->valuep()->typeName() << endl);
            }
        }
    }

    // Walk each typedef in the clone and substitute+fold parameter expressions
    for (AstNode* stmtp = newModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
        AstTypedef* const tdp = VN_CAST(stmtp, Typedef);
        if (!tdp || !tdp->childDTypep()) continue;

        // Check if this typedef has any RANGE nodes with parameter references
        bool hasRanges = false;
        tdp->childDTypep()->foreach([&](AstRange*) { hasRanges = true; });
        if (!hasRanges) continue;

        UINFO(9, "DEPGRAPH: applyResolvedToClone TYPEDEF '" << tdp->name()
                                                            << "' pre-fold ranges:" << endl);
        tdp->childDTypep()->foreach([&](AstRange* rangep) {
            UINFO(9, "DEPGRAPH:   RANGE <"
                         << AstNode::nodeAddr(rangep)
                         << "> back=" << (rangep->backp() ? rangep->backp()->typeName() : "<null>")
                         << " left=" << (rangep->leftp() ? rangep->leftp()->typeName() : "<null>")
                         << " right="
                         << (rangep->rightp() ? rangep->rightp()->typeName() : "<null>") << endl);
        });

        // Substitute parameter values in the typedef's dtype subtree
        substVisitor.substitute(tdp->childDTypep());

        // Fold the substituted expressions to constants
        tdp->childDTypep()->foreach([](AstRange* rangep) {
            if (rangep->leftp()) { V3Const::constifyParamsEdit(rangep->leftp()); }
            if (rangep->rightp()) { V3Const::constifyParamsEdit(rangep->rightp()); }
        });

        UINFO(9, "DEPGRAPH: applyResolvedToClone TYPEDEF '" << tdp->name()
                                                            << "' post-fold ranges:" << endl);
        tdp->childDTypep()->foreach([&](AstRange* rangep) {
            UINFO(9,
                  "DEPGRAPH:   RANGE <"
                      << AstNode::nodeAddr(rangep)
                      << "> back=" << (rangep->backp() ? rangep->backp()->typeName() : "<null>")
                      << " left=" << (rangep->leftp() ? rangep->leftp()->typeName() : "<null>")
                      << " right=" << (rangep->rightp() ? rangep->rightp()->typeName() : "<null>")
                      << " leftNode="
                      << (rangep->leftp() ? AstNode::nodeAddr(rangep->leftp()) : "<null>")
                      << " rightNode="
                      << (rangep->rightp() ? AstNode::nodeAddr(rangep->rightp()) : "<null>")
                      << endl);
        });

        ++typedefApplied;
        UINFO(5, "DEPGRAPH: applyResolvedToClone TYPEDEF '"
                     << tdp->name() << "' parameter expressions folded" << endl);
    }
    UINFO(5,
          "DEPGRAPH: applyResolvedToClone applied " << typedefApplied << " TYPEDEF fixes" << endl);
}

//======================================================================
// Debugging

void V3LinkDotDepGraph::dumpGraph() {
    UINFO(5, "DEPGRAPH: ========== DEPENDENCY GRAPH DUMP ==========" << endl);
    UINFO(5, "DEPGRAPH: Total nodes: " << s_allNodes.size() << "  Iterations: " << s_iterationCount
                                       << endl);

    // Group nodes by owner module for clearer output
    std::map<string, std::vector<const DepNode*>> byOwner;
    for (const DepNode* nodep : s_allNodes) { byOwner[nodeOwnerName(nodep)].push_back(nodep); }

    for (const auto& kv : byOwner) {
        UINFO(5, "DEPGRAPH: --- Module: " << kv.first << " ---" << endl);
        for (const DepNode* nodep : kv.second) { dumpNode(nodep); }
    }

    UINFO(5, "DEPGRAPH: ========== END GRAPH DUMP ==========" << endl);
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

    const string addrStr = nodep->nodep ? (" <" + AstNode::nodeAddr(nodep->nodep) + ">") : "";
    UINFO(5, "DEPGRAPH:   " << nodeTypeName(nodep->nodeType) << " '" << nodeName(nodep) << "'"
                            << addrStr << " resolved=" << (nodep->resolved ? "Y" : "N") << " iter="
                            << nodep->resolvedIteration << extra << (nodep->resolved ? " [R]" : "")
                            << " pendingDeps=" << nodep->dependsOn.size() << endl);
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

    const auto formatParamTypeResolution
        = [](const AstParamTypeDType* ptdp, const DepNode* dnp) -> string {
        if (!ptdp || !dnp || !dnp->resolved) return "";
        AstNodeDType* const dtypep = ptdp->dtypep();
        if (!dtypep) return "";
        string widthStr;
        if (dnp->resolvedWidth > 0)
            widthStr = " [w" + std::to_string(dnp->resolvedWidth) + "]";
        else if (dtypep->width() > 0)
            widthStr = " [w" + std::to_string(dtypep->width()) + "]";
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
            if (!targetName.empty())
                cellStr = " via " + targetName + " (" + cellName + ")";
            else
                cellStr = " via " + cellName;
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

    const string connector = isLast ? "+-- " : "|-- ";
    const string extension = isLast ? "    " : "|   ";

    // Print module header
    string modType = "MODULE";
    if (VN_IS(modp, Iface))
        modType = "IFACE";
    else if (VN_IS(modp, Class))
        modType = "CLASS";
    else if (VN_IS(modp, Package))
        modType = "PACKAGE";

    UINFO(5, "DEPGRAPH: " << prefix << connector << modp->name() << " : " << modType << endl);

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
                items.push_back({"", "GPARAM " + varp->name() + " <" + AstNode::nodeAddr(varp)
                                         + ">" + valStr + resolved});
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
                items.push_back({"", "LPARAM " + varp->name() + " <" + AstNode::nodeAddr(varp)
                                         + ">" + valStr + resolved});
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
            items.push_back({"", "TYPEDEF " + tdp->name() + " <" + AstNode::nodeAddr(tdp) + ">"
                                     + widthStr + resolved});
        } else if (AstParamTypeDType* const ptdp = VN_CAST(stmtp, ParamTypeDType)) {
            const DepNode* const dnp = find(ptdp);
            string resolved = dnp ? (dnp->resolved ? " [resolved]" : " [pending]") : "";
            string targetStr = formatParamTypeResolution(ptdp, dnp);
            items.push_back({"", "PARAMTYPE " + ptdp->name() + " <" + AstNode::nodeAddr(ptdp) + ">"
                                     + resolved + targetStr});
        }
    }

    // Include module-level REFDTYPE nodes to surface instance context in tree
    for (DepNode* const dnp : s_allNodes) {
        if (!dnp || dnp->nodeType != NodeType::REFDTYPE) continue;
        if (dnp->ownerModp != modp) continue;
        string suffix = formatRefDTypeResolution(dnp);
        const string rdAddr = dnp->nodep ? (" <" + AstNode::nodeAddr(dnp->nodep) + ">") : "";
        items.push_back({"", "REFDTYPE " + nodeName(dnp) + rdAddr + suffix});
    }

    // Print items
    for (size_t i = 0; i < items.size(); ++i) {
        bool itemIsLast = (i == items.size() - 1);
        // Check if there are child cells after this
        bool hasChildCells = false;
        for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (VN_IS(stmtp, Cell)) {
                hasChildCells = true;
                break;
            }
        }
        if (hasChildCells) itemIsLast = false;

        const string itemConnector = itemIsLast ? "+-- " : "|-- ";
        UINFO(5, "DEPGRAPH: " << childPrefix << itemConnector << items[i].second << endl);
    }

    // Collect and print child cells
    std::vector<AstCell*> cells;
    for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
        if (AstCell* const cellp = VN_CAST(stmtp, Cell)) { cells.push_back(cellp); }
    }

    for (size_t i = 0; i < cells.size(); ++i) {
        AstCell* const cellp = cells[i];
        bool cellIsLast = (i == cells.size() - 1);
        const string cellConnector = cellIsLast ? "+-- " : "|-- ";
        const string cellExtension = cellIsLast ? "    " : "|   ";

        AstNodeModule* const childModp = cellp->modp();
        string childModName = childModp ? childModp->name() : "<unlinked>";

        UINFO(5, "DEPGRAPH: " << childPrefix << cellConnector << cellp->name() << " : "
                              << childModName << endl);

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
                    if (VN_IS(cstmtp, Cell)) {
                        hasNestedCells = true;
                        break;
                    }
                }
                if (hasNestedCells) jIsLast = false;
                const string jConnector = jIsLast ? "+-- " : "|-- ";
                UINFO(5, "DEPGRAPH: " << grandchildPrefix << jConnector << childItems[j] << endl);
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
    UINFO(5, "DEPGRAPH: ========== HIERARCHY TREE ==========" << endl);
    UINFO(5, "DEPGRAPH: Total nodes: " << s_allNodes.size() << "  Iterations: " << s_iterationCount
                                       << endl);

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
        UINFO(5, "DEPGRAPH: " << topp->name() << " (top)" << endl);
        // Print top module contents
        std::vector<AstCell*> topCells;
        for (AstNode* stmtp = topp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstCell* const cellp = VN_CAST(stmtp, Cell)) { topCells.push_back(cellp); }
        }
        for (size_t i = 0; i < topCells.size(); ++i) {
            bool isLast = (i == topCells.size() - 1);
            dumpModuleTree(topCells[i]->modp(), "", isLast);
        }
    } else {
        UINFO(5, "DEPGRAPH: <no top module found>" << endl);
    }

    UINFO(5, "DEPGRAPH: ========== END TREE ==========" << endl);
}
