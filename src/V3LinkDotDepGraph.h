// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Dependency graph for parameter/localparam/typedef resolution.
//   Builds a dependency graph after V3Param to correctly resolve
//   interface typedefs that depend on localparams which depend on
//   parameters across module boundaries.
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

#ifndef VERILATOR_V3LINKDOTDEPGRAPH_H_
#define VERILATOR_V3LINKDOTDEPGRAPH_H_

#include "config_build.h"

#include "V3Ast.h"

#include <cstddef>
#include <functional>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

class V3LinkDotDepGraph final {
public:
    // Node types in the dependency graph
    enum class NodeType {
        GPARAM,         // Parameter (AstVar with isGParam)
        LPARAM,         // Localparam (AstVar with isLParam)
        TYPEDEF,        // Typedef (AstTypedef)
        PARAMTYPEDTYPE, // Type parameter (AstParamTypeDType)
        REFDTYPE,       // Reference to a type (AstRefDType)
        STRUCTDTYPE,    // Struct type (AstStructDType)
        UNIONDTYPE,     // Union type (AstUnionDType)
        ATTROF,         // Attribute expression like $bits() (AstAttrOf)
        FUNC            // Function/Task (AstNodeFTask)
    };

    // A node in the dependency graph
    struct DepNode final {
        AstNode* nodep = nullptr;            // The AST node
        NodeType nodeType = NodeType::GPARAM;
        AstNodeModule* ownerModp = nullptr;  // Specialized module/interface owning this
        AstCell* cellp = nullptr;            // Cell instantiation (for cross-module edges)
        std::string cellName;                // Cell name for typedef lookup (survives cloning)
        AstNode* origExprp = nullptr;         // Original expression (pre-constify) for params

        std::set<DepNode*> dependsOn;        // Nodes this depends on
        std::set<DepNode*> dependents;       // Nodes that depend on this

        bool resolved = false;               // Has this been fully resolved?
        int resolvedIteration = -1;          // Which iteration resolved this (-1 = not resolved)
        int resolvedWidth = 0;               // Resolved width (for PARAMTYPEDTYPEs)
        int pendingDeps = 0;                 // Unresolved dependency count (work-queue)

        // Deferred AST mutation state - populated during resolve(), applied in finalizeAST()
        // For PARAMTYPEDTYPE:
        AstNodeDType* deferredDTypep = nullptr;       // Resolved dtype to set
        bool deferredNeedsWidthForce = false;         // Whether to force width
        int deferredForcedWidth = 0;                  // Width to force
        int deferredForcedWidthMin = 0;               // WidthMin to force
        bool deferredNeedsChildDTypeClear = false;    // Whether to clear childDTypep
        AstTypedef* deferredChildTypedefp = nullptr;  // Typedef to set on child RefDType

        // For REFDTYPE:
        AstTypedef* deferredTypedefp = nullptr;       // Typedef to set
        AstNodeDType* deferredRefDTypep = nullptr;    // RefDType to set
        AstNodeModule* deferredClassOwnerp = nullptr; // ClassOrPackage to set

        // For GPARAM/LPARAM:
        AstNode* deferredValuep = nullptr;            // Value expression to set

        // General flags for finalize pass
        bool needsNormalize = false;                  // Needs normalizeRef in finalize
        bool needsNormalizeTree = false;              // Needs normalizeRefTree in finalize
    };

    using NodeMap = std::unordered_map<AstNode*, DepNode*>;

private:
    static NodeMap s_nodes;                  // All nodes in the graph
    static std::vector<DepNode*> s_allNodes; // Ordered list for iteration
    static int s_iterationCount;             // Number of resolution iterations
    static int s_commitChanges;              // Changes applied during per-node commit
    static bool s_enabled;                   // Is the graph active?
    static bool s_preserveCapturedExprs;     // Preserve captured param exprs across reset
    static std::unordered_map<AstRefDType*, std::string> s_refDTypeDotPathRegistry;
    static bool s_useInParam;             // Use DepGraph during V3Param fixed-point loop
    static std::unordered_set<AstNodeModule*> s_builtModules;  // Modules already visited in build

    // Typedef -> class mapping for parameterized class typedefs
    // Key: (typedef owner module name, typedef name), Value: target class
    using TypedefClassKey = std::pair<std::string, std::string>;
    struct TypedefClassKeyHash {
        std::size_t operator()(const TypedefClassKey& k) const {
            return std::hash<std::string>{}(k.first) ^ (std::hash<std::string>{}(k.second) << 1);
        }
    };
    static std::unordered_map<TypedefClassKey, AstClass*, TypedefClassKeyHash> s_typedefClassMap;

    // Forward declare visitor classes as friends
    friend class DepExprVisitor;
    friend class DepGraphBuildVisitor;

    // Internal helpers
    static DepNode* findOrCreateNode(AstNode* nodep, NodeType type, AstNodeModule* ownerModp);
    static void addEdge(DepNode* from, DepNode* to);
    static void collectExpressionDeps(AstNode* exprp, DepNode* depNode, AstNodeModule* scopeModp);
    static NodeType classifyVar(const AstVar* varp);
    static const char* nodeTypeName(NodeType type);

public:
    // Enable/disable the graph
    static void enable(bool flag) {
        s_enabled = flag;
        if (!flag) {
            s_preserveCapturedExprs = false;
            reset();
        }
    }
    static bool enabled() { return s_enabled; }

    // Preserve captured param/localparam expressions across reset/build
    static void preserveCapturedExprs(bool flag) { s_preserveCapturedExprs = flag; }
    static bool preserveCapturedExprs() { return s_preserveCapturedExprs; }

    // Find specialized typedef clone by name; optionally returns owner module
    static AstTypedef* findSpecializedTypedef(const std::string& name,
                                              AstNodeModule** ownerp = nullptr);

    // Reset/clear the graph (keeps cell associations)
    static void reset();
    // Reset everything including cell associations
    static void resetAll();

    // Build the graph from the AST (call after V3Param)
    static void build(AstNetlist* netlistp);
    // Incremental build: add nodes/edges for newly cloned modules
    static void buildIncremental(AstNetlist* netlistp);

    // Utility: find owning module for an AST node
    static AstNodeModule* findOwnerModule(AstNode* nodep);

    // Utility: check if an AST node is in an unspecialized template module
    static bool inTemplateModule(const AstNode* nodep);

    // Guard helpers for DepGraph param flow
    static bool shouldDeferTemplateType(const AstNode* nodep) {
        return useInParam() && inTemplateModule(nodep);
    }
    static bool allowParamMutation() { return !useInParam(); }
    static bool allowBrokenDTypeCheck(const AstNode* nodep) {
        return !useInParam() && !inTemplateModule(nodep);
    }
    // Guard helper: defer const-folding ATTROF when source type is unresolved during DepGraph param flow.
    static bool shouldDeferAttrOf(const AstAttrOf* attrp) {
        if (!attrp) return false;
        if (!useInParam()) return false;  // Only defer during DepGraph param flow
        // Check if the fromp (source type) has width=0, meaning it's not resolved yet
        if (const AstRefDType* const rdp = VN_CAST(attrp->fromp(), RefDType)) {
            const AstNodeDType* const skipped = rdp->skipRefp();
            if (!skipped || skipped->width() == 0) return true;
            if (rdp->refDTypep() && rdp->refDTypep()->width() == 0) return true;
        } else if (const AstNodeDType* const dtp = VN_CAST(attrp->fromp(), NodeDType)) {
            if (dtp->width() == 0) return true;
        }
        return false;
    }
    // Guard helper: defer widthing when dtype is unresolved during DepGraph param flow.
    static bool shouldDeferDType(const AstNodeDType* dtypep) {
        auto debug = []() -> int { return V3Error::debugDefault(); };  // EOM
        if (!dtypep) {
            UINFO(5, "DEPGRAPH: shouldDeferDType null dtypep -> true\n");
            return true;
        }
        // Check for RequireDType directly to avoid recursion in skipRefOrNullp
        if (VN_IS(dtypep, RequireDType)) {
            UINFO(5, "DEPGRAPH: shouldDeferDType is RequireDType for " << dtypep << " -> true\n");
            return true;
        }
        if (const AstParamTypeDType* const ptdp = VN_CAST(dtypep, ParamTypeDType)) {
            if (ptdp->subDTypep() && VN_IS(ptdp->subDTypep(), RequireDType)) {
                UINFO(5, "DEPGRAPH: shouldDeferDType ParamTypeDType -> RequireDType for " << dtypep << " -> true\n");
                return true;
            }
        }

        // Use skipRefOrNullp to catch unresolved ParamType/RequireDType chains.
        const AstNodeDType* const basep = dtypep->skipRefOrNullp();
        if (!basep) {
            UINFO(5, "DEPGRAPH: shouldDeferDType skipRefOrNullp null for " << dtypep << " -> true\n");
            return true;
        }
        if (VN_IS(basep, RequireDType)) {
            UINFO(5, "DEPGRAPH: shouldDeferDType basep is RequireDType for " << dtypep << " -> true\n");
            return true;
        }
        if (const AstParamTypeDType* const ptdp = VN_CAST(basep, ParamTypeDType)) {
            if (ptdp->subDTypep() && VN_IS(ptdp->subDTypep(), RequireDType)) {
                UINFO(5, "DEPGRAPH: shouldDeferDType ParamTypeDType -> RequireDType for " << dtypep << " -> true\n");
                return true;
            }
        }
        if (const AstNodeUOrStructDType* const uorp = VN_CAST(basep, NodeUOrStructDType)) {
            if (!uorp->dtypep()) {
                UINFO(5, "DEPGRAPH: shouldDeferDType UOrStruct missing dtypep for " << basep
                            << " -> true\n");
                return true;
            }
        }
        UINFO(5, "DEPGRAPH: shouldDeferDType " << dtypep << " basep=" << basep
                    << " -> false\n");
        return false;
    }

    // Track per-node commit changes
    static void commitChange() { ++s_commitChanges; }

    // Resolve all dependencies using fixed-point iteration
    // Returns number of iterations needed
    static int resolve();

    // Iteration boundary hook (recompute pending deps / mark-ready)
    static void beginIteration(AstNetlist* netlistp);

    // Optional post-iteration cleanup hook (no structural changes by default)
    static void postIterationCleanup(AstNetlist* netlistp);

    // Optional post-width cleanup hook (called from V3Width in param flow)
    static void postWidthCleanup(AstNode* nodep);

    // Apply resolved typedefs to RefDType nodes
    // Returns number of changes applied (for fixed-point looping)
    static int apply();

    // Finalize AST: apply all deferred mutations from resolve() in a single pass
    // This is the ONLY place that mutates the AST based on DepGraph results
    // Call this after the V3Param fixed-point loop completes
    static void finalizeAST();

    // Use DepGraph during V3Param fixed-point loop
    static void useInParam(bool flag) { s_useInParam = flag; }
    static bool useInParam() { return s_useInParam; }

    // Sync RefDType widths with their refDTypep targets in a specific module.
    // Call this BEFORE widthParamsEdit to ensure $bits() expressions get correct values.
    static void syncRefDTypeWidths(AstNodeModule* modp);

    // Mark template module types as didWidth(true) to prevent V3Width errors
    // during V3Param. Must be called BEFORE V3Param::param().
    // Template modules have unresolved parameters, so their types may have
    // incorrect widths. Marking them prevents spurious errors.
    static void markTemplateTypes(AstNetlist* netlistp);

    // Register cell association for a node (called from linkdot during primary pass)
    // This captures which cell a PARAMTYPEDTYPE references through
    // typedefName is the name of the typedef being referenced (e.g., "a_t" in "types.a_t")
    // contextModp is the module where the typedef reference is made (may differ from PARAMTYPEDTYPE owner)
    static void registerCellAssociation(AstNode* nodep, AstCell* cellp,
                                        const string& typedefName,
                                        AstNodeModule* contextModp = nullptr,
                                        const string& assocCellName = "");
    // Register transient cell context for RefDType created from dotted datatype references
    static void registerRefDTypeDotPath(AstRefDType* refp, const std::string& cellName,
                                        AstNodeModule* contextModp = nullptr);
    static void registerRefDTypeScopedTypedef(AstRefDType* refp, AstTypedef* tdp);
    static void registerTypedefScopedTypedef(AstTypedef* typedefp, AstTypedef* scopedp);

    // Capture original param/localparam expression before constification
    static void captureParamExpr(AstVar* varp, AstNodeModule* ownerModp);
    static void captureParamExpr(AstVar* varp, AstNode* exprp, AstNodeModule* ownerModp);

    // Capture type parameter binding for specialized classes
    static void captureParamTypeDType(AstParamTypeDType* ptdp, AstNodeDType* dtypep,
                                      AstNodeModule* ownerModp);

    // Register typedef -> class mapping for parameterized class typedefs
    static void registerTypedefClass(AstTypedef* tdp, AstClass* classp, AstNodeModule* ownerModp);
    // Lookup registered typedef class
    static AstClass* findTypedefClass(const std::string& ownerName, const std::string& typedefName);

    // Statistics
    static std::size_t size() { return s_allNodes.size(); }
    static int iterationCount() { return s_iterationCount; }

    // Find a node by AST pointer
    static const DepNode* find(AstNode* nodep);
    static DepNode* findMutable(AstNode* nodep);

    // Iterate over all nodes
    static void forEach(const std::function<void(const DepNode&)>& fn);

    // Debugging - print the entire graph
    static void dumpGraph();
    static void dumpGraphDepsTree();  // Dependency edge tree view
    static void dumpGraphTree(AstNetlist* netlistp);  // Hierarchy tree view
    static void dumpNode(const DepNode* nodep);
    static string nodeName(const DepNode* nodep);
    static string nodeOwnerName(const DepNode* nodep);

private:
    // Helper for tree dump
    static void dumpModuleTree(AstNodeModule* modp, const string& prefix, bool isLast);
    // Helper for resolution - re-evaluate a single node
    static void reEvaluateNode(DepNode* nodep);
    // Helper for buildIncremental - update edges to specialized nodes
    static void updateEdgesToSpecialized();
};

#endif  // VERILATOR_V3LINKDOTDEPGRAPH_H_
