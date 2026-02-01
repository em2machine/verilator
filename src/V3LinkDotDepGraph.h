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

    // A node in the dependency graph - shadow data structure for parameters/types
    // Execution model:
    //   1. Build: Create nodes, capture initial state from AST, create edges
    //   2. Resolve: OOO execution - read from parent DepNodes, compute, store in self, wake children
    //   3. FinalizeAST: Apply resolved state to AST before V3Param creates clones
    struct DepNode final {
        // === Identity (set during build, immutable) ===
        AstNode* nodep = nullptr;            // The AST node (for finalizeAST to update)
        NodeType nodeType = NodeType::GPARAM;
        AstNodeModule* ownerModp = nullptr;  // Module/interface owning this node
        AstCell* cellp = nullptr;            // Cell instantiation (for cross-module edges)
        std::string cellName;                // Cell name for typedef lookup (survives cloning)

        // === Edges (set during build) ===
        std::set<DepNode*> dependsOn;        // Parent nodes this depends on (read during execute)
        std::set<DepNode*> dependents;       // Child nodes that depend on this (wake on commit)

        // === Initial state (captured from AST during build) ===
        int initialWidth = 0;                // Width from AST at build time
        AstNode* initialValuep = nullptr;    // Value expression from AST at build time (cloned)

        // === Execution state ===
        bool resolved = false;               // Has this node completed execution?
        int resolvedIteration = -1;          // Which iteration resolved this (-1 = not resolved)
        int pendingDeps = 0;                 // Unresolved parent count (ready when 0)

        // === Resolved state (computed during execute, applied in finalizeAST) ===
        // These are the "outputs" of this node that children can read
        int resolvedWidth = 0;               // Computed width (for $bits())
        AstNodeDType* resolvedTypep = nullptr;  // Computed type (for type parameters)
        AstNode* resolvedValuep = nullptr;   // Computed value (for value parameters)

        // === Legacy deferred state (to be migrated to resolved state) ===
        AstNodeDType* deferredDTypep = nullptr;
        bool deferredNeedsWidthForce = false;
        int deferredForcedWidth = 0;
        int deferredForcedWidthMin = 0;
        bool deferredNeedsChildDTypeClear = false;
        AstTypedef* deferredChildTypedefp = nullptr;
        AstTypedef* deferredTypedefp = nullptr;
        AstNodeDType* deferredRefDTypep = nullptr;
        AstNodeModule* deferredClassOwnerp = nullptr;
        AstNode* deferredValuep = nullptr;
        bool needsNormalize = false;
        bool needsNormalizeTree = false;

        // Legacy - to be removed
        AstNode* origExprp = nullptr;
    };

    using NodeMap = std::unordered_map<AstNode*, DepNode*>;

private:
    static NodeMap s_nodes;                  // All nodes in the graph
    static std::vector<DepNode*> s_allNodes; // Ordered list for iteration
    static int s_iterationCount;             // Number of resolution iterations
    static int s_commitChanges;              // OLD ARCHITECTURE: commit tracking (kept for API compat)
    static bool s_enabled;                   // Is the graph active?
    static bool s_preserveCapturedExprs;     // OLD ARCHITECTURE: preserve exprs across reset (not needed)
    static std::unordered_map<AstRefDType*, std::string> s_refDTypeDotPathRegistry;
    static bool s_useInParam;             // OLD ARCHITECTURE: interleaved V3Param (not needed)
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

    // Debug: dump dependency graph tree view
    static void dumpGraph(const char* stageName);

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

    // OLD ARCHITECTURE: Track per-node commit changes (kept for API compat)
    static void commitChange() { ++s_commitChanges; }

    // Resolve all dependencies using OOO execution model
    // Returns number of nodes resolved
    static int resolve();

    // OLD ARCHITECTURE: Iteration hooks (stubs - not needed in new architecture)
    static void beginIteration(AstNetlist* netlistp);
    static void postIterationCleanup(AstNetlist* netlistp);
    static void postWidthCleanup(AstNode* nodep);

    // OLD ARCHITECTURE: Apply changes (returns commit count for compat)
    static int apply();

    // NEW ARCHITECTURE: Finalize AST after resolution
    // This is the ONLY place that mutates the AST based on DepGraph results
    // Call this after resolve() completes
    static void finalizeAST();

    // OLD ARCHITECTURE: Interleaved V3Param flag (not needed)
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
    // Find a node by name, owner module, and type
    static DepNode* findByNameAndOwner(const string& name, AstNodeModule* ownerModp, NodeType type);

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
