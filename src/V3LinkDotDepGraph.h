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
        // These are the "boundary conditions" for graph execution - either from defaults or overrides
        int initialWidth = 0;                // Width from AST at build time (value params)
        AstNode* initialValuep = nullptr;    // Value expression (GPARAM/LPARAM) - cloned
        AstNodeDType* initialTypep = nullptr; // Bound dtype (PARAMTYPEDTYPE) - cloned

        // === Execution state ===
        bool resolved = false;               // Has this node completed execution?
        int resolvedIteration = -1;          // Which iteration resolved this (-1 = not resolved)
        int pendingDeps = 0;                 // Unresolved parent count (ready when 0)

        // === Resolved state (computed during execute, applied in finalizeAST) ===
        // These are the "outputs" of this node that children can read
        int resolvedWidth = 0;               // Computed width (for $bits())
        AstNodeDType* resolvedTypep = nullptr;  // Computed type (for type parameters)
        AstNode* resolvedValuep = nullptr;   // Computed value (for value parameters)
        AstTypedef* resolvedTypedefp = nullptr; // Resolved typedef (for REFDTYPE retargeting)
        AstNodeModule* resolvedOwnerModp = nullptr; // Owner module of resolved type (for class scope)
    };

    using NodeMap = std::unordered_map<AstNode*, DepNode*>;

private:
    static NodeMap s_nodes;                  // All nodes in the graph
    static std::vector<DepNode*> s_allNodes; // Ordered list for iteration
    static int s_iterationCount;             // Number of resolution iterations
    static bool s_enabled;                   // Is the graph active?
    static std::unordered_map<AstRefDType*, std::string> s_refDTypeDotPathRegistry;
    static std::unordered_set<AstNodeModule*> s_builtModules;  // Modules already visited in build

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
        if (!flag) reset();
    }
    static bool enabled() { return s_enabled; }

    // Find specialized typedef clone by name; optionally returns owner module
    static AstTypedef* findSpecializedTypedef(const std::string& name,
                                              AstNodeModule** ownerp = nullptr);

    // Reset/clear the graph (keeps cell associations)
    static void reset();
    // Reset everything including cell associations
    static void resetAll();

    // Build the graph from the AST
    static void build(AstNetlist* netlistp);

    // Debug: dump dependency graph tree view
    static void dumpGraph(const char* stageName);

    // Utility: find owning module for an AST node
    static AstNodeModule* findOwnerModule(AstNode* nodep);

    // Utility: check if an AST node is in an unspecialized template module
    static bool inTemplateModule(const AstNode* nodep);


    // Resolve all dependencies using OOO execution model
    // Returns number of nodes resolved
    static int resolve();

    // Finalize AST after resolution
    // This is the ONLY place that mutates the AST based on DepGraph results
    // Call this after resolve() completes
    static void finalizeAST();

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
    static void dumpGraphDepsTree(const char* stageName = "");  // Dependency tree (what each node depends on)
    static void dumpGraphDependentsTree(const char* stageName = "");  // Dependents tree (what depends on each node)
    static void dumpGraphTree(AstNetlist* netlistp);  // Hierarchy tree view
    static void dumpNode(const DepNode* nodep);
    static string nodeName(const DepNode* nodep);
    static string nodeOwnerName(const DepNode* nodep);

private:
    // Helper for tree dump
    static void dumpModuleTree(AstNodeModule* modp, const string& prefix, bool isLast);
    // Helper for resolution - re-evaluate a single node
    static void reEvaluateNode(DepNode* nodep);
};

#endif  // VERILATOR_V3LINKDOTDEPGRAPH_H_
