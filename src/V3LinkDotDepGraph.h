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

class VSymEnt;  // Forward declaration for unified registration function

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
        std::string cellPath;                // Full hierarchical path to cell context (e.g., "t.u_sub")
        AstPin* pinp = nullptr;              // Parameter pin to update in finalizeAST (for GPARAMs)

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

    // Key for per-cell-context DepNodes: (AstNode*, cellPath)
    struct NodeKey {
        AstNode* nodep;
        std::string cellPath;
        bool operator==(const NodeKey& other) const {
            return nodep == other.nodep && cellPath == other.cellPath;
        }
    };
    struct NodeKeyHash {
        size_t operator()(const NodeKey& key) const {
            return std::hash<AstNode*>()(key.nodep) ^ (std::hash<std::string>()(key.cellPath) << 1);
        }
    };
    using NodeMap = std::unordered_map<NodeKey, DepNode*, NodeKeyHash>;

private:
    static NodeMap s_nodes;                  // All nodes in the graph
    static std::vector<DepNode*> s_allNodes; // Ordered list for iteration
    static int s_iterationCount;             // Number of resolution iterations
    static bool s_enabled;                   // Is the graph active?
    static bool s_executing;                 // Are we currently in DepGraph execution?
    static std::unordered_map<AstRefDType*, std::string> s_refDTypeDotPathRegistry;
    static std::unordered_set<AstNodeModule*> s_builtModules;  // Modules already visited in build

    // Forward declare visitor classes as friends
    friend class DepExprVisitor;
    friend class DepGraphBuildVisitor;

    // Internal helpers
    static DepNode* findOrCreateNode(AstNode* nodep, NodeType type, AstNodeModule* ownerModp,
                                     const std::string& cellPath = "");
    static void addEdge(DepNode* from, DepNode* to);
    static void collectExpressionDeps(AstNode* exprp, DepNode* depNode, AstNodeModule* scopeModp,
                                      const std::string& cellPathOverride = "",
                                      bool hasCellPathOverride = false);
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

    // Check if DepGraph is currently in execution phase
    // Used by V3Width to avoid adding cloned types to global type table
    static bool isExecuting() { return s_executing; }
    // Set execution flag - keeps type table clean for entire DepGraph flow
    // (build, resolve, finalizeAST, and V3Param cloning)
    static void setExecuting(bool flag) { s_executing = flag; }

    // Finalize AST after resolution
    // This is the ONLY place that mutates the AST based on DepGraph results
    // Call this after resolve() completes
    static void finalizeAST();

    // Cleanup cloned types after V3Param completes
    // Call this after V3Param finishes to avoid dangling pointers in type table
    static void cleanupClonedTypes();

    // Apply resolved LPARAM values to a cloned module for a specific cell context
    // Called by V3Param after cloning a module for a cell
    // srcModp: the template module that was cloned
    // newModp: the cloned module
    // cellPath: the hierarchical path to the cell (e.g., "t.u_sub8")
    static void applyResolvedToClone(AstNodeModule* srcModp, AstNodeModule* newModp,
                                     const std::string& cellPath);

    // Register cell association for interface port -> connected interface instance
    // portPath: hierarchical path to the interface port (e.g., "t.u_subA.io")
    // ifaceCellPath: hierarchical path to the connected interface instance (e.g., "t.subA_io")
    static void registerCellAssociation(const std::string& portPath, const std::string& ifaceCellPath);
    // Register transient cell context for RefDType created from dotted datatype references
    static void registerRefDTypeDotPath(AstRefDType* refp, const std::string& cellName,
                                        AstNodeModule* contextModp = nullptr);

    // Unified registration for interface typedef context - handles both DepGraph and IfaceCapture
    // This eliminates duplicate cell checks and consolidates registration logic.
    // Parameters:
    //   refp: The RefDType being registered
    //   stageLabel: "typedef" or "paramtype" for debug output
    //   dotPos: Current dot position state
    //   dotIsFinal: Whether this is the final segment of a dotted reference
    //   dotText: The dotted text (e.g., "io" from "io.data_t")
    //   dotSymp: Symbol entry for the dotted reference
    //   curSymp: Current symbol table entry
    //   modp: Current module context
    //   nodep: Original AST node being processed
    //   promoteVarCb: Callback for promoting vars to param types (for IfaceCapture)
    //   indentFn: Callback for debug indentation
    static void registerIfaceTypedefContext(
        AstRefDType* refp, const char* stageLabel, int dotPos, bool dotIsFinal,
        const std::string& dotText, VSymEnt* dotSymp, VSymEnt* curSymp,
        AstNodeModule* modp, AstNode* nodep,
        const std::function<bool(AstVar*, AstRefDType*)>& promoteVarCb,
        const std::function<std::string()>& indentFn);
    static void registerRefDTypeScopedTypedef(AstRefDType* refp, AstTypedef* tdp);
    static void registerTypedefScopedTypedef(AstTypedef* typedefp, AstTypedef* scopedp);

    // Query resolved ATTROF value for a given AstAttrOf node.
    // Returns the resolved constant value, or nullptr if not resolved.
    // Used by V3Width to get DepGraph-computed $bits() values.
    static AstConst* getResolvedAttrOf(const AstAttrOf* nodep);

    // Statistics
    static std::size_t size() { return s_allNodes.size(); }
    static int iterationCount() { return s_iterationCount; }

    // Find a node by AST pointer and cell path (for per-cell-context nodes)
    static const DepNode* find(AstNode* nodep, const std::string& cellPath = "");
    static DepNode* findMutable(AstNode* nodep, const std::string& cellPath = "");
    // Find a node by name, owner module, type, and cellPath
    static DepNode* findByNameAndOwner(const string& name, AstNodeModule* ownerModp, NodeType type,
                                       const std::string& cellPath = "");

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
