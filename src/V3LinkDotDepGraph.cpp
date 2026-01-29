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
int V3LinkDotDepGraph::s_commitChanges = 0;
bool V3LinkDotDepGraph::s_enabled = false;
bool V3LinkDotDepGraph::s_preserveCapturedExprs = false;
bool V3LinkDotDepGraph::s_useInParam = false;
std::unordered_map<AstRefDType*, std::string> V3LinkDotDepGraph::s_refDTypeDotPathRegistry;
std::unordered_set<AstNodeModule*> V3LinkDotDepGraph::s_builtModules;
std::unordered_map<V3LinkDotDepGraph::TypedefClassKey, AstClass*,
                   V3LinkDotDepGraph::TypedefClassKeyHash> V3LinkDotDepGraph::s_typedefClassMap;
static std::unordered_map<AstRefDType*, AstTypedef*> s_refDTypeScopedTypedefs;
static std::unordered_map<AstTypedef*, AstTypedef*> s_typedefScopedTypedefs;

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
    if (reinterpret_cast<uintptr_t>(nodep) < 4096) return nullptr;
    for (AstNode* curp = nodep; curp; curp = curp->backp()) {
        if (reinterpret_cast<uintptr_t>(curp) < 4096) return nullptr;
        if (AstNodeModule* const modp = VN_CAST(curp, NodeModule)) return modp;
    }
    return nullptr;
}

bool V3LinkDotDepGraph::inTemplateModule(const AstNode* nodep) {
    const AstNodeModule* const modp = findOwnerModule(const_cast<AstNode*>(nodep));
    if (!modp) return true;
    if (modp->isTop()) return false;
    return modp->hasGParam() && modp->name().find("__") == string::npos;
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
    case NodeType::ATTROF: return "ATTROF";
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
    // Note: Do NOT clear s_refDTypeScopedTypedefs here - populated during linkdot primary
    // and needed during graph build which occurs later.
    s_iterationCount = 0;
    s_builtModules.clear();
}

void V3LinkDotDepGraph::resetAll() {
    reset();
    s_cellAssociations.clear();
    s_refDTypeDotPathRegistry.clear();
    s_refDTypeScopedTypedefs.clear();
    s_typedefScopedTypedefs.clear();
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
                  << "' in " << (contextModp ? contextModp->name() : "<unknown>")
                  << " ptr=" << cvtToHex(refp) << endl);
}

void V3LinkDotDepGraph::registerRefDTypeScopedTypedef(AstRefDType* refp, AstTypedef* tdp) {
    if (!refp || !tdp) return;
    s_refDTypeScopedTypedefs[refp] = tdp;
    UINFO(5, "DEPGRAPH: registered refdtype scoped typedef '" << refp->name()
              << "' -> '" << tdp->name() << "'" << endl);
}

void V3LinkDotDepGraph::registerTypedefScopedTypedef(AstTypedef* typedefp, AstTypedef* scopedp) {
    if (!typedefp || !scopedp) return;
    s_typedefScopedTypedefs[typedefp] = scopedp;
    UINFO(5, "DEPGRAPH: registered typedef scoped typedef '" << typedefp->name()
              << "' -> '" << scopedp->name() << "'" << endl);
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

V3LinkDotDepGraph::DepNode* V3LinkDotDepGraph::findMutable(AstNode* nodep) {
    const auto it = s_nodes.find(nodep);
    if (it == s_nodes.end()) return nullptr;
    return it->second;
}

AstTypedef* V3LinkDotDepGraph::findSpecializedTypedef(const std::string& name,
                                                      AstNodeModule** ownerp) {
    for (DepNode* const candNodep : s_allNodes) {
        if (!candNodep || candNodep->nodeType != NodeType::TYPEDEF) continue;
        AstTypedef* const candTdp = VN_CAST(candNodep->nodep, Typedef);
        if (!candTdp || candTdp->name() != name) continue;
        if (candNodep->ownerModp && candNodep->ownerModp->name().find("__") != string::npos) {
            if (ownerp) *ownerp = candNodep->ownerModp;
            return candTdp;
        }
    }
    return nullptr;
}

V3LinkDotDepGraph::DepNode* V3LinkDotDepGraph::findOrCreateNode(AstNode* nodep, NodeType type,
                                                                 AstNodeModule* ownerModp) {
    if (!nodep) return nullptr;
    auto it = s_nodes.find(nodep);
    if (it != s_nodes.end()) return it->second;

    if (type == NodeType::PARAMTYPEDTYPE) {
        UASSERT_OBJ(ownerModp, nodep,
                    "DEPGRAPH: PARAMTYPEDTYPE node created with null owner module");
    }

    DepNode* const depNodep = new DepNode;
    depNodep->nodep = nodep;
    depNodep->nodeType = type;
    depNodep->ownerModp = ownerModp;
    s_nodes[nodep] = depNodep;
    s_allNodes.push_back(depNodep);

    UINFO(9, "DEPGRAPH: created " << nodeTypeName(type) << " node '" << nodeName(depNodep)
              << "' owner=" << nodeOwnerName(depNodep) << endl);

    // For REFDTYPE nodes, look up cellName from the registry
    if (type == NodeType::REFDTYPE) {
        if (AstRefDType* const rdp = VN_CAST(nodep, RefDType)) {
            const auto regIt = s_refDTypeDotPathRegistry.find(rdp);
            if (regIt != s_refDTypeDotPathRegistry.end()) {
                depNodep->cellName = regIt->second;
                UINFO(5, "DEPGRAPH: REFDTYPE '" << rdp->name() << "' cellName='" << depNodep->cellName
                          << "' from registry in " << (ownerModp ? ownerModp->name() : "<unknown>") << endl);
            } else if (AstRefDType* const origRefp = rdp->clonep()) {
                const auto origIt = s_refDTypeDotPathRegistry.find(origRefp);
                if (origIt != s_refDTypeDotPathRegistry.end()) {
                    depNodep->cellName = origIt->second;
                    UINFO(5, "DEPGRAPH: REFDTYPE '" << rdp->name() << "' cellName='" << depNodep->cellName
                              << "' inherited from clone in " << (ownerModp ? ownerModp->name() : "<unknown>") << endl);
                }
            }
        }
    }
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

static bool normalizeRef(AstRefDType* rdp, AstNodeDType* newRefDTypep = nullptr,
                         AstTypedef* newTypedefp = nullptr,
                         AstNodeModule* newClassOwnerp = nullptr) {
    if (!rdp) return false;
    bool changed = false;

    // Defensive: clear obviously invalid pointers before dereferencing
    if (AstTypedef* const tdp = rdp->typedefp()) {
        if (reinterpret_cast<uintptr_t>(tdp) < 4096) {
            UINFO(5, "DEPGRAPH: commit clear invalid typedefp for RefDType '" << rdp->name()
                      << "' typedefp=" << tdp << endl);
            rdp->typedefp(nullptr);
            rdp->dtypep(nullptr);
            rdp->didWidth(false);
            changed = true;
        }
    }
    if (AstNodeDType* const refp = rdp->refDTypep()) {
        if (reinterpret_cast<uintptr_t>(refp) < 4096) {
            UINFO(5, "DEPGRAPH: commit clear invalid refDTypep for RefDType '" << rdp->name()
                      << "' refDTypep=" << refp << endl);
            rdp->refDTypep(nullptr);
            rdp->dtypep(nullptr);
            rdp->didWidth(false);
            changed = true;
        }
    }
    if (AstNodeDType* const refp = rdp->refDTypep()) {
        if (VN_DELETED(refp) || VN_DELETED(refp->backp()) || !refp->backp()) {
            AstNodeModule* const refOwnerp = V3LinkDotDepGraph::findOwnerModule(refp);
            UINFO(5, "DEPGRAPH: commit clear dangling refDTypep for RefDType '" << rdp->name()
                      << "' refDTypep=" << refp
                      << " refOwner='" << (refOwnerp ? refOwnerp->name() : "<null>") << "'"
                      << endl);
            rdp->refDTypep(nullptr);
            rdp->dtypep(nullptr);
            rdp->didWidth(false);
            changed = true;
        }
    }

    // Explicit retargets from dependency resolution.
    if (newTypedefp && rdp->typedefp() != newTypedefp) {
        rdp->typedefp(newTypedefp);
        rdp->refDTypep(nullptr);
        rdp->dtypep(nullptr);
        if (newClassOwnerp) rdp->classOrPackagep(newClassOwnerp);
        rdp->didWidth(false);
        changed = true;
    }
    if (newRefDTypep && rdp->refDTypep() != newRefDTypep) {
        rdp->refDTypep(newRefDTypep);
        rdp->typedefp(nullptr);
        rdp->dtypep(nullptr);
        rdp->didWidth(false);
        changed = true;
    }

    // Enforce invariant: RefDType should not keep both typedefp and refDTypep.
    // V3Dead expects typedefp to be nullptr when elimCells is true.
    // Always clear typedefp when refDTypep is set.
    if (rdp->refDTypep() && rdp->typedefp()) {
        AstTypedef* const curTdp = rdp->typedefp();
        AstNodeDType* const curRefp = rdp->refDTypep();
        AstNodeModule* const tOwnerp = curTdp ? V3LinkDotDepGraph::findOwnerModule(curTdp) : nullptr;
        AstNodeModule* const rOwnerp = curRefp ? V3LinkDotDepGraph::findOwnerModule(curRefp) : nullptr;
        UINFO(5, "DEPGRAPH: commit clear typedefp for RefDType '" << rdp->name()
                  << "' (refDTypep is set) typedef='" << (curTdp ? curTdp->name() : "<null>")
                  << "' typedefp=" << curTdp
                  << "' typedefBackp=" << (curTdp ? curTdp->backp() : nullptr)
                  << "' typedefOwner='" << (tOwnerp ? tOwnerp->name() : "<null>")
                  << "' refDType='" << (curRefp ? curRefp->prettyTypeName() : "<null>")
                  << "' refDTypep=" << curRefp
                  << "' refBackp=" << (curRefp ? curRefp->backp() : nullptr)
                  << "' refOwner='" << (rOwnerp ? rOwnerp->name() : "<null>")
                  << "'" << endl);
        rdp->typedefp(nullptr);
        rdp->dtypep(nullptr);
        rdp->didWidth(false);
        changed = true;
    }

    // Clear template/removed typedef pointers to avoid dangling links after V3Dead
    if (AstTypedef* const tdp = rdp->typedefp()) {
        if (VN_DELETED(tdp) || VN_DELETED(tdp->backp()) || !tdp->backp()) {
            AstNodeModule* const tdOwnerp = V3LinkDotDepGraph::findOwnerModule(tdp);
            UINFO(5, "DEPGRAPH: commit clear dangling typedefp for RefDType '" << rdp->name()
                      << "' typedef='" << tdp->name()
                      << "' typedefp=" << tdp
                      << "' typedefOwner='" << (tdOwnerp ? tdOwnerp->name() : "<null>")
                      << "'" << endl);
            rdp->typedefp(nullptr);
            rdp->dtypep(nullptr);
            rdp->didWidth(false);
            changed = true;
        } else {
            AstNodeModule* const tdOwnerp = V3LinkDotDepGraph::findOwnerModule(tdp);
            AstNodeModule* const rdOwnerp = V3LinkDotDepGraph::findOwnerModule(rdp);
            if (tdOwnerp && !rdOwnerp && tdOwnerp->hasGParam() && !tdOwnerp->isTop()
                && tdOwnerp->name().find("__") == string::npos) {
                UINFO(5, "DEPGRAPH: commit refdtype has null owner but template typedef '"
                          << tdp->name() << "'" << endl);
                if (AstTypedef* const specTdp
                    = V3LinkDotDepGraph::findSpecializedTypedef(tdp->name(), nullptr)) {
                    UINFO(5, "DEPGRAPH: commit retarget null-owner refdtype '" << rdp->name()
                              << "' to specialized typedef '" << specTdp->name() << "'" << endl);
                    rdp->typedefp(specTdp);
                    rdp->dtypep(nullptr);
                    rdp->didWidth(false);
                    changed = true;
                } else {
                    UINFO(5, "DEPGRAPH: commit clear template typedefp '" << tdp->name()
                              << "' for null-owner RefDType '" << rdp->name() << "'" << endl);
                    rdp->typedefp(nullptr);
                    rdp->dtypep(nullptr);
                    rdp->didWidth(false);
                    changed = true;
                }
            }
            if (tdOwnerp && rdOwnerp && rdOwnerp->name().find("__") != string::npos
                && tdOwnerp->hasGParam() && tdOwnerp->name().find("__") == string::npos) {
                if (AstTypedef* const specTdp
                    = V3LinkDotDepGraph::findSpecializedTypedef(tdp->name(), nullptr)) {
                    UINFO(5, "DEPGRAPH: commit retarget template typedefp '" << tdp->name()
                              << "' to specialized typedefp for RefDType '" << rdp->name()
                              << "'" << endl);
                    rdp->typedefp(specTdp);
                    rdp->dtypep(nullptr);
                    rdp->didWidth(false);
                    changed = true;
                }
            }
            // Clear typedefp if it points to a template module typedef - these will be deleted
            // by V3Dead and must not be referenced from specialized modules.
            // Top modules must keep their typedefp even if parameterized, since there is no clone.
            if (tdOwnerp && rdOwnerp && rdOwnerp->name().find("__") != string::npos
                && !tdOwnerp->isTop() && tdOwnerp->hasGParam()
                && tdOwnerp->name().find("__") == string::npos) {
                UINFO(5, "DEPGRAPH: commit clear template typedefp '" << tdp->name()
                          << "' for RefDType '" << rdp->name() << "'" << endl);
                rdp->typedefp(nullptr);
                rdp->dtypep(nullptr);
                rdp->didWidth(false);
                changed = true;
            }
        }
    }
    // Move template refDTypep targets to TYPETABLE so they survive template deletion.
    // Top modules must keep their types in place since there is no clone.
    if (AstNodeDType* const subp = rdp->refDTypep()) {
        AstNodeModule* const subOwnerp = V3LinkDotDepGraph::findOwnerModule(subp);
        AstNodeModule* const rdOwnerp = V3LinkDotDepGraph::findOwnerModule(rdp);
        if (subOwnerp && rdOwnerp && rdOwnerp->name().find("__") != string::npos
            && !subOwnerp->isTop() && subOwnerp->hasGParam()
            && subOwnerp->name().find("__") == string::npos
            && subp->backp()) {
            if (AstParamTypeDType* const subPtdp = VN_CAST(subp, ParamTypeDType)) {
                if (AstParamTypeDType* const clonePtdp = subPtdp->clonep()) {
                    AstNodeModule* const cloneOwnerp = V3LinkDotDepGraph::findOwnerModule(clonePtdp);
                    if (cloneOwnerp && cloneOwnerp->name().find("__") != string::npos) {
                        UINFO(5, "DEPGRAPH: commit retarget refDTypep target '" << subp->name()
                                  << "' to clone '" << cloneOwnerp->name()
                                  << "' for RefDType '" << rdp->name() << "'" << endl);
                        rdp->refDTypep(clonePtdp);
                        rdp->dtypep(nullptr);
                        rdp->didWidth(false);
                        changed = true;
                        goto skip_move_refdtypep;
                    }
                }
                if (rdOwnerp) {
                    for (AstNode* stmtp = rdOwnerp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                        if (AstParamTypeDType* const localPtdp = VN_CAST(stmtp, ParamTypeDType)) {
                            if (localPtdp->name() == subPtdp->name()) {
                                UINFO(5, "DEPGRAPH: commit retarget refDTypep target '"
                                          << subPtdp->name() << "' to '" << rdOwnerp->name()
                                          << "' for RefDType '" << rdp->name() << "'" << endl);
                                rdp->refDTypep(localPtdp);
                                rdp->dtypep(nullptr);
                                rdp->didWidth(false);
                                changed = true;
                                goto skip_move_refdtypep;
                            }
                        }
                    }
                }
            }
            UINFO(5, "DEPGRAPH: commit move refDTypep target '" << subp->prettyTypeName()
                      << "' from template '" << subOwnerp->name()
                      << "' to TYPETABLE for RefDType '" << rdp->name() << "'" << endl);
            subp->unlinkFrBack();
            v3Global.rootp()->typeTablep()->addTypesp(subp);
            changed = true;
        }
    }
    // Retarget refDTypep from base module to specialized owner even when the base
    // module is not a GParam template (e.g. interface-driven specialization).
    if (AstParamTypeDType* const subPtdp = VN_CAST(rdp->refDTypep(), ParamTypeDType)) {
        AstNodeModule* const subOwnerp = V3LinkDotDepGraph::findOwnerModule(subPtdp);
        AstNodeModule* const rdOwnerp = V3LinkDotDepGraph::findOwnerModule(rdp);
        if (subOwnerp && rdOwnerp && subOwnerp != rdOwnerp) {
            const string rdOwnerName = rdOwnerp->name();
            const size_t rdSuffixPos = rdOwnerName.find("__");
            if (rdSuffixPos != string::npos
                && rdOwnerName.substr(0, rdSuffixPos) == subOwnerp->name()) {
                AstParamTypeDType* replacementp = nullptr;
                for (AstNode* stmtp = rdOwnerp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                    if (AstParamTypeDType* const candp = VN_CAST(stmtp, ParamTypeDType)) {
                        if (candp->name() == subPtdp->name()) {
                            replacementp = candp;
                            break;
                        }
                    }
                }
                if (replacementp && replacementp != subPtdp) {
                    UINFO(5, "DEPGRAPH: commit retarget refDTypep target '" << subPtdp->name()
                              << "' to specialized owner '" << rdOwnerp->name()
                              << "' for RefDType '" << rdp->name() << "'" << endl);
                    rdp->refDTypep(replacementp);
                    rdp->dtypep(nullptr);
                    rdp->didWidth(false);
                    changed = true;
                }
            }
        }
    }
skip_move_refdtypep:
    // Clear stale refDTypep when typedefp already points to specialized module
    if (rdp->typedefp() && rdp->refDTypep()) {
        AstTypedef* const curTdp = rdp->typedefp();
        AstNodeDType* const curRefp = rdp->refDTypep();
        const bool allowBoth = curTdp && curRefp
                               && (curTdp->subDTypep() == curRefp
                                   || (curTdp->subDTypep()
                                       && curTdp->subDTypep()->skipRefp() == curRefp));
        AstNodeModule* const tdOwnerp = V3LinkDotDepGraph::findOwnerModule(curTdp);
        if (!allowBoth && tdOwnerp && tdOwnerp->name().find("__") != string::npos) {
            UINFO(5, "DEPGRAPH: commit clear stale refDTypep for '" << rdp->name()
                      << "' in specialized module '" << tdOwnerp->name() << "'" << endl);
            rdp->refDTypep(nullptr);
            rdp->dtypep(nullptr);
            rdp->didWidth(false);
            changed = true;
        }
    }
    // Sync cached width with committed target
    if (AstNodeDType* const refp = rdp->refDTypep()) {
        if (refp->width() > 0 && refp->width() != rdp->width()) {
            UINFO(5, "DEPGRAPH: commit sync RefDType '" << rdp->name()
                      << "' w" << rdp->width() << " -> w" << refp->width() << endl);
            rdp->dtypep(refp);
            rdp->widthForce(refp->width(), refp->widthMin());
            changed = true;
        }
    }

    if (AstTypedef* const dbgTdp = rdp->typedefp()) {
        UINFO(5, "DEPGRAPH: commit RefDType typedefp summary name='" << dbgTdp->name()
                  << "' typedefp=" << dbgTdp
                  << " ptr=" << static_cast<const void*>(dbgTdp)
                  << " backp=" << dbgTdp->backp()
                  << " backpPtr=" << static_cast<const void*>(dbgTdp->backp())
                  << " dtypep=" << dbgTdp->dtypep()
                  << " dtypepPtr=" << static_cast<const void*>(dbgTdp->dtypep())
                  << " childDTypep=" << dbgTdp->childDTypep()
                  << " childDTypepPtr=" << static_cast<const void*>(dbgTdp->childDTypep())
                  << endl);
    }
    if (AstNodeDType* const dbgRefp = rdp->refDTypep()) {
        UINFO(5, "DEPGRAPH: commit RefDType refDTypep summary type='"
                  << dbgRefp->prettyTypeName() << "' refDTypep=" << dbgRefp
                  << " ptr=" << static_cast<const void*>(dbgRefp)
                  << " backp=" << dbgRefp->backp()
                  << " backpPtr=" << static_cast<const void*>(dbgRefp->backp())
                  << endl);
    }

    if (changed) V3LinkDotDepGraph::commitChange();
    return changed;
}

static void normalizeRefTree(AstNode* nodep, const char* context = nullptr) {
    if (!nodep) return;
    if (context && std::string(context) == "template-skip") {
        if (AstNodeModule* const modp = VN_CAST(nodep, NodeModule)) {
            modp->foreach([&](AstTypedef* tdp) {
                if (!tdp) return;
                UINFO(5, "DEPGRAPH: template-skip typedef name='" << tdp->name()
                          << "' typedefp=" << tdp
                          << " ptr=" << static_cast<const void*>(tdp)
                          << " backp=" << tdp->backp()
                          << " backpPtr=" << static_cast<const void*>(tdp->backp())
                          << " dtypep=" << tdp->dtypep()
                          << " dtypepPtr=" << static_cast<const void*>(tdp->dtypep())
                          << " childDTypep=" << tdp->childDTypep()
                          << " childDTypepPtr=" << static_cast<const void*>(tdp->childDTypep())
                          << endl);
                // Keep childDTypep intact during template-skip so RefDTypes can still
                // resolve against typedefs before commit-time retargeting.
            });
            modp->foreach([&](AstRefDType* rdp) {
                if (!rdp) return;
                AstTypedef* const tdp = rdp->typedefp();
                if (!tdp) return;
                AstNodeModule* const tdOwnerp = V3LinkDotDepGraph::findOwnerModule(tdp);
                if (tdOwnerp != modp) return;
                UINFO(5, "DEPGRAPH: template-skip refdtype name='" << rdp->name()
                          << "' refdtypep=" << rdp
                          << " typedefp=" << tdp
                          << " refDTypep=" << rdp->refDTypep()
                          << " dtypep=" << rdp->dtypep()
                          << endl);
            });
        }
    }
    int refCount = 0;
    nodep->foreach([&](AstRefDType* rdp) {
        ++refCount;
        normalizeRef(rdp);
    });
    if (context) {
        string nodeName;
        if (AstTypedef* const tdp = VN_CAST(nodep, Typedef)) nodeName = tdp->name();
        if (AstParamTypeDType* const ptdp = VN_CAST(nodep, ParamTypeDType)) nodeName = ptdp->name();
        UINFO(5, "DEPGRAPH: normalizeRefTree " << context << " on " << nodep->typeName()
                  << " name=" << (nodeName.empty() ? "<anon>" : nodeName)
                  << " nodep=" << nodep
                  << " refs=" << refCount << endl);
    }
}

static void forEachRefDType(AstNodeModule* ownerModp, const std::function<void(AstRefDType*)>& fn) {
    if (v3Global.rootp()->typeTablep()) {
        v3Global.rootp()->typeTablep()->foreach([&](AstRefDType* rdp) { fn(rdp); });
    }
    if (ownerModp) ownerModp->foreach([&](AstRefDType* rdp) { fn(rdp); });
}

static void logRefDTypeState(const char* tag, const AstRefDType* rdp) {
    if (!rdp) return;
    UINFO(5, "DEPGRAPH: " << tag << " RefDType '" << rdp->name()
              << "' typedefp=" << rdp->typedefp()
              << " refDTypep=" << rdp->refDTypep()
              << " dtypep=" << rdp->dtypep()
              << endl);
}

static void commitRefDType(V3LinkDotDepGraph::DepNode* nodep) {
    if (!nodep || !nodep->nodep) return;
    if (AstRefDType* const rdp = VN_CAST(nodep->nodep, RefDType)) {
        // Apply deferredTypedefp during commit so dependent nodes see correct target.
        // This must happen before normalizeRef and width sync.
        if (nodep->deferredTypedefp && rdp->typedefp() != nodep->deferredTypedefp) {
            UINFO(5, "DEPGRAPH: commit apply deferredTypedefp '" << rdp->name()
                      << "' -> " << nodep->deferredTypedefp->name()
                      << " in " << (nodep->deferredClassOwnerp ? nodep->deferredClassOwnerp->name() : "<null>") << endl);
            rdp->typedefp(nodep->deferredTypedefp);
            rdp->dtypep(nullptr);
            rdp->didWidth(false);
        }
        // Apply deferredRefDTypep during commit so dependent nodes see correct target.
        // This must happen before normalizeRef and width sync.
        if (nodep->deferredRefDTypep && rdp->refDTypep() != nodep->deferredRefDTypep) {
            UINFO(5, "DEPGRAPH: commit apply deferredRefDTypep '" << rdp->name()
                      << "' -> " << nodep->deferredRefDTypep->name()
                      << " w" << nodep->deferredRefDTypep->width() << endl);
            rdp->refDTypep(nodep->deferredRefDTypep);
            rdp->typedefp(nullptr);
            rdp->dtypep(nullptr);
            rdp->didWidth(false);
        }

        AstTypedef* const tdp = rdp->typedefp();
        AstNodeDType* const refp = rdp->refDTypep();
        UINFO(5, "DEPGRAPH: commit REFDTYPE '" << rdp->name() << "'@"
                  << V3LinkDotDepGraph::nodeOwnerName(nodep)
                  << " typedefp=" << tdp
                  << " typedefBackp=" << (tdp ? tdp->backp() : nullptr)
                  << " refDTypep=" << refp
                  << " dtypep=" << rdp->dtypep()
                  << endl);

        // Update REFDTYPE's width from its target. This is critical for ATTROF ($bits)
        // which depends on REFDTYPE and needs the correct width.
        AstNodeDType* targetp = nullptr;
        if (refp) {
            targetp = refp->skipRefp();
            if (!targetp) targetp = refp;
        } else if (tdp && tdp->subDTypep()) {
            targetp = tdp->subDTypep()->skipRefp();
            if (!targetp) targetp = tdp->subDTypep();
        }
        if (targetp && targetp->width() > 0 && rdp->width() != targetp->width()) {
            UINFO(5, "DEPGRAPH: commit REFDTYPE '" << rdp->name()
                      << "' width " << rdp->width() << " -> " << targetp->width() << endl);
            rdp->widthForce(targetp->width(), targetp->widthMin());
            rdp->dtypep(targetp);
        }

        normalizeRef(rdp);
        if (AstTypedef* const postTdp = rdp->typedefp()) {
            AstNodeModule* const tdOwnerp = V3LinkDotDepGraph::findOwnerModule(postTdp);
            AstNodeModule* const rdOwnerp = V3LinkDotDepGraph::findOwnerModule(rdp);
            if (tdOwnerp && !rdOwnerp && tdOwnerp->hasGParam()
                && tdOwnerp->name().find("__") == string::npos) {
                UINFO(5, "DEPGRAPH: normalizeRef refdtype has null owner but template typedef name='"
                          << postTdp->name() << "' refdtype='" << rdp->name() << "'" << endl);
            }
            if (tdOwnerp && rdOwnerp && rdOwnerp != tdOwnerp && tdOwnerp->hasGParam()
                && tdOwnerp->name().find("__") == string::npos) {
                UINFO(5, "DEPGRAPH: commit REFDTYPE still points at template typedef name='"
                          << postTdp->name() << "' refdtype='" << rdp->name()
                          << "' refOwner='" << rdOwnerp->name()
                          << "' typedefOwner='" << tdOwnerp->name()
                          << "'" << endl);
            }
        }
        logRefDTypeState("commit REFDTYPE post", rdp);
    }
}

static void commitGParam(V3LinkDotDepGraph::DepNode* nodep) {
    (void)nodep;
}

static void commitLParam(V3LinkDotDepGraph::DepNode* nodep) {
    (void)nodep;
}

static void commitStructUnion(AstNodeUOrStructDType* usp, AstNodeModule* ownerModp) {
    if (!usp || !ownerModp) return;
    const bool isSpecialized = ownerModp->name().find("__") != string::npos;
    if (isSpecialized && usp->width() > 0) {
        // Store deferred retargets for RefDTypes pointing at template versions
        forEachRefDType(ownerModp, [&](AstRefDType* rdp) {
            if (!rdp) return;
            V3LinkDotDepGraph::DepNode* const rdpNode = V3LinkDotDepGraph::findMutable(rdp);
            if (!rdpNode) return;

            if (AstNodeUOrStructDType* const curp = VN_CAST(rdp->refDTypep(), NodeUOrStructDType)) {
                if (curp->name() == usp->name() && curp->width() != usp->width()) {
                    UINFO(5, "DEPGRAPH: deferred retarget RefDType '" << rdp->name()
                              << "' to specialized " << usp->prettyTypeName()
                              << " w" << usp->width() << endl);
                    rdpNode->deferredRefDTypep = usp;
                    rdpNode->needsNormalize = true;
                }
            }
            AstTypedef* const tdp = rdp->typedefp();
            if (rdp->refDTypep() == usp
                || (tdp && tdp->subDTypep() == usp)
                || (tdp && tdp->name() == usp->name())) {
                rdpNode->needsNormalize = true;
            }
        });
    }

    // Mark for normalizeRefTree in finalize pass
    V3LinkDotDepGraph::DepNode* const uspNode = V3LinkDotDepGraph::findMutable(usp);
    if (uspNode) {
        uspNode->needsNormalizeTree = true;
    }
}

static void commitTypedef(V3LinkDotDepGraph::DepNode* nodep) {
    if (!nodep || !nodep->nodep) return;
    AstTypedef* const tdp = VN_CAST(nodep->nodep, Typedef);
    AstNodeModule* const ownerModp = nodep->ownerModp;
    if (!tdp || !ownerModp) return;

    UINFO(5, "DEPGRAPH: commit TYPEDEF node='" << tdp->name()
              << "' typedefp=" << tdp
              << " ptr=" << static_cast<const void*>(tdp)
              << " owner='" << ownerModp->name()
              << "' backp=" << tdp->backp()
              << " backpPtr=" << static_cast<const void*>(tdp->backp())
              << " dtypep=" << tdp->dtypep()
              << " dtypepPtr=" << static_cast<const void*>(tdp->dtypep())
              << " childDTypep=" << tdp->childDTypep()
              << " childDTypepPtr=" << static_cast<const void*>(tdp->childDTypep())
              << endl);

    // For specialized modules, check if the typedef's CLASSREFDTYPE needs to be updated
    // to point to the correct specialized class based on the owner's type parameter bindings.
    // This handles cases like: typedef uvm_object_registry#(uvm_object_string_pool#(T)) type_id;
    // where T has been substituted with a concrete type.
    const bool isSpecialized = ownerModp->name().find("__") != string::npos;
    if (isSpecialized) {
        // Use dtypep() not childDTypep() - the typedef's type is stored in dtypep
        if (AstClassRefDType* const crdtp = VN_CAST(tdp->dtypep(), ClassRefDType)) {
            if (AstClass* const currentClassp = crdtp->classp()) {
                const string currentClassName = currentClassp->name();
                const string currentOrigName = currentClassp->origName();

                // Get the owner module's base name
                string ownerBaseName = ownerModp->origName();
                if (ownerBaseName.empty()) {
                    ownerBaseName = ownerModp->name();
                    const size_t pos = ownerBaseName.find("__");
                    if (pos != string::npos) ownerBaseName = ownerBaseName.substr(0, pos);
                }

                AstClass* foundNewClassp = nullptr;

                // Case 1: this_type pattern - typedef points to the same base class as owner
                // e.g., in uvm_object_registry__Tz3: typedef uvm_object_registry#(T) this_type;
                // The typedef should point to uvm_object_registry__Tz3 itself
                if (currentOrigName == ownerBaseName) {
                    if (AstClass* const ownerClassp = VN_CAST(ownerModp, Class)) {
                        if (ownerClassp != currentClassp) {
                            foundNewClassp = ownerClassp;
                            UINFO(5, "DEPGRAPH: commit TYPEDEF '" << tdp->name()
                                      << "' this_type pattern: updating from '"
                                      << currentClassName << "' to '"
                                      << foundNewClassp->name() << "' in "
                                      << ownerModp->name() << endl);
                        }
                    }
                }

                // Case 2: type_id pattern - typedef points to a different class parameterized with owner
                // e.g., in uvm_object_string_pool__Tz2: typedef uvm_object_registry#(uvm_object_string_pool#(T)) type_id;
                // Need to find uvm_object_registry specialized with T=uvm_object_string_pool__Tz2
                if (!foundNewClassp) {
                    V3LinkDotDepGraph::forEach([&](const V3LinkDotDepGraph::DepNode& candNode) {
                        if (foundNewClassp) return;  // Already found
                        if (candNode.nodeType != V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE) return;
                        AstParamTypeDType* const candPtdp = VN_CAST(candNode.nodep, ParamTypeDType);
                        if (!candPtdp || candPtdp->name() != "T") return;
                        if (!candNode.ownerModp) return;

                        // Check if this is a specialization of the same base class as current
                        const string candOwnerName = candNode.ownerModp->name();
                        if (candOwnerName.find(currentOrigName + "__") == string::npos) return;

                        // Check if the T parameter is bound to our owner module type
                        if (AstClassRefDType* const boundCrdtp
                            = VN_CAST(candPtdp->subDTypep(), ClassRefDType)) {
                            if (AstClass* const boundClassp = boundCrdtp->classp()) {
                                if (boundClassp->name() == ownerModp->name()) {
                                    // Found a match
                                    if (AstClass* const newClassp
                                        = VN_CAST(candNode.ownerModp, Class)) {
                                        if (newClassp != currentClassp) {
                                            foundNewClassp = newClassp;
                                        }
                                    }
                                }
                            }
                        }
                    });
                    if (foundNewClassp) {
                        UINFO(5, "DEPGRAPH: commit TYPEDEF '" << tdp->name()
                                  << "' type_id pattern: updating from '"
                                  << currentClassName << "' to '"
                                  << foundNewClassp->name() << "' in "
                                  << ownerModp->name() << endl);
                    }
                }

                if (foundNewClassp) {
                    crdtp->classp(foundNewClassp);
                    // Also update the typedef-class mapping
                    V3LinkDotDepGraph::registerTypedefClass(tdp, foundNewClassp, ownerModp);
                }
            }
        }
    }

    // Check if this is a template typedef
    const bool isTemplate = ownerModp->hasGParam()
                            && ownerModp->name().find("__") == string::npos;

    // For template typedefs, find the specialized clone to retarget RefDTypes
    AstTypedef* specializedTdp = nullptr;
    AstNodeModule* specializedOwnerp = nullptr;
    if (isTemplate) {
        specializedTdp = V3LinkDotDepGraph::findSpecializedTypedef(tdp->name(), &specializedOwnerp);
        if (specializedTdp && specializedOwnerp) {
            UINFO(5, "DEPGRAPH: found specialized typedef '" << tdp->name()
                      << "' in '" << specializedOwnerp->name()
                      << "' for template in '" << ownerModp->name() << "'" << endl);
        }
    }

    for (V3LinkDotDepGraph::DepNode* const depNodep : nodep->dependents) {
        if (!depNodep || depNodep->nodeType != V3LinkDotDepGraph::NodeType::REFDTYPE) continue;
        if (AstRefDType* const rdp = VN_CAST(depNodep->nodep, RefDType)) {
            // For template typedefs, store deferred retarget to specialized
            if (isTemplate && specializedTdp && depNodep->ownerModp
                && depNodep->ownerModp->name().find("__") != string::npos) {
                UINFO(5, "DEPGRAPH: deferred retarget TYPEDEF dep RefDType '" << rdp->name()
                          << "' from template '" << ownerModp->name()
                          << "' to specialized '" << specializedOwnerp->name() << "'" << endl);
                depNodep->deferredTypedefp = specializedTdp;
                depNodep->deferredClassOwnerp = specializedOwnerp;
            }
            depNodep->needsNormalize = true;
        }
    }
    for (V3LinkDotDepGraph::DepNode* const depNodep : nodep->dependsOn) {
        if (!depNodep || depNodep->nodeType != V3LinkDotDepGraph::NodeType::REFDTYPE) continue;
        depNodep->needsNormalize = true;
    }
    // Mark for normalizeRefTree in finalize pass
    nodep->needsNormalizeTree = true;
}

static void commitParamType(V3LinkDotDepGraph::DepNode* nodep) {
    if (!nodep || !nodep->nodep) return;
    AstParamTypeDType* const ptdp = VN_CAST(nodep->nodep, ParamTypeDType);
    AstNodeModule* const ownerModp = nodep->ownerModp;
    if (!ptdp || !ownerModp) return;

    UINFO(0, "DEPGRAPH: commitParamType " << ptdp->name() << " in " << ownerModp->name()
              << " subDTypep=" << (ptdp->subDTypep() ? ptdp->subDTypep()->prettyTypeName() : "null")
              << " dependsOn=" << nodep->dependsOn.size() << endl);

    // Handle REQUIREDTYPE resolution for interface typedefs (applies to ALL modules)
    // This must happen before V3Width runs on dependent nodes
    if (AstRequireDType* const reqp = VN_CAST(ptdp->subDTypep(), RequireDType)) {
        UINFO(0, "DEPGRAPH: commitParamType " << ptdp->name() << " has REQUIREDTYPE" << endl);
        // Find the resolved typedef from our dependency edge
        for (V3LinkDotDepGraph::DepNode* const depNodep : nodep->dependsOn) {
            UINFO(0, "DEPGRAPH: checking dependency TYPEDEF=" << (depNodep->nodeType == V3LinkDotDepGraph::NodeType::TYPEDEF) << endl);
            if (!depNodep || depNodep->nodeType != V3LinkDotDepGraph::NodeType::TYPEDEF) continue;
            AstTypedef* const tdp = VN_CAST(depNodep->nodep, Typedef);
            if (!tdp || !tdp->subDTypep()) continue;
            // Found the target typedef - delete REQUIREDTYPE and set dtypep to resolved type
            AstNodeDType* const resolvedTypep = tdp->subDTypep();
            UINFO(0, "DEPGRAPH: commit PARAMTYPE '" << ptdp->name()
                      << "' resolving REQUIREDTYPE to " << resolvedTypep->prettyTypeName()
                      << " from typedef '" << tdp->name() << "' in " << ownerModp->name() << endl);
            // Delete the REQUIREDTYPE child - don't replace, just remove
            reqp->unlinkFrBack();
            VL_DO_DANGLING(reqp->deleteTree(), reqp);
            // Set dtypep to the original resolved type (not a clone)
            // This makes PARAMTYPEDTYPE reference the interface's type directly
            ptdp->dtypep(resolvedTypep);
            ptdp->widthForce(resolvedTypep->width(), resolvedTypep->widthMin());
            break;
        }
    }

    // Apply deferred DType and child clear immediately during commit
    // This is needed if dependent nodes (like structs) need to see the resolved type immediately
    if (nodep->deferredDTypep || nodep->deferredNeedsChildDTypeClear) {
        UINFO(5, "DEPGRAPH: commitParamType applying deferred dtype/clear for " << ptdp->name() << endl);

        if (nodep->deferredDTypep) {
            ptdp->dtypep(nodep->deferredDTypep);
        }

        if (nodep->deferredNeedsChildDTypeClear) {
            if (AstNodeDType* const childp = ptdp->getChildDTypep()) {
                AstNodeDType* newChildp = nullptr;
                // If the new type is inside the child we are about to delete (e.g. unwrapping REQUIREDTYPE),
                // we must rescue it and make it the new child to preserve ownership.
                if (nodep->deferredDTypep && nodep->deferredDTypep->backp() == childp) {
                    newChildp = nodep->deferredDTypep;
                    newChildp->unlinkFrBack();
                }

                if (childp->backp() == ptdp) {
                    // Child is owned by this node - safe to delete
                    childp->unlinkFrBack();
                    VL_DO_DANGLING(childp->deleteTree(), childp);
                }
                ptdp->childDTypep(newChildp);
            }
        }

        // Clear flags so finalizeParamType doesn't redo it
        nodep->deferredDTypep = nullptr;
        nodep->deferredNeedsChildDTypeClear = false;
    }

    const bool isSpecialized = ownerModp->name().find("__") != string::npos;
    if (!isSpecialized) return;

    // Apply deferred width immediately during commit so dependent nodes see it.
    // This is needed because LPARAM nodes call widthParamsEdit during execute,
    // which needs the PARAMTYPEDTYPE's width to be correct.
    if (nodep->resolvedWidth > 0 && ptdp->width() != nodep->resolvedWidth) {
        UINFO(5, "DEPGRAPH: commit apply PARAMTYPEDTYPE '" << ptdp->name()
                  << "' width " << ptdp->width() << " -> " << nodep->resolvedWidth
                  << " in " << ownerModp->name() << endl);
        ptdp->widthForce(nodep->resolvedWidth, nodep->resolvedWidth);
    }

    // Get resolved width from subDTypep or from dependency chain
    AstNodeDType* const subp = ptdp->subDTypep();
    int resolvedWidth = subp ? subp->width() : ptdp->width();

    // If subDTypep has width=0, try to get width from dependency chain
    // The dependency (TYPEDEF/REFDTYPE) should have the resolved width from the struct
    if (resolvedWidth <= 0) {
        for (V3LinkDotDepGraph::DepNode* const depNodep : nodep->dependsOn) {
            if (!depNodep || !depNodep->nodep) continue;
            AstNodeDType* depDTypep = nullptr;
            if (depNodep->nodeType == V3LinkDotDepGraph::NodeType::TYPEDEF) {
                if (AstTypedef* const tdp = VN_CAST(depNodep->nodep, Typedef)) {
                    depDTypep = tdp->subDTypep();
                }
            } else if (depNodep->nodeType == V3LinkDotDepGraph::NodeType::REFDTYPE) {
                depDTypep = VN_CAST(depNodep->nodep, RefDType);
            } else if (depNodep->nodeType == V3LinkDotDepGraph::NodeType::STRUCTDTYPE) {
                depDTypep = VN_CAST(depNodep->nodep, NodeUOrStructDType);
            }
            if (depDTypep) {
                AstNodeDType* const skipped = depDTypep->skipRefp();
                const int depWidth = skipped ? skipped->width() : depDTypep->width();
                if (depWidth > 0) {
                    resolvedWidth = depWidth;
                    UINFO(5, "DEPGRAPH: commitParamType '" << ptdp->name()
                              << "' got width " << resolvedWidth << " from dependency" << endl);
                    // Update the PARAMTYPEDTYPE's width
                    ptdp->widthForce(resolvedWidth, resolvedWidth);
                    break;
                }
            }
        }
    }

    if (resolvedWidth <= 0) return;

    // Store deferred retargets for RefDTypes
    forEachRefDType(ownerModp, [&](AstRefDType* rdp) {
        if (!rdp) return;
        AstNodeModule* const rdpOwnerp = V3LinkDotDepGraph::findOwnerModule(rdp);
        if (!rdpOwnerp || rdpOwnerp != ownerModp) return;
        V3LinkDotDepGraph::DepNode* const rdpNode = V3LinkDotDepGraph::findMutable(rdp);
        if (!rdpNode) return;

        if (AstParamTypeDType* const curp = VN_CAST(rdp->refDTypep(), ParamTypeDType)) {
            AstNodeDType* const curSubp = curp->subDTypep();
            const int curWidth = curSubp ? curSubp->width() : curp->width();
            if (curp->name() == ptdp->name() && resolvedWidth > curWidth) {
                UINFO(5, "DEPGRAPH: deferred retarget RefDType '" << rdp->name()
                          << "' to specialized PARAMTYPEDTYPE w" << resolvedWidth << endl);
                rdpNode->deferredRefDTypep = ptdp;
                rdpNode->needsNormalize = true;
            }
        }
    });

    // Find target typedef for retargeting
    AstTypedef* targetTdp = nullptr;
    AstNodeModule* targetOwnerp = nullptr;
    for (V3LinkDotDepGraph::DepNode* const depNodep : nodep->dependsOn) {
        if (!depNodep || depNodep->nodeType != V3LinkDotDepGraph::NodeType::TYPEDEF) continue;
        AstTypedef* const candTdp = VN_CAST(depNodep->nodep, Typedef);
        if (!candTdp || candTdp->name() != ptdp->name()) continue;
        if (depNodep->ownerModp && depNodep->ownerModp->name().find("__") != string::npos) {
            targetTdp = candTdp;
            targetOwnerp = depNodep->ownerModp;
            break;
        }
    }

    // Store deferred typedef retargets
    if (targetTdp) {
        forEachRefDType(ownerModp, [&](AstRefDType* rdp) {
            if (!rdp || rdp->name() != ptdp->name()) return;
            AstTypedef* const currentTdp = rdp->typedefp();
            if (!currentTdp) return;
            AstNodeModule* const currentOwnerp = V3LinkDotDepGraph::findOwnerModule(currentTdp);
            if (!currentOwnerp || currentOwnerp->name().find("__") != string::npos) return;
            V3LinkDotDepGraph::DepNode* const rdpNode = V3LinkDotDepGraph::findMutable(rdp);
            if (!rdpNode) return;
            UINFO(5, "DEPGRAPH: deferred retarget RefDType '" << rdp->name()
                      << "' typedefp from '" << currentOwnerp->name()
                      << "' to '" << targetOwnerp->name() << "'" << endl);
            rdpNode->deferredTypedefp = targetTdp;
            rdpNode->deferredClassOwnerp = targetOwnerp;
            rdpNode->needsNormalize = true;
        });
    }

    // Store deferred child RefDType retarget
    if (AstRefDType* const childRdp = VN_CAST(ptdp->childDTypep(), RefDType)) {
        AstTypedef* const childTdp = childRdp->typedefp();
        if (childTdp) {
            AstNodeModule* const childTdOwnerp = V3LinkDotDepGraph::findOwnerModule(childTdp);
            if (childTdOwnerp && childTdOwnerp->hasGParam()
                && childTdOwnerp->name().find("__") == string::npos) {
                V3LinkDotDepGraph::DepNode* const childRdpNode = V3LinkDotDepGraph::findMutable(childRdp);
                if (childRdpNode) {
                    if (targetTdp) {
                        UINFO(5, "DEPGRAPH: deferred retarget PARAMTYPE child RefDType '" << childRdp->name()
                                  << "' typedefp from '" << childTdOwnerp->name()
                                  << "' to '" << targetOwnerp->name() << "'" << endl);
                        childRdpNode->deferredTypedefp = targetTdp;
                        childRdpNode->deferredClassOwnerp = targetOwnerp;
                    }
                    childRdpNode->needsNormalize = true;
                }
            }
        }
    }
}

// ATTROF nodes don't need special commit handling - V3Width handles the replacement
static void commitAttrOf(V3LinkDotDepGraph::DepNode* nodep) {
    if (!nodep || !nodep->nodep) return;
    AstAttrOf* const attrp = VN_CAST(nodep->nodep, AttrOf);
    if (!attrp) return;

    // Just log for debugging - V3Width will handle the actual replacement
    UINFO(9, "DEPGRAPH: commit ATTROF '" << attrp->attrType().ascii() << "'" << endl);
}

static void commitResolvedNode(V3LinkDotDepGraph::DepNode* nodep) {
    if (!nodep || !nodep->nodep) return;
    if (nodep->nodeType == V3LinkDotDepGraph::NodeType::REFDTYPE) {
        commitRefDType(nodep);
    } else if (nodep->nodeType == V3LinkDotDepGraph::NodeType::GPARAM) {
        commitGParam(nodep);
    } else if (nodep->nodeType == V3LinkDotDepGraph::NodeType::LPARAM) {
        commitLParam(nodep);
    } else if (nodep->nodeType == V3LinkDotDepGraph::NodeType::TYPEDEF) {
        commitTypedef(nodep);
    } else if (nodep->nodeType == V3LinkDotDepGraph::NodeType::STRUCTDTYPE
               || nodep->nodeType == V3LinkDotDepGraph::NodeType::UNIONDTYPE) {
        commitStructUnion(VN_CAST(nodep->nodep, NodeUOrStructDType), nodep->ownerModp);
    } else if (nodep->nodeType == V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE) {
        commitParamType(nodep);
    } else if (nodep->nodeType == V3LinkDotDepGraph::NodeType::ATTROF) {
        commitAttrOf(nodep);
    }
}

void V3LinkDotDepGraph::addEdge(DepNode* from, DepNode* to) {
    if (!from || !to) return;
    if (from == to) {
        UINFO(5, "DEPGRAPH: skip self-edge '" << nodeName(from) << "'@" << nodeOwnerName(from)
                  << " type=" << nodeTypeName(from->nodeType) << " nodep=" << from->nodep << endl);
        return;
    }
    from->dependsOn.insert(to);
    to->dependents.insert(from);
    UINFO(9, "DEPGRAPH: edge '" << nodeName(from) << "'@" << nodeOwnerName(from)
              << " type=" << nodeTypeName(from->nodeType) << " nodep=" << from->nodep
              << " --> '" << nodeName(to) << "'@" << nodeOwnerName(to)
              << " type=" << nodeTypeName(to->nodeType) << " nodep=" << to->nodep << endl);
    if (from->nodeType == NodeType::PARAMTYPEDTYPE
        && (to->nodeType == NodeType::PARAMTYPEDTYPE || to->nodeType == NodeType::TYPEDEF)) {
        UINFO(5, "DEPGRAPH: paramtype edge '" << nodeName(from) << "'@" << nodeOwnerName(from)
                    << " cell='" << from->cellName << "' -> '" << nodeName(to) << "'@"
                    << nodeOwnerName(to) << " type=" << nodeTypeName(to->nodeType)
                    << " cell='" << to->cellName << "'" << endl);
    }
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
        AstNodeModule* ownerp = V3LinkDotDepGraph::findOwnerModule(nodep);
        // For cloned RefDTypes (not attached to AST), use depNode's owner as fallback
        if (!ownerp && m_depNode && m_depNode->ownerModp) ownerp = m_depNode->ownerModp;
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
            if (m_depNode && m_depNode->ownerModp) {
                const bool isTemplateOwner = ptOwnerp && ptOwnerp->hasGParam()
                                            && ptOwnerp->name().find("__") == string::npos;
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
                V3LinkDotDepGraph::DepNode* const ptNodep
                    = V3LinkDotDepGraph::findOrCreateNode(
                        targetPtdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, ptOwnerp);
                // Skip edge if REFDTYPE is child of the PARAMTYPE (would create cycle)
                const bool isSelfRef = (m_depNode && m_depNode->nodep == targetPtdp);
                if (!isSelfRef) {
                    V3LinkDotDepGraph::addEdge(targetp, ptNodep);
                    UINFO(5, "DEPGRAPH: refdtype '" << nodep->name() << "' -> paramtype '"
                              << targetPtdp->name() << "' in "
                              << (ptOwnerp ? ptOwnerp->name() : "<null>")
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
        if (ownerp) {
            V3LinkDotDepGraph::DepNode* const attrNodep
                = V3LinkDotDepGraph::findOrCreateNode(
                    nodep, V3LinkDotDepGraph::NodeType::ATTROF, ownerp);
            V3LinkDotDepGraph::addEdge(m_depNode, attrNodep);
            UINFO(5, "DEPGRAPH: expr depends on ATTROF '" << nodep->attrType().ascii()
                      << "' in " << ownerp->name() << endl);

            // Also add edge from ATTROF to its source REFDTYPE (for captured expressions)
            if (AstRefDType* const rdp = VN_CAST(nodep->fromp(), RefDType)) {
                AstNodeModule* rdpOwnerp = V3LinkDotDepGraph::findOwnerModule(rdp);
                if (!rdpOwnerp) rdpOwnerp = ownerp;
                V3LinkDotDepGraph::DepNode* const rdpNodep
                    = V3LinkDotDepGraph::findOrCreateNode(
                        rdp, V3LinkDotDepGraph::NodeType::REFDTYPE, rdpOwnerp);
                V3LinkDotDepGraph::addEdge(attrNodep, rdpNodep);
                UINFO(5, "DEPGRAPH: ATTROF '" << nodep->attrType().ascii()
                          << "' depends on REFDTYPE '" << rdp->name()
                          << "' in " << rdpOwnerp->name() << endl);

                // Also add edge from REFDTYPE to PARAMTYPEDTYPE if applicable
                if (AstParamTypeDType* const ptdp = VN_CAST(rdp->refDTypep(), ParamTypeDType)) {
                    AstNodeModule* ptdOwnerp = V3LinkDotDepGraph::findOwnerModule(ptdp);
                    if (!ptdOwnerp) ptdOwnerp = rdpOwnerp;
                    V3LinkDotDepGraph::DepNode* const ptdNodep
                        = V3LinkDotDepGraph::findOrCreateNode(
                            ptdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, ptdOwnerp);
                    V3LinkDotDepGraph::addEdge(rdpNodep, ptdNodep);
                    UINFO(5, "DEPGRAPH: REFDTYPE '" << rdp->name()
                              << "' depends on PARAMTYPEDTYPE '" << ptdp->name()
                              << "' in " << ptdOwnerp->name() << endl);
                }
            }
        }
        // Don't iterate children - the ATTROF node handles its own dependencies
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
        // Template modules have GParams but no specialization suffix. Top modules must
        // still be visited/resolved, even if parameterized, since there is no clone.
        if (nodep->dead()) return;
        if (!nodep->isTop() && nodep->hasGParam() && nodep->name().find("__") == string::npos) {
            UINFO(9, "DEPGRAPH: skip template module " << nodep->name() << endl);
            // Cleanup RefDTypes in template modules to avoid dangling typedefp after V3Dead
            normalizeRefTree(nodep, "template-skip");
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
                        // Relink RefDTypes to PARAMTYPEDTYPEs in the specialized module
                        clonedExprp->foreach([&](AstRefDType* rdp) {
                            for (AstNode* stmtp = m_modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                                if (AstParamTypeDType* const ptdp = VN_CAST(stmtp, ParamTypeDType)) {
                                    if (ptdp->name() == rdp->name()) {
                                        UINFO(5, "DEPGRAPH: relinked RefDType '" << rdp->name()
                                                  << "' to PARAMTYPEDTYPE in " << m_modp->name() << endl);
                                        rdp->refDTypep(ptdp);
                                        rdp->typedefp(nullptr);
                                        ++relinkedRefs;
                                        break;
                                    }
                                }
                            }
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
                    // Relink RefDTypes to PARAMTYPEDTYPEs in the specialized module
                    clonedExprp->foreach([&](AstRefDType* rdp) {
                        // Look for PARAMTYPEDTYPE with matching name in specialized module
                        for (AstNode* stmtp = m_modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                            if (AstParamTypeDType* const ptdp = VN_CAST(stmtp, ParamTypeDType)) {
                                if (ptdp->name() == rdp->name()) {
                                    UINFO(5, "DEPGRAPH: relinked RefDType '" << rdp->name()
                                              << "' to PARAMTYPEDTYPE in " << m_modp->name() << endl);
                                    rdp->refDTypep(ptdp);
                                    rdp->typedefp(nullptr);
                                    ++relinkedRefs;
                                    break;
                                }
                            }
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
        }

        // Also collect dependencies from the dtype (e.g., localparam tm_region_t foo = ...)
        // The localparam depends on the PARAMTYPEDTYPE for its type.
        if (AstNodeDType* const dtypep = nodep->dtypep()) {
            if (AstRefDType* const rdtp = VN_CAST(dtypep, RefDType)) {
                if (AstParamTypeDType* const ptdp = VN_CAST(rdtp->refDTypep(), ParamTypeDType)) {
                    AstNodeModule* const ptdOwnerp = V3LinkDotDepGraph::findOwnerModule(ptdp);
                    V3LinkDotDepGraph::DepNode* const ptdNodep
                        = V3LinkDotDepGraph::findOrCreateNode(
                            ptdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, ptdOwnerp);
                    V3LinkDotDepGraph::addEdge(depNodep, ptdNodep);
                    UINFO(5, "DEPGRAPH: param '" << nodep->name() << "' depends on paramtype '"
                              << ptdp->name() << "' in " << (ptdOwnerp ? ptdOwnerp->name() : "<null>") << endl);
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
                deps << V3LinkDotDepGraph::nodeName(dep)
                     << "@" << V3LinkDotDepGraph::nodeOwnerName(dep);
            }
            UINFO(5, "DEPGRAPH: deps for '" << nodep->name() << "'@" << m_modp->name()
                      << " = [" << deps.str() << "]" << endl);
        }
    }

    void visit(AstTypedef* nodep) override {
        if (!m_modp) return;

        V3LinkDotDepGraph::DepNode* const depNodep
            = V3LinkDotDepGraph::findOrCreateNode(nodep, V3LinkDotDepGraph::NodeType::TYPEDEF, m_modp);

        if (nodep->name() == "type_id") {
            AstRefDType* const childRefp = VN_CAST(nodep->subDTypep(), RefDType);
            const bool scopedHit = childRefp
                                  && s_refDTypeScopedTypedefs.find(childRefp)
                                         != s_refDTypeScopedTypedefs.end();
            UINFO(5, "DEPGRAPH: typedef type_id in "
                      << (m_modp ? m_modp->name() : "<null>")
                      << " child_ref=" << (childRefp ? childRefp->name() : "<none>")
                      << " scoped_hit=" << (scopedHit ? "yes" : "no") << endl);
            const auto tdIt = s_typedefScopedTypedefs.find(nodep);
            if (tdIt != s_typedefScopedTypedefs.end()) {
                AstTypedef* const scopeTdp = tdIt->second;
                AstNodeModule* const tdOwnerp = V3LinkDotDepGraph::findOwnerModule(scopeTdp);
                V3LinkDotDepGraph::DepNode* const tdNodep
                    = V3LinkDotDepGraph::findOrCreateNode(
                        scopeTdp, V3LinkDotDepGraph::NodeType::TYPEDEF, tdOwnerp);
                V3LinkDotDepGraph::addEdge(depNodep, tdNodep);
                UINFO(5, "DEPGRAPH: typedef type_id edge to scoped typedef '" << scopeTdp->name()
                          << "' in " << (tdOwnerp ? tdOwnerp->name() : "<null>") << endl);
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
            UINFO(5, "DEPGRAPH: typedef '" << nodep->name() << "' subDTypep="
                      << (dtypep ? dtypep->prettyTypeName() : "<null>")
                      << " type=" << (dtypep ? dtypep->typeName() : "<null>") << endl);
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
                    UINFO(5, "DEPGRAPH: typedef '" << nodep->name() << "' checking member '"
                              << memp->name() << "' subDTypep="
                              << (memDTypep ? memDTypep->prettyTypeName() : "<null>") << endl);
                    if (AstRefDType* const refp = VN_CAST(memDTypep, RefDType)) {
                        V3LinkDotDepGraph::DepNode* const refNodep
                            = V3LinkDotDepGraph::findOrCreateNode(
                                refp, V3LinkDotDepGraph::NodeType::REFDTYPE, m_modp);
                        V3LinkDotDepGraph::addEdge(uspNodep, refNodep);

                        // If the RefDType points to a PARAMTYPEDTYPE, add direct edge to it.
                        // This ensures the struct waits for the PARAMTYPEDTYPE to be resolved.
                        AstNodeDType* const targetp = refp->refDTypep();
                        UINFO(5, "DEPGRAPH: typedef '" << nodep->name() << "' member '" << memp->name()
                                  << "' targetp=" << (targetp ? targetp->prettyTypeName() : "<null>")
                                  << " type=" << (targetp ? targetp->typeName() : "<null>") << endl);
                        if (AstParamTypeDType* const ptdp = VN_CAST(targetp, ParamTypeDType)) {
                            AstNodeModule* const ptdOwnerp = V3LinkDotDepGraph::findOwnerModule(ptdp);
                            V3LinkDotDepGraph::DepNode* const ptdNodep = V3LinkDotDepGraph::findOrCreateNode(
                                ptdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, ptdOwnerp ? ptdOwnerp : m_modp);
                            V3LinkDotDepGraph::addEdge(uspNodep, ptdNodep);
                            UINFO(5, "DEPGRAPH: typedef '" << nodep->name() << "' struct member '"
                                      << memp->name() << "' -> PARAMTYPEDTYPE '" << ptdp->name() << "'" << endl);
                        }

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

        // Traverse the default type to collect dependencies (e.g. ranges using other params)
        if (nodep->subDTypep()) {
            if (nodep->name() == "T") {
                 UINFO(0, "DEPGRAPH: DEBUG: visit ParamTypeDType 'T' in " << m_modp->name() << " collecting deps from subDTypep\n");
            }
            V3LinkDotDepGraph::collectExpressionDeps(nodep->subDTypep(), depNodep, m_modp);
        } else {
            if (nodep->name() == "T") {
                 UINFO(0, "DEPGRAPH: DEBUG: visit ParamTypeDType 'T' in " << m_modp->name() << " has NO subDTypep\n");
            }
        }

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
                                // Only match paramtypes owned by the current module to avoid
                                // cross-module name collisions (e.g., class-local T vs module T).
                                if (pair.second->ownerModp != m_modp) continue;
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
                    V3LinkDotDepGraph::addEdge(depNodep, tdNodep);
                    UINFO(5, "DEPGRAPH: added edge from paramtype '"
                              << nodep->name() << "' to typedef '"
                              << typedefName << "' in " << targetModp->name() << endl);
                } else if (targetPtdp && targetModp) {
                    V3LinkDotDepGraph::DepNode* const ptdNodep
                        = V3LinkDotDepGraph::findOrCreateNode(
                            targetPtdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, targetModp);
                    V3LinkDotDepGraph::addEdge(depNodep, ptdNodep);
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

        // findOrCreateNode handles registry lookup for cellName
        V3LinkDotDepGraph::DepNode* const depNodep
            = V3LinkDotDepGraph::findOrCreateNode(nodep, V3LinkDotDepGraph::NodeType::REFDTYPE, m_modp);

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

            V3LinkDotDepGraph::DepNode* const ptdNodep = V3LinkDotDepGraph::findOrCreateNode(
                targetPtdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, ptdOwnerp);
            V3LinkDotDepGraph::addEdge(depNodep, ptdNodep);
        }

        // If this RefDType has an explicit class/package scope, add edge to that typedef/paramtype
        if (AstClassOrPackageRef* const scopeRefp
            = VN_CAST(nodep->classOrPackageOpp(), ClassOrPackageRef)) {
            if (AstTypedef* const scopeTdp
                = VN_CAST(scopeRefp->classOrPackageNodep(), Typedef)) {
                AstNodeModule* const tdOwnerp = V3LinkDotDepGraph::findOwnerModule(scopeTdp);
                V3LinkDotDepGraph::DepNode* const tdNodep
                    = V3LinkDotDepGraph::findOrCreateNode(
                        scopeTdp, V3LinkDotDepGraph::NodeType::TYPEDEF, tdOwnerp);
                V3LinkDotDepGraph::addEdge(depNodep, tdNodep);
                UINFO(5, "DEPGRAPH: refdtype '" << nodep->name()
                          << "' scoped by typedef '" << scopeTdp->name()
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
                                    candTdp, V3LinkDotDepGraph::NodeType::TYPEDEF, tdOwnerp);
                            V3LinkDotDepGraph::addEdge(depNodep, tdNodep);
                            UINFO(5, "DEPGRAPH: refdtype '" << nodep->name()
                                      << "' scoped by class '" << scopeClassp->name()
                                      << "' typedef '" << candTdp->name() << "'" << endl);
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
                UINFO(5, "DEPGRAPH: refdtype '" << nodep->name()
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
                          << (m_modp ? m_modp->name() : "<null>")
                          << " refdtype='" << nodep->name() << "'"
                          << " parent='" << parentTdp->name() << "'"
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
                V3LinkDotDepGraph::DepNode* const tdNodep
                    = V3LinkDotDepGraph::findOrCreateNode(
                        scopeTdp, V3LinkDotDepGraph::NodeType::TYPEDEF, tdOwnerp);
                V3LinkDotDepGraph::addEdge(depNodep, tdNodep);
                UINFO(5, "DEPGRAPH: refdtype '" << nodep->name()
                          << "' scoped by registered typedef '" << scopeTdp->name()
                          << "' in " << (tdOwnerp ? tdOwnerp->name() : "<null>") << endl);
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

        // Add dependency edges to member types.
        // The struct's width depends on its members' widths, so we need edges to:
        // 1. Member's RefDType
        // 2. Member's PARAMTYPEDTYPE (if the RefDType points to one)
        for (AstMemberDType* memp = nodep->membersp(); memp;
             memp = VN_AS(memp->nextp(), MemberDType)) {
            if (AstRefDType* const refp = VN_CAST(memp->subDTypep(), RefDType)) {
                AstNodeModule* const refOwnerp = V3LinkDotDepGraph::findOwnerModule(refp);
                V3LinkDotDepGraph::DepNode* const refNodep = V3LinkDotDepGraph::findOrCreateNode(
                    refp, V3LinkDotDepGraph::NodeType::REFDTYPE, refOwnerp ? refOwnerp : m_modp);
                V3LinkDotDepGraph::addEdge(depNodep, refNodep);

                // If the RefDType points to a PARAMTYPEDTYPE, add direct edge to it.
                // This ensures the struct waits for the PARAMTYPEDTYPE to be resolved.
                AstNodeDType* const targetp = refp->refDTypep();
                if (AstParamTypeDType* const ptdp = VN_CAST(targetp, ParamTypeDType)) {
                    AstNodeModule* const ptdOwnerp = V3LinkDotDepGraph::findOwnerModule(ptdp);
                    V3LinkDotDepGraph::DepNode* const ptdNodep = V3LinkDotDepGraph::findOrCreateNode(
                        ptdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, ptdOwnerp ? ptdOwnerp : m_modp);
                    V3LinkDotDepGraph::addEdge(depNodep, ptdNodep);
                    UINFO(5, "DEPGRAPH: struct '" << nodep->name() << "' member '" << memp->name()
                              << "' -> PARAMTYPEDTYPE '" << ptdp->name() << "'" << endl);
                }

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
                    V3LinkDotDepGraph::DepNode* const ptdNodep = V3LinkDotDepGraph::findOrCreateNode(
                        ptdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, ptdOwnerp ? ptdOwnerp : m_modp);
                    V3LinkDotDepGraph::addEdge(depNodep, ptdNodep);
                    UINFO(5, "DEPGRAPH: union '" << nodep->name() << "' member '" << memp->name()
                              << "' -> PARAMTYPEDTYPE '" << ptdp->name() << "'" << endl);
                }

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

    void visit(AstAttrOf* nodep) override {
        if (!m_modp) return;
        // Only interested in dimension/bits attributes that depend on types
        if (nodep->attrType() != VAttrType::DIM_BITS
            && nodep->attrType() != VAttrType::DIM_DIMENSIONS
            && nodep->attrType() != VAttrType::DIM_HIGH
            && nodep->attrType() != VAttrType::DIM_LEFT
            && nodep->attrType() != VAttrType::DIM_LOW
            && nodep->attrType() != VAttrType::DIM_RIGHT
            && nodep->attrType() != VAttrType::DIM_SIZE
            && nodep->attrType() != VAttrType::DIM_UNPK_DIMENSIONS) {
            return;
        }

        // Create ATTROF node in the graph
        V3LinkDotDepGraph::DepNode* const depNodep
            = V3LinkDotDepGraph::findOrCreateNode(nodep, V3LinkDotDepGraph::NodeType::ATTROF, m_modp);

        // Add dependency on the fromp (typically a RefDType for $bits(type))
        if (AstRefDType* const rdp = VN_CAST(nodep->fromp(), RefDType)) {
            AstNodeModule* rdpOwnerp = V3LinkDotDepGraph::findOwnerModule(rdp);
            if (!rdpOwnerp) rdpOwnerp = m_modp;
            V3LinkDotDepGraph::DepNode* const rdpNodep = V3LinkDotDepGraph::findOrCreateNode(
                rdp, V3LinkDotDepGraph::NodeType::REFDTYPE, rdpOwnerp);
            V3LinkDotDepGraph::addEdge(depNodep, rdpNodep);
            UINFO(5, "DEPGRAPH: ATTROF '" << nodep->attrType().ascii()
                      << "' depends on REFDTYPE '" << rdp->name()
                      << "' in " << m_modp->name() << endl);

            // Also add edge from REFDTYPE to PARAMTYPEDTYPE if applicable
            if (AstParamTypeDType* const ptdp = VN_CAST(rdp->refDTypep(), ParamTypeDType)) {
                AstNodeModule* ptdOwnerp = V3LinkDotDepGraph::findOwnerModule(ptdp);
                if (!ptdOwnerp) ptdOwnerp = rdpOwnerp;
                V3LinkDotDepGraph::DepNode* const ptdNodep = V3LinkDotDepGraph::findOrCreateNode(
                    ptdp, V3LinkDotDepGraph::NodeType::PARAMTYPEDTYPE, ptdOwnerp);
                V3LinkDotDepGraph::addEdge(rdpNodep, ptdNodep);
                UINFO(5, "DEPGRAPH: REFDTYPE '" << rdp->name()
                          << "' depends on PARAMTYPEDTYPE '" << ptdp->name()
                          << "' in " << m_modp->name() << endl);
            }
        }

        // Also collect any expression dependencies from fromp/dimp
        V3LinkDotDepGraph::collectExpressionDeps(nodep->fromp(), depNodep, m_modp);
        V3LinkDotDepGraph::collectExpressionDeps(nodep->dimp(), depNodep, m_modp);
    }

    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    explicit DepGraphBuildVisitor(AstNetlist* netlistp) {
        iterateConst(netlistp);
    }
};

void V3LinkDotDepGraph::build(AstNetlist* netlistp) {
    UINFO(5, "DEPGRAPH: building dependency graph" << endl);
    reset();
    DepGraphBuildVisitor{netlistp};
    updateEdgesToSpecialized();
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
            nodep->pendingDeps = pending;
            UINFO(9, "DEPGRAPH: pendingDeps '" << nodeName(nodep) << "'@" << nodeOwnerName(nodep)
                      << " = " << nodep->pendingDeps << endl);
        }
    };
    recomputePendingDeps();
    UINFO(5, "DEPGRAPH: built " << s_allNodes.size() << " nodes" << endl);
}

// Update edges for REFDTYPE nodes that point to template nodes when specialized versions exist
void V3LinkDotDepGraph::updateEdgesToSpecialized() {
    int updatedEdges = 0;
    for (DepNode* nodep : s_allNodes) {
        if (!nodep || nodep->nodeType != NodeType::REFDTYPE) continue;
        if (!nodep->ownerModp) continue;

        // Check each dependency - if it points to a template, find specialized version
        std::set<DepNode*> newDeps;
        bool changed = false;

        for (DepNode* const depNodep : nodep->dependsOn) {
            if (!depNodep || !depNodep->ownerModp) {
                newDeps.insert(depNodep);
                continue;
            }

            // If this node is in a specialized module, retarget deps that still point
            // at the base module to the matching node in the specialized owner.
            const string ownerName = nodep->ownerModp->name();
            const size_t ownerSuffixPos = ownerName.find("__");
            if (ownerSuffixPos != string::npos) {
                const string baseOwnerName = ownerName.substr(0, ownerSuffixPos);
                if (depNodep->ownerModp->name() == baseOwnerName) {
                    DepNode* specializedOwnerNodep = nullptr;
                    const string nodeNameStr = nodeName(depNodep);
                    for (DepNode* const candp : s_allNodes) {
                        if (!candp || candp == depNodep) continue;
                        if (candp->nodeType != depNodep->nodeType) continue;
                        if (candp->ownerModp != nodep->ownerModp) continue;
                        if (nodeName(candp) != nodeNameStr) continue;
                        specializedOwnerNodep = candp;
                        break;
                    }
                    if (specializedOwnerNodep) {
                        newDeps.insert(specializedOwnerNodep);
                        changed = true;
                        UINFO(5, "DEPGRAPH: updated edge from '" << nodeName(nodep)
                                  << "'@" << nodep->ownerModp->name()
                                  << " to specialized owner '" << nodeName(specializedOwnerNodep)
                                  << "'@" << specializedOwnerNodep->ownerModp->name()
                                  << " (was base @" << depNodep->ownerModp->name() << ")" << endl);
                        ++updatedEdges;
                        continue;
                    }
                }
            }

            // Check if dependency is to a template module
            const bool isTemplate = depNodep->ownerModp->hasGParam()
                                    && depNodep->ownerModp->name().find("__") == string::npos;
            if (!isTemplate) {
                newDeps.insert(depNodep);
                continue;
            }

            // Search for specialized version of this node
            DepNode* specializedNodep = nullptr;
            const string templateBaseName = depNodep->ownerModp->name();
            const string nodeNameStr = nodeName(depNodep);

            // If the REFDTYPE has a cellName, use it to find the correct specialization
            // by looking up which specialized module the cell instantiates
            string targetSpecSuffix;
            if (!nodep->cellName.empty() && nodep->ownerModp) {
                // Find the cell in the owner module and get its specialized module
                for (AstNode* stmtp = nodep->ownerModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                    if (AstCell* const cellp = VN_CAST(stmtp, Cell)) {
                        if (cellp->name() == nodep->cellName && cellp->modp()) {
                            const string cellModName = cellp->modp()->name();
                            const size_t suffixPos = cellModName.find("__");
                            if (suffixPos != string::npos) {
                                targetSpecSuffix = cellModName.substr(suffixPos);
                                UINFO(9, "DEPGRAPH: updateEdges cellName '" << nodep->cellName
                                          << "' -> module '" << cellModName
                                          << "' suffix '" << targetSpecSuffix << "'" << endl);
                            }
                            break;
                        }
                    }
                }
            }

            for (DepNode* const candp : s_allNodes) {
                if (!candp || candp == depNodep) continue;
                if (candp->nodeType != depNodep->nodeType) continue;
                if (!candp->ownerModp) continue;
                if (nodeName(candp) != nodeNameStr) continue;

                // Check if candidate is a specialization of the template
                const string candOwnerName = candp->ownerModp->name();
                if (candOwnerName.find(templateBaseName + "__") != string::npos) {
                    // If we have a target suffix from cellName lookup, prefer exact match
                    if (!targetSpecSuffix.empty()) {
                        if (candOwnerName.find(targetSpecSuffix) != string::npos) {
                            specializedNodep = candp;
                            UINFO(9, "DEPGRAPH: updateEdges matched via cellName suffix '"
                                      << targetSpecSuffix << "' -> " << candOwnerName << endl);
                            break;
                        }
                        // Don't use fallback if we have a specific target
                        continue;
                    }
                    // Found a specialized version - prefer one in same module hierarchy
                    const string ownerName = nodep->ownerModp->name();
                    const size_t ownerSuffixPos = ownerName.find("__");
                    if (ownerSuffixPos != string::npos) {
                        const string ownerSuffix = ownerName.substr(ownerSuffixPos);
                        // Check for matching suffix pattern
                        if (candOwnerName.find(ownerSuffix) != string::npos
                            || ownerSuffix.find(candOwnerName.substr(candOwnerName.find("__"))) != string::npos) {
                            specializedNodep = candp;
                            break;
                        }
                    }
                    // Fallback: use first specialized version found (only if no cellName target)
                    if (!specializedNodep) specializedNodep = candp;
                }
            }

            if (specializedNodep) {
                newDeps.insert(specializedNodep);
                changed = true;
                UINFO(5, "DEPGRAPH: updated edge from '" << nodeName(nodep)
                          << "'@" << nodep->ownerModp->name()
                          << " to specialized '" << nodeName(specializedNodep)
                          << "'@" << specializedNodep->ownerModp->name()
                          << " (was template @" << depNodep->ownerModp->name() << ")" << endl);
                ++updatedEdges;

                // Store deferred typedefp for REFDTYPE nodes pointing to specialized typedef
                // This will be applied during commit/finalize, not here during graph build
                if (nodep->nodeType == NodeType::REFDTYPE
                    && specializedNodep->nodeType == NodeType::TYPEDEF) {
                    if (AstTypedef* const specTdp = VN_CAST(specializedNodep->nodep, Typedef)) {
                        nodep->deferredTypedefp = specTdp;
                        nodep->deferredClassOwnerp = specializedNodep->ownerModp;
                        UINFO(5, "DEPGRAPH: deferred REFDTYPE '" << nodeName(nodep)
                                  << "' typedefp to specialized typedef in "
                                  << specializedNodep->ownerModp->name() << endl);
                    }
                }
            } else {
                newDeps.insert(depNodep);
            }
        }

        if (changed) {
            // Update edges
            for (DepNode* const oldDepp : nodep->dependsOn) {
                if (oldDepp) oldDepp->dependents.erase(nodep);
            }
            nodep->dependsOn = newDeps;
            for (DepNode* const newDepp : newDeps) {
                if (newDepp) newDepp->dependents.insert(nodep);
            }
        }
    }
    if (updatedEdges > 0) {
        UINFO(5, "DEPGRAPH: updated " << updatedEdges << " edges to specialized nodes" << endl);
    }
}

void V3LinkDotDepGraph::buildIncremental(AstNetlist* netlistp) {
    if (!netlistp) return;
    bool anyNew = false;
    for (AstNodeModule* modp = netlistp->modulesp(); modp;
         modp = VN_AS(modp->nextp(), NodeModule)) {
        if (s_builtModules.insert(modp).second) {
            anyNew = true;
        }
    }
    if (!anyNew) return;
    UINFO(5, "DEPGRAPH: incremental build for new modules" << endl);
    DepGraphBuildVisitor{netlistp};

    // Update edges from existing REFDTYPE nodes to point to newly created specialized nodes
    updateEdgesToSpecialized();

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
        nodep->pendingDeps = pending;
        UINFO(9, "DEPGRAPH: pendingDeps '" << nodeName(nodep) << "'@" << nodeOwnerName(nodep)
                  << " = " << nodep->pendingDeps << endl);
    }
}

void V3LinkDotDepGraph::beginIteration(AstNetlist* netlistp) {
    if (!netlistp) return;
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
        nodep->pendingDeps = pending;
        UINFO(9, "DEPGRAPH: pendingDeps '" << nodeName(nodep) << "'@" << nodeOwnerName(nodep)
                  << " = " << nodep->pendingDeps << endl);
    }
}

void V3LinkDotDepGraph::postIterationCleanup(AstNetlist* netlistp) {
    (void)netlistp;
}

void V3LinkDotDepGraph::postWidthCleanup(AstNode* nodep) {
    if (!nodep) return;
    if (useInParam()) return;
    if (AstNodeModule* const ownerModp = findOwnerModule(nodep)) {
        const bool hasSpecSuffix = ownerModp->name().find("__") != string::npos;
        if (!ownerModp->isTop() && !hasSpecSuffix && ownerModp->hasGParam()) return;
    }
    normalizeRefTree(nodep, "post-width");
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
        // Skip template modules (unspecialized) - they have params but no __ suffix.
        // Top modules must still be resolved even if parameterized, since there is no clone.
        const bool hasSpecSuffix = ownerModp->name().find("__") != string::npos;
        if (!ownerModp->isTop() && !hasSpecSuffix && ownerModp->hasGParam()) {
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
        // Normalize RefDTypes touched by widthing in this typedef subtree
        normalizeRefTree(tdp, "typedef-width");

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
                // Follow PARAMTYPEDTYPE dependency - prefer resolved deferred dtype
                AstParamTypeDType* const depPtdp = VN_CAST(depNodep->nodep, ParamTypeDType);
                if (depNodep->resolved) {
                    if (depNodep->deferredDTypep) {
                        targetDTypep = depNodep->deferredDTypep;
                        targetName = targetDTypep->prettyTypeName();
                        UINFO(5, "DEPGRAPH: found paramtype dtype '" << targetName
                                  << "' via deferred dependency for paramtype '" << ptdp->name()
                                  << "' in " << nodeOwnerName(nodep) << endl);
                        break;
                    }
                    if (depPtdp && depPtdp->subDTypep()) {
                        targetDTypep = depPtdp->subDTypep();
                        targetName = depPtdp->name();
                        UINFO(5, "DEPGRAPH: found paramtype '" << targetName
                                  << "' via dependency edge for paramtype '" << ptdp->name()
                                  << "' in " << nodeOwnerName(nodep) << endl);
                        break;
                    }
                }
            }
        }

        // If no dependency edge found a typedef/paramtype, use the PARAMTYPEDTYPE's
        // own subDTypep which should have been resolved through graph edges.
        if (!targetDTypep) {
            if (AstNodeDType* const subp = ptdp->subDTypep()) {
                targetDTypep = subp;
                targetName = subp->prettyTypeName();
                UINFO(5, "DEPGRAPH: using paramtype subDTypep '" << targetName
                          << "' for dtypep in " << nodeOwnerName(nodep) << endl);
            }
        }

        // If the target is a RequireDType wrapper, unwrap to the actual dtype.
        if (AstRequireDType* const reqp = VN_CAST(targetDTypep, RequireDType)) {
            if (AstNodeDType* const lhsp = VN_CAST(reqp->lhsp(), NodeDType)) {
                targetDTypep = lhsp;
                targetName = lhsp->prettyTypeName();
                UINFO(5, "DEPGRAPH: unwrapped RequireDType to '" << targetName
                          << "' for paramtype '" << ptdp->name() << "' in "
                          << nodeOwnerName(nodep) << endl);

                // Apply immediately because dependent nodes (e.g. typedefs) in the same
                // execution batch need to see the unwrapped type to run V3Width.
                AstNodeDType* newChildp = lhsp;
                newChildp->unlinkFrBack();
                // Remove existing child (the REQUIREDTYPE) before setting new child
                if (AstNode* const existingChildp = ptdp->childDTypep()) {
                    if (existingChildp->backp() == ptdp) {
                        existingChildp->unlinkFrBack();
                        VL_DO_DANGLING(existingChildp->deleteTree(), existingChildp);
                    }
                }
                ptdp->childDTypep(newChildp);
                ptdp->dtypep(newChildp);

                // Resolve any PARSEREF nodes in the unwrapped type to VarRef nodes.
                // The PARSEREF TLEN in range [TLEN-1:0] needs to be linked to the actual
                // TLEN parameter before V3Width can evaluate the range.
                if (AstNodeModule* const ownerModp = nodep->ownerModp) {
                    // Collect ParseRefs first to avoid modifying tree during iteration
                    std::vector<AstParseRef*> parseRefs;
                    newChildp->foreach([&](AstParseRef* parseRefp) {
                        parseRefs.push_back(parseRefp);
                    });
                    UINFO(5, "DEPGRAPH: found " << parseRefs.size() << " ParseRefs in unwrapped type for "
                              << ptdp->name() << " in " << ownerModp->name() << endl);
                    for (AstParseRef* parseRefp : parseRefs) {
                        const string& refName = parseRefp->name();
                        UINFO(5, "DEPGRAPH: resolving PARSEREF '" << refName << "' in " << ownerModp->name() << endl);
                        // Find the parameter in the owner module
                        for (AstNode* stmtp = ownerModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                            if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                                if (varp->name() == refName) {
                                    UINFO(5, "DEPGRAPH: replacing PARSEREF '" << refName << "' with VARREF to "
                                              << varp << endl);
                                    // Replace PARSEREF with VARREF
                                    AstVarRef* const varRefp = new AstVarRef{
                                        parseRefp->fileline(), varp, VAccess::READ};
                                    parseRefp->replaceWith(varRefp);
                                    VL_DO_DANGLING(parseRefp->deleteTree(), parseRefp);
                                    break;
                                }
                            }
                        }
                    }
                }

                // Run V3Width on the unwrapped type to evaluate parameterized range expressions
                // like [TLEN-1:0]. Without this, BASICDTYPE 'logic' has width=1 instead of
                // the expected width from the resolved parameter (e.g., TLEN=8 -> width=8).
                // Skip if the REFDTYPE points to a template typedef - its parameters have X values.
                // Only specialized clones have resolved parameter values.
                bool skipWidth = false;
                if (AstRefDType* const refp = VN_CAST(newChildp, RefDType)) {
                    if (AstTypedef* const tdp = refp->typedefp()) {
                        AstNodeModule* const tdOwnerp = findOwnerModule(tdp);
                        if (tdOwnerp && tdOwnerp->hasGParam()
                            && tdOwnerp->name().find("__") == string::npos) {
                            skipWidth = true;
                            UINFO(5, "DEPGRAPH: skip widthParamsEdit - REFDTYPE points to template typedef '"
                                      << tdp->name() << "' in " << tdOwnerp->name() << endl);
                        }
                    }
                }
                if (!skipWidth) {
                    V3Width::widthParamsEdit(newChildp);
                    V3Const::constifyParamsEdit(newChildp);
                }
                targetDTypep = newChildp;  // Update to use widthed type
                targetName = newChildp->prettyTypeName();
            }
        }

        if (targetDTypep) {
            // Store deferred mutations instead of immediately mutating AST.
            // These will be applied in finalizeAST() after the resolution loop.
            AstNodeDType* const resolvedDTypep = targetDTypep->skipRefOrNullp();
            AstNodeDType* const finalDTypep = resolvedDTypep ? resolvedDTypep : targetDTypep;

            // If we already applied immediate update (above), deferredDTypep is redundant for dtypep/childClear
            // but might be needed for width or other logic.
            // However, we should be consistent.
            bool alreadyApplied = (ptdp->dtypep() == targetDTypep || ptdp->childDTypep() == targetDTypep);

            if (!alreadyApplied) {
                // Store deferred dtype
                nodep->deferredDTypep = finalDTypep;
            }
            nodep->resolvedWidth = finalDTypep->width();

            UINFO(5, "DEPGRAPH: deferred paramtype '" << ptdp->name()
                      << "' dtypep to '" << targetName
                      << "' (width=" << finalDTypep->width() << ")"
                      << " in " << nodeOwnerName(nodep) << endl);

            // Store deferred width force
            nodep->deferredNeedsWidthForce = true;
            nodep->deferredForcedWidth = finalDTypep->width();
            nodep->deferredForcedWidthMin = finalDTypep->widthMin();

            // Store deferred child typedef retarget
            if (targetTypedefp) {
                nodep->deferredChildTypedefp = targetTypedefp;
                UINFO(5, "DEPGRAPH: deferred paramtype '" << ptdp->name()
                          << "' child RefDType typedefp to '"
                          << targetTypedefp->name() << "' in "
                          << nodeOwnerName(nodep) << endl);
            }

            // Store deferred childDTypep clear
            if (!alreadyApplied) {
                if (AstNodeDType* const childp = ptdp->getChildDTypep()) {
                    if (childp != finalDTypep) {
                        nodep->deferredNeedsChildDTypeClear = true;
                        UINFO(5, "DEPGRAPH: deferred paramtype '" << ptdp->name()
                                  << "' childDTypep clear in " << nodeOwnerName(nodep) << endl);
                    }
                }
            }
            // normalizeRefTree moved to finalizeAST()
        } else {
            UINFO(9, "DEPGRAPH: no resolved dependency for paramtype '" << ptdp->name()
                      << "' in " << nodeOwnerName(nodep) << endl);
        }
    } else if (nodep->nodeType == NodeType::REFDTYPE) {
        // REFDTYPE resolution is now simple: edges point to correct (specialized) nodes
        // after updateEdgesToSpecialized() runs in buildIncremental().
        // Just use the dependency edge directly - no fallback searches needed.
        AstRefDType* const rdp = VN_CAST(nodep->nodep, RefDType);
        if (!rdp || !nodep->ownerModp) return;

        for (DepNode* const depNodep : nodep->dependsOn) {
            if (!depNodep || !depNodep->nodep) continue;

            if (depNodep->nodeType == NodeType::TYPEDEF) {
                AstTypedef* const tdp = VN_CAST(depNodep->nodep, Typedef);
                if (tdp && rdp->typedefp() != tdp) {
                    nodep->deferredTypedefp = tdp;
                    AstNodeModule* const ownerp = findOwnerModule(tdp);
                    if (AstClass* const classp = VN_CAST(ownerp, Class)) {
                        nodep->deferredClassOwnerp = classp;
                    }
                    nodep->needsNormalize = true;
                    UINFO(5, "DEPGRAPH: deferred retarget refdtype '" << rdp->name()
                              << "' typedefp to '" << tdp->name() << "' in "
                              << nodeOwnerName(nodep) << endl);
                }
                break;
            } else if (depNodep->nodeType == NodeType::PARAMTYPEDTYPE) {
                AstParamTypeDType* const ptdp = VN_CAST(depNodep->nodep, ParamTypeDType);
                if (ptdp && rdp->refDTypep() != ptdp) {
                    nodep->deferredRefDTypep = ptdp;
                    nodep->needsNormalize = true;
                    UINFO(5, "DEPGRAPH: deferred retarget refdtype '" << rdp->name()
                              << "' refDTypep to '" << ptdp->name() << "' in "
                              << nodeOwnerName(nodep) << endl);
                }
                break;
            }
        }
    } else if (nodep->nodeType == NodeType::GPARAM || nodep->nodeType == NodeType::LPARAM) {
        AstVar* const varp = VN_CAST(nodep->nodep, Var);
        if (!varp) return;
        if (nodep->origExprp) {
            if (varp->valuep()) varp->valuep()->unlinkFrBack()->deleteTree();
            AstNode* const clonedExprp = nodep->origExprp->cloneTree(false);
            // Relink RefDTypes in the cloned expression to ParamTypeDType in this module
            AstNodeModule* const ownerModp
                = nodep->ownerModp ? nodep->ownerModp : V3LinkDotDepGraph::findOwnerModule(varp);
            if (ownerModp) {
                clonedExprp->foreach([&](AstRefDType* rdp) {
                    for (AstNode* stmtp = ownerModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                        if (AstParamTypeDType* const ptdp = VN_CAST(stmtp, ParamTypeDType)) {
                            if (ptdp->name() == rdp->name()) {
                                rdp->refDTypep(ptdp);
                                rdp->typedefp(nullptr);
                                if (ptdp->width() > 0) {
                                    rdp->dtypep(ptdp);
                                    rdp->widthForce(ptdp->width(), ptdp->widthMin());
                                    rdp->didWidth(false);
                                }
                                break;
                            }
                        }
                    }
                });
            }
            varp->valuep(clonedExprp);
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
        if (nodep->nodeType == NodeType::LPARAM && varp->name() == "p_a") {
            AstNode* const valuep = varp->valuep();
            UINFO(5, "DEPGRAPH: pre-width LPARAM p_a valuep=" << valuep
                      << " valuepPtr=" << static_cast<const void*>(valuep)
                      << " backp=" << (valuep ? valuep->backp() : nullptr)
                      << " dtypep=" << (valuep ? valuep->dtypep() : nullptr)
                      << " type=" << (valuep ? valuep->typeName() : "<null>") << endl);
            if (AstAttrOf* const attrp = VN_CAST(valuep, AttrOf)) {
                AstNode* const fromp = attrp->fromp();
                AstNodeDType* const fromdtp = fromp ? fromp->dtypep() : nullptr;
                UINFO(5, "DEPGRAPH: pre-width p_a AttrOf fromp=" << fromp
                          << " fromdtp=" << fromdtp
                          << " fromdtpW=" << (fromdtp ? fromdtp->width() : 0) << endl);
                if (AstRefDType* const rdp = VN_CAST(fromp, RefDType)) {
                    AstNodeDType* const refdtp = rdp->refDTypep();
                    UINFO(5, "DEPGRAPH: pre-width p_a RefDType refDTypep=" << refdtp
                              << " refDTypepW=" << (refdtp ? refdtp->width() : 0)
                              << " dtypep=" << rdp->dtypep()
                              << " dtypepW=" << (rdp->dtypep() ? rdp->dtypep()->width() : 0)
                              << endl);
                }
            }
        }
        V3Width::widthParamsEdit(varp);
        if (nodep->nodeType == NodeType::LPARAM && varp->name() == "p_a") {
            AstNode* const valuep = varp->valuep();
            UINFO(5, "DEPGRAPH: post-width LPARAM p_a valuep=" << valuep
                      << " valuepPtr=" << static_cast<const void*>(valuep)
                      << " backp=" << (valuep ? valuep->backp() : nullptr)
                      << " dtypep=" << (valuep ? valuep->dtypep() : nullptr)
                      << " type=" << (valuep ? valuep->typeName() : "<null>")
                      << " varWidth=" << varp->width() << endl);
        }
        // Normalize RefDTypes touched by widthing in this param subtree
        normalizeRefTree(varp, "param-width");
        V3Const::constifyParamsEdit(varp);
    } else if (nodep->nodeType == NodeType::ATTROF) {
        // ATTROF nodes like $bits() - the commit phase handles replacement with CONST
        // Just ensure the source type is resolved by checking dependencies
        AstAttrOf* const attrp = VN_CAST(nodep->nodep, AttrOf);
        if (!attrp) return;

        // Get the resolved width from the fromp
        AstNodeDType* fromdtp = nullptr;
        if (AstRefDType* const rdp = VN_CAST(attrp->fromp(), RefDType)) {
            fromdtp = rdp->skipRefp();
            if (!fromdtp) fromdtp = rdp->refDTypep();
            if (!fromdtp) fromdtp = rdp->dtypep();
        } else if (AstNodeDType* const dtp = VN_CAST(attrp->fromp(), NodeDType)) {
            fromdtp = dtp->skipRefp();
        }

        if (fromdtp && fromdtp->width() > 0) {
            UINFO(5, "DEPGRAPH: re-evaluate ATTROF '" << attrp->attrType().ascii()
                      << "' fromdtp width=" << fromdtp->width()
                      << " in " << nodeOwnerName(nodep) << endl);
        }
    } else if (nodep->nodeType == NodeType::STRUCTDTYPE
               || nodep->nodeType == NodeType::UNIONDTYPE) {
        // Re-width the struct/union after its member types are resolved.
        // This is needed because member types (like ParamTypeDType T) may have been
        // resolved to their final widths, and the struct's width needs to be recalculated.
        AstNodeUOrStructDType* const usp = VN_CAST(nodep->nodep, NodeUOrStructDType);
        if (!usp) return;
        const int oldWidth = usp->width();

        // First, update member RefDTypes to have the correct width from their target.
        // The RefDType may have been resolved before its target ParamTypeDType was widthed.
        for (AstMemberDType* memp = usp->membersp(); memp;
             memp = VN_AS(memp->nextp(), MemberDType)) {
            if (AstRefDType* const rdp = VN_CAST(memp->subDTypep(), RefDType)) {
                if (AstParamTypeDType* const ptdp = VN_CAST(rdp->refDTypep(), ParamTypeDType)) {
                    // Get the resolved width from the ParamTypeDType
                    const int ptdpWidth = ptdp->width();
                    if (ptdpWidth > 0 && rdp->width() != ptdpWidth) {
                        UINFO(5, "DEPGRAPH: update member RefDType '" << rdp->name()
                                  << "' width " << rdp->width() << " -> " << ptdpWidth << endl);
                        rdp->widthForce(ptdpWidth, ptdpWidth);
                        rdp->dtypep(ptdp);
                        memp->widthForce(ptdpWidth, ptdpWidth);
                    }
                }
            }
        }

        // Debug: log member types before widthing
        UINFO(5, "DEPGRAPH: re-evaluate STRUCTDTYPE '" << usp->name()
                  << "' oldWidth=" << oldWidth << " in " << nodeOwnerName(nodep) << endl);
        for (AstMemberDType* memp = usp->membersp(); memp;
             memp = VN_AS(memp->nextp(), MemberDType)) {
            AstNodeDType* const subp = memp->subDTypep();
            UINFO(5, "DEPGRAPH:   member '" << memp->name() << "' subDTypep="
                      << (subp ? subp->prettyTypeName() : "<null>")
                      << " w=" << (subp ? subp->width() : 0) << endl);
        }

        V3Width::widthParamsEdit(usp);
        UINFO(5, "DEPGRAPH: re-evaluate STRUCTDTYPE '" << usp->name()
                  << "' width " << oldWidth << " -> " << usp->width()
                  << " in " << nodeOwnerName(nodep) << endl);
    }
    // GPARAM and LPARAM values are already computed by V3Param, no need to re-evaluate
}

//======================================================================
// Resolution

int V3LinkDotDepGraph::resolve() {
    UINFO(5, "DEPGRAPH: starting iterative resolution" << endl);

    s_iterationCount = 0;
    s_commitChanges = 0;
    std::deque<DepNode*> ready;
    for (DepNode* nodep : s_allNodes) {
        if (!nodep || nodep->resolved) continue;
        if (nodep->pendingDeps == 0) ready.push_back(nodep);
    }
    UINFO(5, "DEPGRAPH: ready queue initialized with " << ready.size() << " nodes" << endl);

    while (!ready.empty()) {
        DepNode* nodep = ready.front();
        ready.pop_front();
        if (!nodep || nodep->resolved) continue;
        if (nodep->pendingDeps > 0) continue;

        UINFO(9, "DEPGRAPH: execute '" << nodeName(nodep) << "'@" << nodeOwnerName(nodep)
                  << " type=" << nodeTypeName(nodep->nodeType)
                  << " nodep=" << nodep->nodep
                  << " pendingDeps=" << nodep->pendingDeps << endl);

        reEvaluateNode(nodep);
        commitResolvedNode(nodep);

        // Always mark as resolved - if commit skipped replacement (e.g., width=0),
        // the guards in V3Width/V3Const will handle it later.
        nodep->resolved = true;
        nodep->resolvedIteration = ++s_iterationCount;
        UINFO(9, "DEPGRAPH: resolved '" << nodeName(nodep) << "'@" << nodeOwnerName(nodep)
                  << " step " << s_iterationCount << endl);

        for (DepNode* const depNodep : nodep->dependents) {
            if (!depNodep || depNodep->resolved) continue;
            if (depNodep->pendingDeps > 0) --depNodep->pendingDeps;
            UINFO(9, "DEPGRAPH: decrement pendingDeps '" << nodeName(depNodep) << "'@"
                      << nodeOwnerName(depNodep) << " = " << depNodep->pendingDeps << endl);
            if (depNodep->pendingDeps == 0) ready.push_back(depNodep);
        }
    }

    UINFO(5, "DEPGRAPH: resolution complete in " << s_iterationCount << " steps" << endl);

    // Check for unresolved nodes
    int unresolvedCount = 0;
    for (DepNode* nodep : s_allNodes) {
        if (!nodep->resolved) {
            ++unresolvedCount;
            UINFO(9, "DEPGRAPH: unresolved node '" << nodeName(nodep) << "'@"
                      << nodeOwnerName(nodep)
                      << " type=" << nodeTypeName(nodep->nodeType)
                      << " nodep=" << nodep->nodep << endl);
            for (DepNode* const depp : nodep->dependsOn) {
                if (!depp || depp->resolved) continue;
                UINFO(9, "DEPGRAPH:   pending dep -> '" << nodeName(depp) << "'@"
                          << nodeOwnerName(depp)
                          << " type=" << nodeTypeName(depp->nodeType)
                          << " nodep=" << depp->nodep << endl);
            }
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
                AstTypedef* const curTdp = rdp->typedefp();
                AstNodeDType* const curRefp = rdp->refDTypep();
                AstNodeModule* const tOwnerp = curTdp ? findOwnerModule(curTdp) : nullptr;
                AstNodeModule* const rOwnerp = curRefp ? findOwnerModule(curRefp) : nullptr;
                UINFO(1, "DEPGRAPH: WARNING refdtype has both typedefp and refDTypep set: "
                          << nodeName(nodep) << "@" << nodeOwnerName(nodep)
                          << " typedef='" << (curTdp ? curTdp->name() : "<null>")
                          << "' typedefp=" << curTdp
                          << "' typedefBackp=" << (curTdp ? curTdp->backp() : nullptr)
                          << "' typedefOwner='" << (tOwnerp ? tOwnerp->name() : "<null>")
                          << "' refDType='" << (curRefp ? curRefp->prettyTypeName() : "<null>")
                          << "' refDTypep=" << curRefp
                          << "' refBackp=" << (curRefp ? curRefp->backp() : nullptr)
                          << "' refOwner='" << (rOwnerp ? rOwnerp->name() : "<null>")
                          << "' dtypep=" << rdp->dtypep()
                          << endl);
            }
        }
        UINFO(1, "DEPGRAPH: ========== END REFDTYPE SUMMARY ==========" << endl);
    }

    return s_iterationCount;
}

//======================================================================
// Apply - update RefDType pointers after resolution

int V3LinkDotDepGraph::apply() {
    // All AST mutations are now deferred to finalizeAST().
    // This function just returns the commit change count for fixed-point convergence.
    UINFO(5, "DEPGRAPH: apply complete - commit changes " << s_commitChanges << endl);
    return s_commitChanges;
}

//======================================================================
// Finalize AST - apply all deferred mutations in a single pass

static void finalizeParamType(V3LinkDotDepGraph::DepNode* nodep) {
    AstParamTypeDType* const ptdp = VN_CAST(nodep->nodep, ParamTypeDType);
    if (!ptdp) return;

    UINFO(5, "DEPGRAPH: finalizeParamType '" << ptdp->name()
              << "' deferredDTypep=" << nodep->deferredDTypep
              << " needsWidthForce=" << nodep->deferredNeedsWidthForce
              << " needsChildDTypeClear=" << nodep->deferredNeedsChildDTypeClear
              << endl);

    // Apply deferred dtype
    if (nodep->deferredDTypep) {
        ptdp->dtypep(nodep->deferredDTypep);
    }

    // Apply deferred width
    if (nodep->deferredNeedsWidthForce) {
        ptdp->widthForce(nodep->deferredForcedWidth, nodep->deferredForcedWidthMin);
        ptdp->didWidth(true);
    }

    // Apply deferred child typedef retarget
    if (nodep->deferredChildTypedefp) {
        if (AstRequireDType* const reqp = VN_CAST(ptdp->getChildDTypep(), RequireDType)) {
            if (AstRefDType* const refp = VN_CAST(reqp->lhsp(), RefDType)) {
                refp->refDTypep(nullptr);
                refp->typedefp(nodep->deferredChildTypedefp);
            }
        }
    }

    // Clear childDTypep if needed
    if (nodep->deferredNeedsChildDTypeClear) {
        if (AstNodeDType* const childp = ptdp->getChildDTypep()) {
            AstNodeDType* newChildp = nullptr;
            // If the new type is inside the child we are about to delete (e.g. unwrapping REQUIREDTYPE),
            // we must rescue it and make it the new child to preserve ownership.
            if (nodep->deferredDTypep && nodep->deferredDTypep->backp() == childp) {
                newChildp = nodep->deferredDTypep;
                newChildp->unlinkFrBack();
            }

            if (childp->backp() == ptdp) {
                // Child is owned by this node - safe to delete
                childp->unlinkFrBack();
                VL_DO_DANGLING(childp->deleteTree(), childp);
            }
            ptdp->childDTypep(newChildp);
        }
    }

    // Normalize RefDTypes in this paramtype subtree
    normalizeRefTree(ptdp, "finalize-paramtype");
}

static void finalizeRefDType(V3LinkDotDepGraph::DepNode* nodep) {
    AstRefDType* const rdp = VN_CAST(nodep->nodep, RefDType);
    if (!rdp) return;

    UINFO(5, "DEPGRAPH: finalizeRefDType '" << rdp->name()
              << "' deferredTypedefp=" << nodep->deferredTypedefp
              << " deferredRefDTypep=" << nodep->deferredRefDTypep
              << " deferredClassOwnerp=" << nodep->deferredClassOwnerp
              << endl);

    // Apply deferred typedef
    if (nodep->deferredTypedefp) {
        rdp->typedefp(nodep->deferredTypedefp);
        rdp->refDTypep(nullptr);
        rdp->dtypep(nullptr);
        rdp->didWidth(false);
    }

    // Apply deferred refDTypep
    if (nodep->deferredRefDTypep) {
        rdp->refDTypep(nodep->deferredRefDTypep);
        rdp->typedefp(nullptr);
        rdp->dtypep(nullptr);
        rdp->didWidth(false);
    }

    // Apply deferred class owner
    if (nodep->deferredClassOwnerp) {
        rdp->classOrPackagep(nodep->deferredClassOwnerp);
    }
}

static void finalizeTypedef(V3LinkDotDepGraph::DepNode* nodep) {
    AstTypedef* const tdp = VN_CAST(nodep->nodep, Typedef);
    if (!tdp) return;

    UINFO(5, "DEPGRAPH: finalizeTypedef '" << tdp->name() << "'" << endl);

    // Typedefs don't have deferred state currently - they're handled via normalizeRef
    // This is a placeholder for future deferred typedef mutations
}

static void finalizeParam(V3LinkDotDepGraph::DepNode* nodep) {
    AstVar* const varp = VN_CAST(nodep->nodep, Var);
    if (!varp) return;

    UINFO(5, "DEPGRAPH: finalizeParam '" << varp->name()
              << "' deferredValuep=" << nodep->deferredValuep
              << endl);

    // Apply deferred value
    if (nodep->deferredValuep) {
        if (varp->valuep()) {
            varp->valuep()->unlinkFrBack()->deleteTree();
        }
        varp->valuep(nodep->deferredValuep->cloneTree(false));
        varp->didWidth(false);
        V3Width::widthParamsEdit(varp);
        V3Const::constifyParamsEdit(varp);
    }
}

// ATTROF replacement is handled by V3Width, not here

void V3LinkDotDepGraph::finalizeAST() {
    if (!s_enabled) return;

    UINFO(5, "DEPGRAPH: ========== finalizeAST - applying deferred mutations ==========" << endl);

    int paramTypeCount = 0;
    int refDTypeCount = 0;
    int typedefCount = 0;
    int paramCount = 0;
    int normalizeCount = 0;
    int normalizeTreeCount = 0;

    // First pass: apply deferred mutations by node type
    for (DepNode* nodep : s_allNodes) {
        if (!nodep || !nodep->resolved) continue;

        switch (nodep->nodeType) {
        case NodeType::PARAMTYPEDTYPE:
            finalizeParamType(nodep);
            ++paramTypeCount;
            break;
        case NodeType::REFDTYPE:
            finalizeRefDType(nodep);
            ++refDTypeCount;
            break;
        case NodeType::TYPEDEF:
            finalizeTypedef(nodep);
            ++typedefCount;
            break;
        case NodeType::GPARAM:
        case NodeType::LPARAM:
            finalizeParam(nodep);
            ++paramCount;
            break;
        case NodeType::ATTROF:
            // ATTROF replacement is handled by V3Width, not here
            break;
        default:
            break;
        }
    }

    // Second pass: apply deferred normalizations
    for (DepNode* nodep : s_allNodes) {
        if (!nodep || !nodep->nodep) continue;

        if (nodep->needsNormalize) {
            if (AstRefDType* const rdp = VN_CAST(nodep->nodep, RefDType)) {
                // Apply any deferred state before normalizing
                if (nodep->deferredTypedefp) {
                    rdp->typedefp(nodep->deferredTypedefp);
                    rdp->refDTypep(nullptr);
                }
                if (nodep->deferredRefDTypep) {
                    rdp->refDTypep(nodep->deferredRefDTypep);
                    rdp->typedefp(nullptr);
                }
                if (nodep->deferredClassOwnerp) {
                    rdp->classOrPackagep(nodep->deferredClassOwnerp);
                }
                normalizeRef(rdp);
                ++normalizeCount;
            }
        }

        if (nodep->needsNormalizeTree) {
            normalizeRefTree(nodep->nodep, "finalize");
            ++normalizeTreeCount;
        }
    }

    // Global cleanup pass for all RefDTypes (handles nodes not in DepGraph)
    forEachRefDType(nullptr, [](AstRefDType* rdp) {
        if (!rdp) return;
        normalizeRef(rdp);
    });

    // Re-width all structs in TYPETABLE. Structs may have been cloned during V3Param
    // with width=0, and need to be re-widthed based on their resolved member types.
    int structCount = 0;
    if (AstNetlist* const netlistp = v3Global.rootp()) {
        if (AstTypeTable* const typetablep = netlistp->typeTablep()) {
            for (AstNode* nodep = typetablep->typesp(); nodep; nodep = nodep->nextp()) {
                if (AstNodeUOrStructDType* const usp = VN_CAST(nodep, NodeUOrStructDType)) {
                    const int oldWidth = usp->width();
                    UINFO(5, "DEPGRAPH: finalizeAST checking struct '" << usp->name()
                              << "' width=" << oldWidth << endl);
                    // Update member types to have correct width from their subDTypep
                    for (AstMemberDType* memp = usp->membersp(); memp;
                         memp = VN_AS(memp->nextp(), MemberDType)) {
                        AstNodeDType* const subp = memp->subDTypep();
                        UINFO(5, "DEPGRAPH: finalizeAST   member '" << memp->name()
                                  << "' memp->width=" << memp->width()
                                  << " subp=" << (subp ? subp->prettyTypeName() : "<null>")
                                  << " subp->width=" << (subp ? subp->width() : -1) << endl);
                        if (subp && subp->width() > 0 && memp->width() != subp->width()) {
                            UINFO(5, "DEPGRAPH: finalizeAST update member '" << memp->name()
                                      << "' width " << memp->width() << " -> " << subp->width() << endl);
                            memp->widthForce(subp->width(), subp->widthMin());
                            memp->dtypep(subp);
                        }
                    }
                    V3Width::widthParamsEdit(usp);
                    if (usp->width() != oldWidth) {
                        UINFO(5, "DEPGRAPH: finalizeAST re-width struct '" << usp->name()
                                  << "' " << oldWidth << " -> " << usp->width() << endl);
                    }
                    ++structCount;
                }
            }
        }
    }

    UINFO(5, "DEPGRAPH: finalizeAST complete - PARAMTYPE=" << paramTypeCount
              << " REFDTYPE=" << refDTypeCount
              << " TYPEDEF=" << typedefCount
              << " PARAM=" << paramCount
              << " normalize=" << normalizeCount
              << " normalizeTree=" << normalizeTreeCount
              << " struct=" << structCount
              << endl);
}

//======================================================================
// Mark template types BEFORE V3Param

void V3LinkDotDepGraph::markTemplateTypes(AstNetlist* netlistp) {
    (void)netlistp;
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
