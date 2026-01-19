// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator:
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

#include "V3LinkDotIfaceCapture.h"

#include "V3Error.h"
#include "V3Global.h"

VL_DEFINE_DEBUG_FUNCTIONS;

V3LinkDotIfaceCapture::CapturedMap V3LinkDotIfaceCapture::s_map{};
V3LinkDotIfaceCapture::LocalparamMap V3LinkDotIfaceCapture::s_localparamMap{};
bool V3LinkDotIfaceCapture::s_enabled = true;
bool V3LinkDotIfaceCapture::s_explicitlyDisabled = false;

AstNodeModule* V3LinkDotIfaceCapture::findOwnerModule(AstNode* nodep) {
    for (AstNode* curp = nodep; curp; curp = curp->backp()) {
        if (AstNodeModule* const modp = VN_CAST(curp, NodeModule)) return modp;
    }
    return nullptr;
}

bool V3LinkDotIfaceCapture::finalizeCapturedEntry(CapturedMap::iterator it, const char* reasonp) {
    CapturedIfaceTypedef& entry = it->second;
    AstRefDType* const pendingRefp = entry.pendingClonep;
    AstTypedef* const reboundTypedefp = entry.typedefp;
    if (!pendingRefp || !reboundTypedefp) return false;
    if (entry.cellp) pendingRefp->user2p(entry.cellp);
    pendingRefp->user3(false);
    pendingRefp->typedefp(reboundTypedefp);
    entry.pendingClonep = nullptr;
    return true;
}

bool V3LinkDotIfaceCapture::shouldApplyToClone(const CapturedIfaceTypedef& entry,
                                               const AstNodeModule* srcModp,
                                               const AstCell* cloneCellp) {
    if (!entry.cellp || !cloneCellp) return true;
    if (entry.typedefOwnerModp != srcModp) return true;
    if (entry.cellp == cloneCellp) return true;
    if (entry.cellp->name() == cloneCellp->name()) return true;

    // If the entry cell is a direct child of srcModp, treat as a sibling and skip.
    for (AstNode* stmtp = srcModp ? srcModp->stmtsp() : nullptr; stmtp; stmtp = stmtp->nextp()) {
        if (AstCell* const cellp = VN_CAST(stmtp, Cell)) {
            if (cellp->name() == entry.cellp->name()) return false;
        }
    }

    // Otherwise, keep entry (nested interface chains should still apply).
    return true;
}

string V3LinkDotIfaceCapture::extractIfacePortName(const string& dotText) {
    string name = dotText;
    const size_t dotPos = name.find('.');
    if (dotPos != string::npos) name = name.substr(0, dotPos);
    const size_t braPos = name.find("__BRA__");
    if (braPos != string::npos) name = name.substr(0, braPos);
    return name;
}

void V3LinkDotIfaceCapture::add(AstRefDType* refp, AstCell* cellp, AstNodeModule* ownerModp,
                                AstTypedef* typedefp, AstNodeModule* typedefOwnerModp,
                                AstVar* ifacePortVarp) {
    if (!refp) return;
    if (!typedefp) typedefp = refp->typedefp();
    if (!typedefOwnerModp && typedefp) typedefOwnerModp = findOwnerModule(typedefp);
    s_map[refp] = CapturedIfaceTypedef{
        CaptureType::IFACE, refp,    cellp,        nullptr, ownerModp, typedefp,
        nullptr, typedefOwnerModp,   nullptr, ifacePortVarp};
}

void V3LinkDotIfaceCapture::addClass(AstRefDType* refp, AstClass* origClassp,
                                     AstNodeModule* ownerModp, AstTypedef* typedefp,
                                     AstNodeModule* typedefOwnerModp) {
    if (!refp) return;
    if (!typedefp) typedefp = refp->typedefp();
    if (!typedefOwnerModp && typedefp) typedefOwnerModp = findOwnerModule(typedefp);
    s_map[refp] = CapturedIfaceTypedef{CaptureType::CLASS, refp,      nullptr,
                                       origClassp,         ownerModp, typedefp,
                                       nullptr, typedefOwnerModp,   nullptr,   nullptr};
}

const V3LinkDotIfaceCapture::CapturedIfaceTypedef*
V3LinkDotIfaceCapture::find(const AstRefDType* refp) {
    if (!refp) return nullptr;
    const auto it = s_map.find(refp);
    if (VL_UNLIKELY(it == s_map.end())) return nullptr;
    return &it->second;
}

bool V3LinkDotIfaceCapture::erase(const AstRefDType* refp) {
    if (!refp) return false;
    const auto it = s_map.find(refp);
    if (it == s_map.end()) return false;
    s_map.erase(it);
    return true;
}

bool V3LinkDotIfaceCapture::replaceRef(const AstRefDType* oldRefp, AstRefDType* newRefp) {
    if (!oldRefp || !newRefp) return false;
    const auto it = s_map.find(oldRefp);
    if (it == s_map.end()) return false;
    auto entry = it->second;
    entry.refp = newRefp;
    s_map.erase(it);
    s_map.emplace(newRefp, entry);
    return true;
}

bool V3LinkDotIfaceCapture::replaceTypedef(const AstRefDType* refp, AstTypedef* newTypedefp) {
    if (!refp || !newTypedefp) return false;
    auto it = s_map.find(refp);
    if (it == s_map.end()) return false;
    it->second.typedefp = newTypedefp;
    it->second.typedefOwnerModp = findOwnerModule(newTypedefp);

    // For CLASS captures, update the RefDType node directly
    if (it->second.captureType == CaptureType::CLASS && it->second.refp) {
        it->second.refp->typedefp(newTypedefp);
        // Also update classOrPackagep to point to the specialized class
        if (AstClass* const newClassp = VN_CAST(it->second.typedefOwnerModp, Class)) {
            it->second.refp->classOrPackagep(newClassp);
        }
        UINFO(9, "class capture updated RefDType typedefp: " << it->second.refp << " -> "
                                                             << newTypedefp);
    }

    finalizeCapturedEntry(it, "typedef clone");
    return true;
}

void V3LinkDotIfaceCapture::propagateClone(const AstRefDType* origRefp, AstRefDType* newRefp) {
    if (!origRefp || !newRefp) return;
    const auto it = s_map.find(origRefp);
    UASSERT_OBJ(it != s_map.end(), origRefp,
                "iface capture propagateClone missing entry for orig=" << cvtToStr(origRefp));
    CapturedIfaceTypedef& entry = it->second;

    if (entry.cellp) newRefp->user2p(entry.cellp);
    newRefp->user3(false);
    entry.pendingClonep = newRefp;

    // If replaceTypedef was already called (interface cloned before module),
    // entry.typedefp will differ from the original RefDType's typedef.
    // In that case, finalize now with the updated typedef.
    if (entry.typedefp && origRefp->typedefp() && entry.typedefp != origRefp->typedefp()) {
        finalizeCapturedEntry(it, "ref clone");
    }

    // Handle PARAMTYPEDTYPE references: find the correct PARAMTYPEDTYPE in the cloned interface
    // The cloned cell's modp() should now point to the cloned interface
    if (entry.paramTypep && entry.cellp) {
        AstParamTypeDType* const origParamTypep = VN_CAST(origRefp->refDTypep(), ParamTypeDType);
        if (origParamTypep) {
            // Find the cloned cell - it should have the same name as the original
            // and be in the cloned module (newRefp's owner)
            AstCell* clonedCellp = entry.cellp->clonep();
            if (!clonedCellp) {
                // Try to find via user2p which may have been set during cloning
                clonedCellp = VN_CAST(newRefp->user2p(), Cell);
            }
            UINFO(9, "propagateClone paramtype: origCellp=" << entry.cellp
                      << " clonedCellp=" << clonedCellp
                      << " clonedCellp->modp()=" << (clonedCellp ? clonedCellp->modp() : nullptr)
                      << endl);
            if (clonedCellp && clonedCellp->modp()) {
                // Check if the cloned cell's modp() is different from the original
                // If it's the same, the nested interface hasn't been cloned yet
                AstNodeModule* const clonedModp = clonedCellp->modp();
                AstNodeModule* const origModp = entry.cellp->modp();
                UINFO(9, "propagateClone paramtype: origModp=" << (origModp ? origModp->name() : "<null>")
                          << " clonedModp=" << (clonedModp ? clonedModp->name() : "<null>")
                          << endl);
                if (clonedModp != origModp) {
                    // Search for the PARAMTYPEDTYPE with the same name in the cloned interface
                    const string& paramTypeName = origParamTypep->name();
                    for (AstNode* stmtp = clonedModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                        if (AstParamTypeDType* const ptdp = VN_CAST(stmtp, ParamTypeDType)) {
                            if (ptdp->name() == paramTypeName) {
                                newRefp->refDTypep(ptdp);
                                UINFO(9, "propagateClone updated cloned RefDType refDTypep: " << newRefp
                                          << " -> " << ptdp << " in " << clonedModp->name() << endl);
                                break;
                            }
                        }
                    }
                } else {
                    // Nested interface not cloned yet - store for deferred processing
                    UINFO(9, "propagateClone: nested interface not cloned yet, deferring refp="
                              << newRefp << " paramTypeName=" << origParamTypep->name() << endl);
                    entry.pendingClonep = newRefp;
                }
            }
        }
    }
}

template <typename FilterFn, typename Fn>
void V3LinkDotIfaceCapture::forEachImpl(FilterFn&& filter, Fn&& fn) {
    std::vector<const AstRefDType*> keys;
    keys.reserve(s_map.size());
    for (const auto& kv : s_map) keys.push_back(kv.first);

    for (const AstRefDType* key : keys) {
        const auto it = s_map.find(key);
        if (it == s_map.end()) continue;

        CapturedIfaceTypedef& entry = it->second;
        if (entry.cellp && entry.refp && entry.refp->user2p() != entry.cellp) {
            entry.refp->user2p(entry.cellp);
        }
        if (!filter(entry)) continue;
        fn(entry);
    }
}

void V3LinkDotIfaceCapture::forEach(const std::function<void(const CapturedIfaceTypedef&)>& fn) {
    if (!fn) return;
    forEachImpl([](const CapturedIfaceTypedef&) { return true; }, fn);
}

void V3LinkDotIfaceCapture::forEachOwned(
    const AstNodeModule* ownerModp, const std::function<void(const CapturedIfaceTypedef&)>& fn) {
    if (!ownerModp || !fn) return;
    forEachImpl(
        [ownerModp](const CapturedIfaceTypedef& e) {
            return e.ownerModp == ownerModp || e.typedefOwnerModp == ownerModp;
        },
        fn);
}

// replaces the lambda used in V3LinkDot.cpp for iface capture
void V3LinkDotIfaceCapture::captureTypedefContext(
    AstRefDType* refp, const char* stageLabel, int dotPos, bool dotIsFinal,
    const std::string& dotText, VSymEnt* dotSymp, VSymEnt* curSymp, AstNodeModule* modp,
    AstNode* nodep, const std::function<bool(AstVar*, AstRefDType*)>& promoteVarCb,
    const std::function<std::string()>& indentFn) {
    if (!enabled() || !refp) return;

    UINFO(9, indentFn() << "iface capture capture request stage=" << stageLabel
                        << " typedef=" << refp << " name=" << refp->name() << " dotPos=" << dotPos
                        << " dotText='" << dotText << "' dotSym=" << dotSymp);

    const AstCell* ifaceCellp = nullptr;
    if (dotSymp && VN_IS(dotSymp->nodep(), Cell)) {
        const AstCell* const cellp = VN_AS(dotSymp->nodep(), Cell);
        if (cellp->modp() && VN_IS(cellp->modp(), Iface)) ifaceCellp = cellp;
    }
    if (!ifaceCellp) {
        UINFO(9, indentFn() << "iface capture capture skipped typedef=" << refp
                            << " (no iface context)");
        return;
    }

    AstVar* ifacePortVarp = nullptr;
    if (!dotText.empty() && curSymp) {
        const std::string portName = extractIfacePortName(dotText);
        if (VSymEnt* const portSymp = curSymp->findIdFallback(portName)) {
            ifacePortVarp = VN_CAST(portSymp->nodep(), Var);
            UINFO(9, indentFn() << "iface capture found port var '" << portName << "' -> "
                                << ifacePortVarp);
        }
    }

    refp->user2p(const_cast<AstCell*>(ifaceCellp));
    // Check if refDTypep is a ParamTypeDType - if so, use addParamType instead of add
    if (AstParamTypeDType* const paramTypep = VN_CAST(refp->refDTypep(), ParamTypeDType)) {
        V3LinkDotIfaceCapture::addParamType(refp, const_cast<AstCell*>(ifaceCellp), modp,
                                            paramTypep, nullptr, ifacePortVarp);
    } else {
        V3LinkDotIfaceCapture::add(refp, const_cast<AstCell*>(ifaceCellp), modp, refp->typedefp(),
                                   nullptr, ifacePortVarp);
    }

    UINFO(9, indentFn() << "iface capture capture success typedef=" << refp
                        << " cell=" << ifaceCellp
                        << " mod=" << (ifaceCellp->modp() ? ifaceCellp->modp()->name() : "<null>")
                        << " dotPos=" << dotPos);
    if (!dotIsFinal) return;

    AstVar* enclosingVarp = nullptr;
    for (AstNode* curp = nodep; curp; curp = curp->backp()) {
        if (AstVar* const varp = VN_CAST(curp, Var)) {
            enclosingVarp = varp;
            break;
        }
        if (VN_IS(curp, ParamTypeDType)) break;
        if (VN_IS(curp, NodeModule)) break;
    }
    if (!enclosingVarp || enclosingVarp->user3SetOnce()) return;
    UINFO(9, indentFn() << "iface capture typedef owner var=" << enclosingVarp
                        << " name=" << enclosingVarp->prettyName());

    if (promoteVarCb && promoteVarCb(enclosingVarp, refp)) return;
    UINFO(9, indentFn() << "iface capture failed to convert owner var name="
                        << enclosingVarp->prettyName());
}

void V3LinkDotIfaceCapture::addLocalparam(AstVar* varp, AstNode* exprp,
                                          AstNodeModule* ownerModp) {
    if (!varp || !exprp) return;
    // Only capture if not already captured
    if (s_localparamMap.find(varp) != s_localparamMap.end()) return;
    // Clone the expression to preserve it
    AstNode* const clonedExprp = exprp->cloneTree(false);
    s_localparamMap[varp] = CapturedIfaceLocalparam{varp, clonedExprp, ownerModp};
    UINFO(5, "LOCALPARAM-CAPTURE var=" << varp->name()
              << " owner=" << (ownerModp ? ownerModp->name() : "<null>")
              << " expr=" << clonedExprp << endl);
}
const V3LinkDotIfaceCapture::CapturedIfaceLocalparam*
V3LinkDotIfaceCapture::findLocalparam(const AstVar* varp) {
    if (!varp) return nullptr;
    const auto it = s_localparamMap.find(varp);
    if (it == s_localparamMap.end()) return nullptr;
    return &it->second;
}
void V3LinkDotIfaceCapture::forEachLocalparamOwned(
    const AstNodeModule* ownerModp,
    const std::function<void(const CapturedIfaceLocalparam&)>& fn) {
    if (!ownerModp || !fn) return;
    for (const auto& kv : s_localparamMap) {
        if (kv.second.ownerModp == ownerModp) {
            fn(kv.second);
        }
    }
}

void V3LinkDotIfaceCapture::addParamType(AstRefDType* refp, AstCell* cellp,
                                          AstNodeModule* ownerModp,
                                          AstParamTypeDType* paramTypep,
                                          AstNodeModule* paramTypeOwnerModp,
                                          AstVar* ifacePortVarp) {
    if (!refp) return;
    if (!paramTypeOwnerModp && paramTypep) paramTypeOwnerModp = findOwnerModule(paramTypep);
    s_map[refp] = CapturedIfaceTypedef{
        CaptureType::IFACE, refp, cellp, nullptr, ownerModp, nullptr,
        paramTypep, paramTypeOwnerModp, nullptr, ifacePortVarp};
}

bool V3LinkDotIfaceCapture::replaceParamType(const AstRefDType* refp,
                                              AstParamTypeDType* newParamTypep) {
    if (!refp || !newParamTypep) return false;
    auto it = s_map.find(refp);
    if (it == s_map.end()) return false;
    it->second.paramTypep = newParamTypep;
    it->second.typedefOwnerModp = findOwnerModule(newParamTypep);
    // Update the RefDType's refDTypep
    if (it->second.refp) {
        it->second.refp->refDTypep(newParamTypep);
    }
    // Also update any pending cloned RefDType that was deferred because
    // the nested interface wasn't cloned yet at propagateClone time
    if (it->second.pendingClonep) {
        it->second.pendingClonep->refDTypep(newParamTypep);
        UINFO(9, "replaceParamType also updated pendingClonep: " << it->second.pendingClonep
                  << " -> " << newParamTypep << endl);
    }
    return true;
}
