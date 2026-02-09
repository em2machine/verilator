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
V3LinkDotIfaceCapture::CrossIfaceMap V3LinkDotIfaceCapture::s_crossIfaceMap{};
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
    UINFO(0, "forEachOwned: checking entries for ownerModp=" << ownerModp->name()
              << " map size=" << s_map.size() << endl);
    forEachImpl(
        [ownerModp](const CapturedIfaceTypedef& e) {
            const bool matches = e.ownerModp == ownerModp || e.typedefOwnerModp == ownerModp;
            UINFO(0, "forEachOwned filter: entry refp=" << e.refp
                      << " e.ownerModp=" << (e.ownerModp ? e.ownerModp->name() : "<null>")
                      << " e.typedefOwnerModp=" << (e.typedefOwnerModp ? e.typedefOwnerModp->name() : "<null>")
                      << " matches=" << matches << endl);
            return matches;
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

    // Do NOT promote interface parent VARs - they have VARREFs pointing to them from interface
    // port connections. Deleting these VARs would leave dangling VARREFs.
    if (enclosingVarp->isIfaceParent()) {
        UINFO(9, indentFn() << "iface capture skipping isIfaceParent var promotion");
        return;
    }

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
    UINFO(9, "addParamType: refp=" << refp
              << " ownerModp=" << (ownerModp ? ownerModp->name() : "<null>")
              << " paramTypep=" << paramTypep
              << " paramTypeOwnerModp=" << (paramTypeOwnerModp ? paramTypeOwnerModp->name() : "<null>")
              << endl);
    // Dump the PARAMTYPEDTYPE's subDTypep chain to see what's there at capture time
    if (paramTypep) {
        UINFO(9, "addParamType: paramTypep subDTypep chain:" << endl);
        paramTypep->foreach([&](AstRefDType* innerRefp) {
            UINFO(9, "  inner RefDType: " << innerRefp
                      << " refDTypep=" << innerRefp->refDTypep()
                      << (innerRefp->refDTypep() ? " refDTypep->name=" : "")
                      << (innerRefp->refDTypep() ? innerRefp->refDTypep()->prettyTypeName() : "")
                      << endl);
        });
    }
    s_map[refp] = CapturedIfaceTypedef{
        CaptureType::IFACE, refp, cellp, nullptr, ownerModp, nullptr,
        paramTypep, paramTypeOwnerModp, nullptr, ifacePortVarp};

    // Also capture REFDTYPEs inside the PARAMTYPEDTYPE's subDTypep chain.
    // These REFDTYPEs may have refDTypep pointing to nodes in a nested interface
    // that will be cloned separately. We need to track them so we can update
    // their refDTypep when the nested interface is cloned.
    if (paramTypep) {
        paramTypep->foreach([&](AstRefDType* innerRefp) {
            if (innerRefp == refp) return;  // Skip the outer RefDType we already captured
            if (!innerRefp->refDTypep()) return;  // Skip if no refDTypep

            // Check if refDTypep is in a different interface (nested interface)
            AstNodeModule* const refOwnerModp = findOwnerModule(innerRefp->refDTypep());
            if (refOwnerModp && VN_IS(refOwnerModp, Iface) && refOwnerModp != paramTypeOwnerModp) {
                // This REFDTYPE has refDTypep pointing to a node in a different interface
                // Capture it so we can update it when that interface is cloned
                if (s_map.find(innerRefp) == s_map.end()) {
                    UINFO(9, "addParamType: also capturing inner RefDType " << innerRefp
                              << " refDTypep owner=" << refOwnerModp->name() << endl);
                    // Find the cell for the nested interface
                    AstCell* nestedCellp = nullptr;
                    for (AstNode* stmtp = paramTypeOwnerModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                        if (AstCell* const cp = VN_CAST(stmtp, Cell)) {
                            if (cp->modp() == refOwnerModp) {
                                nestedCellp = cp;
                                break;
                            }
                        }
                    }
                    s_map[innerRefp] = CapturedIfaceTypedef{
                        CaptureType::IFACE, innerRefp, nestedCellp, nullptr, paramTypeOwnerModp,
                        innerRefp->typedefp(), nullptr, refOwnerModp, nullptr, nullptr};
                }
            }
        });
    }
}

bool V3LinkDotIfaceCapture::replaceParamType(const AstRefDType* refp,
                                              AstParamTypeDType* newParamTypep) {
    UINFO(9, "replaceParamType called: refp=" << refp
              << " newParamTypep=" << (newParamTypep ? newParamTypep->name() : "<null>") << endl);
    if (!refp || !newParamTypep) return false;
    auto it = s_map.find(refp);
    if (it == s_map.end()) {
        UINFO(9, "replaceParamType: entry not found for refp=" << refp << endl);
        return false;
    }
    UINFO(9, "replaceParamType: found entry, pendingClonep="
              << it->second.pendingClonep << endl);
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

void V3LinkDotIfaceCapture::addCrossIfaceRefDType(AstRefDType* refp, AstNodeModule* ownerModp,
                                                   AstNodeDType* targetDTypep,
                                                   AstNodeModule* targetModp) {
    if (!refp || !targetDTypep || !targetModp) {
        UINFO(9, "addCrossIfaceRefDType: skipping due to null arg"
                  << " refp=" << cvtToHex(refp)
                  << " targetDTypep=" << cvtToHex(targetDTypep)
                  << " targetModp=" << cvtToHex(targetModp) << endl);
        return;
    }
    if (s_crossIfaceMap.find(refp) != s_crossIfaceMap.end()) {
        UINFO(9, "addCrossIfaceRefDType: already captured refp=" << refp << endl);
        return;  // Already captured
    }
    UINFO(5, "CROSS-IFACE-CAPTURE: refp=" << refp
              << " in " << (ownerModp ? ownerModp->name() : "<null>")
              << " -> targetDTypep=" << targetDTypep
              << " in " << targetModp->name()
              << " (crossIfaceMap size now " << (s_crossIfaceMap.size() + 1) << ")" << endl);
    s_crossIfaceMap[refp] = CrossIfaceRefDType{refp, ownerModp, targetDTypep, targetModp};
}

void V3LinkDotIfaceCapture::fixupCrossIfaceRefs(AstNodeModule* clonedModp,
                                                 AstNodeModule* templateModp) {
    if (!clonedModp || !templateModp) {
        UINFO(9, "fixupCrossIfaceRefs: skipping due to null arg"
                  << " clonedModp=" << cvtToHex(clonedModp)
                  << " templateModp=" << cvtToHex(templateModp) << endl);
        return;
    }
    UINFO(5, "CROSS-IFACE-FIXUP: clonedModp=" << clonedModp->name()
              << " templateModp=" << templateModp->name()
              << " crossIfaceMap size=" << s_crossIfaceMap.size() << endl);

    // Helper lambda to fix cross-interface refs in a node tree
    auto fixCrossIfaceRefsInTree = [&](AstNode* rootp, const char* location) {
        int fixed = 0;
        rootp->foreach([&](AstRefDType* refp) {
            if (!refp->refDTypep()) return;
            AstNodeModule* const targetModp = findOwnerModule(refp->refDTypep());
            if (targetModp == templateModp) {
                // This REFDTYPE has refDTypep pointing to the template interface
                // Check if there's a cloned version
                AstNodeDType* const clonedDTypep = refp->refDTypep()->clonep();
                if (clonedDTypep) {
                    UINFO(9, "CROSS-IFACE-FIXUP (" << location << "): fixing refp=" << refp
                              << " old refDTypep=" << refp->refDTypep()
                              << " new refDTypep=" << clonedDTypep << endl);
                    refp->refDTypep(clonedDTypep);
                    if (refp->dtypep() && findOwnerModule(refp->dtypep()) == templateModp) {
                        AstNodeDType* const clonedDtypep = refp->dtypep()->clonep();
                        if (clonedDtypep) refp->dtypep(clonedDtypep);
                    }
                    ++fixed;
                }
            }
        });
        return fixed;
    };

    // Walk all types in the type table
    if (v3Global.rootp() && v3Global.rootp()->typeTablep()) {
        int typeTableFixed = 0;
        for (AstNode* nodep = v3Global.rootp()->typeTablep()->typesp(); nodep;
             nodep = nodep->nextp()) {
            typeTableFixed += fixCrossIfaceRefsInTree(nodep, "type table");
        }
        if (typeTableFixed > 0) {
            UINFO(5, "CROSS-IFACE-FIXUP: fixed " << typeTableFixed
                      << " refs in type table for " << templateModp->name() << endl);
        }
    }

    // Walk all modules to fix cross-interface refs
    if (v3Global.rootp()) {
        int moduleFixed = 0;
        int moduleChecked = 0;
        int refsChecked = 0;
        for (AstNode* nodep = v3Global.rootp()->modulesp(); nodep; nodep = nodep->nextp()) {
            if (AstNodeModule* const modp = VN_CAST(nodep, NodeModule)) {
                // Only fix cloned modules (name contains "__")
                if (modp->name().find("__") != string::npos) {
                    ++moduleChecked;
                    // Count refs and check why they're not being fixed
                    modp->foreach([&](AstRefDType* refp) {
                        ++refsChecked;
                        if (!refp->refDTypep()) return;
                        AstNodeModule* const targetModp = findOwnerModule(refp->refDTypep());
                        if (targetModp == templateModp) {
                            AstNodeDType* const clonedDTypep = refp->refDTypep()->clonep();
                            UINFO(5, "CROSS-IFACE-FIXUP (module " << modp->name()
                                      << "): found ref to template, refp=" << refp
                                      << " refDTypep=" << refp->refDTypep()
                                      << " clonep()=" << clonedDTypep << endl);
                        }
                    });
                    moduleFixed += fixCrossIfaceRefsInTree(modp, modp->name().c_str());
                }
            }
        }
        UINFO(5, "CROSS-IFACE-FIXUP: checked " << moduleChecked << " modules, "
                  << refsChecked << " refs, fixed " << moduleFixed
                  << " for " << templateModp->name() << endl);
    }

    // Find all entries where targetModp matches templateModp and fix them up
    int fixedCount = 0;
    int skippedCount = 0;
    for (auto& kv : s_crossIfaceMap) {
        const AstRefDType* const mapKey = kv.first;
        CrossIfaceRefDType& entry = kv.second;
        UINFO(9, "fixupCrossIfaceRefs: checking entry mapKey=" << cvtToHex(mapKey)
                  << " entry.refp=" << cvtToHex(entry.refp)
                  << " same=" << (mapKey == entry.refp)
                  << " targetModp=" << (entry.targetModp ? entry.targetModp->name() : "<null>")
                  << endl);
        if (entry.targetModp != templateModp) {
            ++skippedCount;
            continue;
        }

        UINFO(9, "fixupCrossIfaceRefs: processing entry refp=" << entry.refp
                  << " ownerModp=" << (entry.ownerModp ? entry.ownerModp->name() : "<null>")
                  << " targetDTypep=" << entry.targetDTypep
                  << " targetModp=" << entry.targetModp->name() << endl);

        // The target dtype should have a clonep() pointing to the cloned version
        AstNodeDType* const clonedTargetDTypep = entry.targetDTypep->clonep();
        if (clonedTargetDTypep) {
            UINFO(5, "CROSS-IFACE-FIXUP: SUCCESS via clonep() refp=" << entry.refp
                      << " old refDTypep=" << entry.refp->refDTypep()
                      << " old dtypep=" << entry.refp->dtypep()
                      << " new refDTypep=" << clonedTargetDTypep << endl);
            // Fix the original REFDTYPE
            entry.refp->refDTypep(clonedTargetDTypep);
            if (entry.refp->dtypep() == entry.targetDTypep) {
                entry.refp->dtypep(clonedTargetDTypep);
                UINFO(5, "CROSS-IFACE-FIXUP: also updated dtypep" << endl);
            }
            // Also fix any clones of the REFDTYPE that were created during V3Width processing
            // These clones may have been created by iterateEditMoveDTypep
            for (AstRefDType* clonedRefp = entry.refp->clonep(); clonedRefp;
                 clonedRefp = clonedRefp->clonep()) {
                if (clonedRefp->refDTypep() == entry.targetDTypep) {
                    UINFO(5, "CROSS-IFACE-FIXUP: also fixing clone " << clonedRefp << endl);
                    clonedRefp->refDTypep(clonedTargetDTypep);
                }
                if (clonedRefp->dtypep() == entry.targetDTypep) {
                    clonedRefp->dtypep(clonedTargetDTypep);
                }
            }
            ++fixedCount;
        } else {
            // clonep() is null - the target wasn't cloned in this operation
            // This can happen if the cloning order is different
            // Try to find the cloned dtype by name in the cloned module
            const string& targetName = entry.targetDTypep->prettyName();
            UINFO(9, "fixupCrossIfaceRefs: clonep() is null, searching by name '"
                      << targetName << "' in " << clonedModp->name() << endl);
            bool found = false;
            for (AstNode* stmtp = clonedModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                if (AstNodeDType* const dtp = VN_CAST(stmtp, NodeDType)) {
                    UINFO(9, "  checking dtype: " << dtp->prettyName() << endl);
                    if (dtp->prettyName() == targetName) {
                        UINFO(5, "CROSS-IFACE-FIXUP: SUCCESS via name lookup refp=" << entry.refp
                                  << " old refDTypep=" << entry.refp->refDTypep()
                                  << " old dtypep=" << entry.refp->dtypep()
                                  << " new refDTypep=" << dtp << endl);
                        entry.refp->refDTypep(dtp);
                        // Also update dtypep if it points to the same template dtype
                        if (entry.refp->dtypep() == entry.targetDTypep) {
                            entry.refp->dtypep(dtp);
                            UINFO(5, "CROSS-IFACE-FIXUP: also updated dtypep" << endl);
                        }
                        ++fixedCount;
                        found = true;
                        break;
                    }
                }
            }
            if (!found) {
                UINFO(5, "CROSS-IFACE-FIXUP: FAILED to find cloned dtype for refp=" << entry.refp
                          << " targetName=" << targetName
                          << " in " << clonedModp->name() << endl);
            }
        }
    }
    UINFO(5, "CROSS-IFACE-FIXUP: done for " << templateModp->name()
              << " fixed=" << fixedCount << " skipped=" << skippedCount << endl);
}

void V3LinkDotIfaceCapture::finalizeIfaceCapture() {
    if (!s_enabled) return;

    UINFO(4, "finalizeIfaceCapture: fixing remaining cross-interface refs" << endl);

    // Build a map of template modules to their cloned versions
    // Template modules are those marked dead() or without "__" in name
    // Cloned modules have "__" in their name
    std::map<AstNodeModule*, AstNodeModule*> templateToCloneMap;
    std::set<AstNodeModule*> templateModules;

    if (!v3Global.rootp()) return;

    // First pass: identify template modules/interfaces (dead or no "__" in name)
    // The top-level module is a special case - it's never a template
    for (AstNode* nodep = v3Global.rootp()->modulesp(); nodep; nodep = nodep->nextp()) {
        if (AstNodeModule* const modp = VN_CAST(nodep, NodeModule)) {
            // Skip the top-level module - it's never a template
            if (modp->isTop()) {
                UINFO(9, "finalizeIfaceCapture: skipping top module " << modp->name() << endl);
                continue;
            }
            // Skip packages - they don't get cloned
            if (VN_IS(modp, Package)) continue;
            if (modp->dead() || modp->name().find("__") == string::npos) {
                templateModules.insert(modp);
                UINFO(9, "finalizeIfaceCapture: template "
                          << (VN_IS(modp, Iface) ? "interface" : "module")
                          << " " << modp->name() << endl);
            }
        }
    }

    // Second pass: for each cloned module, find its template
    // The template name is the part before "__"
    for (AstNode* nodep = v3Global.rootp()->modulesp(); nodep; nodep = nodep->nextp()) {
        if (AstNodeModule* const modp = VN_CAST(nodep, NodeModule)) {
            if (!modp->dead() && modp->name().find("__") != string::npos) {
                // Extract template name (part before "__")
                const string& name = modp->name();
                const size_t pos = name.find("__");
                if (pos != string::npos) {
                    const string templateName = name.substr(0, pos);
                    // Find the template module
                    for (AstNodeModule* tmplp : templateModules) {
                        if (tmplp->name() == templateName) {
                            templateToCloneMap[tmplp] = modp;
                            UINFO(9, "finalizeIfaceCapture: " << templateName
                                      << " -> " << modp->name() << endl);
                            break;
                        }
                    }
                }
            }
        }
    }

    // Helper lambda to fix a refDTypep if it points to a template module
    auto fixRefDType = [&](AstRefDType* refp, const char* location) -> bool {
        bool fixed = false;

        // Fix refDTypep if it points to a template module
        if (refp->refDTypep()) {
            AstNodeModule* const targetModp = findOwnerModule(refp->refDTypep());

            // Debug: log what we're checking
            UINFO(9, "finalizeIfaceCapture: checking refp=" << refp
                      << " refDTypep=" << refp->refDTypep()
                      << " targetModp=" << (targetModp ? targetModp->name() : "<null>")
                      << " dead=" << (targetModp ? targetModp->dead() : false) << endl);

            if (targetModp) {
                // Check if target is a template module (dead or in our template set)
                auto it = templateToCloneMap.find(targetModp);
                if (it != templateToCloneMap.end()) {
                    AstNodeModule* const clonedModp = it->second;

                    // Try to find the cloned dtype using clonep()
                    AstNodeDType* clonedDTypep = refp->refDTypep()->clonep();
                    if (clonedDTypep) {
                        UINFO(5, "finalizeCapture (" << location << "): fixing refDTypep via clonep() refp=" << refp
                                  << " old=" << refp->refDTypep()
                                  << " new=" << clonedDTypep << endl);
                        refp->refDTypep(clonedDTypep);
                        // Also fix dtypep if it points to the same template
                        if (refp->dtypep() && findOwnerModule(refp->dtypep()) == targetModp) {
                            if (AstNodeDType* const clonedDtypep = refp->dtypep()->clonep()) {
                                refp->dtypep(clonedDtypep);
                            }
                        }
                        fixed = true;
                    } else {
                        // Fallback: search by name in the cloned module
                        const string& targetName = refp->refDTypep()->prettyName();
                        for (AstNode* stmtp = clonedModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                            if (AstNodeDType* const dtp = VN_CAST(stmtp, NodeDType)) {
                                if (dtp->prettyName() == targetName) {
                                    UINFO(5, "finalizeCapture (" << location << "): fixing refDTypep via name lookup refp="
                                              << refp << " old=" << refp->refDTypep()
                                              << " new=" << dtp << endl);
                                    refp->refDTypep(dtp);
                                    if (refp->dtypep() && findOwnerModule(refp->dtypep()) == targetModp) {
                                        refp->dtypep(dtp);
                                    }
                                    fixed = true;
                                    break;
                                }
                            }
                        }
                    }
                } else if (targetModp->dead()) {
                    UINFO(5, "finalizeIfaceCapture: WARNING - refp=" << refp
                              << " refDTypep points to dead module " << targetModp->name()
                              << " but no clone mapping found" << endl);
                }
            }
        }

        // Also fix typedefp if it points to a template module
        // typedefp can point to AstTypedef or AstNodeDType (like BASICDTYPE)
        if (refp->typedefp()) {
            AstNodeModule* const typedefModp = findOwnerModule(refp->typedefp());

            UINFO(9, "finalizeIfaceCapture: checking refp=" << refp
                      << " typedefp=" << refp->typedefp()
                      << " typedefModp=" << (typedefModp ? typedefModp->name() : "<null>")
                      << " dead=" << (typedefModp ? typedefModp->dead() : false) << endl);

            if (typedefModp) {
                auto it = templateToCloneMap.find(typedefModp);
                if (it != templateToCloneMap.end()) {
                    AstNodeModule* const clonedModp = it->second;

                    // Try to find the cloned typedef using clonep()
                    if (AstNode* const clonedp = refp->typedefp()->clonep()) {
                        if (AstTypedef* const clonedTypedefp = VN_CAST(clonedp, Typedef)) {
                            UINFO(5, "finalizeCapture (" << location << "): fixing typedefp via clonep() refp=" << refp
                                      << " old=" << refp->typedefp()
                                      << " new=" << clonedTypedefp << endl);
                            refp->typedefp(clonedTypedefp);
                            fixed = true;
                        }
                    } else {
                        // Fallback: search by name in the cloned module
                        const string& targetName = refp->typedefp()->name();
                        for (AstNode* stmtp = clonedModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                            if (AstTypedef* const tdp = VN_CAST(stmtp, Typedef)) {
                                if (tdp->name() == targetName) {
                                    UINFO(5, "finalizeCapture (" << location << "): fixing typedefp via name lookup refp="
                                              << refp << " old=" << refp->typedefp()
                                              << " new=" << tdp << endl);
                                    refp->typedefp(tdp);
                                    fixed = true;
                                    break;
                                }
                            }
                        }
                    }
                } else if (typedefModp->dead()) {
                    UINFO(5, "finalizeIfaceCapture: WARNING - refp=" << refp
                              << " typedefp points to dead module " << typedefModp->name()
                              << " but no clone mapping found" << endl);
                }
            }
        }

        if (!fixed && refp->refDTypep()) {
            AstNodeModule* const targetModp = findOwnerModule(refp->refDTypep());
            if (targetModp && templateToCloneMap.count(targetModp)) {
                UINFO(5, "finalizeCapture (" << location << "): FAILED to fix refp=" << refp
                          << " target=" << refp->refDTypep()
                          << " in template " << targetModp->name() << endl);
            }
        }
        return fixed;
    };

    int typeTableFixed = 0;
    int moduleFixed = 0;

    // Walk the type table
    if (v3Global.rootp()->typeTablep()) {
        for (AstNode* nodep = v3Global.rootp()->typeTablep()->typesp(); nodep;
             nodep = nodep->nextp()) {
            nodep->foreach([&](AstRefDType* refp) {
                if (fixRefDType(refp, "type table")) ++typeTableFixed;
            });
        }
    }

    // Walk all non-dead modules (both cloned and non-cloned)
    // Non-cloned modules like 'top' can also contain REFDTYPEs with typedefp
    // pointing to template interfaces (e.g., in $bits(iface_port[0].type_t) expressions)
    for (AstNode* nodep = v3Global.rootp()->modulesp(); nodep; nodep = nodep->nextp()) {
        if (AstNodeModule* const modp = VN_CAST(nodep, NodeModule)) {
            if (!modp->dead()) {
                modp->foreach([&](AstRefDType* refp) {
                    if (fixRefDType(refp, modp->name().c_str())) ++moduleFixed;
                });
            }
        }
    }

    UINFO(4, "finalizeIfaceCapture: fixed " << typeTableFixed << " in type table, "
              << moduleFixed << " in modules" << endl);

    // Clear the maps as we're done with capture
    s_crossIfaceMap.clear();
}
