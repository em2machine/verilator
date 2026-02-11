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

bool V3LinkDotIfaceCapture::finalizeCapturedEntry(CapturedMap::iterator it, const char* reasonp,
                                                   AstCell* matchCellp) {
    CapturedIfaceTypedef& entry = it->second;
    AstTypedef* const reboundTypedefp = entry.typedefp;
    UINFO(9, "iface capture finalizeCapturedEntry(" << reasonp << "): refp="
              << (entry.refp ? entry.refp->name() : "<null>")
              << " typedefp=" << (reboundTypedefp ? reboundTypedefp->name() : "<null>")
              << " pendingClones.size=" << entry.pendingClones.size()
              << " matchCellp=" << (matchCellp ? matchCellp->name() : "<null>")
              << " matchCellp(ptr)=" << cvtToHex(matchCellp)
              << endl);
    if (entry.pendingClones.empty() || !reboundTypedefp) return false;
    bool anyUpdated = false;
    auto it2 = entry.pendingClones.begin();
    while (it2 != entry.pendingClones.end()) {
        if (!it2->refp) {
            it2 = entry.pendingClones.erase(it2);
            continue;
        }
        // Disambiguation: match pending clone by cell pointer.
        // matchCellp is the cell that triggered the interface cloning (e.g.,
        // port_types in child__Iz3). The pending clone's cellp was recorded
        // at propagateClone time via entry.cellp->clonep().
        // If matchCellp is provided, only update the matching clone.
        // If matchCellp is nullptr, update all (no disambiguation needed).
        bool matches = false;
        if (!matchCellp) {
            matches = true;  // No disambiguation — update all
        } else if (!it2->cellp) {
            matches = true;  // No cell context on pending clone — always match
        } else if (it2->cellp == matchCellp) {
            matches = true;  // Exact cell pointer match
        }
        UINFO(9, "iface capture   pendingClone: refp=" << it2->refp->name()
                  << " cellp=" << (it2->cellp ? it2->cellp->name() : "<null>")
                  << " cellp(ptr)=" << cvtToHex(it2->cellp)
                  << " matches=" << matches << endl);
        if (matches) {
            UINFO(9, "iface capture   -> UPDATING typedefp to " << reboundTypedefp->name()
                      << " in " << (findOwnerModule(reboundTypedefp) ? findOwnerModule(reboundTypedefp)->name() : "<null>")
                      << endl);
            if (entry.cellp) it2->refp->user2p(entry.cellp);
            it2->refp->user3(false);
            it2->refp->typedefp(reboundTypedefp);
            it2 = entry.pendingClones.erase(it2);
            anyUpdated = true;
        } else {
            ++it2;
        }
    }
    return anyUpdated;
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
        nullptr, typedefOwnerModp,   {}, ifacePortVarp};
}

void V3LinkDotIfaceCapture::addClass(AstRefDType* refp, AstClass* origClassp,
                                     AstNodeModule* ownerModp, AstTypedef* typedefp,
                                     AstNodeModule* typedefOwnerModp) {
    if (!refp) return;
    if (!typedefp) typedefp = refp->typedefp();
    if (!typedefOwnerModp && typedefp) typedefOwnerModp = findOwnerModule(typedefp);
    s_map[refp] = CapturedIfaceTypedef{CaptureType::CLASS, refp,      nullptr,
                                       origClassp,         ownerModp, typedefp,
                                       nullptr, typedefOwnerModp,   {},   nullptr};
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

bool V3LinkDotIfaceCapture::replaceTypedef(const AstRefDType* refp, AstTypedef* newTypedefp,
                                           AstCell* matchCellp) {
    if (!refp || !newTypedefp) return false;
    auto it = s_map.find(refp);
    if (it == s_map.end()) return false;
    UINFO(9, "iface capture replaceTypedef: refp=" << refp->name()
              << " newTypedefp=" << newTypedefp->name()
              << " owner=" << (findOwnerModule(newTypedefp) ? findOwnerModule(newTypedefp)->name() : "<null>")
              << " matchCellp=" << (matchCellp ? matchCellp->name() : "<null>")
              << " pendingClones.size=" << it->second.pendingClones.size()
              << endl);
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

    finalizeCapturedEntry(it, "typedef clone", matchCellp);
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
    // Store the cloned cell for disambiguation: when the nested interface
    // is later cloned, we match by cell pointer to find the right clone.
    AstCell* clonedCellp = entry.cellp ? entry.cellp->clonep() : nullptr;
    UINFO(9, "iface capture propagateClone: orig=" << origRefp->name()
              << " new=" << newRefp
              << " entry.cellp=" << (entry.cellp ? entry.cellp->name() : "<null>")
              << " clonedCellp=" << (clonedCellp ? clonedCellp->name() : "<null>")
              << " clonedCellp(ptr)=" << cvtToHex(clonedCellp)
              << " pendingClones.size=" << entry.pendingClones.size()
              << endl);
    entry.pendingClones.push_back({newRefp, clonedCellp});

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
                    entry.pendingClones.push_back({newRefp, clonedCellp});
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
    UINFO(9, "iface capture forEachOwned: checking entries for ownerModp=" << ownerModp->name()
              << " map size=" << s_map.size() << endl);
    forEachImpl(
        [ownerModp](const CapturedIfaceTypedef& e) {
            const bool matches = e.ownerModp == ownerModp || e.typedefOwnerModp == ownerModp;
            UINFO(9, "iface capture forEachOwned filter: entry refp=" << e.refp
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
    UINFO(9, "iface capture localparam: var=" << varp->name()
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
        paramTypep, paramTypeOwnerModp, {}, ifacePortVarp};

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
                        innerRefp->typedefp(), nullptr, refOwnerModp, {}, nullptr};
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
    UINFO(9, "replaceParamType: found entry, pendingClones.size="
              << it->second.pendingClones.size() << endl);
    it->second.paramTypep = newParamTypep;
    it->second.typedefOwnerModp = findOwnerModule(newParamTypep);
    // Update the RefDType's refDTypep
    if (it->second.refp) {
        it->second.refp->refDTypep(newParamTypep);
    }
    // Also update any pending cloned RefDTypes that were deferred because
    // the nested interface wasn't cloned yet at propagateClone time
    AstNodeModule* const paramOwnerModp = findOwnerModule(newParamTypep);
    auto pit = it->second.pendingClones.begin();
    while (pit != it->second.pendingClones.end()) {
        if (!pit->refp) {
            pit = it->second.pendingClones.erase(pit);
            continue;
        }
        bool matches = !pit->cellp || !paramOwnerModp
                       || pit->cellp->modp() == paramOwnerModp;
        if (matches) {
            pit->refp->refDTypep(newParamTypep);
            UINFO(9, "replaceParamType also updated pendingClone: " << pit->refp
                      << " -> " << newParamTypep << endl);
            pit = it->second.pendingClones.erase(pit);
        } else {
            ++pit;
        }
    }
    return true;
}

void V3LinkDotIfaceCapture::finalizeIfaceCapture() {
    if (!s_enabled) return;

    UINFO(4, "finalizeIfaceCapture: fixing remaining cross-interface refs" << endl);

    // Heuristic-based fixups for any remaining cross-interface refs.
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

    // Phase 2: Fix pointers that point to DEAD template modules.
    // V3Param's cloneRelinkGen() sets typedefp/refDTypep correctly at clone time.
    // The only pointers that need fixing here are ones still pointing to template
    // modules (marked dead) that will be deleted by V3Dead.
    // We NEVER redirect pointers to live modules — those were set correctly by V3Param.

    // Helper: find a matching node by name in a cloned module
    auto findInClone = [](AstNodeModule* cloneModp, const string& name,
                          bool wantTypedef) -> AstNode* {
        for (AstNode* stmtp = cloneModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (wantTypedef) {
                if (AstTypedef* const tdp = VN_CAST(stmtp, Typedef)) {
                    if (tdp->name() == name) return tdp;
                }
            } else {
                if (AstNodeDType* const dtp = VN_CAST(stmtp, NodeDType)) {
                    if (dtp->prettyName() == name) return dtp;
                }
            }
        }
        return nullptr;
    };

    // Helper: fix a single REFDTYPE's pointers if they point to dead modules
    auto fixDeadRefs = [&](AstRefDType* refp, const char* location) -> int {
        int fixed = 0;

        // Fix refDTypep pointing to dead module
        if (refp->refDTypep()) {
            AstNodeModule* const targetModp = findOwnerModule(refp->refDTypep());
            if (targetModp && targetModp->dead()) {
                auto it = templateToCloneMap.find(targetModp);
                if (it != templateToCloneMap.end()) {
                    const string& targetName = refp->refDTypep()->prettyName();
                    if (AstNode* const newp = findInClone(it->second, targetName, false)) {
                        UINFO(9, "iface capture finalizeCapture (" << location
                                  << "): fixing refDTypep refp=" << refp
                                  << " dead=" << targetModp->name()
                                  << " -> " << it->second->name() << endl);
                        refp->refDTypep(VN_AS(newp, NodeDType));
                        ++fixed;
                    }
                }
            }
        }

        // Fix typedefp pointing to dead module
        if (refp->typedefp()) {
            AstNodeModule* const typedefModp = findOwnerModule(refp->typedefp());
            if (typedefModp && typedefModp->dead()) {
                auto it = templateToCloneMap.find(typedefModp);
                if (it != templateToCloneMap.end()) {
                    const string& tdName = refp->typedefp()->name();
                    if (AstNode* const newp = findInClone(it->second, tdName, true)) {
                        UINFO(9, "iface capture finalizeCapture (" << location
                                  << "): fixing typedefp refp=" << refp
                                  << " dead=" << typedefModp->name()
                                  << " -> " << it->second->name() << endl);
                        refp->typedefp(VN_AS(newp, Typedef));
                        ++fixed;
                    }
                }
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
                typeTableFixed += fixDeadRefs(refp, "type table");
            });
        }
    }

    // Walk all non-dead modules
    for (AstNode* nodep = v3Global.rootp()->modulesp(); nodep; nodep = nodep->nextp()) {
        if (AstNodeModule* const modp = VN_CAST(nodep, NodeModule)) {
            if (modp->dead()) continue;
            modp->foreach([&](AstRefDType* refp) {
                moduleFixed += fixDeadRefs(refp, modp->name().c_str());
            });
        }
    }

    UINFO(4, "finalizeIfaceCapture: fixed " << typeTableFixed << " in type table, "
              << moduleFixed << " in modules" << endl);

    // Assert: no REFDTYPE in any live module should have typedefp or refDTypep
    // pointing to a dead module. If this fires, V3Param's cloneRelinkGen() failed
    // to redirect a pointer, or something corrupted it after cloning.
    for (AstNode* nodep = v3Global.rootp()->modulesp(); nodep; nodep = nodep->nextp()) {
        if (AstNodeModule* const modp = VN_CAST(nodep, NodeModule)) {
            if (modp->dead()) continue;
            modp->foreach([&](AstRefDType* refp) {
                if (refp->typedefp()) {
                    AstNodeModule* const ownerModp = findOwnerModule(refp->typedefp());
                    UASSERT_OBJ(!ownerModp || !ownerModp->dead(), refp,
                                "REFDTYPE '" << refp->name()
                                << "' in live module '" << modp->name()
                                << "' has typedefp pointing to dead module '"
                                << ownerModp->name() << "'");
                }
                if (refp->refDTypep()) {
                    AstNodeModule* const ownerModp = findOwnerModule(refp->refDTypep());
                    UASSERT_OBJ(!ownerModp || !ownerModp->dead(), refp,
                                "REFDTYPE '" << refp->name()
                                << "' in live module '" << modp->name()
                                << "' has refDTypep pointing to dead module '"
                                << ownerModp->name() << "'");
                }
            });
        }
    }
    if (v3Global.rootp()->typeTablep()) {
        for (AstNode* nodep = v3Global.rootp()->typeTablep()->typesp(); nodep;
             nodep = nodep->nextp()) {
            nodep->foreach([&](AstRefDType* refp) {
                if (refp->typedefp()) {
                    AstNodeModule* const ownerModp = findOwnerModule(refp->typedefp());
                    UASSERT_OBJ(!ownerModp || !ownerModp->dead(), refp,
                                "REFDTYPE '" << refp->name()
                                << "' in type table has typedefp pointing to dead module '"
                                << ownerModp->name() << "'");
                }
                if (refp->refDTypep()) {
                    AstNodeModule* const ownerModp = findOwnerModule(refp->refDTypep());
                    UASSERT_OBJ(!ownerModp || !ownerModp->dead(), refp,
                                "REFDTYPE '" << refp->name()
                                << "' in type table has refDTypep pointing to dead module '"
                                << ownerModp->name() << "'");
                }
            });
        }
    }

}
