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

        // Fix refDTypep if it points to a template or wrong-clone module.
        // Skip if the target is in the same module as the REFDTYPE itself
        // (module-local references like $bits(p_data_t) → own PARAMTYPEDTYPE).
        if (refp->refDTypep()) {
            AstNodeModule* const targetModp = findOwnerModule(refp->refDTypep());
            AstNodeModule* const refOwnerModp = findOwnerModule(refp);

            // Debug: log what we're checking
            UINFO(9, "finalizeIfaceCapture: checking refp=" << refp
                      << " refDTypep=" << refp->refDTypep()
                      << " refOwnerModp=" << (refOwnerModp ? refOwnerModp->name() : "<null>")
                      << " targetModp=" << (targetModp ? targetModp->name() : "<null>")
                      << " dead=" << (targetModp ? targetModp->dead() : false) << endl);

            if (targetModp && targetModp != refOwnerModp) {
                // Find the correct cloned module to redirect to.
                // targetModp may be a template (direct lookup) or a wrong clone
                // (need to find template first via origName, then look up correct clone).
                AstNodeModule* correctCloneModp = nullptr;
                auto it = templateToCloneMap.find(targetModp);
                if (it != templateToCloneMap.end()) {
                    correctCloneModp = it->second;
                } else if (targetModp->name().find("__") != string::npos) {
                    // refDTypep points to a clone — find its template via origName
                    for (AstNodeModule* tmplp : templateModules) {
                        if (tmplp->name() == targetModp->origName()) {
                            auto it2 = templateToCloneMap.find(tmplp);
                            if (it2 != templateToCloneMap.end()
                                && it2->second != targetModp) {
                                correctCloneModp = it2->second;
                            }
                            break;
                        }
                    }
                }

                if (correctCloneModp) {
                    // Search by name in the correct cloned module
                    const string& targetName = refp->refDTypep()->prettyName();
                    for (AstNode* stmtp = correctCloneModp->stmtsp(); stmtp;
                         stmtp = stmtp->nextp()) {
                        if (AstNodeDType* const dtp = VN_CAST(stmtp, NodeDType)) {
                            if (dtp->prettyName() == targetName) {
                                UINFO(5, "finalizeCapture (" << location
                                          << "): fixing refDTypep refp=" << refp
                                          << " old=" << refp->refDTypep()
                                          << " new=" << dtp << endl);
                                refp->refDTypep(dtp);
                                if (refp->dtypep()
                                    && findOwnerModule(refp->dtypep()) == targetModp) {
                                    refp->dtypep(dtp);
                                }
                                fixed = true;
                                break;
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
                // Find the correct cloned module to redirect to.
                // typedefModp may be a template (direct lookup) or a wrong clone
                // (need to find template first via origName, then look up correct clone).
                AstNodeModule* correctCloneModp = nullptr;
                auto it = templateToCloneMap.find(typedefModp);
                if (it != templateToCloneMap.end()) {
                    correctCloneModp = it->second;
                } else if (typedefModp->name().find("__") != string::npos) {
                    // typedefp points to a clone — find its template via origName
                    for (AstNodeModule* tmplp : templateModules) {
                        if (tmplp->name() == typedefModp->origName()) {
                            auto it2 = templateToCloneMap.find(tmplp);
                            if (it2 != templateToCloneMap.end()
                                && it2->second != typedefModp) {
                                correctCloneModp = it2->second;
                            }
                            break;
                        }
                    }
                }

                if (correctCloneModp) {
                    // Search by name in the correct cloned module
                    const string& targetName = refp->typedefp()->name();
                    for (AstNode* stmtp = correctCloneModp->stmtsp(); stmtp;
                         stmtp = stmtp->nextp()) {
                        if (AstTypedef* const tdp = VN_CAST(stmtp, Typedef)) {
                            if (tdp->name() == targetName) {
                                UINFO(5, "finalizeCapture (" << location
                                          << "): fixing typedefp refp=" << refp
                                          << " old=" << refp->typedefp()
                                          << " new=" << tdp << endl);
                                refp->typedefp(tdp);
                                fixed = true;
                                break;
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

    // Walk all non-dead modules and fix typedefp/refDTypep pointers.
    // For each module, build a per-module template→clone interface map from its cells.
    // This correctly handles multi-instantiation where child__Iz3 references types_if__Cz1
    // and child__Iz4 references types_if__Cz2 — the global templateToCloneMap can only
    // hold one mapping per template, causing cross-wiring.
    for (AstNode* nodep = v3Global.rootp()->modulesp(); nodep; nodep = nodep->nextp()) {
        if (AstNodeModule* const modp = VN_CAST(nodep, NodeModule)) {
            if (modp->dead()) continue;

            // Build per-module template→clone map from this module's cells
            std::map<AstNodeModule*, AstNodeModule*> localTemplateToCloneMap;
            for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                if (AstCell* const cellp = VN_CAST(stmtp, Cell)) {
                    AstNodeModule* const cellModp = cellp->modp();
                    if (!cellModp || !VN_IS(cellModp, Iface)) continue;
                    if (cellModp->name().find("__") == string::npos) continue;
                    // Find the template interface by origName
                    for (AstNodeModule* tmplp : templateModules) {
                        if (VN_IS(tmplp, Iface) && tmplp->name() == cellModp->origName()) {
                            localTemplateToCloneMap[tmplp] = cellModp;
                            break;
                        }
                    }
                    // Also recurse: the cloned interface may itself contain cells
                    // pointing to other cloned interfaces (e.g., bus_if__Cz1 contains types_if__Cz1)
                    for (AstNode* sp = cellModp->stmtsp(); sp; sp = sp->nextp()) {
                        if (AstCell* const innerCellp = VN_CAST(sp, Cell)) {
                            AstNodeModule* const innerModp = innerCellp->modp();
                            if (!innerModp || !VN_IS(innerModp, Iface)) continue;
                            if (innerModp->name().find("__") == string::npos) continue;
                            for (AstNodeModule* tmplp : templateModules) {
                                if (VN_IS(tmplp, Iface) && tmplp->name() == innerModp->origName()) {
                                    localTemplateToCloneMap[tmplp] = innerModp;
                                    break;
                                }
                            }
                        }
                    }
                }
            }

            // Override the global map with per-module map for this module's fixup
            std::map<AstNodeModule*, AstNodeModule*> savedMap;
            if (!localTemplateToCloneMap.empty()) {
                savedMap = templateToCloneMap;
                for (auto& kv : localTemplateToCloneMap) {
                    templateToCloneMap[kv.first] = kv.second;
                }
            }

            modp->foreach([&](AstRefDType* refp) {
                if (fixRefDType(refp, modp->name().c_str())) ++moduleFixed;
            });

            // Restore global map
            if (!localTemplateToCloneMap.empty()) {
                templateToCloneMap = savedMap;
            }
        }
    }

    UINFO(4, "finalizeIfaceCapture: fixed " << typeTableFixed << " in type table, "
              << moduleFixed << " in modules" << endl);

}
