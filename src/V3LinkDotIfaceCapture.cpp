// -*- mode: C++; c-file-style: "cc-mode" -*-
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

void V3LinkDotIfaceCapture::dumpEntries(const string& label) {
    UINFO(9, "========== iface capture dumpEntries: " << label
              << " (entries=" << s_map.size()
              << " localparams=" << s_localparamMap.size() << ") ==========" << endl);
    int idx = 0;
    for (const auto& pair : s_map) {
        const CaptureKey& key = pair.first;
        const CapturedEntry& entry = pair.second;
        const char* captType = (entry.captureType == CaptureType::IFACE) ? "IFACE" : "CLASS";
        UINFO(9, "  [" << idx << "] " << captType
                  << " key=(" << cvtToHex(key.templateRefp) << ",'" << key.cellPath << "')"
                  << " ref='" << (entry.refp ? entry.refp->name() : "<null>") << "'"
                  << " refp=" << cvtToHex(entry.refp)
                  << " cellPath='" << entry.cellPath << "'"
                  << " ownerMod=" << (entry.ownerModp ? entry.ownerModp->name() : "<null>")
                  << " typedefp=" << (entry.typedefp ? entry.typedefp->name() : "<null>")
                  << " typedefOwnerModName='" << entry.typedefOwnerModName << "'"
                  << " paramTypep=" << (entry.paramTypep ? entry.paramTypep->name() : "<null>")
                  << " ifacePortVarp=" << (entry.ifacePortVarp ? entry.ifacePortVarp->name() : "<null>")
                  << endl);
        ++idx;
    }
    for (const auto& pair : s_localparamMap) {
        const CapturedIfaceLocalparam& lp = pair.second;
        UINFO(9, "  LP: var='" << (lp.varp ? lp.varp->name() : "<null>") << "'"
                  << " ownerMod=" << (lp.ownerModp ? lp.ownerModp->name() : "<null>")
                  << " origExprp=" << (lp.origExprp ? "yes" : "no")
                  << endl);
    }
    UINFO(9, "========== end iface capture dumpEntries ==========" << endl);
}

string V3LinkDotIfaceCapture::extractIfacePortName(const string& dotText) {
    string name = dotText;
    const size_t dotPos = name.find('.');
    if (dotPos != string::npos) name = name.substr(0, dotPos);
    const size_t braPos = name.find("__BRA__");
    if (braPos != string::npos) name = name.substr(0, braPos);
    return name;
}

string V3LinkDotIfaceCapture::lastPathComponent(const string& cellPath) {
    UASSERT(!cellPath.empty(), "lastPathComponent called with empty cellPath");
    const size_t dotPos = cellPath.rfind('.');
    if (dotPos == string::npos) return cellPath;
    const string result = cellPath.substr(dotPos + 1);
    UASSERT(!result.empty(),
            "lastPathComponent produced empty result from '" << cellPath << "'");
    return result;
}

void V3LinkDotIfaceCapture::add(AstRefDType* refp, const string& cellPath,
                                AstNodeModule* ownerModp, AstTypedef* typedefp,
                                const string& typedefOwnerModName,
                                AstVar* ifacePortVarp) {
    UASSERT(refp, "add() called with null refp");
    UASSERT(ownerModp, "add() called with null ownerModp for refp='" << refp->name() << "'");
    if (!typedefp) typedefp = refp->typedefp();
    string tdOwnerName = typedefOwnerModName;
    if (tdOwnerName.empty() && typedefp) {
        AstNodeModule* const tdOwnerModp = findOwnerModule(typedefp);
        if (tdOwnerModp) tdOwnerName = tdOwnerModp->name();
    }
    const CaptureKey key{refp, cellPath};
    s_map[key] = CapturedEntry{CaptureType::IFACE, refp, cellPath, nullptr,
                               ownerModp, typedefp, nullptr, tdOwnerName, ifacePortVarp};
    UINFO(9, "iface capture add: refp=" << refp->name()
              << " cellPath='" << cellPath << "'"
              << " ownerMod=" << (ownerModp ? ownerModp->name() : "<null>")
              << " typedefp=" << (typedefp ? typedefp->name() : "<null>")
              << " typedefOwnerModName='" << tdOwnerName << "'"
              << endl);
}

void V3LinkDotIfaceCapture::addClass(AstRefDType* refp, AstClass* origClassp,
                                     AstNodeModule* ownerModp, AstTypedef* typedefp,
                                     const string& typedefOwnerModName) {
    UASSERT(refp, "addClass() called with null refp");
    UASSERT(ownerModp, "addClass() called with null ownerModp");
    if (!typedefp) typedefp = refp->typedefp();
    string tdOwnerName = typedefOwnerModName;
    if (tdOwnerName.empty() && typedefp) {
        AstNodeModule* const tdOwnerModp = findOwnerModule(typedefp);
        if (tdOwnerModp) tdOwnerName = tdOwnerModp->name();
    }
    // For CLASS captures, use the class name as cellPath
    UASSERT_OBJ(origClassp, refp,
                "addClass() called with null origClassp for refp='" << refp->name() << "'");
    const string cellPath = origClassp->name();
    UASSERT(!cellPath.empty(), "addClass() produced empty cellPath from class='" << origClassp->name() << "'");
    const CaptureKey key{refp, cellPath};
    s_map[key] = CapturedEntry{CaptureType::CLASS, refp, cellPath, origClassp,
                               ownerModp, typedefp, nullptr, tdOwnerName, nullptr};
    UINFO(9, "iface capture addClass: refp=" << refp->name()
              << " cellPath='" << cellPath << "'"
              << " ownerMod=" << (ownerModp ? ownerModp->name() : "<null>")
              << endl);
}

const V3LinkDotIfaceCapture::CapturedEntry*
V3LinkDotIfaceCapture::find(const AstRefDType* refp, const string& cellPath) {
    if (!refp) return nullptr;
    const CaptureKey key{refp, cellPath};
    const auto it = s_map.find(key);
    if (VL_UNLIKELY(it == s_map.end())) return nullptr;
    return &it->second;
}

bool V3LinkDotIfaceCapture::erase(const AstRefDType* refp, const string& cellPath) {
    if (!refp) return false;
    const CaptureKey key{refp, cellPath};
    const auto it = s_map.find(key);
    if (it == s_map.end()) return false;
    s_map.erase(it);
    return true;
}

const V3LinkDotIfaceCapture::CapturedEntry*
V3LinkDotIfaceCapture::findAny(const AstRefDType* refp) {
    if (!refp) return nullptr;
    for (const auto& kv : s_map) {
        if (kv.first.templateRefp == refp) return &kv.second;
    }
    return nullptr;
}

bool V3LinkDotIfaceCapture::eraseAll(const AstRefDType* refp) {
    if (!refp) return false;
    bool any = false;
    for (auto it = s_map.begin(); it != s_map.end();) {
        if (it->first.templateRefp == refp) {
            it = s_map.erase(it);
            any = true;
        } else {
            ++it;
        }
    }
    return any;
}

bool V3LinkDotIfaceCapture::replaceRef(const AstRefDType* oldRefp, AstRefDType* newRefp,
                                       const string& cellPath) {
    if (!oldRefp || !newRefp) return false;
    const CaptureKey oldKey{oldRefp, cellPath};
    const auto it = s_map.find(oldKey);
    if (it == s_map.end()) return false;
    auto entry = it->second;
    UASSERT(entry.cellPath == cellPath,
            "replaceRef key/entry cellPath mismatch: key='" << cellPath
            << "' entry='" << entry.cellPath << "'");
    entry.refp = newRefp;
    entry.cellPath = cellPath;  // keep consistent
    s_map.erase(it);
    const CaptureKey newKey{newRefp, cellPath};
    s_map.emplace(newKey, entry);
    return true;
}

bool V3LinkDotIfaceCapture::replaceTypedef(const AstRefDType* refp, const string& cellPath,
                                           AstTypedef* newTypedefp) {
    if (!refp || !newTypedefp) return false;
    const CaptureKey key{refp, cellPath};
    auto it = s_map.find(key);
    if (it == s_map.end()) return false;
    CapturedEntry& entry = it->second;
    AstNodeModule* const newOwnerModp = findOwnerModule(newTypedefp);
    if (!newOwnerModp) {
        UINFO(1, "iface capture replaceTypedef WARNING: findOwnerModule returned null"
                  " for newTypedefp='" << newTypedefp->name() << "'" << endl);
    }
    UINFO(9, "iface capture replaceTypedef: refp=" << refp->name()
              << " cellPath='" << cellPath << "'"
              << " newTypedefp=" << newTypedefp->name()
              << " owner=" << (newOwnerModp ? newOwnerModp->name() : "<null>")
              << endl);
    entry.typedefp = newTypedefp;
    if (newOwnerModp) entry.typedefOwnerModName = newOwnerModp->name();

    // For CLASS captures, also update classOrPackagep
    if (entry.captureType == CaptureType::CLASS && entry.refp) {
        entry.refp->typedefp(newTypedefp);
        if (AstClass* const newClassp = VN_CAST(newOwnerModp, Class)) {
            entry.refp->classOrPackagep(newClassp);
        }
        UINFO(9, "class capture updated RefDType typedefp: " << entry.refp << " -> "
                                                             << newTypedefp << endl);
    } else {
        // IFACE capture: update the RefDType's typedefp
        UASSERT(entry.refp, "replaceTypedef: entry has null refp");
        entry.refp->typedefp(newTypedefp);
    }
    return true;
}

void V3LinkDotIfaceCapture::propagateClone(const AstRefDType* origRefp, AstRefDType* newRefp,
                                           const string& cellPath) {
    UASSERT(origRefp, "propagateClone() called with null origRefp");
    UASSERT(newRefp, "propagateClone() called with null newRefp");
    const CaptureKey origKey{origRefp, cellPath};
    const auto it = s_map.find(origKey);
    if (it == s_map.end()) {
        // Try empty cellPath as fallback (PARAMTYPEDTYPE entries may have empty cellPath)
        const CaptureKey emptyKey{origRefp, ""};
        const auto it2 = s_map.find(emptyKey);
        if (it2 == s_map.end()) {
            UINFO(9, "iface capture propagateClone: no entry for orig="
                      << origRefp->name() << " cellPath='" << cellPath << "' — skipping" << endl);
            return;
        }
        // Create new entry for the clone with the provided cellPath.
        // This fallback is expected for PARAMTYPEDTYPE entries captured with empty dotText.
        CapturedEntry newEntry = it2->second;
        UASSERT(newEntry.refp, "propagateClone empty-key fallback found entry with null refp");
        newEntry.refp = newRefp;
        newEntry.cellPath = cellPath;
        const CaptureKey newKey{newRefp, cellPath};
        s_map[newKey] = newEntry;
        UINFO(1, "iface capture propagateClone (empty-key fallback): orig=" << origRefp->name()
                  << " new=" << newRefp->name()
                  << " cellPath='" << cellPath << "'" << endl);
        return;
    }
    // Create a new entry for the cloned RefDType, inheriting cellPath
    CapturedEntry newEntry = it->second;
    newEntry.refp = newRefp;
    const CaptureKey newKey{newRefp, cellPath};
    s_map[newKey] = newEntry;
    UINFO(9, "iface capture propagateClone: orig=" << origRefp->name()
              << " new=" << newRefp->name()
              << " cellPath='" << cellPath << "'" << endl);
}

template <typename FilterFn, typename Fn>
void V3LinkDotIfaceCapture::forEachImpl(FilterFn&& filter, Fn&& fn) {
    std::vector<CaptureKey> keys;
    keys.reserve(s_map.size());
    for (const auto& kv : s_map) keys.push_back(kv.first);

    for (const CaptureKey& key : keys) {
        const auto it = s_map.find(key);
        if (it == s_map.end()) continue;
        CapturedEntry& entry = it->second;
        if (!filter(entry)) continue;
        fn(entry);
    }
}

void V3LinkDotIfaceCapture::forEach(const std::function<void(const CapturedEntry&)>& fn) {
    if (!fn) return;
    forEachImpl([](const CapturedEntry&) { return true; }, fn);
}

void V3LinkDotIfaceCapture::forEachOwned(
    const AstNodeModule* ownerModp, const std::function<void(const CapturedEntry&)>& fn) {
    if (!ownerModp || !fn) return;
    const string ownerName = ownerModp->name();
    UINFO(9, "iface capture forEachOwned: ownerModp=" << ownerName
              << " map size=" << s_map.size() << endl);
    forEachImpl(
        [ownerModp, &ownerName](const CapturedEntry& e) {
            // Match by ownerModp pointer or typedefOwnerModName string
            const bool matches = e.ownerModp == ownerModp
                                 || e.typedefOwnerModName == ownerName;
            UINFO(9, "iface capture forEachOwned filter: ref='"
                      << (e.refp ? e.refp->name() : "<null>")
                      << "' cellPath='" << e.cellPath
                      << "' ownerMod=" << (e.ownerModp ? e.ownerModp->name() : "<null>")
                      << " typedefOwnerModName='" << e.typedefOwnerModName
                      << "' matches=" << matches << endl);
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

    // Use dotText as the hierarchical cellPath key component.
    // dotText is the full dot-separated path from the owning module to the
    // interface cell (e.g. "a_inst", "wif.a_inst", "outer.mid.inner").
    // Fall back to ifaceCellp->name() only when dotText is empty
    // (expected for PARAMTYPEDTYPE entries where dotText is not set).
    const string cellPath = dotText.empty() ? ifaceCellp->name() : dotText;
    if (dotText.empty()) {
        UINFO(5, indentFn() << "iface capture using ifaceCellp->name() fallback: '"
                            << cellPath << "' (dotText empty)" << endl);
    }
    UASSERT(!cellPath.empty(),
            "captureTypedefContext: cellPath is empty for refp='" << refp->name() << "'");

    AstVar* ifacePortVarp = nullptr;
    if (!dotText.empty() && curSymp) {
        const std::string portName = extractIfacePortName(dotText);
        if (VSymEnt* const portSymp = curSymp->findIdFallback(portName)) {
            ifacePortVarp = VN_CAST(portSymp->nodep(), Var);
            UINFO(9, indentFn() << "iface capture found port var '" << portName << "' -> "
                                << ifacePortVarp);
        }
    }

    // Check if refDTypep is a ParamTypeDType - if so, use addParamType instead of add
    if (AstParamTypeDType* const paramTypep = VN_CAST(refp->refDTypep(), ParamTypeDType)) {
        V3LinkDotIfaceCapture::addParamType(refp, cellPath, modp,
                                            paramTypep, "", ifacePortVarp);
    } else {
        V3LinkDotIfaceCapture::add(refp, cellPath, modp, refp->typedefp(),
                                   "", ifacePortVarp);
    }

    UINFO(9, indentFn() << "iface capture capture success typedef=" << refp
                        << " cell=" << ifaceCellp
                        << " cellPath='" << cellPath << "'"
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

void V3LinkDotIfaceCapture::addParamType(AstRefDType* refp, const string& cellPath,
                                          AstNodeModule* ownerModp,
                                          AstParamTypeDType* paramTypep,
                                          const string& paramTypeOwnerModName,
                                          AstVar* ifacePortVarp) {
    UASSERT(refp, "addParamType() called with null refp");
    UASSERT(ownerModp, "addParamType() called with null ownerModp for refp='" << refp->name() << "'");
    UASSERT_OBJ(paramTypep, refp,
                "addParamType() called with null paramTypep for refp='" << refp->name() << "'");
    string ptOwnerName = paramTypeOwnerModName;
    if (ptOwnerName.empty() && paramTypep) {
        AstNodeModule* const ptOwnerModp = findOwnerModule(paramTypep);
        if (ptOwnerModp) ptOwnerName = ptOwnerModp->name();
    }
    UINFO(9, "addParamType: refp=" << refp
              << " cellPath='" << cellPath << "'"
              << " ownerModp=" << (ownerModp ? ownerModp->name() : "<null>")
              << " paramTypep=" << paramTypep
              << " paramTypeOwnerModName='" << ptOwnerName << "'"
              << endl);
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
    const CaptureKey key{refp, cellPath};
    s_map[key] = CapturedEntry{CaptureType::IFACE, refp, cellPath, nullptr,
                               ownerModp, nullptr, paramTypep, ptOwnerName, ifacePortVarp};

    // Also capture REFDTYPEs inside the PARAMTYPEDTYPE's subDTypep chain.
    if (paramTypep) {
        paramTypep->foreach([&](AstRefDType* innerRefp) {
            if (innerRefp == refp) return;
            if (!innerRefp->refDTypep()) return;

            AstNodeModule* const refOwnerModp = findOwnerModule(innerRefp->refDTypep());
            if (refOwnerModp && VN_IS(refOwnerModp, Iface)
                && refOwnerModp->name() != ptOwnerName) {
                const CaptureKey innerKey{innerRefp, cellPath};
                if (s_map.find(innerKey) == s_map.end()) {
                    // Find the cell name for the nested interface
                    string nestedCellName;
                    AstNodeModule* const ptOwnerModp = findOwnerModule(paramTypep);
                    if (ptOwnerModp) {
                        for (AstNode* stmtp = ptOwnerModp->stmtsp(); stmtp;
                             stmtp = stmtp->nextp()) {
                            if (AstCell* const cp = VN_CAST(stmtp, Cell)) {
                                if (cp->modp() == refOwnerModp) {
                                    nestedCellName = cp->name();
                                    break;
                                }
                            }
                        }
                    }
                    if (nestedCellName.empty()) {
                        UINFO(1, "addParamType WARNING: could not find cell for nested iface '"
                                  << refOwnerModp->name() << "' in '"
                                  << (ptOwnerModp ? ptOwnerModp->name() : "<null>")
                                  << "' — using parent cellPath='" << cellPath << "'" << endl);
                    }
                    UINFO(9, "addParamType: also capturing inner RefDType " << innerRefp
                              << " refDTypep owner=" << refOwnerModp->name()
                              << " nestedCellName='" << nestedCellName << "'" << endl);
                    s_map[innerKey] = CapturedEntry{
                        CaptureType::IFACE, innerRefp, nestedCellName.empty() ? cellPath : nestedCellName,
                        nullptr, ptOwnerModp,
                        innerRefp->typedefp(), nullptr, refOwnerModp->name(), nullptr};
                }
            }
        });
    }
}

bool V3LinkDotIfaceCapture::replaceParamType(const AstRefDType* refp, const string& cellPath,
                                              AstParamTypeDType* newParamTypep) {
    UINFO(9, "replaceParamType called: refp=" << refp
              << " cellPath='" << cellPath << "'"
              << " newParamTypep=" << (newParamTypep ? newParamTypep->name() : "<null>") << endl);
    if (!refp || !newParamTypep) return false;
    const CaptureKey key{refp, cellPath};
    auto it = s_map.find(key);
    if (it == s_map.end()) {
        UINFO(9, "replaceParamType: entry not found for refp=" << refp
                  << " cellPath='" << cellPath << "'" << endl);
        return false;
    }
    CapturedEntry& entry = it->second;
    entry.paramTypep = newParamTypep;
    AstNodeModule* const paramOwnerModp = findOwnerModule(newParamTypep);
    if (paramOwnerModp) {
        entry.typedefOwnerModName = paramOwnerModp->name();
    } else {
        UINFO(1, "replaceParamType WARNING: findOwnerModule returned null"
                  " for newParamTypep='" << newParamTypep->name()
                  << "' — typedefOwnerModName left as '" << entry.typedefOwnerModName << "'" << endl);
    }
    UASSERT(entry.refp, "replaceParamType: entry has null refp");
    entry.refp->refDTypep(newParamTypep);
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
                            auto existing = templateToCloneMap.find(tmplp);
                            if (existing != templateToCloneMap.end()) {
                                UINFO(1, "iface capture WARNING: finalizeIfaceCapture"
                                          " multiple clones for template '"
                                          << templateName << "': existing='"
                                          << existing->second->name()
                                          << "' new='" << modp->name()
                                          << "' — keeping first" << endl);
                            } else {
                                templateToCloneMap[tmplp] = modp;
                            }
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
