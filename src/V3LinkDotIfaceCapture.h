// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Interface typedef capture helper.
//   Stores (refp, typedefp, cellp, owners, pendingClone) so LinkDot can
//   rebind refs when symbol lookup fails, and V3Param clones can retarget
//   typedefs without legacy paths.
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

#ifndef VERILATOR_V3LINKDOTIFACECAPTURE_H_
#define VERILATOR_V3LINKDOTIFACECAPTURE_H_

#include "config_build.h"

#include "V3Ast.h"
#include "V3SymTable.h"

#include <cstddef>
#include <functional>
#include <unordered_map>

class V3LinkDotIfaceCapture final {
public:
    enum class CaptureType { IFACE, CLASS };
    struct CapturedIfaceTypedef final {
        CaptureType captureType = CaptureType::IFACE;
        AstRefDType* refp = nullptr;
        AstCell* cellp = nullptr;  // now for IFACE captures
        AstClass* origClassp = nullptr;  // new for CLASS captures
        // Module where the RefDType lives
        AstNodeModule* ownerModp = nullptr;
        // Typedef definition being referenced
        AstTypedef* typedefp = nullptr;
        // For PARAMTYPEDTYPE
        AstParamTypeDType* paramTypep = nullptr;
        // Interface/module that owns typedefp
        AstNodeModule* typedefOwnerModp = nullptr;
        // Cloned RefDTypes awaiting typedef rebinding (one per module clone).
        // Each entry is (clonedRefDType, clonedCell) — the cell is used to
        // disambiguate which clone should receive which typedef.
        struct PendingClone {
            AstRefDType* refp = nullptr;
            AstCell* cellp = nullptr;  // The cloned cell whose modp() owns the target typedef
        };
        std::vector<PendingClone> pendingClones;
        // Interface port variable for matching during cloning
        AstVar* ifacePortVarp = nullptr;
    };

    using CapturedMap = std::unordered_map<const AstRefDType*, CapturedIfaceTypedef>;

    // Captured localparam expression for interfaces/classes
    struct CapturedIfaceLocalparam final {
        AstVar* varp = nullptr;           // The localparam variable
        AstNode* origExprp = nullptr;     // Clone of original expression (before constification)
        AstNodeModule* ownerModp = nullptr;  // Owning interface/class
    };
    using LocalparamMap = std::unordered_map<const AstVar*, CapturedIfaceLocalparam>;

    // Deferred fixup: records that a REFDTYPE's typedefp/refDTypep should be
    // redirected from a node in templateModp to the corresponding node in cloneModp.
    // Recorded at V3Param clone time (when we know the exact clone mapping),
    // applied at finalizeIfaceCapture (when all clones exist and have correct types).
    struct DeferredRefFixup final {
        AstRefDType* refp = nullptr;           // The REFDTYPE to fix
        AstNodeModule* templateModp = nullptr;  // Template interface containing the old target
        AstNodeModule* cloneModp = nullptr;     // Cloned interface containing the correct target
    };

private:
    static CapturedMap s_map;
    static LocalparamMap s_localparamMap;
    static std::vector<DeferredRefFixup> s_deferredFixups;
    static bool s_enabled;
    static bool s_explicitlyDisabled;  // Set when explicitly disabled by DepGraph

    static bool finalizeCapturedEntry(CapturedMap::iterator it, const char* reasonp,
                                      AstCell* matchCellp = nullptr);
    static string extractIfacePortName(const string& dotText);

    template <typename FilterFn, typename Fn>
    static void forEachImpl(FilterFn&& filter, Fn&& fn);

public:
    static void enable(bool flag) {
        if (flag && s_explicitlyDisabled) {
            // Error if trying to re-enable after explicit disable
            v3fatal("V3LinkDotIfaceCapture::enable(true) called after explicit disable. "
                    "DepGraph is replacing IfaceCapture - this should not happen.");
        }
        s_enabled = flag;
        if (!flag) {
            s_explicitlyDisabled = true;  // Mark as explicitly disabled
            s_map.clear();
            s_localparamMap.clear();
            s_deferredFixups.clear();
        }
    }
    static bool enabled() { return s_enabled; }
    static bool explicitlyDisabled() { return s_explicitlyDisabled; }
    static void reset() {
        s_map.clear();
        s_localparamMap.clear();
        s_deferredFixups.clear();
    }
    static AstNodeModule* findOwnerModule(AstNode* nodep);
    static void add(AstRefDType* refp, AstCell* cellp, AstNodeModule* ownerModp,
                    AstTypedef* typedefp = nullptr, AstNodeModule* typedefOwnerModp = nullptr,
                    AstVar* ifacePortVarp = nullptr);
    static void addClass(AstRefDType* refp, AstClass* origClassp, AstNodeModule* ownerModp,
                         AstTypedef* typedefp = nullptr,
                         AstNodeModule* typedefOwnerModp = nullptr);
    static void addParamType(AstRefDType* refp, AstCell* cellp,
                  AstNodeModule* ownerModp,
                  AstParamTypeDType* paramTypep,
                  AstNodeModule* paramTypeOwnerModp,
                  AstVar* ifacePortVarp);
    static const CapturedIfaceTypedef* find(const AstRefDType* refp);
    static void forEach(const std::function<void(const CapturedIfaceTypedef&)>& fn);
    static void forEachOwned(const AstNodeModule* ownerModp,
                             const std::function<void(const CapturedIfaceTypedef&)>& fn);
    static bool replaceRef(const AstRefDType* oldRefp, AstRefDType* newRefp);
    static bool replaceTypedef(const AstRefDType* refp, AstTypedef* newTypedefp,
                               AstCell* matchCellp = nullptr);
    static bool erase(const AstRefDType* refp);
    static std::size_t size() { return s_map.size(); }
    static void propagateClone(const AstRefDType* origRefp, AstRefDType* newRefp);

    static bool shouldApplyToClone(const CapturedIfaceTypedef& entry,
                                   const AstNodeModule* srcModp,
                                   const AstCell* cloneCellp);

    static void
    captureTypedefContext(AstRefDType* refp, const char* stageLabel, int dotPos, bool dotIsFinal,
                          const std::string& dotText, VSymEnt* dotSymp, VSymEnt* curSymp,
                          AstNodeModule* modp, AstNode* nodep,
                          const std::function<bool(AstVar*, AstRefDType*)>& promoteVarCb,
                          const std::function<std::string()>& indentFn);

    // Localparam expression capture
    static void addLocalparam(AstVar* varp, AstNode* exprp, AstNodeModule* ownerModp);
    static const CapturedIfaceLocalparam* findLocalparam(const AstVar* varp);
    static void forEachLocalparamOwned(
        const AstNodeModule* ownerModp,
        const std::function<void(const CapturedIfaceLocalparam&)>& fn);
    static std::size_t localparamSize() { return s_localparamMap.size(); }

    static bool replaceParamType(const AstRefDType* refp,
                                              AstParamTypeDType* newParamTypep);


    // Record a deferred fixup: refp's typedefp/refDTypep should be redirected
    // from a node in templateModp to the corresponding node in cloneModp.
    // Called from V3Param at clone time when we know the exact instance→clone mapping.
    static void addDeferredFixup(AstRefDType* refp, AstNodeModule* templateModp,
                                 AstNodeModule* cloneModp);

    // Called after V3Param but before V3Dead to fix any remaining cross-interface refs
    // that were created during V3Width::widthParamsEdit() and weren't captured earlier.
    // This walks the type table and all cloned modules to fix refDTypep pointers
    // that still point to template nodes (which will be deleted by V3Dead).
    static void finalizeIfaceCapture();
};

#endif  // VERILATOR_V3LINKDOTIFACECAPTURE_H_
