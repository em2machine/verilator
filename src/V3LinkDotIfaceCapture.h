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
        // Interface/module that owns typedefp
        AstNodeModule* typedefOwnerModp = nullptr;
        // Cloned RefDType awaiting typedef rebinding
        AstRefDType* pendingClonep = nullptr;
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

private:
    static CapturedMap s_map;
    static LocalparamMap s_localparamMap;
    static bool s_enabled;

    static AstNodeModule* findOwnerModule(AstNode* nodep);
    static bool finalizeCapturedEntry(CapturedMap::iterator it, const char* reasonp);
    static string extractIfacePortName(const string& dotText);

    template <typename FilterFn, typename Fn>
    static void forEachImpl(FilterFn&& filter, Fn&& fn);

public:
    static void enable(bool flag) {
        s_enabled = flag;
        if (!flag) {
            s_map.clear();
            s_localparamMap.clear();
        }
    }
    static bool enabled() { return s_enabled; }
    static void reset() {
        s_map.clear();
        s_localparamMap.clear();
    }
    static void add(AstRefDType* refp, AstCell* cellp, AstNodeModule* ownerModp,
                    AstTypedef* typedefp = nullptr, AstNodeModule* typedefOwnerModp = nullptr,
                    AstVar* ifacePortVarp = nullptr);
    static void addClass(AstRefDType* refp, AstClass* origClassp, AstNodeModule* ownerModp,
                         AstTypedef* typedefp = nullptr,
                         AstNodeModule* typedefOwnerModp = nullptr);
    static const CapturedIfaceTypedef* find(const AstRefDType* refp);
    static void forEach(const std::function<void(const CapturedIfaceTypedef&)>& fn);
    static void forEachOwned(const AstNodeModule* ownerModp,
                             const std::function<void(const CapturedIfaceTypedef&)>& fn);
    static bool replaceRef(const AstRefDType* oldRefp, AstRefDType* newRefp);
    static bool replaceTypedef(const AstRefDType* refp, AstTypedef* newTypedefp);
    static bool erase(const AstRefDType* refp);
    static std::size_t size() { return s_map.size(); }
    static void propagateClone(const AstRefDType* origRefp, AstRefDType* newRefp);

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
};

#endif  // VERILATOR_V3LINKDOTIFACECAPTURE_H_
