// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Interface typedef capture helper.
//   Keyed by (templateRefp, cellPath) so each clone gets its own entry.
//   No pointer-chasing disambiguation — cellPath strings are stable,
//   hierarchical, and exact.  V3Param clones create new entries;
//   replaceTypedef is a direct lookup.
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
#include <string>
#include <unordered_map>

class V3LinkDotIfaceCapture final {
public:
    enum class CaptureType { IFACE, CLASS };

    // Composite map key: (template RefDType pointer, hierarchical cell path).
    // Each clone of the same template RefDType gets its own entry because
    // the cloned RefDType pointer differs.  The cellPath disambiguates
    // entries that reference through different interface instances.
    // cellPath is the dot-separated path from the owning module to the
    // interface cell, e.g. "a_inst", "wif.a_inst", "outer.mid.inner".
    struct CaptureKey final {
        const AstRefDType* templateRefp = nullptr;
        string cellPath;  // Hierarchical, e.g. "wif.a_inst" — stable, never mutated
        bool operator==(const CaptureKey& o) const {
            return templateRefp == o.templateRefp && cellPath == o.cellPath;
        }
    };
    struct CaptureKeyHash final {
        size_t operator()(const CaptureKey& k) const {
            size_t h = std::hash<const void*>{}(k.templateRefp);
            h ^= std::hash<string>{}(k.cellPath) + 0x9e3779b9 + (h << 6) + (h >> 2);
            return h;
        }
    };

    struct CapturedEntry final {
        CaptureType captureType = CaptureType::IFACE;
        AstRefDType* refp = nullptr;
        string cellPath;  // Hierarchical path (e.g. "wif.a_inst") — immutable key component
        AstClass* origClassp = nullptr;  // For CLASS captures
        // Module where the RefDType lives
        AstNodeModule* ownerModp = nullptr;
        // Typedef definition being referenced
        AstTypedef* typedefp = nullptr;
        // For PARAMTYPEDTYPE
        AstParamTypeDType* paramTypep = nullptr;
        // Name of the module/interface that owns the typedef (stable string)
        string typedefOwnerModName;
        // Interface port variable for matching during cloning
        AstVar* ifacePortVarp = nullptr;
    };

    using CapturedMap = std::unordered_map<CaptureKey, CapturedEntry, CaptureKeyHash>;

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
    static bool s_explicitlyDisabled;  // Set when explicitly disabled by DepGraph

    static string extractIfacePortName(const string& dotText);

    template <typename FilterFn, typename Fn>
    static void forEachImpl(FilterFn&& filter, Fn&& fn);

public:
    static void enable(bool flag) {
        if (flag && s_explicitlyDisabled) {
            v3fatal("V3LinkDotIfaceCapture::enable(true) called after explicit disable. "
                    "DepGraph is replacing IfaceCapture - this should not happen.");
        }
        s_enabled = flag;
        if (!flag) {
            s_explicitlyDisabled = true;
            s_map.clear();
            s_localparamMap.clear();
        }
    }
    static bool enabled() { return s_enabled; }
    static bool explicitlyDisabled() { return s_explicitlyDisabled; }
    static void reset() {
        s_map.clear();
        s_localparamMap.clear();
    }
    static AstNodeModule* findOwnerModule(AstNode* nodep);
    // Extract the last dot-separated component from a cellPath
    static string lastPathComponent(const string& cellPath);
    static void add(AstRefDType* refp, const string& cellPath, AstNodeModule* ownerModp,
                    AstTypedef* typedefp = nullptr,
                    const string& typedefOwnerModName = "",
                    AstVar* ifacePortVarp = nullptr);
    static void addClass(AstRefDType* refp, AstClass* origClassp, AstNodeModule* ownerModp,
                         AstTypedef* typedefp = nullptr,
                         const string& typedefOwnerModName = "");
    static void addParamType(AstRefDType* refp, const string& cellPath,
                             AstNodeModule* ownerModp,
                             AstParamTypeDType* paramTypep,
                             const string& paramTypeOwnerModName,
                             AstVar* ifacePortVarp);
    static const CapturedEntry* find(const AstRefDType* refp, const string& cellPath);
    // Search all entries for a given refp regardless of cellPath (for resolve-pass checks)
    static const CapturedEntry* findAny(const AstRefDType* refp);
    static bool eraseAll(const AstRefDType* refp);
    static void forEach(const std::function<void(const CapturedEntry&)>& fn);
    static void forEachOwned(const AstNodeModule* ownerModp,
                             const std::function<void(const CapturedEntry&)>& fn);
    static bool replaceRef(const AstRefDType* oldRefp, AstRefDType* newRefp,
                           const string& cellPath);
    static bool replaceTypedef(const AstRefDType* refp, const string& cellPath,
                               AstTypedef* newTypedefp);
    static bool erase(const AstRefDType* refp, const string& cellPath);
    static std::size_t size() { return s_map.size(); }
    // Create a new entry for a cloned RefDType, inheriting cellPath from the original
    static void propagateClone(const AstRefDType* origRefp, AstRefDType* newRefp,
                               const string& cellPath);

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

    static bool replaceParamType(const AstRefDType* refp, const string& cellPath,
                                 AstParamTypeDType* newParamTypep);

    // Debug: dump all captured entries
    static void dumpEntries(const string& label);

    // Called after V3Param but before V3Dead to fix any remaining cross-interface refs
    // that still point to template nodes (which will be deleted by V3Dead).
    static void finalizeIfaceCapture();
};

#endif  // VERILATOR_V3LINKDOTIFACECAPTURE_H_
