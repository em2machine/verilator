// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Replicate modules for parameterization
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
// PARAM TRANSFORMATIONS:
//   Top down traversal:
//      For each cell:
//          If parameterized,
//              Determine all parameter widths, constant values.
//              (Interfaces also matter, as if a module is parameterized
//              this effectively changes the width behavior of all that
//              reference the iface.)
//
//              Clone module cell calls, renaming with __{par1}_{par2}_...
//              Substitute constants for cell's module's parameters.
//              Relink pins and cell and ifacerefdtype to point to new module.
//
//              For interface Parent's we have the AstIfaceRefDType::cellp()
//              pointing to this module.  If that parent cell's interface
//              module gets parameterized, AstIfaceRefDType::cloneRelink
//              will update AstIfaceRefDType::cellp(), and V3LinkDot will
//              see the new interface.
//
//              However if a submodule's AstIfaceRefDType::ifacep() points
//              to the old (unparameterized) interface and needs correction.
//              To detect this we must walk all pins looking for interfaces
//              that the parent has changed and propagate down.
//
//          Then process all modules called by that cell.
//          (Cells never referenced after parameters expanded must be ignored.)
//
//   After we complete parameters, the varp's will be wrong (point to old module)
//   and must be relinked.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Param.h"

#include "V3Case.h"
#include "V3Const.h"
#include "V3EmitV.h"
#include "V3Hasher.h"
#include "V3LinkDotDepGraph.h"
#include "V3LinkDotIfaceCapture.h"
#include "V3MemberMap.h"
#include "V3Os.h"
#include "V3Parse.h"
#include "V3Simulate.h"
#include "V3Stats.h"
#include "V3Unroll.h"
#include "V3Width.h"

#include <cctype>
#include <cstdlib>
#include <deque>
#include <map>
#include <memory>
#include <vector>
#include <unordered_map>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Hierarchical block and parameter db (modules without parameters are also handled)

class ParameterizedHierBlocks final {
    using HierBlockOptsByOrigName = std::multimap<std::string, const V3HierarchicalBlockOption*>;
    using HierMapIt = HierBlockOptsByOrigName::const_iterator;
    using HierBlockModMap = std::map<const std::string, AstNodeModule*>;
    using ParamConstMap = std::map<const std::string, std::unique_ptr<AstConst>>;
    using GParamsMap = std::map<const std::string, AstVar*>;  // key:parameter name value:parameter

    // MEMBERS
    const bool m_hierSubRun;  // Is in sub-run for hierarchical verilation
    // key:Original module name, value:HiearchyBlockOption*
    // If a module is parameterized, the module is uniquified to overridden parameters.
    // This is why HierBlockOptsByOrigName is multimap.
    HierBlockOptsByOrigName m_hierBlockOptsByOrigName;
    // key:mangled module name, value:AstNodeModule*
    HierBlockModMap m_hierBlockMod;
    // Overridden parameters of the hierarchical block
    std::map<const V3HierarchicalBlockOption*, ParamConstMap> m_hierParams;
    // Parameter variables of hierarchical blocks
    std::map<const std::string, GParamsMap> m_modParams;

    // METHODS

public:
    ParameterizedHierBlocks(const V3HierBlockOptSet& hierOpts, AstNetlist* nodep)
        : m_hierSubRun{(!v3Global.opt.hierBlocks().empty() || v3Global.opt.hierChild())
                       // Exclude consolidation
                       && !v3Global.opt.hierParamFile().empty()} {
        for (const auto& hierOpt : hierOpts) {
            m_hierBlockOptsByOrigName.emplace(hierOpt.second.origName(), &hierOpt.second);
            const V3HierarchicalBlockOption::ParamStrMap& params = hierOpt.second.params();
            ParamConstMap& consts = m_hierParams[&hierOpt.second];
            for (V3HierarchicalBlockOption::ParamStrMap::const_iterator pIt = params.begin();
                 pIt != params.end(); ++pIt) {
                std::unique_ptr<AstConst> constp{AstConst::parseParamLiteral(
                    new FileLine{FileLine::builtInFilename()}, pIt->second)};
                UASSERT(constp, pIt->second << " is not a valid parameter literal");
                const bool inserted = consts.emplace(pIt->first, std::move(constp)).second;
                UASSERT(inserted, pIt->first << " is already added");
            }
            // origName may be already registered, but it's fine.
            m_modParams.insert({hierOpt.second.origName(), {}});
        }
        for (AstNodeModule* modp = nodep->modulesp(); modp;
             modp = VN_AS(modp->nextp(), NodeModule)) {
            if (hierOpts.find(modp->prettyName()) != hierOpts.end()) {
                m_hierBlockMod.emplace(modp->name(), modp);
            }
            // Recursive hierarchical module may change its name, so we have to match its origName.
            // Collect values from recursive cloned module as parameters in the top module could be
            // overridden.
            const string actualModName = modp->recursiveClone() ? modp->origName() : modp->name();
            const auto defParamIt = m_modParams.find(actualModName);
            if (defParamIt != m_modParams.end()) {
                // modp is the original of parameterized hierarchical block
                for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                    if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                        if (varp->isGParam()) defParamIt->second.emplace(varp->name(), varp);
                    }
                }
            }
        }
    }
    bool hierSubRun() const { return m_hierSubRun; }
    bool isHierBlock(const string& origName) const {
        return m_hierBlockOptsByOrigName.find(origName) != m_hierBlockOptsByOrigName.end();
    }
    AstNodeModule* findByParams(const string& origName, AstPin* firstPinp,
                                const AstNodeModule* modp) {
        UASSERT(isHierBlock(origName), origName << " is not hierarchical block");
        // This module is a hierarchical block. Need to replace it by the --lib-create wrapper.
        const std::pair<HierMapIt, HierMapIt> candidates
            = m_hierBlockOptsByOrigName.equal_range(origName);
        const auto paramsIt = m_modParams.find(origName);
        UASSERT_OBJ(paramsIt != m_modParams.end(), modp, origName << " must be registered");
        HierMapIt hierIt;
        for (hierIt = candidates.first; hierIt != candidates.second; ++hierIt) {
            bool found = true;
            size_t paramIdx = 0;
            const ParamConstMap& params = m_hierParams[hierIt->second];
            UASSERT(params.size() == hierIt->second->params().size(), "not match");
            for (AstPin* pinp = firstPinp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
                if (!pinp->exprp()) continue;
                if (const AstVar* const modvarp = pinp->modVarp()) {
                    AstConst* const constp = VN_AS(pinp->exprp(), Const);
                    UASSERT_OBJ(constp, pinp,
                                "parameter for a hierarchical block must have been constified");
                    const auto paramIt = paramsIt->second.find(modvarp->name());
                    UASSERT_OBJ(paramIt != paramsIt->second.end(), modvarp, "must be registered");
                    AstConst* const defValuep = VN_CAST(paramIt->second->valuep(), Const);
                    if (defValuep && areSame(constp, defValuep)) {
                        UINFO(5, "Setting default value of " << constp << " to " << modvarp);
                        continue;  // Skip this parameter because setting the same value
                    }
                    const auto pIt = vlstd::as_const(params).find(modvarp->name());
                    UINFO(5, "Comparing " << modvarp->name() << " " << constp);
                    if (pIt == params.end() || paramIdx >= params.size()
                        || !areSame(constp, pIt->second.get())) {
                        found = false;
                        break;
                    }
                    UINFO(5, "Matched " << modvarp->name() << " " << constp << " and "
                                        << pIt->second.get());
                    ++paramIdx;
                }
            }
            if (found && paramIdx == hierIt->second->params().size()) break;
        }
        UASSERT_OBJ(hierIt != candidates.second, firstPinp, "No --lib-create wrapper found");
        // parameter settings will be removed in the bottom of caller visitCell().
        const HierBlockModMap::const_iterator modIt
            = m_hierBlockMod.find(hierIt->second->mangledName());
        UASSERT_OBJ(modIt != m_hierBlockMod.end(), firstPinp,
                    hierIt->second->mangledName() << " is not found");

        const auto it = vlstd::as_const(m_hierBlockMod).find(hierIt->second->mangledName());
        if (it == m_hierBlockMod.end()) return nullptr;
        return it->second;
    }
    static bool areSame(AstConst* pinValuep, AstConst* hierOptParamp) {
        if (pinValuep->isString()) {
            return pinValuep->num().toString() == hierOptParamp->num().toString();
        }

        if (hierOptParamp->isDouble()) {
            double var;
            if (pinValuep->isDouble()) {
                var = pinValuep->num().toDouble();
            } else {  // Cast from integer to real
                V3Number varNum{pinValuep, V3Number::Double{}, 0.0};
                varNum.opIToRD(pinValuep->num());
                var = varNum.toDouble();
            }
            return V3Number::epsilonEqual(var, hierOptParamp->num().toDouble());
        } else {  // Now integer type is assumed
            // Bitwidth of hierOptParamp is accurate because V3Width already calculated in the
            // previous run. Bitwidth of pinValuep is before width analysis, so pinValuep is casted
            // to hierOptParamp width.
            V3Number varNum{pinValuep, hierOptParamp->num().width()};
            if (pinValuep->isDouble()) {  // Need to cast to int
                // Parameter is actually an integral type, but passed value is floating point.
                // Conversion from real to integer uses rounding in V3Width.cpp
                varNum.opRToIRoundS(pinValuep->num());
            } else if (pinValuep->isSigned()) {
                varNum.opExtendS(pinValuep->num(), pinValuep->num().width());
            } else {
                varNum.opAssign(pinValuep->num());
            }
            V3Number isEq{pinValuep, 1};
            isEq.opEq(varNum, hierOptParamp->num());
            return isEq.isNeqZero();
        }
    }
};

//######################################################################
// Remove parameters from cells and build new modules

class ParamProcessor final {
    // NODE STATE - Local
    //   AstVar::user3()        // int    Global parameter number (for naming new module)
    //                          //        (0=not processed, 1=iterated, but no number,
    //                          //         65+ parameter numbered)
    // NODE STATE - Shared with ParamVisitor
    //   AstNodeModule::user3p()  // AstNodeModule* Unaltered copy of the parameterized module.
    //                               The module/class node may be modified according to parameter
    //                               values and an unchanged copy is needed to instantiate
    //                               modules/classes with different parameters.
    //   AstNodeModule::user2() // bool   True if processed
    //   AstGenFor::user2()     // bool   True if processed
    //   AstVar::user2()        // bool   True if constant propagated
    //   AstCell::user2p()      // string* Generate portion of hierarchical name
    //   AstNodeModule:user4p() // AstNodeModule* Parametrized copy with default parameters
    const VNUser2InUse m_inuser2;
    const VNUser3InUse m_inuser3;
    const VNUser4InUse m_inuser4;
    // User1 used by constant function simulations

    // TYPES
    // Note may have duplicate entries
    using IfaceRefRefs = std::deque<std::pair<AstIfaceRefDType*, AstIfaceRefDType*>>;

    // STATE
    using CloneMap = std::unordered_map<const AstNode*, AstNode*>;
    struct ModInfo final {
        AstNodeModule* const m_modp;  // Module with specified name
        CloneMap m_cloneMap;  // Map of old-varp -> new cloned varp
        explicit ModInfo(AstNodeModule* modp)
            : m_modp{modp} {}
    };
    std::map<const std::string, ModInfo> m_modNameMap;  // Hash of created module flavors by name

    std::map<const std::string, std::string>
        m_longMap;  // Hash of very long names to unique identity number
    int m_longId = 0;

    // All module names that are loaded from source code
    // Generated modules by this visitor is not included
    VStringSet m_allModuleNames;

    CloneMap m_originalParams;  // Map between parameters of copied parameteized classes and their
                                // original nodes

    std::map<const V3Hash, int> m_valueMap;  // Hash of node hash to param value
    int m_nextValue = 1;  // Next value to use in m_valueMap

    const AstNodeModule* m_modp = nullptr;  // Current module being processed

    // Database to get lib-create wrapper that matches parameters in hierarchical Verilation
    ParameterizedHierBlocks m_hierBlocks;
    // Default parameter values key:parameter name, value:default value (can be nullptr)
    using DefaultValueMap = std::map<std::string, AstNode*>;
    // Default parameter values of hierarchical blocks
    std::map<AstNodeModule*, DefaultValueMap> m_defaultParameterValues;
    VNDeleter m_deleter;  // Used to delay deletion of nodes
    // Class default paramater dependencies
    std::vector<std::pair<AstParamTypeDType*, int>> m_classParams;
    std::unordered_map<AstParamTypeDType*, int> m_paramIndex;

    // member names cached for fast lookup
    VMemberMap m_memberMap;

    // METHODS

    static void makeSmallNames(AstNodeModule* modp) {
        std::vector<int> usedLetter;
        usedLetter.resize(256);
        // Pass 1, assign first letter to each gparam's name
        for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                if (varp->isGParam() || varp->isIfaceRef()) {
                    char ch = varp->name()[0];
                    ch = std::toupper(ch);
                    if (ch < 'A' || ch > 'Z') ch = 'Z';
                    varp->user3(usedLetter[static_cast<int>(ch)] * 256 + ch);
                    usedLetter[static_cast<int>(ch)]++;
                }
            } else if (AstParamTypeDType* const typep = VN_CAST(stmtp, ParamTypeDType)) {
                const char ch = 'T';
                typep->user3(usedLetter[static_cast<int>(ch)] * 256 + ch);
                usedLetter[static_cast<int>(ch)]++;
            }
        }
    }
    static string paramSmallName(AstNodeModule* modp, AstNode* varp) {
        if (varp->user3() <= 1) makeSmallNames(modp);
        int index = varp->user3() / 256;
        const char ch = varp->user3() & 255;
        string st = cvtToStr(ch);
        while (index) {
            st += cvtToStr(char((index % 25) + 'A'));
            index /= 26;
        }
        return st;
    }

    static string paramValueString(const AstNode* nodep) {
        if (const AstRefDType* const refp = VN_CAST(nodep, RefDType)) {
            nodep = refp->skipRefToNonRefp();
        }
        string key = nodep->name();
        if (const AstIfaceRefDType* const ifrtp = VN_CAST(nodep, IfaceRefDType)) {
            if (ifrtp->cellp() && ifrtp->cellp()->modp()) {
                key = ifrtp->cellp()->modp()->name();
            } else if (ifrtp->ifacep()) {
                key = ifrtp->ifacep()->name();
            } else {
                nodep->v3fatalSrc("Can't parameterize interface without module name");
            }
        } else if (const AstNodeUOrStructDType* const dtypep
                   = VN_CAST(nodep, NodeUOrStructDType)) {
            key += " ";
            key += dtypep->verilogKwd();
            key += " {";
            for (const AstNode* memberp = dtypep->membersp(); memberp;
                 memberp = memberp->nextp()) {
                key += paramValueString(memberp);
                key += ";";
            }
            key += "}";
        } else if (const AstMemberDType* const dtypep = VN_CAST(nodep, MemberDType)) {
            key += " ";
            key += paramValueString(dtypep->subDTypep());
        } else if (const AstBasicDType* const dtypep = VN_CAST(nodep, BasicDType)) {
            if (dtypep->isSigned()) key += " signed";
            if (dtypep->isRanged()) {
                key += "[" + cvtToStr(dtypep->left()) + ":" + cvtToStr(dtypep->right()) + "]";
            }
        } else if (const AstPackArrayDType* const dtypep = VN_CAST(nodep, PackArrayDType)) {
            key += "[";
            key += cvtToStr(dtypep->left());
            key += ":";
            key += cvtToStr(dtypep->right());
            key += "] ";
            key += paramValueString(dtypep->subDTypep());
        } else if (const AstInitArray* const initp = VN_CAST(nodep, InitArray)) {
            key += "{";
            for (auto it : initp->map()) {
                key += paramValueString(it.second->valuep());
                key += ",";
            }
            key += "}";
        } else if (const AstClassRefDType* const classRefp = VN_CAST(nodep, ClassRefDType)) {
            // For parameterized class types, use the original class name (without specialization
            // suffix) plus the actual type parameter values. This ensures equivalent class types
            // get the same string representation regardless of which AST node is used.
            if (classRefp->classp()) {
                const string& className = classRefp->classp()->name();
                const string& origName = classRefp->classp()->origName();
                const bool isSpecialized = (className != origName);
                UINFO(9, "paramValueString ClassRefDType: name=" << className
                         << " origName=" << origName << " isSpecialized=" << isSpecialized
                         << " hasParams=" << (classRefp->paramsp() ? "Y" : "N")
                         << " classHasGParam=" << classRefp->classp()->hasGParam() << endl);

                if (classRefp->paramsp()) {
                    // Has explicit type parameters - use origName + params
                    key = origName;
                    key += "#(";
                    for (AstPin* pinp = classRefp->paramsp(); pinp;
                         pinp = VN_AS(pinp->nextp(), Pin)) {
                        if (pinp != classRefp->paramsp()) key += ",";
                        if (pinp->exprp()) {
                            key += paramValueString(pinp->exprp());
                        }
                    }
                    key += ")";
                } else if (isSpecialized) {
                    // Already specialized class (e.g., c1__Tz1_TBz1) - use full name
                    // This ensures different specializations are distinguished
                    key = className;
                } else {
                    // Unspecialized class with no params - use origName
                    key = origName;
                }
            } else {
                key += classRefp->prettyDTypeName(true);
            }
        } else if (const AstNodeDType* const dtypep = VN_CAST(nodep, NodeDType)) {
            key += dtypep->prettyDTypeName(true);
        }
        UASSERT_OBJ(!key.empty(), nodep, "Parameter yielded no value string");
        return key;
    }

    string paramValueNumber(AstNode* nodep) {
        // For type parameters (NodeDType), use only the string representation for hashing.
        // Using V3Hasher::uncachedHash includes AST node pointer which differs for equivalent
        // types represented by different AST nodes (e.g., parameterized class specializations).
        // For value parameters, we can still use the AST hash for better collision resistance.
        if (AstRefDType* const refp = VN_CAST(nodep, RefDType)) {
            nodep = refp->skipRefToNonRefp();
        }
        const string paramStr = paramValueString(nodep);
        V3Hash hash;
        if (VN_IS(nodep, NodeDType)) {
            // Type parameter: use only string-based hash for type equivalence
            hash = V3Hash{paramStr};
        } else {
            // Value parameter: use AST hash + string for better collision resistance
            hash = V3Hasher::uncachedHash(nodep) + paramStr;
        }
        // Force hash collisions -- for testing only
        // cppcheck-suppress unreadVariable
        if (VL_UNLIKELY(v3Global.opt.debugCollision())) hash = V3Hash{paramStr};
        int num;
        const auto pair = m_valueMap.emplace(hash, 0);
        if (pair.second) pair.first->second = m_nextValue++;
        num = pair.first->second;
        return "z"s + cvtToStr(num);
    }
    string moduleCalcName(const AstNodeModule* srcModp, const string& longname) {
        string newname = longname;
        if (longname.length() > 30) {
            const auto pair = m_longMap.emplace(longname, "");
            if (pair.second) {
                newname = srcModp->name();
                // We use all upper case above, so lower here can't conflict
                newname += "__pi" + cvtToStr(++m_longId);
                pair.first->second = newname;
            }
            newname = pair.first->second;
        }
        UINFO(4, "Name: " << srcModp->name() << "->" << longname << "->" << newname);
        return newname;
    }
    AstNodeDType* arraySubDTypep(AstNodeDType* nodep) {
        // If an unpacked array, return the subDTypep under it
        if (const AstUnpackArrayDType* const adtypep = VN_CAST(nodep, UnpackArrayDType)) {
            return adtypep->subDTypep();
        }
        // We have not resolved parameter of the child yet, so still
        // have BracketArrayDType's. We'll presume it'll end up as assignment
        // compatible (or V3Width will complain).
        if (const AstBracketArrayDType* const adtypep = VN_CAST(nodep, BracketArrayDType)) {
            return adtypep->subDTypep();
        }
        return nullptr;
    }
    bool isString(AstNodeDType* nodep) {
        if (AstBasicDType* const basicp = VN_CAST(nodep->skipRefToNonRefp(), BasicDType))
            return basicp->isString();
        return false;
    }
    void collectPins(CloneMap* clonemapp, AstNodeModule* modp, bool originalIsCopy) {
        // Grab all I/O so we can remap our pins later
        for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            const AstNode* originalParamp = nullptr;
            if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                if (varp->isIO() || varp->isGParam() || varp->isIfaceRef()) {
                    // Cloning saved a pointer to the new node for us, so just follow that link.
                    originalParamp = varp->clonep();
                }
            } else if (AstParamTypeDType* const ptp = VN_CAST(stmtp, ParamTypeDType)) {
                if (ptp->isGParam()) originalParamp = ptp->clonep();
            }
            if (originalIsCopy) originalParamp = m_originalParams[originalParamp];
            if (originalParamp) clonemapp->emplace(originalParamp, stmtp);
        }
    }
    void relinkPins(const CloneMap* clonemapp, AstPin* startpinp) {
        for (AstPin* pinp = startpinp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            if (pinp->modVarp()) {
                // Find it in the clone structure
                // UINFO(8,"Clone find 0x"<<hex<<(uint32_t)pinp->modVarp());
                const auto cloneiter = clonemapp->find(pinp->modVarp());
                UASSERT_OBJ(cloneiter != clonemapp->end(), pinp,
                            "Couldn't find pin in clone list");
                pinp->modVarp(VN_AS(cloneiter->second, Var));
            } else if (pinp->modPTypep()) {
                const auto cloneiter = clonemapp->find(pinp->modPTypep());
                UASSERT_OBJ(cloneiter != clonemapp->end(), pinp,
                            "Couldn't find pin in clone list");
                pinp->modPTypep(VN_AS(cloneiter->second, ParamTypeDType));
            } else {
                pinp->v3fatalSrc("Not linked?");
            }
        }
    }
    void relinkPinsByName(AstPin* startpinp, AstNodeModule* modp) {
        std::map<const string, AstVar*> nameToPin;
        for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                if (varp->isIO() || varp->isGParam() || varp->isIfaceRef()) {
                    nameToPin.emplace(varp->name(), varp);
                }
            }
        }
        for (AstPin* pinp = startpinp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            if (const AstVar* const varp = pinp->modVarp()) {
                const auto varIt = vlstd::as_const(nameToPin).find(varp->name());
                UASSERT_OBJ(varIt != nameToPin.end(), varp,
                            "Not found in " << modp->prettyNameQ());
                pinp->modVarp(varIt->second);
            }
        }
    }
    // Check if parameter setting during instantiation is simple enough for hierarchical Verilation
    void checkSupportedParam(AstNodeModule* modp, AstPin* pinp) const {
        // InitArray is not supported because that can not be set via -G
        // option.
        if (pinp->modVarp()) {
            bool supported = false;
            if (const AstConst* const constp = VN_CAST(pinp->exprp(), Const)) {
                supported = !constp->isOpaque();
            }
            if (!supported) {
                pinp->v3error(
                    AstNode::prettyNameQ(modp->origName())
                    << " has hier_block metacomment, hierarchical Verilation"
                    << " supports only integer/floating point/string and type param parameters");
            }
        }
    }
    bool moduleExists(const string& modName) const {
        if (m_allModuleNames.find(modName) != m_allModuleNames.end()) return true;
        if (m_modNameMap.find(modName) != m_modNameMap.end()) return true;
        return false;
    }

    string parameterizedHierBlockName(AstNodeModule* modp, AstPin* paramPinsp) {
        // Create a unique name in the following steps
        //  - Make a long name that includes all parameters, that appear
        //    in the alphabetical order.
        //  - Hash the long name to get valid Verilog symbol
        UASSERT_OBJ(modp->hierBlock(), modp, "should be used for hierarchical block");

        std::map<string, AstNode*> pins;

        AstPin* pinp = paramPinsp;
        while (pinp) {
            checkSupportedParam(modp, pinp);
            if (const AstVar* const varp = pinp->modVarp()) {
                if (!pinp->exprp()) continue;
                if (varp->isGParam()) pins.emplace(varp->name(), pinp->exprp());
            } else if (VN_IS(pinp->exprp(), BasicDType) || VN_IS(pinp->exprp(), NodeDType)) {
                pins.emplace(pinp->name(), pinp->exprp());
            }
            pinp = VN_AS(pinp->nextp(), Pin);
        }

        const auto pair = m_defaultParameterValues.emplace(
            std::piecewise_construct, std::forward_as_tuple(modp), std::forward_as_tuple());
        if (pair.second) {  // Not cached yet, so check parameters
            // Using map with key=string so that we can scan it in deterministic order
            DefaultValueMap params;
            for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                    if (varp->isGParam()) {
                        AstConst* const constp = VN_CAST(varp->valuep(), Const);
                        // constp can be nullptr if the parameter is not used to instantiate sub
                        // module. varp->valuep() is not constified yet in the case.
                        // nullptr means that the parameter is using some default value.
                        params.emplace(varp->name(), constp);
                    }
                } else if (AstParamTypeDType* const p = VN_CAST(stmtp, ParamTypeDType)) {
                    AstNode* const dtypep = static_cast<AstNode*>(p->skipRefp());
                    params.emplace(p->name(), dtypep);
                }
            }
            pair.first->second = std::move(params);
        }
        const auto paramsIt = pair.first;
        if (paramsIt->second.empty()) return modp->origName();  // modp has no parameter

        string longname = modp->origName();
        for (auto&& defaultValue : paramsIt->second) {
            const auto pinIt = pins.find(defaultValue.first);
            // If the pin does not have a value assigned, use the default one.
            const AstNode* const nodep = pinIt == pins.end() ? defaultValue.second : pinIt->second;
            // This longname is not valid as verilog symbol, but ok, because it will be hashed
            longname += "_" + defaultValue.first + "=";
            // constp can be nullptr

            if (const AstConst* const p = VN_CAST(nodep, Const)) {
                // Treat modules parameterized with the same values but with different type as the
                // same.
                longname += p->num().ascii(false);
            } else if (nodep) {
                std::stringstream type;
                V3EmitV::verilogForTree(nodep, type);
                longname += type.str();
            }
        }
        UINFO(9, "       module params longname: " << longname);

        const auto iter = m_longMap.find(longname);
        if (iter != m_longMap.end()) return iter->second;  // Already calculated

        VHashSha256 hash;
        // Calculate hash using longname
        // The hash is used as the module suffix to find a module name that is unique in the design
        hash.insert(longname);
        while (true) {
            // Copy VHashSha256 just in case of hash collision
            VHashSha256 hashStrGen = hash;
            // Hex string must be a safe suffix for any symbol
            const string hashStr = hashStrGen.digestHex();
            for (string::size_type i = 1; i < hashStr.size(); ++i) {
                string newName = modp->origName();
                // Don't use '__' not to be encoded when this module is loaded later by Verilator
                if (newName.at(newName.size() - 1) != '_') newName += '_';
                newName += hashStr.substr(0, i);
                if (!moduleExists(newName)) {
                    m_longMap.emplace(longname, newName);
                    return newName;
                }
            }
            // Hash collision. maybe just v3error is practically enough
            hash.insert(V3Os::trueRandom(64));
        }
    }
    void replaceRefsRecurse(AstNode* const nodep, const AstClass* const oldClassp,
                            AstClass* const newClassp) {
        // Self references linked in the first pass of V3LinkDot.cpp should point to the default
        // instance.
        if (AstClassRefDType* const classRefp = VN_CAST(nodep, ClassRefDType)) {
            if (classRefp->classp() == oldClassp) classRefp->classp(newClassp);
        } else if (AstClassOrPackageRef* const classRefp = VN_CAST(nodep, ClassOrPackageRef)) {
            if (classRefp->classOrPackageSkipp() == oldClassp)
                classRefp->classOrPackagep(newClassp);
        } else if (AstTypedef* const typedefp = VN_CAST(nodep, Typedef)) {
            // Update typedefs that refer to the old class to point to the new class
            if (typedefp->subDTypep()) {
                if (AstClassRefDType* const classRefp = VN_CAST(typedefp->subDTypep(), ClassRefDType)) {
                    if (classRefp->classp() == oldClassp) {
                        classRefp->classp(newClassp);
                    }
                }
            }
        } else if (AstNodeFTaskRef* const ftaskRefp = VN_CAST(nodep, NodeFTaskRef)) {
            // Also update FuncRef/TaskRef packagep to point to new class
            // This fixes static method calls through typedefs in parameterized classes
            if (ftaskRefp->classOrPackagep() == oldClassp)
                ftaskRefp->classOrPackagep(newClassp);
            // Also update taskp if it points to a function in the old class
            if (AstNodeFTask* const oldTaskp = ftaskRefp->taskp()) {
                if (oldTaskp->classOrPackagep() == oldClassp) {
                    // Find the corresponding function in the new class
                    if (AstNodeFTask* const newTaskp
                        = VN_CAST(m_memberMap.findMember(newClassp, oldTaskp->name()),
                                  NodeFTask)) {
                        ftaskRefp->taskp(newTaskp);
                    }
                }
            }
        }

        if (nodep->op1p()) replaceRefsRecurse(nodep->op1p(), oldClassp, newClassp);
        if (nodep->op2p()) replaceRefsRecurse(nodep->op2p(), oldClassp, newClassp);
        if (nodep->op3p()) replaceRefsRecurse(nodep->op3p(), oldClassp, newClassp);
        if (nodep->op4p()) replaceRefsRecurse(nodep->op4p(), oldClassp, newClassp);
        if (nodep->nextp()) replaceRefsRecurse(nodep->nextp(), oldClassp, newClassp);
    }
    // Return true on success, false on error
    bool deepCloneModule(AstNodeModule* srcModp, AstNode* ifErrorp, AstPin* paramsp,
                         const string& newname, const IfaceRefRefs& ifaceRefRefs) {
        // Deep clone of new module
        // Note all module internal variables will be re-linked to the new modules by clone
        // However links outside the module (like on the upper cells) will not.
        AstNodeModule* newModp;
        if (srcModp->user3p()) {
            newModp = VN_CAST(srcModp->user3p()->cloneTree(false), NodeModule);
        } else {
            newModp = srcModp->cloneTree(false);
        }

        // cloneTree(false) temporarily populates origNode->clonep() for every node under
        // srcModp.  The capture list still stores those orig AstRefDType* pointers, so walking
        // it lets us follow clonep() into newModp and scrub each clone with the saved
        // interface context before newModp is re-linked.  we have pointers to the same nodes saved
        // in the capture map, so we can use them to scrub the new module.

        if (V3LinkDotIfaceCapture::enabled()) {
            AstCell* const cloneCellp = VN_CAST(ifErrorp, Cell);
            UINFO(9, "iface capture clone: srcModp=" << srcModp->name()
                      << " newModp=" << newModp->name()
                      << " cloneCellp=" << (cloneCellp ? cloneCellp->name() : "<null>")
                      << " ifaceRefRefs.size=" << ifaceRefRefs.size() << endl);
            V3LinkDotIfaceCapture::forEachOwned(
                srcModp, [&](const V3LinkDotIfaceCapture::CapturedIfaceTypedef& entry) {
                    if (!entry.refp) return;

                    UINFO(9, "iface capture entry: refp=" << entry.refp->name()
                              << " typedefp=" << (entry.typedefp ? entry.typedefp->name() : "<null>")
                              << " paramTypep=" << (entry.paramTypep ? entry.paramTypep->name() : "<null>")
                              << " cellp=" << (entry.cellp ? entry.cellp->name() : "<null>")
                              << " cellp->modp=" << (entry.cellp && entry.cellp->modp() ? entry.cellp->modp()->name() : "<null>")
                              << " ownerModp=" << (entry.ownerModp ? entry.ownerModp->name() : "<null>")
                              << " typedefOwnerModp=" << (entry.typedefOwnerModp ? entry.typedefOwnerModp->name() : "<null>")
                              << " ifacePortVarp=" << (entry.ifacePortVarp ? entry.ifacePortVarp->name() : "<null>")
                              << endl);

                    if (!V3LinkDotIfaceCapture::shouldApplyToClone(entry, srcModp, cloneCellp)) {
                        UINFO(9, "iface capture shouldApplyToClone=false, skipping" << endl);
                        return;
                    }

                    // Handle TYPEDEF references
                    if (AstTypedef* const origTypedefp = entry.typedefp) {
                        AstTypedef* targetTypedefp = nullptr;
                        const string& typedefName = origTypedefp->name();

                        for (auto it = ifaceRefRefs.cbegin(); it != ifaceRefRefs.cend(); ++it) {
                            const AstIfaceRefDType* const portIrefp = it->first;
                            AstNodeModule* const pinIfacep = it->second->ifaceViaCellp();
                            if (!pinIfacep) continue;

                            if (entry.ifacePortVarp) {
                                AstNodeDType* const portDTypep = entry.ifacePortVarp->subDTypep();
                                AstIfaceRefDType* entryPortIrefp = VN_CAST(portDTypep, IfaceRefDType);
                                if (!entryPortIrefp && arraySubDTypep(portDTypep)) {
                                    entryPortIrefp
                                        = VN_CAST(arraySubDTypep(portDTypep), IfaceRefDType);
                                }
                                if (entryPortIrefp != portIrefp) continue;
                            }

                            for (AstNode* stmtp = pinIfacep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                                if (AstTypedef* const tdp = VN_CAST(stmtp, Typedef)) {
                                    if (tdp->name() == typedefName) {
                                        targetTypedefp = tdp;
                                        break;
                                    }
                                }
                            }
                            if (targetTypedefp) break;
                        }

                        UINFO(9, "iface capture after ifaceRefRefs search: targetTypedefp="
                                  << (targetTypedefp ? targetTypedefp->name() : "<null>")
                                  << " for typedef '" << typedefName << "'" << endl);

                        // If ifaceRefRefs didn't find it, try the cloned cell's interface.
                        // entry.cellp is the original cell (e.g., port_types in template child).
                        // Its clonep() gives the cloned cell in newModp, whose modp() points
                        // to the correct cloned interface for this specific instance.
                        if (!targetTypedefp && entry.cellp) {
                            AstCell* const clonedCellp = entry.cellp->clonep();
                            UINFO(9, "iface capture cloned cell search: entry.cellp="
                                      << entry.cellp->name()
                                      << " clonedCellp=" << (clonedCellp ? clonedCellp->name() : "<null>")
                                      << " clonedCellp->modp=" << (clonedCellp && clonedCellp->modp() ? clonedCellp->modp()->name() : "<null>")
                                      << " origModp=" << (entry.cellp->modp() ? entry.cellp->modp()->name() : "<null>")
                                      << " same=" << (clonedCellp && clonedCellp->modp() == entry.cellp->modp())
                                      << endl);
                            if (clonedCellp) {
                                AstNodeModule* const clonedModp = clonedCellp->modp();
                                if (clonedModp && clonedModp != entry.cellp->modp()) {
                                    for (AstNode* stmtp = clonedModp->stmtsp(); stmtp;
                                         stmtp = stmtp->nextp()) {
                                        if (AstTypedef* const tdp = VN_CAST(stmtp, Typedef)) {
                                            if (tdp->name() == typedefName) {
                                                targetTypedefp = tdp;
                                                UINFO(9, "iface capture found typedef '"
                                                          << typedefName << "' via cloned cell '"
                                                          << clonedCellp->name() << "' in "
                                                          << clonedModp->name() << endl);
                                                break;
                                            }
                                        }
                                    }
                                }
                            }
                        }

                        if (!targetTypedefp) {
                            targetTypedefp = origTypedefp->clonep();
                            UINFO(9, "iface capture fallback to clonep(): "
                                      << (targetTypedefp ? targetTypedefp->name() : "<null>")
                                      << " owner="
                                      << (targetTypedefp ? V3LinkDotIfaceCapture::findOwnerModule(targetTypedefp) : nullptr)
                                      << endl);
                        }

                        UINFO(9, "iface capture FINAL targetTypedefp="
                                  << (targetTypedefp ? targetTypedefp->name() : "<null>")
                                  << " for refp=" << entry.refp->name()
                                  << " in srcModp=" << srcModp->name()
                                  << " -> newModp=" << newModp->name() << endl);

                        if (targetTypedefp) {
                            V3LinkDotIfaceCapture::replaceTypedef(entry.refp, targetTypedefp,
                                                                  cloneCellp);
                        }
                    }
                    // Handle PARAMTYPEDTYPE references
                    else if (AstParamTypeDType* const origParamTypep = entry.paramTypep) {
                        AstParamTypeDType* targetParamTypep = nullptr;
                        const string& paramTypeName = origParamTypep->name();

                        // First try ifaceRefRefs (for port connections)
                        for (auto it = ifaceRefRefs.cbegin(); it != ifaceRefRefs.cend(); ++it) {
                            const AstIfaceRefDType* const portIrefp = it->first;
                            AstNodeModule* const pinIfacep = it->second->ifaceViaCellp();
                            if (!pinIfacep) continue;

                            if (entry.ifacePortVarp) {
                                AstNodeDType* const portDTypep = entry.ifacePortVarp->subDTypep();
                                AstIfaceRefDType* entryPortIrefp = VN_CAST(portDTypep, IfaceRefDType);
                                if (!entryPortIrefp && arraySubDTypep(portDTypep)) {
                                    entryPortIrefp
                                        = VN_CAST(arraySubDTypep(portDTypep), IfaceRefDType);
                                }
                                if (entryPortIrefp != portIrefp) continue;
                            }

                            for (AstNode* stmtp = pinIfacep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                                if (AstParamTypeDType* const ptdp = VN_CAST(stmtp, ParamTypeDType)) {
                                    if (ptdp->name() == paramTypeName) {
                                        targetParamTypep = ptdp;
                                        break;
                                    }
                                }
                            }
                            if (targetParamTypep) break;
                        }

                        // If not found via ifaceRefRefs, try searching in newModp
                        // This handles the case where the entry was matched via typedefOwnerModp
                        // (i.e., the PARAMTYPEDTYPE is in the interface being cloned)
                        if (!targetParamTypep && entry.typedefOwnerModp == srcModp) {
                            // Search in the new cloned module for the PARAMTYPEDTYPE
                            for (AstNode* stmtp = newModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                                if (AstParamTypeDType* const ptdp = VN_CAST(stmtp, ParamTypeDType)) {
                                    if (ptdp->name() == paramTypeName) {
                                        targetParamTypep = ptdp;
                                        break;
                                    }
                                }
                            }
                        }

                        // Check if PARAMTYPEDTYPE is a statement of srcModp
                        bool paramTypeIsSrcModStmt = false;
                        for (AstNode* stmtp = srcModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                            if (AstParamTypeDType* const ptdp = VN_CAST(stmtp, ParamTypeDType)) {
                                if (ptdp->name() == paramTypeName) {
                                    paramTypeIsSrcModStmt = true;
                                    break;
                                }
                            }
                        }

                        // Skip replaceParamType if:
                        // 1. PARAMTYPEDTYPE is a statement of srcModp (the interface being cloned)
                        // 2. typedefOwnerModp matches srcModp (owned by this interface)
                        // 3. There's actually a PIN for this PARAMTYPEDTYPE on cloneCellp
                        // This means PIN processing will assign its type.
                        bool hasPin = false;
                        if (paramTypeIsSrcModStmt && entry.typedefOwnerModp == srcModp
                            && cloneCellp) {
                            for (AstPin* pinp = cloneCellp->paramsp(); pinp;
                                 pinp = VN_AS(pinp->nextp(), Pin)) {
                                if (pinp->modPTypep()
                                    && pinp->modPTypep()->name() == paramTypeName) {
                                    hasPin = true;
                                    break;
                                }
                            }
                        }
                        if (paramTypeIsSrcModStmt && entry.typedefOwnerModp == srcModp
                            && hasPin) {
                            return;  // Skip - PIN processing will assign its type
                        }

                        // Fallback: try via cellp->modp() for internal cells
                        if (!targetParamTypep && entry.cellp) {
                            AstNodeModule* const cellModp = entry.cellp->modp();
                            if (cellModp) {
                                for (AstNode* stmtp = cellModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                                    if (AstParamTypeDType* const ptdp = VN_CAST(stmtp, ParamTypeDType)) {
                                        if (ptdp->name() == paramTypeName) {
                                            targetParamTypep = ptdp;
                                            break;
                                        }
                                    }
                                }
                            }
                        }

                        if (!targetParamTypep) targetParamTypep = origParamTypep->clonep();

                        if (targetParamTypep) {
                            V3LinkDotIfaceCapture::replaceParamType(entry.refp, targetParamTypep);
                        }
                    }

                    // Propagate to cloned RefDType in new module
                    if (AstRefDType* const clonedRefp = entry.refp->clonep()) {
                        V3LinkDotIfaceCapture::propagateClone(entry.refp, clonedRefp);
                    }
                });
        }

        newModp->name(newname);
        newModp->user2(false);  // We need to re-recurse this module once changed
        newModp->recursive(false);
        newModp->recursiveClone(false);
        newModp->hasGParam(false);
        // Recursion may need level cleanups
        if (newModp->level() <= m_modp->level()) newModp->level(m_modp->level() + 1);
        if ((newModp->level() - srcModp->level()) >= (v3Global.opt.moduleRecursionDepth() - 2)) {
            ifErrorp->v3error("Exceeded maximum --module-recursion-depth of "
                              << v3Global.opt.moduleRecursionDepth());
            VL_DO_DANGLING(newModp->deleteTree(), newModp);
            return false;
        }

        if (AstClass* const newClassp = VN_CAST(newModp, Class)) {
            replaceRefsRecurse(newModp->stmtsp(), newClassp, VN_AS(srcModp, Class));
        }

        // Keep tree sorted by level. Note: Different parameterizations of the same recursive
        // module end up with the same level, which we will need to fix up at the end, as we do not
        // know up front how recursive modules are expanded, and a later expansion might re-use an
        // earlier expansion (see t_recursive_module_bug_2).
        AstNode* insertp = srcModp;
        while (VN_IS(insertp->nextp(), NodeModule)
               && VN_AS(insertp->nextp(), NodeModule)->level() <= newModp->level()) {
            insertp = insertp->nextp();
        }
        insertp->addNextHere(newModp);

        m_modNameMap.emplace(newModp->name(), ModInfo{newModp});
        const auto iter = m_modNameMap.find(newname);
        CloneMap* const clonemapp = &(iter->second.m_cloneMap);
        UINFO(4, "     De-parameterize to new: " << newModp);

        // Grab all I/O so we can remap our pins later
        // Note we allow multiple users of a parameterized model,
        // thus we need to stash this info.
        collectPins(clonemapp, newModp, srcModp->user3p());
        // Relink parameter vars to the new module
        relinkPins(clonemapp, paramsp);

        // Fix any interface references
        for (auto it = ifaceRefRefs.cbegin(); it != ifaceRefRefs.cend(); ++it) {
            const AstIfaceRefDType* const portIrefp = it->first;
            const AstIfaceRefDType* const pinIrefp = it->second;
            AstIfaceRefDType* const cloneIrefp = portIrefp->clonep();
            UINFO(8, "     IfaceOld " << portIrefp);
            UINFO(8, "     IfaceTo  " << pinIrefp);
            UASSERT_OBJ(cloneIrefp, portIrefp, "parameter clone didn't hit AstIfaceRefDType");
            UINFO(8, "     IfaceClo " << cloneIrefp);
            cloneIrefp->ifacep(pinIrefp->ifaceViaCellp());
            UINFO(8, "     IfaceNew " << cloneIrefp);
        }

        // Record deferred fixups for REFDTYPEs in the cloned module whose
        // typedefp/refDTypep still points to a template interface's node.
        // Build a template→clone interface map from:
        //   1. ifaceRefRefs (port-connected interfaces — the IFACEREFDTYPE was
        //      already wired to the cloned interface above)
        //   2. newModp's cells that already point to cloned interfaces
        // Then for each REFDTYPE whose target owner is a template in the map,
        // record a deferred fixup with the correct clone module.
        // The actual pointer fixup happens in finalizeIfaceCapture() when all
        // clones exist and have correct types.
        {
            // Helper: find template interface by origName
            auto findTemplate = [](AstNodeModule* cloneModp) -> AstNodeModule* {
                for (AstNode* np = v3Global.rootp()->modulesp(); np; np = np->nextp()) {
                    if (AstIface* const ifp = VN_CAST(np, Iface)) {
                        if (ifp != cloneModp && ifp->name() == cloneModp->origName()) {
                            return ifp;
                        }
                    }
                }
                return nullptr;
            };

            std::map<AstNodeModule*, AstNodeModule*> templateToClone;

            UINFO(9, "iface capture deferred: newModp=" << newModp->name()
                      << " ifaceRefRefs.size=" << ifaceRefRefs.size() << endl);

            // Source 1: ifaceRefRefs — port-connected interfaces
            for (const auto& pair : ifaceRefRefs) {
                const AstIfaceRefDType* const pinIrefp = pair.second;
                AstIface* const cloneIfacep = pinIrefp->ifaceViaCellp();
                UINFO(9, "iface capture deferred: ifaceRefRef pin=" << pinIrefp
                          << " cloneIface=" << (cloneIfacep ? cloneIfacep->name() : "<null>")
                          << " origName=" << (cloneIfacep ? cloneIfacep->origName() : "<null>")
                          << endl);
                if (!cloneIfacep) continue;
                if (cloneIfacep->name().find("__") == string::npos) continue;
                AstNodeModule* const tmplp = findTemplate(cloneIfacep);
                UINFO(9, "iface capture deferred: findTemplate(" << cloneIfacep->name()
                          << ") = " << (tmplp ? tmplp->name() : "<null>") << endl);
                if (tmplp) templateToClone[tmplp] = cloneIfacep;

                // Recurse: cloned interface may contain cells to other cloned interfaces
                for (AstNode* sp = cloneIfacep->stmtsp(); sp; sp = sp->nextp()) {
                    if (AstCell* const innerCellp = VN_CAST(sp, Cell)) {
                        AstNodeModule* const innerModp = innerCellp->modp();
                        if (!innerModp || !VN_IS(innerModp, Iface)) continue;
                        if (innerModp->name().find("__") == string::npos) continue;
                        AstNodeModule* const innerTmplp = findTemplate(innerModp);
                        if (innerTmplp) templateToClone[innerTmplp] = innerModp;
                    }
                }
            }

            // Source 2: newModp's direct cells that point to cloned interfaces
            for (AstNode* stmtp = newModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                AstCell* const cellp = VN_CAST(stmtp, Cell);
                if (!cellp) continue;
                AstNodeModule* const cellModp = cellp->modp();
                if (!cellModp || !VN_IS(cellModp, Iface)) continue;
                if (cellModp->name().find("__") == string::npos) continue;
                AstNodeModule* const tmplp = findTemplate(cellModp);
                if (tmplp) templateToClone[tmplp] = cellModp;

                // Recurse into sub-cells
                for (AstNode* sp = cellModp->stmtsp(); sp; sp = sp->nextp()) {
                    if (AstCell* const innerCellp = VN_CAST(sp, Cell)) {
                        AstNodeModule* const innerModp = innerCellp->modp();
                        if (!innerModp || !VN_IS(innerModp, Iface)) continue;
                        if (innerModp->name().find("__") == string::npos) continue;
                        AstNodeModule* const innerTmplp = findTemplate(innerModp);
                        if (innerTmplp) templateToClone[innerTmplp] = innerModp;
                    }
                }
            }

            // Record deferred fixups for REFDTYPEs whose targets are in template
            // interfaces OR in wrong clones (via clonep() last-writer-wins).
            // Build a reverse map: any clone of the same template → correct clone.
            if (!templateToClone.empty()) {
                // Build set of all clones of templates we know about, mapping
                // each to the correct clone for this module instance.
                // Also include templates themselves.
                std::map<AstNodeModule*, AstNodeModule*> anyToCorrectClone;
                for (const auto& kv : templateToClone) {
                    // template → correct clone
                    anyToCorrectClone[kv.first] = kv.second;
                }
                // Find all other clones of the same templates and map them too
                for (AstNode* np = v3Global.rootp()->modulesp(); np; np = np->nextp()) {
                    AstNodeModule* const modp = VN_CAST(np, NodeModule);
                    if (!modp || modp->dead()) continue;
                    if (modp->name().find("__") == string::npos) continue;
                    // Check if this is a clone of one of our templates
                    for (const auto& kv : templateToClone) {
                        if (modp->origName() == kv.first->name()
                            && modp != kv.second) {
                            // This is a wrong clone — map it to the correct one
                            anyToCorrectClone[modp] = kv.second;
                            break;
                        }
                    }
                }

                UINFO(9, "iface capture deferred: anyToCorrectClone has "
                          << anyToCorrectClone.size() << " entries for "
                          << newModp->name() << ":" << endl);
                for (const auto& kv : anyToCorrectClone) {
                    UINFO(9, "iface capture deferred:   " << kv.first->name()
                              << " -> " << kv.second->name() << endl);
                }

                // Fixups are handled by the pendingClones list in IfaceCapture.
                // When replaceTypedef is called, it updates ALL pending clones.
            }
        }
        // Assign parameters to the constants specified
        // DOES clone() so must be finished with module clonep() before here
        for (AstPin* pinp = paramsp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            if (pinp->exprp()) {
                if (AstVar* const modvarp = pinp->modVarp()) {
                    AstNode* const newp = pinp->exprp();  // Const or InitArray
                    AstConst* const exprp = VN_CAST(newp, Const);
                    AstConst* const origp = VN_CAST(modvarp->valuep(), Const);
                    const bool overridden
                        = !(origp && exprp && ParameterizedHierBlocks::areSame(exprp, origp));
                    // Remove any existing parameter
                    if (modvarp->valuep()) modvarp->valuep()->unlinkFrBack()->deleteTree();
                    // Set this parameter to value requested by cell
                    UINFO(9, "       set param " << modvarp << " = " << newp);
                    modvarp->valuep(newp->cloneTree(false));
                    modvarp->overriddenParam(overridden);
                } else if (AstParamTypeDType* const modptp = pinp->modPTypep()) {
                    AstNodeDType* const dtypep = VN_AS(pinp->exprp(), NodeDType);
                    UASSERT_OBJ(dtypep, pinp, "unlinked param dtype");
                    if (modptp->childDTypep()) modptp->childDTypep()->unlinkFrBack()->deleteTree();
                    // Set this parameter to value requested by cell
                    modptp->childDTypep(dtypep->cloneTree(false));
                    // Later V3LinkDot will convert the ParamDType to a Typedef
                    // Not done here as may be localparams, etc, that also need conversion
                }
            }
        }

        // Apply resolved LPARAM values from DepGraph for this cell context
        // srcModp->someInstanceName() contains the cell path (e.g., "t.u_sub8")
        if (V3LinkDotDepGraph::enabled()) {
            V3LinkDotDepGraph::applyResolvedToClone(srcModp, newModp,
                                                    srcModp->someInstanceName());
        }

        // Restore captured localparam expressions for interfaces/classes
        // After parameters are assigned, restore original expressions.
        // Do NOT constify here - let the normal passes handle ordering.
        if (VN_IS(newModp, Iface) || VN_IS(newModp, Class)) {
            // Build a name-to-var map for the cloned module's vars
            std::unordered_map<std::string, AstVar*> clonedVarsByName;
            for (AstNode* stmtp = newModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                    clonedVarsByName[varp->name()] = varp;
                }
            }

            for (AstNode* stmtp = newModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                    if (varp->varType() != VVarType::LPARAM) continue;
                    // Find the original var in srcModp to look up captured expression
                    AstVar* srcVarp = nullptr;
                    for (AstNode* srcStmtp = srcModp->stmtsp(); srcStmtp;
                        srcStmtp = srcStmtp->nextp()) {
                        if (AstVar* const svp = VN_CAST(srcStmtp, Var)) {
                            if (svp->name() == varp->name()) {
                                srcVarp = svp;
                                break;
                            }
                        }
                    }
                    if (!srcVarp) continue;
                    const auto* captured = V3LinkDotIfaceCapture::findLocalparam(srcVarp);
                    if (captured && captured->origExprp) {
                        UINFO(5, "LOCALPARAM-RESTORE var=" << varp->name()
                              << " in " << newModp->name() << endl);
                        // Replace constified value with clone of original expression
                        if (varp->valuep()) varp->valuep()->unlinkFrBack()->deleteTree();
                        AstNode* newExprp = captured->origExprp->cloneTree(false);

                        // Relink VarRefs in the cloned expression:
                        // 1. First try clonemapp (for vars from source module)
                        // 2. Then try name-based lookup (for vars within same interface)
                        newExprp->foreach([&](AstVarRef* refp) {
                            const auto it = clonemapp->find(refp->varp());
                            if (it != clonemapp->end()) {
                                refp->varp(VN_AS(it->second, Var));
                            } else {
                                // Try name-based lookup for same-interface vars
                                const auto nameIt = clonedVarsByName.find(refp->varp()->name());
                                if (nameIt != clonedVarsByName.end()) {
                                    refp->varp(nameIt->second);
                                }
                            }
                        });

                        varp->valuep(newExprp);
                        // Do NOT constify here - expressions may reference other
                        // localparams that haven't been restored yet.
                        // Mark for later constification.
                    }
                }
            }

            // Now constify all restored localparams in dependency order
            // Use iterative approach: keep trying until no progress
            bool progress = true;
            while (progress) {
                progress = false;
                for (AstNode* stmtp = newModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                    if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                        if (varp->varType() != VVarType::LPARAM) continue;
                        if (!varp->valuep()) continue;
                        if (VN_IS(varp->valuep(), Const)) continue;  // Already done

                        // Check if all referenced localparams are const
                        bool allDepsConst = true;
                        varp->valuep()->foreach([&](const AstVarRef* refp) {
                            if (refp->varp()->varType() == VVarType::LPARAM
                                && refp->varp()->valuep()
                                && !VN_IS(refp->varp()->valuep(), Const)) {
                                allDepsConst = false;
                            }
                        });

                        if (allDepsConst) {
                            V3Width::widthParamsEdit(varp);
                            V3Const::constifyParamsEdit(varp);
                            progress = true;
                        }
                    }
                }
            }
        }

        return true;
    }
    const ModInfo* moduleFindOrClone(AstNodeModule* srcModp, AstNode* ifErrorp, AstPin* paramsp,
                                     const string& newname, const IfaceRefRefs& ifaceRefRefs) {
        // Already made this flavor?
        auto it = m_modNameMap.find(newname);
        if (it != m_modNameMap.end()) {
            UINFO(4, "     De-parameterize to prev: " << it->second.m_modp);
        } else {
            if (!deepCloneModule(srcModp, ifErrorp, paramsp, newname, ifaceRefRefs)) {
                return nullptr;
            }
            it = m_modNameMap.find(newname);
            UASSERT(it != m_modNameMap.end(), "should find just-made module");
        }
        const ModInfo* const modInfop = &(it->second);
        return modInfop;
    }

    void convertToStringp(AstNode* nodep) {
        // Should be called on values of parameters of type string to convert them
        // to properly typed string constants.
        // Has no effect if the value is not a string constant.
        AstConst* const constp = VN_CAST(nodep, Const);
        // Check if it wasn't already converted
        if (constp && !constp->num().isString()) {
            constp->replaceWith(
                new AstConst{constp->fileline(), AstConst::String{}, constp->num().toString()});
            constp->deleteTree();
        }
    }

    // Helper to resolve DOT to RefDType for class type references
    void resolveDotToTypedef(AstNode* exprp) {
        AstDot* const dotp = VN_CAST(exprp, Dot);
        if (!dotp) return;
        const AstClassOrPackageRef* const classRefp = VN_CAST(dotp->lhsp(), ClassOrPackageRef);
        if (!classRefp) return;
        const AstClass* const lhsClassp = VN_CAST(classRefp->classOrPackageSkipp(), Class);
        if (!lhsClassp) return;
        AstParseRef* const parseRefp = VN_CAST(dotp->rhsp(), ParseRef);
        if (!parseRefp) return;

        AstTypedef* const tdefp
            = VN_CAST(m_memberMap.findMember(lhsClassp, parseRefp->name()), Typedef);
        if (tdefp) {
            AstRefDType* const refp = new AstRefDType{dotp->fileline(), tdefp->name()};
            refp->typedefp(tdefp);
            dotp->replaceWith(refp);
            VL_DO_DANGLING(dotp->deleteTree(), dotp);
        }
    }

    void cellPinCleanup(AstNode* nodep, AstPin* pinp, AstNodeModule* srcModp, string& longnamer,
                        bool& any_overridesr) {
        if (!pinp->exprp()) return;  // No-connect
        if (AstVar* const modvarp = pinp->modVarp()) {
            if (!modvarp->isGParam()) {
                pinp->v3fatalSrc("Attempted parameter setting of non-parameter: Param "
                                 << pinp->prettyNameQ() << " of " << nodep->prettyNameQ());
            } else if (VN_IS(pinp->exprp(), InitArray) && arraySubDTypep(modvarp->subDTypep())) {
                // Array assigned to array
                AstNode* const exprp = pinp->exprp();
                longnamer += "_" + paramSmallName(srcModp, modvarp) + paramValueNumber(exprp);
                any_overridesr = true;
            } else if (VN_IS(pinp->exprp(), InitArray)) {
                // Array assigned to scalar parameter.  Treat the InitArray as a constant
                // integer array and include it in the module name.  Constantify nested
                // expressions before mangling the value number.
                V3Const::constifyParamsEdit(pinp->exprp());
                longnamer
                    += "_" + paramSmallName(srcModp, modvarp) + paramValueNumber(pinp->exprp());
                any_overridesr = true;
            } else {
                UINFO(9, "iface capture cellPinCleanup: before constify pin='" << pinp->name()
                          << "' mod='" << srcModp->name()
                          << "' exprType=" << pinp->exprp()->typeName()
                          << " modvar='" << modvarp->name() << "'"
                          << " modval=" << (modvarp->valuep() ? modvarp->valuep()->typeName() : "null")
                          << (modvarp->valuep() && VN_IS(modvarp->valuep(), Const)
                              ? string(" modvalNum=") + VN_AS(modvarp->valuep(), Const)->num().ascii(false)
                              : string(""))
                          << " w=" << modvarp->width()
                          << endl);
                V3Const::constifyParamsEdit(pinp->exprp());
                UINFO(9, "iface capture cellPinCleanup: after constify pin='" << pinp->name()
                          << "' exprType=" << pinp->exprp()->typeName()
                          << " isConst=" << VN_IS(pinp->exprp(), Const)
                          << (VN_IS(pinp->exprp(), Const)
                              ? string(" val=") + VN_AS(pinp->exprp(), Const)->num().ascii(false)
                              : string(""))
                          << " w=" << pinp->exprp()->width()
                          << endl);
                // String constants are parsed as logic arrays and converted to strings in V3Const.
                // At this moment, some constants may have been already converted.
                // To correctly compare constants, both should be of the same type,
                // so they need to be converted.
                if (isString(modvarp->subDTypep())) {
                    convertToStringp(pinp->exprp());
                    convertToStringp(modvarp->valuep());
                }
                AstConst* const exprp = VN_CAST(pinp->exprp(), Const);
                AstConst* const origp = VN_CAST(modvarp->valuep(), Const);
                if (!exprp) {
                    // With DepGraph architecture, all expressions should be constants
                    // by the time V3Param runs. If not, it's an error.
                    UINFO(9, "iface capture cellPinCleanup: NOT CONST after constify pin='" << pinp->name()
                              << "' mod='" << srcModp->name()
                              << "' exprType=" << pinp->exprp()->typeName() << endl);
                    UINFOTREE(1, pinp, "", "errnode");
                    pinp->v3error("Can't convert defparam value to constant: Param "
                                  << pinp->prettyNameQ() << " of " << nodep->prettyNameQ());
                    AstNode* const pinExprp = pinp->exprp();
                    pinExprp->replaceWith(new AstConst{pinp->fileline(), AstConst::WidthedValue{},
                                                       modvarp->width(), 0});
                    VL_DO_DANGLING(pinExprp->deleteTree(), pinExprp);
                } else if (origp
                           && (exprp->sameTree(origp)
                               || (exprp->num().width() == origp->num().width()
                                   && ParameterizedHierBlocks::areSame(exprp, origp)))) {
                    // Setting parameter to its default value.  Just ignore it.
                    // This prevents making additional modules, and makes coverage more
                    // obvious as it won't show up under a unique module page name.
                    UINFO(9, "iface capture cellPinCleanup: SAME AS DEFAULT pin='" << pinp->name()
                              << "' mod='" << srcModp->name()
                              << "' val=" << exprp->num().ascii(false) << endl);
                } else if (exprp->num().isDouble() || exprp->num().isString()
                           || exprp->num().isFourState() || exprp->num().width() != 32) {
                    longnamer
                        += ("_" + paramSmallName(srcModp, modvarp) + paramValueNumber(exprp));
                    any_overridesr = true;
                } else {
                    longnamer
                        += ("_" + paramSmallName(srcModp, modvarp) + exprp->num().ascii(false));
                    any_overridesr = true;
                }
            }
        } else if (AstParamTypeDType* const modvarp = pinp->modPTypep()) {
            // Handle DOT with ParseRef RHS (e.g., p_class#(8)::p_type)
            // by this point ClassOrPackageRef should be updated to point to the specialized class.
            resolveDotToTypedef(pinp->exprp());

            AstNodeDType* rawTypep = VN_CAST(pinp->exprp(), NodeDType);
            if (rawTypep) V3Width::widthParamsEdit(rawTypep);
            AstNodeDType* exprp = rawTypep ? rawTypep->skipRefToNonRefp() : nullptr;
            const AstNodeDType* origp = modvarp->skipRefToNonRefp();
            if (!exprp) {
                pinp->v3error("Parameter type pin value isn't a type: Param "
                              << pinp->prettyNameQ() << " of " << nodep->prettyNameQ());
            } else if (!origp) {
                pinp->v3error("Parameter type variable isn't a type: Param "
                              << modvarp->prettyNameQ());
            } else {
                UINFO(9, "Parameter type assignment expr=" << exprp << " to " << origp);
                V3Const::constifyParamsEdit(pinp->exprp());  // Reconcile typedefs
                // Constify may have caused pinp->exprp to change
                rawTypep = VN_AS(pinp->exprp(), NodeDType);
                exprp = rawTypep->skipRefToNonRefp();
                if (!modvarp->fwdType().isNodeCompatible(exprp)) {
                    pinp->v3error("Parameter type expression type "
                                      << exprp->prettyDTypeNameQ()
                                      << " violates parameter's forwarding type '"
                                      << modvarp->fwdType().ascii() << "'");
                }
                if (exprp->similarDType(origp)) {
                    // Setting parameter to its default value.  Just ignore it.
                    // This prevents making additional modules, and makes coverage more
                    // obvious as it won't show up under a unique module page name.
                } else {
                    VL_DO_DANGLING(V3Const::constifyParamsEdit(exprp), exprp);
                    rawTypep = VN_CAST(pinp->exprp(), NodeDType);
                    exprp = rawTypep ? rawTypep->skipRefToNonRefp() : nullptr;
                    longnamer += "_" + paramSmallName(srcModp, modvarp)
                                 + paramValueNumber(exprp);
                    any_overridesr = true;
                }
            }
        } else {
            pinp->v3fatalSrc("Parameter not found in sub-module: Param "
                             << pinp->prettyNameQ() << " of " << nodep->prettyNameQ());
        }
    }

    void cellInterfaceCleanup(AstPin* pinsp, AstNodeModule* srcModp, string& longnamer,
                              bool& any_overridesr, IfaceRefRefs& ifaceRefRefs) {
        for (AstPin* pinp = pinsp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            const AstVar* const modvarp = pinp->modVarp();
            if (modvarp && VN_IS(modvarp->subDTypep(), IfaceGenericDType)) continue;
            if (modvarp->isIfaceRef()) {
                AstIfaceRefDType* portIrefp = VN_CAST(modvarp->subDTypep(), IfaceRefDType);
                if (!portIrefp && arraySubDTypep(modvarp->subDTypep())) {
                    portIrefp = VN_CAST(arraySubDTypep(modvarp->subDTypep()), IfaceRefDType);
                }
                AstIfaceRefDType* pinIrefp = nullptr;
                const AstNode* const exprp = pinp->exprp();
                const AstVar* const varp
                    = (exprp && VN_IS(exprp, VarRef)) ? VN_AS(exprp, VarRef)->varp() : nullptr;
                if (varp && varp->subDTypep() && VN_IS(varp->subDTypep(), IfaceRefDType)) {
                    pinIrefp = VN_AS(varp->subDTypep(), IfaceRefDType);
                } else if (varp && varp->subDTypep() && arraySubDTypep(varp->subDTypep())
                           && VN_CAST(arraySubDTypep(varp->subDTypep()), IfaceRefDType)) {
                    pinIrefp = VN_CAST(arraySubDTypep(varp->subDTypep()), IfaceRefDType);
                } else if (exprp && exprp->op1p() && VN_IS(exprp->op1p(), VarRef)
                           && VN_CAST(exprp->op1p(), VarRef)->varp()
                           && VN_CAST(exprp->op1p(), VarRef)->varp()->subDTypep()
                           && arraySubDTypep(VN_CAST(exprp->op1p(), VarRef)->varp()->subDTypep())
                           && VN_CAST(
                               arraySubDTypep(VN_CAST(exprp->op1p(), VarRef)->varp()->subDTypep()),
                               IfaceRefDType)) {
                    pinIrefp
                        = VN_AS(arraySubDTypep(VN_AS(exprp->op1p(), VarRef)->varp()->subDTypep()),
                                IfaceRefDType);
                }

                UINFO(9, "     portIfaceRef " << portIrefp);

                if (!portIrefp) {
                    pinp->v3error("Interface port " << modvarp->prettyNameQ()
                                                    << " is not an interface " << modvarp);
                } else if (!pinIrefp) {
                    pinp->v3error("Interface port "
                                  << modvarp->prettyNameQ()
                                  << " is not connected to interface/modport pin expression");
                } else {
                    UINFO(9, "     pinIfaceRef " << pinIrefp);
                    if (portIrefp->ifaceViaCellp() != pinIrefp->ifaceViaCellp()) {
                        UINFO(9, "     IfaceRefDType needs reconnect  " << pinIrefp);
                        longnamer += ("_" + paramSmallName(srcModp, pinp->modVarp())
                                      + paramValueNumber(pinIrefp));
                        any_overridesr = true;
                        ifaceRefRefs.emplace_back(portIrefp, pinIrefp);
                        if (portIrefp->ifacep() != pinIrefp->ifacep()
                            // Might be different only due to param cloning, so check names too
                            && portIrefp->ifaceName() != pinIrefp->ifaceName()) {
                            pinp->v3error("Port " << pinp->prettyNameQ() << " expects "
                                                  << AstNode::prettyNameQ(portIrefp->ifaceName())
                                                  << " interface but pin connects "
                                                  << AstNode::prettyNameQ(pinIrefp->ifaceName())
                                                  << " interface");
                        }
                    }
                }
            }
        }
    }

    void storeOriginalParams(AstNodeModule* const classp) {
        for (AstNode* stmtp = classp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            AstNode* originalParamp = nullptr;
            if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                if (varp->isGParam()) originalParamp = varp->clonep();
            } else if (AstParamTypeDType* const ptp = VN_CAST(stmtp, ParamTypeDType)) {
                if (ptp->isGParam()) originalParamp = ptp->clonep();
            }
            if (originalParamp) m_originalParams[stmtp] = originalParamp;
        }
    }

    // Set interfaces types inside generic modules
    // to the corresponding values of implicit parameters
    void genericInterfaceVarSetup(const AstPin* const paramsp, const AstPin* const pinsp) {
        std::unordered_map<string, const AstPin*> paramspMap;
        for (const AstPin* pinp = paramsp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            if (VString::startsWith(pinp->name(), "__VGIfaceParam")) {
                paramspMap.insert({pinp->name().substr(std::strlen("__VGIfaceParam")), pinp});
            }
        }

        if (paramspMap.empty()) return;

        for (const AstNode* nodep = pinsp; nodep; nodep = nodep->nextp()) {
            if (const AstPin* const pinp = VN_CAST(nodep, Pin)) {
                if (AstVar* const varp = pinp->modVarp()) {
                    if (AstIfaceGenericDType* const ifaceGDTypep
                        = VN_CAST(varp->childDTypep(), IfaceGenericDType)) {
                        const auto iter = paramspMap.find(varp->name());
                        if (iter == paramspMap.end()) continue;
                        ifaceGDTypep->unlinkFrBack();
                        const AstPin* const paramp = iter->second;
                        paramspMap.erase(iter);
                        const AstIfaceRefDType* const ifacerefp
                            = VN_AS(paramp->exprp(), IfaceRefDType);
                        AstIfaceRefDType* const newIfacerefp = new AstIfaceRefDType{
                            ifaceGDTypep->fileline(), ifaceGDTypep->modportFileline(),
                            ifaceGDTypep->name(), ifacerefp->ifaceName(),
                            ifaceGDTypep->modportName()};
                        newIfacerefp->ifacep(ifacerefp->ifacep());
                        varp->childDTypep(newIfacerefp);
                        VL_DO_DANGLING(m_deleter.pushDeletep(ifaceGDTypep), ifaceGDTypep);
                        if (paramspMap.empty()) return;
                    }
                }
            }
        }

        UASSERT(paramspMap.empty(), "Not every generic interface implicit param is used");
    }

    void resolveDefaultParams(AstNode* nodep) {
        AstClassOrPackageRef* classOrPackageRef = VN_CAST(nodep, ClassOrPackageRef);
        AstClassRefDType* classRefDType = VN_CAST(nodep, ClassRefDType);
        AstClass* classp = nullptr;
        AstPin* paramsp = nullptr;

        if (classOrPackageRef) {
            classp = VN_CAST(classOrPackageRef->classOrPackageSkipp(), Class);
            if (!classp) return;  // No parameters in packages
            paramsp = classOrPackageRef->paramsp();
        } else if (classRefDType) {
            classp = classRefDType->classp();
            paramsp = classRefDType->paramsp();
        } else {
            nodep->v3fatalSrc("resolveDefaultParams called on node which is not a Class ref");
        }

        UASSERT_OBJ(classp, nodep, "Class or interface ref has no classp/ifacep");

        // Get the parameter list for this class
        m_classParams.clear();
        m_paramIndex.clear();
        for (AstNode* stmtp = classp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstParamTypeDType* paramTypep = VN_CAST(stmtp, ParamTypeDType)) {
                // Only consider formal class type parameters (generic parameters),
                // not localparam type declarations inside the class body.
                if (!paramTypep->isGParam()) continue;
                m_paramIndex.emplace(paramTypep, static_cast<int>(m_classParams.size()));
                m_classParams.emplace_back(paramTypep, -1);
            }
        }

        // For each parameter, detect either a dependent default (copy from previous param)
        // or a direct type default (for ex. int). Store dependency index in
        // m_classParams[i].second, default type in defaultTypeNodes[i].
        std::vector<AstNodeDType*> defaultTypeNodes(m_classParams.size(), nullptr);
        for (size_t i = 0; i < m_classParams.size(); ++i) {
            AstParamTypeDType* const paramTypep = m_classParams[i].first;
            // Parser places defaults/constraints under childDTypep as AstRequireDType
            AstRequireDType* const reqDtp = VN_CAST(paramTypep->getChildDTypep(), RequireDType);
            if (!reqDtp) continue;

            // If default is a reference to another param type, record dependency
            if (AstRefDType* const refDtp = VN_CAST(reqDtp->subDTypep(), RefDType)) {
                if (AstParamTypeDType* const sourceParamp
                    = VN_CAST(refDtp->refDTypep(), ParamTypeDType)) {
                    auto it = m_paramIndex.find(sourceParamp);
                    if (it != m_paramIndex.end()) { m_classParams[i].second = it->second; }
                    continue;  // dependency handled
                }
            }

            // If default is a direct type (for ex. int)
            // also record dependency
            if (AstNodeDType* const dtp = VN_CAST(reqDtp->lhsp(), NodeDType)) {
                defaultTypeNodes[i] = dtp;
            }
        }

        // Count existing pins and capture them by index for easy lookup
        std::vector<AstPin*> pinsByIndex;
        for (AstPin* pinp = paramsp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            pinsByIndex.push_back(pinp);
        }

        // For each missing parameter, get its pin from dependency or direct default
        for (size_t paramIdx = pinsByIndex.size(); paramIdx < m_classParams.size(); paramIdx++) {
            const int sourceParamIdx = m_classParams[paramIdx].second;

            AstPin* newPinp = nullptr;

            // Case 1: Dependent default -> clone the source pin's type
            if (sourceParamIdx >= 0) newPinp = pinsByIndex[sourceParamIdx]->cloneTree(false);

            // Case 2: Direct default type (e.g., int), create a new pin with that dtype
            if (!newPinp && defaultTypeNodes[paramIdx]) {
                AstNodeDType* const dtypep = defaultTypeNodes[paramIdx];
                newPinp = new AstPin{dtypep->fileline(), static_cast<int>(paramIdx) + 1,
                                     "__paramNumber" + cvtToStr(paramIdx + 1),
                                     dtypep->cloneTree(false)};
            }

            if (newPinp) {
                newPinp->name("__paramNumber" + cvtToStr(paramIdx + 1));
                newPinp->param(true);
                newPinp->modPTypep(m_classParams[paramIdx].first);
                if (classOrPackageRef) {
                    classOrPackageRef->addParamsp(newPinp);
                } else if (classRefDType) {
                    classRefDType->addParamsp(newPinp);
                }
                // Update local tracking so future dependent defaults can find it
                pinsByIndex.resize(paramIdx + 1, nullptr);
                pinsByIndex[paramIdx] = newPinp;
                if (!paramsp) paramsp = newPinp;
            }
        }
    }

    AstNodeModule* nodeDeparamCommon(AstNode* nodep, AstNodeModule* srcModp, AstPin* paramsp,
                                     AstPin* pinsp, bool any_overrides) {
        // Returns new or reused module
        // Make sure constification worked
        // Must be a separate loop, as constant conversion may have changed some pointers.
        // UINFOTREE(1, nodep, "", "cel2");
        string longname = srcModp->name() + "_";
        if (debug() >= 9 && paramsp) paramsp->dumpTreeAndNext(cout, "-  cellparams: ");

        if (srcModp->hierBlock()) {
            longname = parameterizedHierBlockName(srcModp, paramsp);
            any_overrides = longname != srcModp->name();
        } else {
            for (AstPin* pinp = paramsp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
                cellPinCleanup(nodep, pinp, srcModp, longname /*ref*/, any_overrides /*ref*/);
            }
        }
        IfaceRefRefs ifaceRefRefs;
        cellInterfaceCleanup(pinsp, srcModp, longname /*ref*/, any_overrides /*ref*/,
                             ifaceRefRefs /*ref*/);

        // Default params are resolved as overrides
        // But first check if the default value is equivalent to a basic type (e.g., typedef int)
        bool defaultsResolved = false;
        if (!any_overrides) {
            for (AstPin* pinp = paramsp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
                if (AstParamTypeDType* const modvarp = pinp->modPTypep()) {
                    // Check if the default type parameter resolves to a basic type.
                    // If so, don't treat it as an override - let the explicit basic type param match.
                    // This ensures ClsTypedefParam#() with default typedef int matches ClsTypedefParam#(int).
                    const AstNodeDType* defaultTypep = modvarp->skipRefToNonRefp();
                    if (!VN_IS(defaultTypep, BasicDType)) {
                        any_overrides = true;
                        defaultsResolved = true;
                        break;
                    }
                }
            }
        }

        UINFO(9, "iface capture nodeDeparamCommon: src='" << srcModp->name()
                  << "' longname='" << longname
                  << "' any_overrides=" << any_overrides
                  << " cell='" << nodep->name() << "'" << endl);

        AstNodeModule* newModp = nullptr;
        if (m_hierBlocks.hierSubRun() && m_hierBlocks.isHierBlock(srcModp->origName())) {
            AstNodeModule* const paramedModp
                = m_hierBlocks.findByParams(srcModp->origName(), paramsp, m_modp);
            UASSERT_OBJ(paramedModp, nodep, "Failed to find sub-module for hierarchical block");
            paramedModp->dead(false);
            // We need to relink the pins to the new module
            relinkPinsByName(pinsp, paramedModp);
            newModp = paramedModp;
            // any_overrides = true;  // Unused later, so not needed
        } else if (!any_overrides) {
            UINFO(9, "iface capture nodeDeparamCommon: NO OVERRIDES for '" << srcModp->name()
                      << "' cell='" << nodep->name() << "'" << endl);
            UINFO(8, "Cell parameters all match original values, skipping expansion.");
            // If it's the first use of the default instance, create a copy and store it in user3p.
            // user3p will also be used to check if the default instance is used.
            if (!srcModp->user3p() && (VN_IS(srcModp, Class) || VN_IS(srcModp, Iface))) {
                AstNodeModule* nodeCopyp = srcModp->cloneTree(false);
                // It is a temporary copy of the original class node, stored in order to create
                // another instances. It is needed only during class instantiation.
                UINFO(8, "    Created clone " << nodeCopyp);
                m_deleter.pushDeletep(nodeCopyp);
                srcModp->user3p(nodeCopyp);
                storeOriginalParams(nodeCopyp);
            }
            newModp = srcModp;
        } else {
            const string newname
                = srcModp->hierBlock() ? longname : moduleCalcName(srcModp, longname);
            const ModInfo* const modInfop
                = moduleFindOrClone(srcModp, nodep, paramsp, newname, ifaceRefRefs);
            if (!modInfop) return nullptr;
            // We need to relink the pins to the new module
            relinkPinsByName(pinsp, modInfop->m_modp);
            UINFO(8, "     Done with " << modInfop->m_modp);
            newModp = modInfop->m_modp;
        }

        const bool cloned = (newModp != srcModp);
        UINFO(9, "iface capture module clone src=" << srcModp << " new=" << newModp << " name="
                                                   << newModp->name() << " from cell=" << nodep
                                                   << " cellName=" << nodep->name()
                                                   << " cloned=" << cloned);

        if (defaultsResolved) srcModp->user4p(newModp);

        for (auto* stmtp = newModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstParamTypeDType* dtypep = VN_CAST(stmtp, ParamTypeDType)) {
                if (VN_IS(dtypep->skipRefOrNullp(), VoidDType)) {
                    nodep->v3error(
                        "Class parameter type without default value is never given value"
                        << " (IEEE 1800-2023 6.20.1): " << dtypep->prettyNameQ());
                    VL_DO_DANGLING(m_deleter.pushDeletep(nodep->unlinkFrBack()), nodep);
                }
            }
            if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                if (VN_IS(newModp, Class) && varp->isParam() && !varp->valuep()) {
                    nodep->v3error("Class parameter without default value is never given value"
                                   << " (IEEE 1800-2023 6.20.1): " << varp->prettyNameQ());
                }
            }
        }

        genericInterfaceVarSetup(paramsp, pinsp);

        // Delete the parameters from the cell; they're not relevant any longer.
        if (paramsp) paramsp->unlinkFrBackWithNext()->deleteTree();
        return newModp;
    }

    AstNodeModule* cellDeparam(AstCell* nodep, AstNodeModule* srcModp) {
        // Must always clone __Vrcm (recursive modules)
        AstNodeModule* const newModp = nodeDeparamCommon(nodep, srcModp, nodep->paramsp(),
                                                         nodep->pinsp(), nodep->recursive());
        if (!newModp) return nullptr;
        nodep->modp(newModp);  // Might be unchanged if not cloned (newModp == srcModp)
        nodep->modName(newModp->name());
        nodep->recursive(false);
        return newModp;
    }
    AstNodeModule* ifaceRefDeparam(AstIfaceRefDType* const nodep, AstNodeModule* srcModp) {
        // Check for self-reference pattern: typedef iface#(T) this_type inside interface iface
        // When processing inside a specialized interface, the IfaceRefDType should point to
        // the owner interface, not create an intermediate specialization.
        if (m_modp && VN_IS(m_modp, Iface)) {
            AstIface* ownerIfacep = const_cast<AstIface*>(VN_AS(m_modp, Iface));
            const string ownerOrigName = ownerIfacep->origName().empty()
                                             ? ownerIfacep->name()
                                             : ownerIfacep->origName();
            const string srcOrigName = srcModp->origName().empty()
                                           ? srcModp->name()
                                           : srcModp->origName();
            string ownerBaseName = ownerOrigName;
            const size_t ownerPos = ownerBaseName.find("__");
            if (ownerPos != string::npos) ownerBaseName = ownerBaseName.substr(0, ownerPos);
            string srcBaseName = srcOrigName;
            const size_t srcPos = srcBaseName.find("__");
            if (srcPos != string::npos) srcBaseName = srcBaseName.substr(0, srcPos);

            if (ownerBaseName == srcBaseName) {
                bool allOwnParams = true;
                for (AstPin* pinp = nodep->paramsp(); pinp && allOwnParams;
                     pinp = VN_AS(pinp->nextp(), Pin)) {
                    if (AstRefDType* const refp = VN_CAST(pinp->exprp(), RefDType)) {
                        if (AstParamTypeDType* const ptdp
                            = VN_CAST(refp->refDTypep(), ParamTypeDType)) {
                            AstNodeModule* const ptdOwnerp
                                = V3LinkDotDepGraph::findOwnerModule(ptdp);
                            if (ptdOwnerp != m_modp) allOwnParams = false;
                        } else {
                            allOwnParams = false;
                        }
                    } else {
                        allOwnParams = false;
                    }
                }
                if (allOwnParams) {
                    UINFO(5, "ifaceRefDeparam: self-reference pattern detected in "
                              << ownerIfacep->name() << ", using owner interface" << endl);
                    nodep->ifacep(ownerIfacep);
                    if (nodep->paramsp()) nodep->paramsp()->unlinkFrBackWithNext()->deleteTree();
                    return ownerIfacep;
                }
            }
        }

        AstNodeModule* const newModp
            = nodeDeparamCommon(nodep, srcModp, nodep->paramsp(), nullptr, false);
        if (!newModp) return nullptr;
        nodep->ifacep(VN_AS(newModp, Iface));
        return newModp;
    }
    AstNodeModule* classRefDeparam(AstClassOrPackageRef* nodep, AstNodeModule* srcModp) {
        resolveDefaultParams(nodep);
        AstNodeModule* const newModp
            = nodeDeparamCommon(nodep, srcModp, nodep->paramsp(), nullptr, false);
        if (!newModp) return nullptr;
        nodep->classOrPackagep(newModp);  // Might be unchanged if not cloned (newModp == srcModp)

        // If this ClassOrPackageRef is a child of a RefDType (e.g., typedef class#(T)::member_t),
        // resolve the RefDType's typedef to point to the typedef inside the specialized class.
        // This must also retarget existing typedefp that still points at the original class.
        AstRefDType* const refDTypep = VN_CAST(nodep->backp(), RefDType);
        AstClass* const newClassp = refDTypep ? VN_CAST(newModp, Class) : nullptr;
        if (newClassp) {
            AstTypedef* typedefp = VN_CAST(m_memberMap.findMember(newClassp, refDTypep->name()), Typedef);
            if (!typedefp) {
                for (AstNode* stmtp = newClassp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                    if (AstTypedef* const tdp = VN_CAST(stmtp, Typedef)) {
                        if (tdp->name() == refDTypep->name()) {
                            typedefp = tdp;
                            break;
                        }
                    }
                }
            }
            UINFO(5, "classRefDeparam: ref=" << refDTypep
                                              << " name=" << refDTypep->name()
                                              << " old=" << refDTypep->typedefp()
                                              << " newClass=" << newClassp
                                              << " found=" << typedefp << endl);
            if (typedefp && refDTypep->typedefp() != typedefp) {
                refDTypep->typedefp(typedefp);
                refDTypep->classOrPackagep(newClassp);
                UINFO(9, "Resolved parameterized class typedef: " << refDTypep->name() << " -> "
                                                                  << typedefp << " in "
                                                                  << newClassp->name());
            }
            if (refDTypep->classOrPackageOpp() == nodep) {
                nodep->unlinkFrBack();
                refDTypep->classOrPackageOpp(nullptr);
            }
        }
        return newModp;
    }
    AstNodeModule* classRefDeparam(AstClassRefDType* nodep, AstNodeModule* srcModp) {
        resolveDefaultParams(nodep);

        // Check for self-reference pattern: typedef c1#(REQ, RSP) this_type inside class c1
        // When processing inside a specialized c1 class, the ClassRefDType should point to
        // the owner class, not create an intermediate specialization.
        if (m_modp && VN_IS(m_modp, Class)) {
            AstClass* ownerClassp = const_cast<AstClass*>(VN_AS(m_modp, Class));
            // Check if srcModp is the same base class as the owner
            const string ownerOrigName = ownerClassp->origName().empty()
                                             ? ownerClassp->name()
                                             : ownerClassp->origName();
            const string srcOrigName = srcModp->origName().empty()
                                           ? srcModp->name()
                                           : srcModp->origName();
            // Extract base name (before __) for specialized classes
            string ownerBaseName = ownerOrigName;
            const size_t ownerPos = ownerBaseName.find("__");
            if (ownerPos != string::npos) ownerBaseName = ownerBaseName.substr(0, ownerPos);
            string srcBaseName = srcOrigName;
            const size_t srcPos = srcBaseName.find("__");
            if (srcPos != string::npos) srcBaseName = srcBaseName.substr(0, srcPos);

            if (ownerBaseName == srcBaseName) {
                // Check if all parameters are the owner's own type parameters
                bool allOwnParams = true;
                for (AstPin* pinp = nodep->paramsp(); pinp && allOwnParams;
                     pinp = VN_AS(pinp->nextp(), Pin)) {
                    if (AstRefDType* const refp = VN_CAST(pinp->exprp(), RefDType)) {
                        if (AstParamTypeDType* const ptdp
                            = VN_CAST(refp->refDTypep(), ParamTypeDType)) {
                            // Check if this PARAMTYPEDTYPE belongs to the owner class
                            AstNodeModule* const ptdOwnerp
                                = V3LinkDotDepGraph::findOwnerModule(ptdp);
                            if (ptdOwnerp != m_modp) allOwnParams = false;
                        } else {
                            allOwnParams = false;
                        }
                    } else {
                        allOwnParams = false;
                    }
                }
                if (allOwnParams) {
                    // This is a self-reference - use the owner class directly
                    UINFO(5, "classRefDeparam: self-reference pattern detected in "
                              << ownerClassp->name() << ", using owner class" << endl);
                    nodep->classp(ownerClassp);
                    nodep->classOrPackagep(ownerClassp);
                    // Delete the parameters - they're not needed for self-reference
                    if (nodep->paramsp()) nodep->paramsp()->unlinkFrBackWithNext()->deleteTree();
                    return ownerClassp;
                }
            }
        }

        AstNodeModule* const newModp
            = nodeDeparamCommon(nodep, srcModp, nodep->paramsp(), nullptr, false);
        if (!newModp) return nullptr;
        AstClass* const oldClassp = nodep->classp();
        AstClass* const newClassp = VN_AS(newModp, Class);
        nodep->classp(newClassp);  // Might be unchanged if not cloned (newModp == srcModp)
        nodep->classOrPackagep(newClassp);

        if (oldClassp && newClassp && oldClassp != newClassp && m_modp) {
            std::unordered_map<string, AstTypedef*> memberTypedefs;
            for (AstNode* stmtp = newClassp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                if (AstTypedef* const tdp = VN_CAST(stmtp, Typedef)) {
                    memberTypedefs.emplace(tdp->name(), tdp);
                }
            }

            class RefDTypeRetargetVisitor final : public VNVisitor {
                const AstClass* m_oldClassp;
                AstClass* m_newClassp;
                const std::unordered_map<string, AstTypedef*>& m_memberTypedefs;

                void visit(AstRefDType* refp) override {
                    if (refp->classOrPackagep() == m_oldClassp) {
                        auto it = m_memberTypedefs.find(refp->name());
                        if (it != m_memberTypedefs.end() && refp->typedefp() != it->second) {
                            refp->typedefp(it->second);
                            refp->classOrPackagep(m_newClassp);
                            UINFO(5, "classRefDeparam: retarget refdtype name=" << refp->name()
                                                                                << " ref=" << refp
                                                                                << " typedef=" << it->second
                                                                                << " class=" << m_newClassp << endl);
                        }
                    }
                    iterateChildren(refp);
                }
                void visit(AstNode* nodep) override { iterateChildren(nodep); }

            public:
                RefDTypeRetargetVisitor(const AstClass* oldClassp, AstClass* newClassp,
                                        const std::unordered_map<string, AstTypedef*>& memberTypedefs,
                                        const AstNodeModule* ownerModp)
                    : m_oldClassp(oldClassp)
                    , m_newClassp(newClassp)
                    , m_memberTypedefs(memberTypedefs) {
                    if (ownerModp) iterate(const_cast<AstNodeModule*>(ownerModp));
                }
            } visitor{oldClassp, newClassp, memberTypedefs, m_modp};
            (void)visitor;
        }

        return newClassp;
    }

public:
    AstNodeModule* nodeDeparam(AstNode* nodep, AstNodeModule* srcModp, AstNodeModule* modp,
                               const string& someInstanceName) {
        // Return new or reused de-parameterized module
        m_modp = modp;
        // Cell: Check for parameters in the instantiation.
        // We always run this, even if no parameters, as need to look for interfaces,
        // and remove any recursive references
        UINFO(4, "De-parameterize: " << nodep);
        // Create new module name with _'s between the constants
        UINFOTREE(10, nodep, "", "cell");
        // Evaluate all module constants
        V3Const::constifyParamsEdit(nodep);
        // Set name for warnings for when we param propagate the module
        // For AstIfaceRefDType, name() returns the modport name (often empty),
        // so use cellName() which is the actual cell instance name.
        // If both are empty (interface port, not a cell), skip appending
        // to avoid double-dots in the path.
        string nodeName = nodep->name();
        if (AstIfaceRefDType* const ifaceRefp = VN_CAST(nodep, IfaceRefDType)) {
            if (nodeName.empty()) nodeName = ifaceRefp->cellName();
        }
        const string instanceName
            = nodeName.empty() ? someInstanceName : (someInstanceName + "." + nodeName);
        srcModp->someInstanceName(instanceName);

        AstNodeModule* newModp = nullptr;
        if (AstCell* cellp = VN_CAST(nodep, Cell)) {
            newModp = cellDeparam(cellp, srcModp);
        } else if (AstIfaceRefDType* ifaceRefDTypep = VN_CAST(nodep, IfaceRefDType)) {
            newModp = ifaceRefDeparam(ifaceRefDTypep, srcModp);
        } else if (AstClassRefDType* classRefp = VN_CAST(nodep, ClassRefDType)) {
            newModp = classRefDeparam(classRefp, srcModp);
        } else if (AstClassOrPackageRef* classRefp = VN_CAST(nodep, ClassOrPackageRef)) {
            newModp = classRefDeparam(classRefp, srcModp);
        } else {
            nodep->v3fatalSrc("Expected module parameterization");
        }
        // 'newModp' might be nullptr on error
        if (!newModp) return nullptr;

        // Set name for later warnings
        newModp->someInstanceName(instanceName);

        UINFO(8, "     Done with orig " << nodep);
        // if (debug() >= 10)
        // v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("param-out.tree"));
        return newModp;
    }

    // CONSTRUCTORS
    explicit ParamProcessor(AstNetlist* nodep)
        : m_hierBlocks{v3Global.opt.hierBlocks(), nodep} {
        for (AstNodeModule* modp = nodep->modulesp(); modp;
             modp = VN_AS(modp->nextp(), NodeModule)) {
            m_allModuleNames.insert(modp->name());
        }
    }
    ~ParamProcessor() = default;
    VL_UNCOPYABLE(ParamProcessor);
};

//######################################################################
// Record classes that are referenced with parameter pins

class ClassRefUnlinkerVisitor final : public VNVisitor {

public:
    explicit ClassRefUnlinkerVisitor(AstNetlist* netlistp) { iterate(netlistp); }
    void visit(AstClassOrPackageRef* nodep) override {
        if (nodep->paramsp()) {
            if (AstClass* const classp = VN_CAST(nodep->classOrPackageSkipp(), Class)) {
                if (!classp->user3p()) {
                    // Check if this ClassOrPackageRef is the lhsp of a DOT node
                    AstDot* const dotp = VN_CAST(nodep->backp(), Dot);
                    if (dotp && dotp->lhsp() == nodep) {
                        // Replace DOT with just its rhsp to avoid leaving DOT with null lhsp
                        dotp->replaceWith(dotp->rhsp()->unlinkFrBack());
                        VL_DO_DANGLING2(pushDeletep(dotp), dotp, nodep);
                    } else {
                        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
                    }
                }
            }
        }
    }
    void visit(AstClass* nodep) override {}  // don't iterate inside classes
    void visit(AstNode* nodep) override { iterateChildren(nodep); }
};

//######################################################################
// Process parameter top state

class ParamState final {
public:
    // STATE - across all visitors
    std::vector<AstClass*> m_paramClasses;  // Parameterized classes
    std::vector<AstDot*> m_dots;  // Dot references to process
    std::multimap<int, AstNodeModule*> m_workQueueNext;  // Modules left to process
    // Map from AstNodeModule to set of all AstNodeModules that instantiates it.
    std::unordered_map<AstNodeModule*, std::unordered_set<AstNodeModule*>> m_parentps;
};

//######################################################################
// Process parameter visitor

class ParamVisitor final : public VNVisitor {
    // NODE STATE
    // AstNodeModule::user1 -> bool: already fixed level (temporary)
    // AstNodeDType::user2  -> bool: already visited from typedef

    // STATE - across all visitors
    ParamState& m_state;  // Common state
    ParamProcessor m_processor;  // De-parameterize a cell, build modules
    GenForUnroller m_unroller;  // Unroller for AstGenFor

    bool m_iterateModule = false;  // Iterating module body
    string m_unlinkedTxt;  // Text for AstUnlinkedRef
    std::multimap<bool, AstNode*> m_cellps;  // Cells left to process (in current module)
    std::deque<std::string> m_strings;  // Allocator for temporary strings
    std::map<const AstRefDType*, bool>
        m_isCircular;  // Stores information whether `AstRefDType` is circular

    // STATE - for current visit position (use VL_RESTORER)
    AstNodeModule* m_modp = nullptr;  // Module iterating
    std::unordered_set<std::string> m_ifacePortNames;  // Interface port names in current module
    std::unordered_set<std::string> m_ifaceInstNames;  // Interface decl names in current module
    string m_generateHierName;  // Generate portion of hierarchy name

    // METHODS

    void processWorkQ() {
        UASSERT(!m_iterateModule, "Should not nest");
        std::multimap<int, AstNodeModule*> workQueue;
        m_generateHierName = "";
        m_iterateModule = true;

        // Visit all cells under module, recursively
        while (true) {
            if (workQueue.empty()) std::swap(workQueue, m_state.m_workQueueNext);
            if (workQueue.empty()) break;

            const auto itm = workQueue.cbegin();
            AstNodeModule* const modp = itm->second;
            workQueue.erase(itm);

            // Process once; note user2 will be cleared on specialization, so we will do the
            // specialized module if needed
            if (!modp->user2SetOnce()) {

                // TODO: this really should be an assert, but classes and hier_blocks are
                // special...
                if (modp->someInstanceName().empty()) modp->someInstanceName(modp->origName());

                // Iterate the body
                {
                    VL_RESTORER(m_modp);
                    VL_RESTORER(m_ifacePortNames);
                    VL_RESTORER(m_ifaceInstNames);
                    m_modp = modp;
                    m_ifacePortNames.clear();
                    m_ifaceInstNames.clear();
                    iterateChildren(modp);
                }
            }

            // Process interface cells, then non-interface cells, which may reference an interface
            // cell.
            while (!m_cellps.empty()) {
                const auto itim = m_cellps.cbegin();
                AstNode* const cellp = itim->second;
                m_cellps.erase(itim);

                AstNodeModule* srcModp = nullptr;
                if (const AstCell* modCellp = VN_CAST(cellp, Cell)) {
                    srcModp = modCellp->modp();
                } else if (const AstClassOrPackageRef* classRefp
                           = VN_CAST(cellp, ClassOrPackageRef)) {
                    srcModp = classRefp->classOrPackageSkipp();
                    if (VN_IS(classRefp->classOrPackageNodep(), ParamTypeDType)) continue;
                } else if (const AstClassRefDType* classRefp = VN_CAST(cellp, ClassRefDType)) {
                    srcModp = classRefp->classp();
                } else if (const AstIfaceRefDType* ifaceRefp = VN_CAST(cellp, IfaceRefDType)) {
                    srcModp = ifaceRefp->ifacep();
                } else {
                    cellp->v3fatalSrc("Expected module parameterization");
                }
                if (!srcModp) continue;

                // Update path
                string someInstanceName = modp->someInstanceName();
                if (const string* const genHierNamep = cellp->user2u().to<string*>()) {
                    someInstanceName += *genHierNamep;
                    cellp->user2p(nullptr);
                }

                // Apply parameter specialization
                if (AstNodeModule* const newModp
                    = m_processor.nodeDeparam(cellp, srcModp, modp, someInstanceName)) {

                    // Add the (now potentially specialized) child module to the work queue
                    workQueue.emplace(newModp->level(), newModp);

                    // Add to the hierarchy registry
                    m_state.m_parentps[newModp].insert(modp);
                }
            }
        }

        m_iterateModule = false;
    }


    // Extract the base reference name from a dotted VarXRef (e.g., "iface.FOO" -> "iface")
    string getRefBaseName(const AstVarXRef* refp) {
        const string dotted = refp->dotted();
        if (dotted.empty()) return "";
        return dotted.substr(0, dotted.find('.'));
    }

    void checkParamNotHier(AstNode* valuep) {
        if (!valuep) return;
        valuep->foreachAndNext([&](const AstNodeExpr* exprp) {
            if (const AstVarXRef* const refp = VN_CAST(exprp, VarXRef)) {
                // Allow hierarchical ref to interface params through interface/modport ports
                // or local interface instances
                bool isIfaceRef = false;
                if (refp->varp() && refp->varp()->isIfaceParam()) {
                    const string refname = getRefBaseName(refp);
                    isIfaceRef = !refname.empty()
                                 && (m_ifacePortNames.count(refname)
                                     || m_ifaceInstNames.count(refname));
                }

                if (!isIfaceRef) {
                    refp->v3warn(HIERPARAM, "Parameter values cannot use hierarchical values"
                                            " (IEEE 1800-2023 6.20.2)");
                }
            } else if (const AstNodeFTaskRef* refp = VN_CAST(exprp, NodeFTaskRef)) {
                if (refp->dotted() != "") {
                    refp->v3error("Parameter values cannot call hierarchical functions"
                                  " (IEEE 1800-2023 6.20.2)");
                }
            }
        });
    }

    // Check if cell parameters reference interface ports or local interface instances
    bool cellParamsReferenceIfacePorts(AstCell* cellp) {
        if (!cellp->paramsp()) return false;

        for (AstNode* nodep = cellp->paramsp(); nodep; nodep = nodep->nextp()) {
            if (AstPin* const pinp = VN_CAST(nodep, Pin)) {
                if (AstNode* const exprp = pinp->exprp()) {
                    if (const AstVarXRef* const refp = VN_CAST(exprp, VarXRef)) {
                        const string refname = getRefBaseName(refp);
                        if (!refname.empty()
                            && (m_ifacePortNames.count(refname)
                                || m_ifaceInstNames.count(refname)))
                            return true;
                    }
                }
            }
        }
        return false;
    }

    // A generic visitor for cells and class refs
    void visitCellOrClassRef(AstNode* nodep, bool isIface) {
        // Must do ifaces first, so push to list and do in proper order
        m_strings.emplace_back(m_generateHierName);
        nodep->user2p(&m_strings.back());

        // For interface cells with parameters, specialize first before processing children
        // Only do early specialization if parameters don't reference interface ports
        if (isIface && VN_CAST(nodep, Cell) && VN_CAST(nodep, Cell)->paramsp()) {
            AstCell* const cellp = VN_CAST(nodep, Cell);
            if (!cellParamsReferenceIfacePorts(cellp)) {
                AstNodeModule* const srcModp = cellp->modp();
                m_processor.nodeDeparam(cellp, srcModp, m_modp, m_modp->someInstanceName());
            }
        }

        // Visit parameters in the instantiation.
        iterateChildren(nodep);
        m_cellps.emplace(!isIface, nodep);
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        if (nodep->recursiveClone()) nodep->dead(true);  // Fake, made for recursive elimination
        if (nodep->dead()) return;  // Marked by LinkDot (and above)
        if (AstClass* const classp = VN_CAST(nodep, Class)) {
            if (classp->hasGParam()) {
                // Don't enter into a definition.
                // If a class is used, it will be visited through a reference and cloned
                m_state.m_paramClasses.push_back(classp);
                return;
            }
        }

        if (m_iterateModule) {  // Iterating from processWorkQ
            UINFO(4, " MOD-under-MOD.  " << nodep);
            // Delay until current module is done.
            // processWorkQ() (which we are returning to) will process nodep later
            m_state.m_workQueueNext.emplace(nodep->level(), nodep);
            return;
        }

        // Start traversal at root-like things
        if (nodep->isTop()  // Tops
            || VN_IS(nodep, Class)  //  Moved classes
            || VN_IS(nodep, Package)) {  // Likewise haven't done wrapTopPackages yet
            m_state.m_workQueueNext.emplace(nodep->level(), nodep);
            processWorkQ();
        }
    }

    bool isCircularType(const AstRefDType* nodep) {
        const auto iter = m_isCircular.emplace(nodep, true);
        if (!iter.second) return iter.first->second;
        if (const AstRefDType* const subDTypep = VN_CAST(nodep->subDTypep(), RefDType)) {
            const bool ret = isCircularType(subDTypep);
            iter.first->second = ret;
            return ret;
        }
        iter.first->second = false;
        return false;
    }

    void visit(AstRefDType* nodep) override {
        if (isCircularType(nodep)) {
            nodep->v3error("Typedef's type is circular: " << nodep->prettyName());
        } else if (nodep->typedefp() && nodep->subDTypep()
                   && (VN_IS(nodep->subDTypep()->skipRefOrNullp(), IfaceRefDType)
                       || VN_IS(nodep->subDTypep()->skipRefOrNullp(), ClassRefDType))
                   && !nodep->skipRefp()->user2SetOnce()) {
            iterate(nodep->skipRefp());
        }
        iterateChildren(nodep);
    }
    void visit(AstCell* nodep) override {
        checkParamNotHier(nodep->paramsp());
        // Build cache of locally declared interface instance names
        if (VN_IS(nodep->modp(), Iface)) { m_ifaceInstNames.insert(nodep->name()); }
        visitCellOrClassRef(nodep, VN_IS(nodep->modp(), Iface));
    }
    void visit(AstIfaceRefDType* nodep) override {
        if (nodep->ifacep()) visitCellOrClassRef(nodep, true);
    }
    void visit(AstClassRefDType* nodep) override {
        checkParamNotHier(nodep->paramsp());
        visitCellOrClassRef(nodep, false);
    }
    void visit(AstClassOrPackageRef* nodep) override {
        // If it points to a typedef it is not really a class reference. That typedef will be
        // visited anyway (from its parent node), so even if it points to a parameterized class
        // type, the instance will be created.
        if (!VN_IS(nodep->classOrPackageNodep(), Typedef)) visitCellOrClassRef(nodep, false);
    }

    // Make sure all parameters are constantified
    void visit(AstVar* nodep) override {
        if (nodep->user2SetOnce()) return;  // Process once
        // Build cache of interface port names as we encounter them
        if (nodep->isIfaceRef()) { m_ifacePortNames.insert(nodep->name()); }
        iterateChildren(nodep);
        if (nodep->isParam()) {
            checkParamNotHier(nodep->valuep());
            if (!nodep->valuep() && !VN_IS(m_modp, Class)) {
                nodep->v3error("Parameter without default value is never given value"
                               << " (IEEE 1800-2023 6.20.1): " << nodep->prettyNameQ());
            } else {
                // In visit(AstVar*) for localparams, check if expression contains VARXREF
                // to another localparam (not parameter). Parameters are already const,
                // but localparams may not be evaluated yet.
                bool hasVarXRefToLparam = false;
                nodep->valuep()->foreach([&](const AstVarXRef* xrefp) {
                    if (xrefp->varp() && xrefp->varp()->varType() == VVarType::LPARAM) {
                        hasVarXRefToLparam = true;
                    }
                });
                if (hasVarXRefToLparam) {
                    // Don't constify - let it be evaluated later
                    return;
                }

                V3Const::constifyParamsEdit(nodep);
            }
        }
    }
    void visit(AstParamTypeDType* nodep) override {
        iterateChildren(nodep);
        if (VN_IS(nodep->skipRefOrNullp(), VoidDType)) {
            nodep->v3error("Parameter type without default value is never given value"
                           << " (IEEE 1800-2023 6.20.1): " << nodep->prettyNameQ());
        }
    }
    // Make sure varrefs cause vars to constify before things above
    void visit(AstVarRef* nodep) override {
        // Might jump across functions, so beware if ever add a m_funcp
        if (nodep->varp()) iterate(nodep->varp());
    }
    bool ifaceParamReplace(AstVarXRef* nodep, AstNode* candp) {
        for (; candp; candp = candp->nextp()) {
            if (nodep->name() == candp->name()) {
                if (AstVar* const varp = VN_CAST(candp, Var)) {
                    UINFO(9, "Found interface parameter: " << varp);
                    nodep->varp(varp);
                    return true;
                } else if (const AstPin* const pinp = VN_CAST(candp, Pin)) {
                    UINFO(9, "Found interface parameter: " << pinp);
                    UASSERT_OBJ(pinp->exprp(), pinp, "Interface parameter pin missing expression");
                    nodep->replaceWith(pinp->exprp()->cloneTree(false));
                    VL_DO_DANGLING(pushDeletep(nodep), nodep);
                    return true;
                }
            }
        }
        return false;
    }
    void visit(AstVarXRef* nodep) override {
        if (nodep->containsGenBlock()) {
            // Needs relink, as may remove pointed-to var
            nodep->varp(nullptr);
            return;
        }
        // Check to see if the scope is just an interface because interfaces are special
        const string dotted = nodep->dotted();
        if (!dotted.empty() && nodep->varp() && nodep->varp()->isParam()) {
            const AstNode* backp = nodep;
            while ((backp = backp->backp())) {
                if (VN_IS(backp, NodeModule)) {
                    UINFO(9, "Hit module boundary, done looking for interface");
                    break;
                }
                if (const AstVar* const varp = VN_CAST(backp, Var)) {
                    if (!varp->isIfaceRef()) continue;
                    const AstIfaceRefDType* ifacerefp = nullptr;
                    if (const AstNodeDType* const typep = varp->childDTypep()) {
                        ifacerefp = VN_CAST(typep, IfaceRefDType);
                        if (!ifacerefp) {
                            if (VN_IS(typep, UnpackArrayDType)) {
                                ifacerefp = VN_CAST(typep->getChildDTypep(), IfaceRefDType);
                            }
                        }
                        if (!ifacerefp) {
                            if (VN_IS(typep, BracketArrayDType)) {
                                ifacerefp = VN_CAST(typep->subDTypep(), IfaceRefDType);
                            }
                        }
                    }
                    if (!ifacerefp) continue;
                    // Interfaces passed in on the port map have ifaces
                    if (const AstIface* const ifacep = ifacerefp->ifacep()) {
                        if (dotted == backp->name()) {
                            UINFO(9, "Iface matching scope:  " << ifacep);
                            if (ifaceParamReplace(nodep, ifacep->stmtsp())) {  //
                                return;
                            }
                        }
                    }
                    // Interfaces declared in this module have cells
                    else if (const AstCell* const cellp = ifacerefp->cellp()) {
                        if (dotted == cellp->name()) {
                            UINFO(9, "Iface matching scope:  " << cellp);
                            if (ifaceParamReplace(nodep, cellp->modp()->stmtsp())) {  //
                                return;
                            }
                        }
                    }
                }
            }
        }
    }

    void visit(AstDot* nodep) override {
        iterate(nodep->lhsp());
        // Check if it is a reference to a field of a parameterized class.
        // If so, the RHS should be updated, when the LHS is replaced
        // by a class with actual parameter values.
        const AstClass* lhsClassp = nullptr;
        const AstClassOrPackageRef* const classRefp = VN_CAST(nodep->lhsp(), ClassOrPackageRef);
        if (classRefp) lhsClassp = VN_CAST(classRefp->classOrPackageSkipp(), Class);
        AstNode* rhsDefp = nullptr;
        AstClassOrPackageRef* const rhsp = VN_CAST(nodep->rhsp(), ClassOrPackageRef);
        if (rhsp) rhsDefp = rhsp->classOrPackageNodep();
        if (lhsClassp && rhsDefp) {
            m_state.m_dots.push_back(nodep);
            // No need to iterate into rhsp, because there should be nothing to do
        } else {
            iterate(nodep->rhsp());
        }
    }

    void visit(AstUnlinkedRef* nodep) override {
        AstVarXRef* const varxrefp = VN_CAST(nodep->refp(), VarXRef);
        AstNodeFTaskRef* const taskrefp = VN_CAST(nodep->refp(), NodeFTaskRef);
        if (varxrefp) {
            m_unlinkedTxt = varxrefp->dotted();
        } else if (taskrefp) {
            m_unlinkedTxt = taskrefp->dotted();
        } else {
            nodep->v3fatalSrc("Unexpected AstUnlinkedRef node");
            return;
        }
        iterate(nodep->cellrefp());

        if (varxrefp) {
            varxrefp->dotted(m_unlinkedTxt);
        } else {
            taskrefp->dotted(m_unlinkedTxt);
        }
        nodep->replaceWith(nodep->refp()->unlinkFrBack());
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstCellArrayRef* nodep) override {
        V3Const::constifyParamsEdit(nodep->selp());
        if (const AstConst* const constp = VN_CAST(nodep->selp(), Const)) {
            const string index = AstNode::encodeNumber(constp->toSInt());
            const string replacestr = nodep->name() + "__BRA__??__KET__";
            // Before searching for "__BRA__??__KET__", synthesize it if missing
            if (m_unlinkedTxt.empty()) m_unlinkedTxt = replacestr;
            const size_t pos = m_unlinkedTxt.find(replacestr);
            if (pos == string::npos) {
                nodep->v3error("Could not find array index placeholder in unlinked text: '"
                               << m_unlinkedTxt << "' for node: " << nodep);
                return;
            }
            m_unlinkedTxt.replace(pos, replacestr.length(),
                                  nodep->name() + "__BRA__" + index + "__KET__");
        } else {
            nodep->v3error("Could not expand constant selection inside dotted reference: "
                           << nodep->selp()->prettyNameQ());
            return;
        }
    }

    // Generate Statements
    void visit(AstGenIf* nodep) override {
        UINFO(9, "  GENIF " << nodep);
        iterateAndNextNull(nodep->condp());
        // We suppress errors when widthing params since short-circuiting in
        // the conditional evaluation may mean these error can never occur. We
        // then make sure that short-circuiting is used by constifyParamsEdit.
        V3Width::widthGenerateParamsEdit(nodep);  // Param typed widthing will
                                                  // NOT recurse the body.
        V3Const::constifyGenerateParamsEdit(nodep->condp());  // condp may change
        if (const AstConst* const constp = VN_CAST(nodep->condp(), Const)) {
            if (AstNode* const keepp = (constp->isZero() ? nodep->elsesp() : nodep->thensp())) {
                keepp->unlinkFrBackWithNext();
                nodep->replaceWith(keepp);
            } else {
                nodep->unlinkFrBack();
            }
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            // Normal edit rules will now recurse the replacement
        } else {
            nodep->condp()->v3error("Generate If condition must evaluate to constant");
        }
    }

    void visit(AstGenBlock* nodep) override {
        // Parameter substitution for generated for loops.
        // TODO Unlike generated IF, we don't have to worry about short-circuiting the
        // conditional expression, since this is currently restricted to simple
        // comparisons. If we ever do move to more generic constant expressions, such code
        // will be needed here.
        if (AstGenFor* const forp = VN_AS(nodep->genforp(), GenFor)) {
            // We should have a GENFOR under here.  We will be replacing the begin,
            // so process here rather than at the generate to avoid iteration problems
            UINFO(9, "  BEGIN " << nodep);
            UINFO(9, "  GENFOR " << forp);
            // Visit child nodes before unrolling
            iterateAndNextNull(forp->initsp());
            iterateAndNextNull(forp->condp());
            iterateAndNextNull(forp->incsp());
            V3Width::widthParamsEdit(forp);  // Param typed widthing will NOT recurse the body
            // Outer wrapper around generate used to hold genvar, and to ensure genvar
            // doesn't conflict in V3LinkDot resolution with other genvars
            // Now though we need to change BEGIN("zzz", GENFOR(...)) to
            // a BEGIN("zzz__BRA__{loop#}__KET__")
            const string beginName = nodep->name();
            // Leave the original Begin, as need a container for the (possible) GENVAR
            // Note m_unroller will replace some AstVarRef's to the loop variable with constants
            // Don't remove any deleted nodes in m_unroller until whole process finishes,
            // as some AstXRefs may still point to old nodes.
            VL_DO_DANGLING(m_unroller.unroll(forp, beginName), forp);
            // Blocks were constructed under the special begin, move them up
            // Note forp is null, so grab statements again
            if (AstNode* const stmtsp = nodep->genforp()) {
                stmtsp->unlinkFrBackWithNext();
                nodep->addNextHere(stmtsp);
                // Note this clears nodep->genforp(), so begin is no longer special
            }
        } else {
            VL_RESTORER(m_generateHierName);
            m_generateHierName += "." + nodep->prettyName();
            iterateChildren(nodep);
        }
    }
    void visit(AstGenFor* nodep) override {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc("GENFOR should have been wrapped in BEGIN");
    }
    void visit(AstGenCase* nodep) override {
        UINFO(9, "  GENCASE " << nodep);
        bool hit = false;
        AstNode* keepp = nullptr;
        iterateAndNextNull(nodep->exprp());
        V3Case::caseLint(nodep);
        V3Width::widthParamsEdit(nodep);  // Param typed widthing will NOT recurse the
                                          // body, don't trigger errors yet.
        V3Const::constifyParamsEdit(nodep->exprp());  // exprp may change
        const AstConst* const exprp = VN_AS(nodep->exprp(), Const);
        // Constify
        for (AstGenCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), GenCaseItem)) {
            for (AstNode* ep = itemp->condsp(); ep;) {
                AstNode* const nextp = ep->nextp();  // May edit list
                iterateAndNextNull(ep);
                VL_DO_DANGLING(V3Const::constifyParamsEdit(ep), ep);  // ep may change
                ep = nextp;
            }
        }
        // Item match
        for (AstGenCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), GenCaseItem)) {
            if (!itemp->isDefault()) {
                for (AstNode* ep = itemp->condsp(); ep; ep = ep->nextp()) {
                    if (const AstConst* const ccondp = VN_CAST(ep, Const)) {
                        V3Number match{nodep, 1};
                        match.opEq(ccondp->num(), exprp->num());
                        if (!hit && match.isNeqZero()) {
                            hit = true;
                            keepp = itemp->itemsp();
                        }
                    } else {
                        itemp->v3error("Generate Case item does not evaluate to constant");
                    }
                }
            }
        }
        // Else default match
        for (AstGenCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), GenCaseItem)) {
            if (itemp->isDefault()) {
                if (!hit) {
                    hit = true;
                    keepp = itemp->itemsp();
                }
            }
        }
        // Replace
        if (keepp) {
            keepp->unlinkFrBackWithNext();
            nodep->replaceWith(keepp);
        } else {
            nodep->unlinkFrBack();
        }
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ParamVisitor(ParamState& state, AstNetlist* netlistp)
        : m_state{state}
        , m_processor{netlistp} {

        // Relies on modules already being in top-down-order
        iterate(netlistp);
    }
    ~ParamVisitor() override = default;
    VL_UNCOPYABLE(ParamVisitor);
};

//######################################################################
// Process top handler

class ParamTop final : VNDeleter {
    // NODE STATE
    // AstNodeModule::user1 -> bool: already fixed level (temporary)

    // STATE
    ParamState m_state;  // Common state

    // METHODS

    void relinkDots() {
        // RHSs of AstDots need a relink when LHS is a parameterized class reference
        for (AstDot* const dotp : m_state.m_dots) {
            const AstClassOrPackageRef* const classRefp = VN_AS(dotp->lhsp(), ClassOrPackageRef);
            const AstClass* const lhsClassp = VN_AS(classRefp->classOrPackageSkipp(), Class);
            AstClassOrPackageRef* const rhsp = VN_AS(dotp->rhsp(), ClassOrPackageRef);
            for (auto* itemp = lhsClassp->membersp(); itemp; itemp = itemp->nextp()) {
                if (itemp->name() == rhsp->name()) {
                    rhsp->classOrPackageNodep(itemp);
                    break;
                }
            }
        }
    }

    void fixLevel(AstNodeModule* modp) {
        // Fix up level of module, based on who instantiates it
        if (modp->user1SetOnce()) return;  // Already fixed
        if (m_state.m_parentps[modp].empty()) return;  // Leave top levels alone
        int maxParentLevel = 0;
        for (AstNodeModule* parentp : m_state.m_parentps[modp]) {
            fixLevel(parentp);  // Ensure parent level is correct
            maxParentLevel = std::max(maxParentLevel, parentp->level());
        }
        if (modp->level() <= maxParentLevel) modp->level(maxParentLevel + 1);
        // Not correct fixup of depth(), as it should be mininum.  But depth() is unused
        // past V3LinkParse, so just do something sane in case this code doesn't get updated
        modp->depth(modp->level());
    }

    void resortNetlistModules(AstNetlist* netlistp) {
        // Re-sort module list to be in topological order and fix-up incorrect levels. We need to
        // do this globally at the end due to the presence of recursive modules, which might be
        // expanded in orders that reuse earlier specializations later at a lower level.
        // Gather modules
        std::vector<AstNodeModule*> modps;
        for (AstNodeModule *modp = netlistp->modulesp(), *nextp; modp; modp = nextp) {
            nextp = VN_AS(modp->nextp(), NodeModule);
            modp->unlinkFrBack();
            modps.push_back(modp);
        }

        // Fix-up levels
        const VNUser1InUse user1InUse;
        for (AstNodeModule* const modp : modps) fixLevel(modp);

        // Sort by level
        std::stable_sort(modps.begin(), modps.end(),
                         [](const AstNodeModule* ap, const AstNodeModule* bp) {
                             return ap->level() < bp->level();
                         });

        // Re-insert modules
        for (AstNodeModule* const modp : modps) netlistp->addModulesp(modp);
    }

public:
    // CONSTRUCTORS
    explicit ParamTop(AstNetlist* netlistp) {
        // Relies on modules already being in top-down-order
        ParamVisitor paramVisitor{m_state /*ref*/, netlistp};

        // Mark classes which cannot be removed because they are still referenced
        ClassRefUnlinkerVisitor classUnlinkerVisitor{netlistp};

        netlistp->foreach([](AstNodeFTaskRef* ftaskrefp) {
            AstNodeFTask* ftaskp = ftaskrefp->taskp();
            if (!ftaskp || !ftaskp->classMethod()) return;
            string funcName = ftaskp->name();
            for (AstNode* backp = ftaskrefp->backp(); backp; backp = backp->backp()) {
                if (VN_IS(backp, Class)) {
                    if (backp == ftaskrefp->classOrPackagep())
                        return;  // task is in the same class as reference
                    break;
                }
            }
            AstClass* classp = nullptr;
            for (AstNode* backp = ftaskp->backp(); backp; backp = backp->backp()) {
                if (VN_IS(backp, Class)) {
                    classp = VN_AS(backp, Class);
                    break;
                }
            }
            UASSERT_OBJ(classp, ftaskrefp, "Class method has no class above it");
            if (classp->user3p()) return;  // will not get removed, no need to relink
            AstClass* parametrizedClassp = VN_CAST(classp->user4p(), Class);
            if (!parametrizedClassp) return;
            AstNodeFTask* newFuncp = nullptr;
            parametrizedClassp->exists([&newFuncp, funcName](AstNodeFTask* ftaskp) {
                if (ftaskp->name() == funcName) {
                    newFuncp = ftaskp;
                    return true;
                }
                return false;
            });
            if (newFuncp) {
                // v3error(ftaskp <<"->" << newFuncp);
                ftaskrefp->taskp(newFuncp);
                ftaskrefp->classOrPackagep(parametrizedClassp);
            }
        });

        relinkDots();

        resortNetlistModules(netlistp);

        // For occasional debug only; this will upset VL_LEAK_CHECKS
        // V3Global::dumpCheckGlobalTree("param-predel", 0, dumpTreeEitherLevel() >= 9);

        // Remove defaulted classes
        // Unlike modules, which we keep around and mark dead() for later V3Dead
        std::unordered_set<AstClass*> removedClassps;
        for (AstClass* const classp : m_state.m_paramClasses) {
            if (!classp->user3p()) {
                // If there was an error, don't remove classes as they might
                // have remained referenced, and  will crash in V3Broken or
                // other locations. This is fine, we will abort imminently.
                if (V3Error::errorCount()) continue;
                removedClassps.emplace(classp);
                VL_DO_DANGLING(pushDeletep(classp->unlinkFrBack()), classp);
            } else {
                // Referenced. classp became a specialized class with the default
                // values of parameters and is not a parameterized class anymore
                classp->hasGParam(false);
            }
        }
        // Remove references to defaulted classes
        // Reuse user3 to mark all nodes being deleted
        AstNode::user3ClearTree();
        for (AstClass* classp : removedClassps) {
            classp->foreach([](AstNode* const nodep) { nodep->user3(true); });
        }
        // Set all links pointing to a user3 (deleting) node as null
        netlistp->foreach([](AstNode* const nodep) {
            nodep->foreachLink([&](AstNode** const linkpp, const char*) {
                if (*linkpp && (*linkpp)->user3()) {
                    UINFO(9, "clear   link " << nodep);
                    *linkpp = nullptr;
                    UINFO(9, "cleared link " << nodep);
                }
            });
        });
    }
    ~ParamTop() = default;
    VL_UNCOPYABLE(ParamTop);
};

//######################################################################
// Param class functions

void V3Param::param(AstNetlist* rootp) {
    UINFO(2, __FUNCTION__ << ":");

    // NEW ARCHITECTURE: DepGraph resolves EVERYTHING first, then V3Param runs ONCE
    //
    // Keep s_executing=true for the entire flow (build, resolve, finalizeAST, V3Param).
    // This prevents V3Width::iterateEditMoveDTypep from moving child dtypes to the
    // global type table. Without this, widthParamsEdit calls during V3Param cloning
    // would move BASICDTYPE children out of template VARs, causing cloneTree() to
    // produce clones with dangling dtypep() pointers to the deleted template nodes.
    V3LinkDotDepGraph::setExecuting(true);

    // Phase 1: Build complete dependency graph
    // This captures ALL cells, params, types, $bits() expressions
    UINFO(2, "DEPGRAPH: Phase 1 - Building complete dependency graph" << endl);
    V3LinkDotDepGraph::build(rootp);

    // Phase 2: Resolve all dependencies in topological order
    // This computes all constants by propagating through dependency chains
    UINFO(2, "DEPGRAPH: Phase 2 - Resolving all dependencies" << endl);
    const int depSteps = V3LinkDotDepGraph::resolve();
    UINFO(2, "DEPGRAPH: Resolved " << depSteps << " nodes" << endl);

    // Phase 3: Back-annotate resolved constants to AST
    // This replaces expressions like $bits(var) with their computed constant values
    UINFO(2, "DEPGRAPH: Phase 3 - Back-annotating constants to AST" << endl);
    V3LinkDotDepGraph::finalizeAST();

    // DepGraph flow complete - turn off execution flag so V3Param's
    // widthParamsEdit calls can move child dtypes to the type table normally.
    V3LinkDotDepGraph::setExecuting(false);

    // Phase 4: Run V3Param ONCE - it sees only constants, does simple cloning
    UINFO(2, "DEPGRAPH: Phase 4 - Running V3Param (single pass)" << endl);
    { ParamTop{rootp}; }

    V3Global::dumpCheckGlobalTree("param", 0, dumpTreeEitherLevel() >= 3);
}
