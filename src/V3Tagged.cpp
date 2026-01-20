// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Transform tagged union constructs
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
// V3Tagged's Transformations:
//
// Transform tagged union constructs into low-level bit operations:
//
// 1. AstTaggedExpr (tagged MemberName expr):
//    -> Combine tag bits with member value:
//       (tag_value << max_member_width) | (value & data_mask)
//
// 2. Case matches:
//    case (v) matches
//      tagged Invalid: stmt1
//      tagged Valid .n: stmt2
//    endcase
//    ->
//    { type_of_n n;
//      switch(VL_SEL(v, tag_lsb, tag_width)) {
//        case 0: stmt1; break;
//        case 1: n = VL_SEL(v, 0, member_width); stmt2; break;
//      }
//    }
//
// 3. If matches:
//    if (e matches tagged Valid .n) body
//    ->
//    { type_of_n n;
//      if (VL_SEL(e, tag_lsb, tag_width) == tag_value) {
//        n = VL_SEL(e, 0, member_width);
//        body
//      }
//    }
//
// 4. Member access on tagged union (v.MemberName):
//    -> Extract the data portion (runtime tag check would be added for safety)
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Tagged.h"

#include "V3MemberMap.h"
#include "V3Stats.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Tagged visitor

class TaggedVisitor final : public VNVisitor {
    // STATE
    AstNodeModule* m_modp = nullptr;  // Current module
    VDouble0 m_statTaggedExprs;  // Statistic tracking
    VDouble0 m_statTaggedMatches;  // Statistic tracking
    VMemberMap m_memberMap;  // Cache for O(1) member lookups
    std::map<std::string, AstVar*> m_modVarsByBaseName;  // Cache for O(1) module var lookups

    // METHODS

    // Extract base name from var name (part after last __DOT__ or full name)
    static std::string baseVarName(const std::string& name) {
        const size_t pos = name.rfind("__DOT__");
        if (pos != std::string::npos) return name.substr(pos + 7);  // 7 = strlen("__DOT__")
        return name;
    }

    // Check if a dtype is void
    bool isVoidDType(AstNodeDType* dtp) {
        dtp = dtp->skipRefp();
        return VN_IS(dtp, BasicDType)
               && VN_AS(dtp, BasicDType)->keyword() == VBasicDTypeKwd::CVOID;
    }

    // Check if a dtype is a dynamic type that can't be bit-packed
    // (real, shortreal, string, chandle, class, event)
    bool isDynamicDType(AstNodeDType* dtp) {
        dtp = dtp->skipRefp();
        if (AstBasicDType* const basicp = VN_CAST(dtp, BasicDType)) {
            if (basicp->keyword().isDynamicType()) return true;
        }
        // Class types are also dynamic
        if (VN_IS(dtp, ClassRefDType)) return true;
        return false;
    }

    // Check if union has any dynamic type members
    bool hasDynamicMember(AstUnionDType* unionp) {
        for (AstMemberDType* memberp = unionp->membersp(); memberp;
             memberp = VN_AS(memberp->nextp(), MemberDType)) {
            if (isDynamicDType(memberp->subDTypep())) return true;
        }
        return false;
    }

    // Check if variable name matches target (exact or mangled with __DOT__ prefix)
    static bool varNameMatches(const string& varpName, const string& varName,
                               const string& suffix) {
        if (varpName == varName) return true;
        if (varpName.size() > suffix.size()
            && varpName.substr(varpName.size() - suffix.size()) == suffix)
            return true;
        return false;
    }

    // Search a begin block for a variable by name
    static AstVar* findVarInBegin(AstBegin* beginp, const string& varName, const string& suffix) {
        for (AstNode* stmtp = beginp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            AstVar* const varp = VN_CAST(stmtp, Var);
            if (!varp) continue;
            if (varNameMatches(varp->name(), varName, suffix)) return varp;
        }
        return nullptr;
    }

    // Find AstVar by name in begin block or module containing the if statement
    AstVar* findPatternVar(AstIf* ifp, const string& varName) {
        // The variable may be in:
        // 1. A begin block that is a parent of the if (before V3Begin)
        // 2. The module scope (after V3Begin moves vars to module level)
        // Name may be mangled with scope prefix like "unnamedblk1__DOT__a"
        const string suffix = "__DOT__" + varName;
        for (AstNode* parentp = ifp->backp(); parentp; parentp = parentp->backp()) {
            if (AstBegin* const beginp = VN_CAST(parentp, Begin)) {
                if (AstVar* const varp = findVarInBegin(beginp, varName, suffix)) return varp;
            }
            // Stop at function or module boundary
            if (VN_IS(parentp, NodeFTask) || VN_IS(parentp, NodeModule)) break;
        }
        // Also search module-level vars (V3Begin moves vars from begin blocks to module)
        // Use cached map for O(1) lookup instead of O(n) iteration
        const auto it = m_modVarsByBaseName.find(varName);
        if (it != m_modVarsByBaseName.end()) return it->second;
        return nullptr;
    }

    // Replace all references to pattern variable with the new local variable
    void replacePatternVarRefsRecurse(AstNode* nodep, const string& patternVarName, AstVar* newVarp) {
        if (!nodep) return;
        // Check this node
        if (AstVarRef* const varRefp = VN_CAST(nodep, VarRef)) {
            // Match by base name (pattern variable name might be mangled with prefix)
            const string& refName = varRefp->varp()->name();
            // Check if the reference ends with __DOT__<patternVarName>
            // or if it's exactly the pattern variable name
            const string suffix = "__DOT__" + patternVarName;
            if (refName == patternVarName
                || (refName.size() > suffix.size()
                    && refName.substr(refName.size() - suffix.size()) == suffix)) {
                // Update the reference to point to the new variable
                varRefp->varp(newVarp);
                varRefp->name(newVarp->name());
            }
        }
        // Recurse into children
        if (nodep->op1p()) replacePatternVarRefsRecurse(nodep->op1p(), patternVarName, newVarp);
        if (nodep->op2p()) replacePatternVarRefsRecurse(nodep->op2p(), patternVarName, newVarp);
        if (nodep->op3p()) replacePatternVarRefsRecurse(nodep->op3p(), patternVarName, newVarp);
        if (nodep->op4p()) replacePatternVarRefsRecurse(nodep->op4p(), patternVarName, newVarp);
        // Recurse to siblings
        if (nodep->nextp()) replacePatternVarRefsRecurse(nodep->nextp(), patternVarName, newVarp);
    }

    // Create field extraction assignment: patternVar = structExpr.fieldName
    // Returns assignment node, or nullptr if pattern var not found (caller should skip)
    AstAssign* createFieldAssign(FileLine* fl, AstIf* ifp, AstNodeExpr* structExprp,
                                 bool isUnpacked, const string& fieldName,
                                 AstNodeDType* fieldDTypep, int fieldLsb, int fieldWidth,
                                 const string& varName) {
        AstNodeExpr* fieldExtractp;
        if (isUnpacked) {
            fieldExtractp = new AstStructSel{fl, structExprp, fieldName};
            fieldExtractp->dtypep(fieldDTypep);
        } else {
            fieldExtractp = new AstSel{fl, structExprp, fieldLsb, fieldWidth};
            fieldExtractp->dtypeSetBitSized(fieldWidth, VSigning::UNSIGNED);
        }
        AstVar* const varp = findPatternVar(ifp, varName);
        if (!varp) {
            VL_DO_DANGLING(fieldExtractp->deleteTree(), fieldExtractp);
            return nullptr;
        }
        AstVarRef* const varRefp = new AstVarRef{fl, varp, VAccess::WRITE};
        return new AstAssign{fl, varRefp, fieldExtractp};
    }

    // Create tag extraction from a packed tagged union value
    AstNodeExpr* makeTagExtract(FileLine* fl, AstNodeExpr* valuep, AstUnionDType* unionp) {
        const int tagLsb = unionp->maxMemberWidth();
        const int tagWidth = unionp->tagBitWidth();
        return new AstSel{fl, valuep, tagLsb, tagWidth};
    }

    // Create data extraction from a packed tagged union value
    AstNodeExpr* makeDataExtract(FileLine* fl, AstNodeExpr* valuep, AstUnionDType* unionp,
                                 int memberWidth) {
        if (memberWidth == 0) return nullptr;  // Void member
        return new AstSel{fl, valuep, 0, memberWidth};
    }

    // Create tag extraction from an unpacked tagged union value (struct field access)
    AstNodeExpr* makeTagExtractUnpacked(FileLine* fl, AstNodeExpr* valuep) {
        AstStructSel* const selp = new AstStructSel{fl, valuep, "__Vtag"};
        selp->dtypeSetBitSized(32, VSigning::UNSIGNED);
        return selp;
    }

    // Create data extraction from an unpacked tagged union value (struct field access)
    AstNodeExpr* makeDataExtractUnpacked(FileLine* fl, AstNodeExpr* valuep,
                                         const string& memberName, AstNodeDType* memberDtp) {
        AstStructSel* const selp = new AstStructSel{fl, valuep, memberName};
        selp->dtypep(memberDtp);
        return selp;
    }

    // Extract member data from tagged union value (handles both packed and unpacked)
    // If dtypep is provided, sets it on the result; otherwise uses dtypeSetBitSized for packed
    AstNodeExpr* extractMemberData(FileLine* fl, AstNodeExpr* valuep, AstUnionDType* unionp,
                                   AstMemberDType* memberp, bool isUnpacked,
                                   AstNodeDType* dtypep = nullptr) {
        if (isUnpacked) {
            return makeDataExtractUnpacked(fl, valuep, memberp->name(), memberp->subDTypep());
        }
        AstNodeExpr* const datap = makeDataExtract(fl, valuep, unionp, memberp->width());
        if (!datap) return nullptr;
        if (dtypep) {
            datap->dtypep(dtypep);
        } else {
            datap->dtypeSetBitSized(memberp->width(), VSigning::UNSIGNED);
        }
        return datap;
    }

    // Process ConsPackMember list and create field assignments for pattern variables
    // Returns list of assignments (may be nullptr)
    AstNode* processConsPackMembers(FileLine* fl, AstIf* ifp, AstNodeExpr* dataExtractp,
                                    AstConsPackMember* membersp, bool isUnpacked) {
        AstNode* assignsp = nullptr;
        for (AstConsPackMember* cpm = membersp; cpm; cpm = VN_CAST(cpm->nextp(), ConsPackMember)) {
            // Find PatternVar inside (may be inside Extend)
            AstNode* valuep = cpm->rhsp();
            while (AstExtend* const extp = VN_CAST(valuep, Extend)) valuep = extp->lhsp();
            AstPatternVar* const patVarp = VN_CAST(valuep, PatternVar);
            if (!patVarp) continue;
            AstMemberDType* const fieldDtp = VN_CAST(cpm->dtypep(), MemberDType);
            if (!fieldDtp) continue;
            AstAssign* const assignp = createFieldAssign(
                fl, ifp, dataExtractp->cloneTree(false), isUnpacked, fieldDtp->name(),
                fieldDtp->subDTypep(), fieldDtp->lsb(), fieldDtp->width(), patVarp->name());
            if (assignp) assignsp = AstNode::addNext<AstNode, AstNode>(assignsp, assignp);
        }
        return assignsp;
    }

    // Process PatMember list and create field assignments for pattern variables
    // Returns list of assignments (may be nullptr)
    AstNode* processPatMembers(FileLine* fl, AstIf* ifp, AstNodeExpr* dataExtractp,
                               AstNodeUOrStructDType* structDtp, AstPatMember* membersp,
                               bool isUnpacked,
                               const std::map<string, std::pair<int, int>>* fieldInfo = nullptr) {
        AstNode* assignsp = nullptr;
        for (AstPatMember* patMemp = membersp; patMemp;
             patMemp = VN_CAST(patMemp->nextp(), PatMember)) {
            AstPatternVar* const patVarp = VN_CAST(patMemp->lhssp(), PatternVar);
            if (!patVarp) continue;
            const AstText* const keyTextp = VN_CAST(patMemp->keyp(), Text);
            if (!keyTextp) continue;
            AstMemberDType* const fieldp
                = VN_CAST(m_memberMap.findMember(structDtp, keyTextp->text()), MemberDType);
            if (!fieldp) continue;
            // Use fieldInfo if provided (for anonymous structs), otherwise use fieldp directly
            const int fieldLsb = fieldInfo ? (*fieldInfo).at(fieldp->name()).first : fieldp->lsb();
            const int fieldWidth
                = fieldInfo ? (*fieldInfo).at(fieldp->name()).second : fieldp->width();
            AstAssign* const assignp
                = createFieldAssign(fl, ifp, dataExtractp->cloneTree(false), isUnpacked,
                                    fieldp->name(), fieldp->subDTypep(), fieldLsb, fieldWidth,
                                    patVarp->name());
            if (assignp) assignsp = AstNode::addNext<AstNode, AstNode>(assignsp, assignp);
        }
        return assignsp;
    }

    // Handle TaggedExpr with ConsPackUOrStruct pattern
    // Returns assignments for pattern variables (may be nullptr)
    AstNode* handleConsPackStructPattern(FileLine* fl, AstIf* ifp, AstNodeExpr* exprp,
                                         AstUnionDType* unionp, AstMemberDType* memberp,
                                         AstConsPackUOrStruct* structp, bool isUnpacked) {
        AstNodeDType* const memberDtp = memberp->subDTypep()->skipRefp();
        AstNodeUOrStructDType* const structDtp = VN_CAST(memberDtp, NodeUOrStructDType);
        if (!structDtp) return nullptr;
        AstNodeExpr* const dataExtractp
            = extractMemberData(fl, exprp->cloneTree(false), unionp, memberp, isUnpacked, structDtp);
        AstNode* const assignsp
            = processConsPackMembers(fl, ifp, dataExtractp, structp->membersp(), isUnpacked);
        if (dataExtractp) VL_DO_DANGLING(dataExtractp->deleteTree(), dataExtractp);
        return assignsp;
    }

    // Handle struct pattern inside TaggedPattern (e.g., tagged Member '{field:.var, ...})
    // Returns assignments for pattern variables (may be nullptr)
    AstNode* handleTaggedStructPattern(FileLine* fl, AstIf* ifp, AstNodeExpr* exprp,
                                       AstUnionDType* unionp, AstMemberDType* memberp,
                                       AstPattern* structPatp, bool isUnpacked) {
        AstNodeDType* const memberDtp = memberp->subDTypep()->skipRefp();
        AstNodeUOrStructDType* const structDtp = VN_CAST(memberDtp, NodeUOrStructDType);
        if (!structDtp) return nullptr;
        AstNodeExpr* const dataExtractp
            = extractMemberData(fl, exprp->cloneTree(false), unionp, memberp, isUnpacked, structDtp);
        AstNode* const assignsp = processPatMembers(fl, ifp, dataExtractp, structDtp,
                                                    VN_CAST(structPatp->itemsp(), PatMember),
                                                    isUnpacked, nullptr);
        if (dataExtractp) VL_DO_DANGLING(dataExtractp->deleteTree(), dataExtractp);
        return assignsp;
    }

    // Handle TaggedExpr with Pattern (anonymous struct) pattern
    // Returns assignments for pattern variables (may be nullptr)
    AstNode* handleAnonStructPattern(FileLine* fl, AstIf* ifp, AstNodeExpr* exprp,
                                     AstUnionDType* unionp, AstMemberDType* memberp,
                                     const string& memberName, AstPattern* patternp,
                                     bool isUnpacked) {
        AstNodeDType* const memberDtp = memberp->subDTypep()->skipRefp();
        AstNodeUOrStructDType* const structDtp = VN_CAST(memberDtp, NodeUOrStructDType);
        if (!structDtp) return nullptr;

        // For anonymous structs, compute field LSBs from member definitions
        std::map<string, std::pair<int, int>> fieldInfo;  // name -> (lsb, width)
        int bitOffset = 0;
        std::vector<std::pair<string, int>> fieldOrder;
        for (AstMemberDType* mp = structDtp->membersp(); mp;
             mp = VN_AS(mp->nextp(), MemberDType)) {
            fieldOrder.emplace_back(mp->name(), mp->width());
        }
        for (auto it = fieldOrder.rbegin(); it != fieldOrder.rend(); ++it) {
            fieldInfo[it->first] = std::make_pair(bitOffset, it->second);
            bitOffset += it->second;
        }
        const int structWidth = bitOffset;

        // Extract the struct
        AstNodeExpr* dataExtractp;
        if (isUnpacked) {
            dataExtractp
                = makeDataExtractUnpacked(fl, exprp->cloneTree(false), memberName, memberp->subDTypep());
        } else {
            dataExtractp = makeDataExtract(fl, exprp->cloneTree(false), unionp, structWidth);
            if (dataExtractp) dataExtractp->dtypep(structDtp);
        }

        AstNode* const assignsp = processPatMembers(
            fl, ifp, dataExtractp, structDtp, VN_CAST(patternp->itemsp(), PatMember), isUnpacked,
            &fieldInfo);
        if (dataExtractp) VL_DO_DANGLING(dataExtractp->deleteTree(), dataExtractp);
        return assignsp;
    }

    // Create pattern variable binding for case matches
    // Creates a local variable and assignment for a pattern variable in a case item
    // Returns the created variable (for varDeclsp), and modifies stmtsp to prepend assignment
    AstVar* createCasePatternBinding(AstNode* innerPatternp, bool isVoid, AstMemberDType* memberp,
                                     AstNode* condp, FileLine* fl, bool isUnpacked,
                                     AstUnionDType* unionp, AstVar* tempVarp,
                                     AstNode*& stmtsp /*modified*/) {
        if (!innerPatternp || VN_IS(innerPatternp, PatternStar)) return nullptr;
        AstPatternVar* const patVarp = VN_CAST(innerPatternp, PatternVar);
        if (!patVarp || isVoid) return nullptr;

        const string& varName = patVarp->name();
        const int memberWidth = memberp->width();

        // Create local variable
        // For unpacked: use actual member dtype
        // For packed: use bit-packed type
        AstVar* varp;
        if (isUnpacked) {
            varp = new AstVar{condp->fileline(), VVarType::BLOCKTEMP, varName, memberp->subDTypep()};
        } else {
            varp = new AstVar{condp->fileline(), VVarType::BLOCKTEMP, varName, VFlagBitPacked{},
                              memberWidth};
        }
        varp->funcLocal(true);

        // Create assignment: var = temp_expr.MemberName or temp_expr[0+:memberWidth]
        AstVarRef* const tempVarRd2p = new AstVarRef{fl, tempVarp, VAccess::READ};
        AstNodeExpr* const dataExtractp
            = extractMemberData(fl, tempVarRd2p, unionp, memberp, isUnpacked);
        if (!dataExtractp) return varp;  // Variable created but no assignment needed

        AstVarRef* const varRefp = new AstVarRef{condp->fileline(), varp, VAccess::WRITE};
        AstAssign* const assignp = new AstAssign{fl, varRefp, dataExtractp};

        // Replace pattern variable references in cloned statements
        if (stmtsp) {
            replacePatternVarRefsRecurse(stmtsp, varName, varp);
            AstNode::addNext<AstNode, AstNode>(assignp, stmtsp);
        }
        stmtsp = assignp;
        return varp;
    }

    // Transform: tagged MemberName [expr]
    // Into: (tag << max_member_width) | (expr & ((1 << member_width) - 1))
    AstNodeExpr* transformTaggedExpr(AstTaggedExpr* nodep, AstUnionDType* unionp) {
        FileLine* const fl = nodep->fileline();
        AstMemberDType* const memberp
            = VN_CAST(m_memberMap.findMember(unionp, nodep->name()), MemberDType);
        UASSERT_OBJ(memberp, nodep, "Member not found in tagged union");

        const int tagIndex = memberp->tagIndex();
        const int maxMemberWidth = unionp->maxMemberWidth();
        const int totalWidth = unionp->taggedTotalWidth();

        // Create the tag value positioned at MSB
        // tag_value << max_member_width
        AstNodeExpr* tagValp
            = new AstConst{fl, AstConst::WidthedValue{}, totalWidth, static_cast<uint32_t>(tagIndex)};
        if (maxMemberWidth > 0) {
            tagValp = new AstShiftL{
                fl, tagValp,
                new AstConst{fl, AstConst::WidthedValue{}, 32, static_cast<uint32_t>(maxMemberWidth)}};
            tagValp->dtypeSetBitSized(totalWidth, VSigning::UNSIGNED);
        }

        // Handle member value
        const bool isVoid = isVoidDType(memberp->subDTypep());
        if (isVoid || !nodep->exprp()) {
            // Void member or no expression - just return tag value
            tagValp->dtypep(unionp);
            return tagValp;
        }

        // Get member expression and extend/truncate to maxMemberWidth
        AstNodeExpr* valuep = nodep->exprp()->unlinkFrBack();
        const int memberWidth = memberp->width();

        // Extend value to maxMemberWidth if needed
        if (memberWidth < maxMemberWidth) {
            valuep = new AstExtend{fl, valuep, maxMemberWidth};
            valuep->dtypeSetBitSized(maxMemberWidth, VSigning::UNSIGNED);
        } else if (memberWidth > maxMemberWidth) {
            // Truncate - shouldn't happen but handle defensively
            valuep = new AstSel{fl, valuep, 0, maxMemberWidth};
            valuep->dtypeSetBitSized(maxMemberWidth, VSigning::UNSIGNED);
        }

        // Extend value to total width for OR operation
        if (maxMemberWidth < totalWidth) {
            valuep = new AstExtend{fl, valuep, totalWidth};
            valuep->dtypeSetBitSized(totalWidth, VSigning::UNSIGNED);
        }

        // Combine: tag | value
        AstNodeExpr* resultp = new AstOr{fl, tagValp, valuep};
        resultp->dtypep(unionp);

        return resultp;
    }

    // Transform pattern variable binding into a local variable declaration
    // Returns the variable that was created
    AstVar* createPatternVarBinding(FileLine* fl, const string& varName, AstNodeDType* dtypep,
                                    AstNode* stmtsp) {
        // Create a local variable for the pattern variable
        AstVar* const varp = new AstVar{fl, VVarType::BLOCKTEMP, varName, dtypep};
        varp->funcLocal(true);
        return varp;
    }

    // Transform: if (expr matches tagged MemberName .var) body
    // Into: { type var; if ((expr >> maxMemberW) == tagVal) { var = expr[0 +: memberW]; body } }
    void transformIfMatches(AstIf* ifp, AstMatches* matchesp) {
        FileLine* const fl = matchesp->fileline();

        // Get the expression being matched
        AstNodeExpr* const exprp = matchesp->lhsp();

        // Get the union type - try pattern first (TaggedExpr/TaggedPattern have union dtype),
        // then fall back to LHS expression's dtype
        AstNode* const patternp = matchesp->patternp();
        AstUnionDType* unionp = nullptr;
        if (VN_IS(patternp, TaggedPattern) || VN_IS(patternp, TaggedExpr)) {
            if (patternp->dtypep()) {
                unionp = VN_CAST(patternp->dtypep()->skipRefp(), UnionDType);
            }
        }
        if (!unionp) {
            AstNodeDType* const exprDtp = exprp->dtypep()->skipRefp();
            unionp = VN_CAST(exprDtp, UnionDType);
        }

        if (!unionp || !unionp->isTagged()) {
            matchesp->v3error("Matches expression must be a tagged union type");
            return;
        }

        // Get the pattern - can be either AstTaggedPattern (with binding) or AstTaggedExpr (no
        // binding)
        AstTaggedPattern* const tagPatternp = VN_CAST(matchesp->patternp(), TaggedPattern);
        AstTaggedExpr* const tagExprp = VN_CAST(matchesp->patternp(), TaggedExpr);
        if (!tagPatternp && !tagExprp) {
            matchesp->v3error("Expected tagged pattern in matches expression");
            return;
        }

        const string& memberName = tagPatternp ? tagPatternp->name() : tagExprp->name();
        AstMemberDType* const memberp
            = VN_CAST(m_memberMap.findMember(unionp, memberName), MemberDType);
        if (!memberp) {
            matchesp->v3error("Tagged union member " << AstNode::prettyNameQ(memberName)
                                                     << " not found");
            return;
        }

        const int tagIndex = memberp->tagIndex();
        const int tagWidth = unionp->tagBitWidth();
        const bool isVoid = isVoidDType(memberp->subDTypep());
        const bool isUnpacked = !unionp->packed();

        // Create tag comparison
        // For packed: (expr >> maxMemberWidth) == tagIndex
        // For unpacked: expr.__Vtag == tagIndex
        AstNodeExpr* const exprClonep = exprp->cloneTree(false);
        AstNodeExpr* tagExtractp;
        AstNodeExpr* tagConstp;
        if (isUnpacked) {
            tagExtractp = makeTagExtractUnpacked(fl, exprClonep);
            tagConstp = new AstConst{fl, AstConst::WidthedValue{}, 32, static_cast<uint32_t>(tagIndex)};
        } else {
            tagExtractp = makeTagExtract(fl, exprClonep, unionp);
            tagConstp
                = new AstConst{fl, AstConst::WidthedValue{}, tagWidth, static_cast<uint32_t>(tagIndex)};
        }
        AstNodeExpr* condp = new AstEq{fl, tagExtractp, tagConstp};
        condp->dtypeSetBit();

        // Handle pattern variable binding (only if we have an AstTaggedPattern with inner pattern)
        AstNode* varDeclsp = nullptr;
        AstNode* varAssignsp = nullptr;

        AstNode* const innerPatternp = tagPatternp ? tagPatternp->patternp() : nullptr;
        if (innerPatternp && !VN_IS(innerPatternp, PatternStar)) {
            AstPatternVar* const patVarp = VN_CAST(innerPatternp, PatternVar);
            if (patVarp && !isVoid) {
                const string& varName = patVarp->name();
                const int memberWidth = memberp->width();

                // Create local variable
                // For unpacked: use actual member dtype
                // For packed: use bit-packed type
                AstVar* varp;
                if (isUnpacked) {
                    // Use direct dtype - V3Width has already run so VFlagChildDType won't work
                    varp = new AstVar{fl, VVarType::BLOCKTEMP, varName, memberp->subDTypep()};
                } else {
                    varp = new AstVar{fl, VVarType::BLOCKTEMP, varName, VFlagBitPacked{},
                                      memberWidth};
                }
                varp->funcLocal(true);
                varDeclsp = varp;

                // Create assignment: var = expr.MemberName (unpacked) or expr[0+:memberWidth] (packed)
                AstNodeExpr* const dataExtractp
                    = extractMemberData(fl, exprp->cloneTree(false), unionp, memberp, isUnpacked);
                if (dataExtractp) {
                    AstVarRef* const varRefp = new AstVarRef{fl, varp, VAccess::WRITE};
                    AstAssign* const assignp = new AstAssign{fl, varRefp, dataExtractp};
                    varAssignsp = assignp;
                }
            }
            // Handle struct pattern inside TaggedPattern: tagged Member '{field:.var, ...}
            else if (AstPattern* const structPatp = VN_CAST(innerPatternp, Pattern)) {
                if (AstNode* const assigns = handleTaggedStructPattern(
                        fl, ifp, exprp, unionp, memberp, structPatp, isUnpacked)) {
                    varAssignsp = AstNode::addNext<AstNode, AstNode>(varAssignsp, assigns);
                }
            }
        }

        // Handle TaggedExpr with struct pattern containing pattern variables
        if (tagExprp && !isVoid) {
            if (AstConsPackUOrStruct* const structp = VN_CAST(tagExprp->exprp(), ConsPackUOrStruct)) {
                if (AstNode* const assigns = handleConsPackStructPattern(
                        fl, ifp, exprp, unionp, memberp, structp, isUnpacked)) {
                    varAssignsp = AstNode::addNext<AstNode, AstNode>(varAssignsp, assigns);
                }
            } else if (AstPattern* const patternp = VN_CAST(tagExprp->exprp(), Pattern)) {
                if (AstNode* const assigns = handleAnonStructPattern(
                        fl, ifp, exprp, unionp, memberp, memberName, patternp, isUnpacked)) {
                    varAssignsp = AstNode::addNext<AstNode, AstNode>(varAssignsp, assigns);
                }
            }
        }

        // Get guard expression if present (&&& expr) BEFORE deleting matchesp
        AstNodeExpr* guardp = matchesp->guardp();
        if (guardp) guardp = guardp->unlinkFrBack();

        // Replace the condition (deletes matchesp)
        if (AstNodeExpr* oldCondp = matchesp->unlinkFrBack()) {
            VL_DO_DANGLING(oldCondp->deleteTree(), oldCondp);
        }

        // Add variable declaration and assignment
        if (varDeclsp) {
            // Wrap in a C++ local scope for the pattern variable
            AstNode* const origBodyp
                = ifp->thensp() ? ifp->thensp()->unlinkFrBackWithNext() : nullptr;
            AstCLocalScope* const scopep = new AstCLocalScope{fl, nullptr};

            // Add variable declaration
            AstVar* const varp = VN_AS(varDeclsp, Var);
            scopep->addStmtsp(varDeclsp);

            // Replace pattern variable references in original body
            if (origBodyp && varp) replacePatternVarRefsRecurse(origBodyp, varp->name(), varp);

            // If there's a guard with pattern variable, update references in the guard
            // guardp is already unlinked, no need to clone
            if (guardp && varp) replacePatternVarRefsRecurse(guardp, varp->name(), varp);

            // Build the body
            // If guard present: assignment + if(guard) { original body }
            // If no guard: assignment + original body
            AstNode* innerBodyp;
            if (guardp) {
                // Create inner if for guard
                AstIf* const guardIfp = new AstIf{fl, guardp, origBodyp, nullptr};
                innerBodyp = AstNode::addNext<AstNode, AstNode>(varAssignsp, guardIfp);
            } else {
                innerBodyp = AstNode::addNext<AstNode, AstNode>(varAssignsp, origBodyp);
            }

            // Create new if statement with tag condition
            AstIf* const newIfp = new AstIf{fl, condp, innerBodyp, nullptr};

            // Replace original if with local scope containing var + new if
            scopep->addStmtsp(newIfp);
            ifp->replaceWith(scopep);
            VL_DO_DANGLING(pushDeletep(ifp), ifp);
            // Iterate the new structure to transform any nested matches expressions
            // (e.g., guard expression that is itself a matches expression)
            iterate(scopep);
        } else if (varAssignsp) {
            // Have assignments but no new variable declarations (struct pattern case)
            // Variables were already declared by V3LinkParse in parent begin block
            AstNode* origBodyp = ifp->thensp() ? ifp->thensp()->unlinkFrBackWithNext() : nullptr;
            AstNode* origElsep = ifp->elsesp() ? ifp->elsesp()->unlinkFrBackWithNext() : nullptr;

            // Build the body: assignments + original body
            AstNode* newBodyp = varAssignsp;
            if (origBodyp) newBodyp->addNext(origBodyp);

            // Handle guard if present
            if (guardp) {
                // Create inner if for guard
                AstIf* const guardIfp = new AstIf{fl, guardp, newBodyp, nullptr};
                newBodyp = guardIfp;
            }

            // Create new if with tag condition
            AstIf* const newIfp = new AstIf{fl, condp, newBodyp, origElsep};
            ifp->replaceWith(newIfp);
            VL_DO_DANGLING(pushDeletep(ifp), ifp);
            iterate(newIfp);
        } else if (guardp) {
            // No pattern variable but have guard - AND the conditions
            // guardp is already unlinked, use directly
            AstLogAnd* const combinedCondp = new AstLogAnd{fl, condp, guardp};
            combinedCondp->dtypeSetBit();
            ifp->condp(combinedCondp);
            // Iterate the modified if to transform any nested matches in guard
            iterate(ifp);
        } else {
            // No pattern variable, no guard - just use tag condition
            ifp->condp(condp);
            // Iterate in case there are matches expressions in the body
            iterate(ifp);
        }

        ++m_statTaggedMatches;
    }

    // Transform case matches statements
    void transformCaseMatches(AstCase* casep) {
        FileLine* const fl = casep->fileline();

        // Get the expression being matched
        AstNodeExpr* const exprp = casep->exprp();
        AstNodeDType* const exprDtp = exprp->dtypep()->skipRefp();
        AstUnionDType* const unionp = VN_CAST(exprDtp, UnionDType);

        if (!unionp || !unionp->isTagged()) {
            casep->v3error("Case matches expression must be a tagged union type");
            return;
        }

        const int tagWidth = unionp->tagBitWidth();
        const bool isUnpacked = !unionp->packed();

        // Create a variable to hold the expression (evaluate once)
        // For packed: use bit-packed variable
        // For unpacked: use the union dtype
        AstVar* tempVarp;
        if (isUnpacked) {
            // Use direct dtype - V3Width has already run so VFlagChildDType won't work
            tempVarp = new AstVar{fl, VVarType::BLOCKTEMP, "__Vtagged_expr", unionp};
        } else {
            const int totalWidth = unionp->taggedTotalWidth();
            tempVarp = new AstVar{fl, VVarType::BLOCKTEMP, "__Vtagged_expr", VFlagBitPacked{},
                                  totalWidth};
        }
        tempVarp->funcLocal(true);

        // Assign expression to temp variable
        AstVarRef* const tempVarWrp = new AstVarRef{fl, tempVarp, VAccess::WRITE};
        AstAssign* const tempAssignp = new AstAssign{fl, tempVarWrp, exprp->cloneTree(false)};

        // Create tag extraction expression
        AstVarRef* const tempVarRd1p = new AstVarRef{fl, tempVarp, VAccess::READ};
        AstNodeExpr* tagExprp;
        if (isUnpacked) {
            tagExprp = makeTagExtractUnpacked(fl, tempVarRd1p);
        } else {
            tagExprp = makeTagExtract(fl, tempVarRd1p, unionp);
        }

        // Process each case item and convert to regular case
        AstNode* newCaseItemsp = nullptr;
        AstNode* varDeclsp = nullptr;

        for (AstCaseItem* itemp = casep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {
            if (itemp->isDefault()) {
                // Default case - just keep as is
                AstCaseItem* const newItemp = new AstCaseItem{
                    itemp->fileline(), nullptr,
                    itemp->stmtsp() ? itemp->stmtsp()->cloneTree(true) : nullptr};
                newCaseItemsp = AstNode::addNext<AstNode, AstNode>(newCaseItemsp, newItemp);
                continue;
            }

            // Process tagged patterns (AstTaggedPattern or AstTaggedExpr)
            for (AstNode* condp = itemp->condsp(); condp; condp = condp->nextp()) {
                AstTaggedPattern* const tagPatternp = VN_CAST(condp, TaggedPattern);
                AstTaggedExpr* const tagExprCondp = VN_CAST(condp, TaggedExpr);
                if (!tagPatternp && !tagExprCondp) continue;

                const string& memberName
                    = tagPatternp ? tagPatternp->name() : tagExprCondp->name();
                AstMemberDType* const memberp
                    = VN_CAST(m_memberMap.findMember(unionp, memberName), MemberDType);
                if (!memberp) {
                    condp->v3error("Tagged union member " << AstNode::prettyNameQ(memberName)
                                                         << " not found");
                    continue;
                }

                const int tagIndex = memberp->tagIndex();
                const bool isVoid = isVoidDType(memberp->subDTypep());

                // Create case condition: tagIndex as constant
                // For unpacked: use 32-bit constant
                // For packed: use tag width
                AstConst* tagConstp;
                if (isUnpacked) {
                    tagConstp = new AstConst{itemp->fileline(), AstConst::WidthedValue{}, 32,
                                             static_cast<uint32_t>(tagIndex)};
                } else {
                    tagConstp = new AstConst{itemp->fileline(), AstConst::WidthedValue{}, tagWidth,
                                             static_cast<uint32_t>(tagIndex)};
                }

                // Handle pattern variable binding (only for AstTaggedPattern with inner pattern)
                AstNode* stmtsp = itemp->stmtsp() ? itemp->stmtsp()->cloneTree(true) : nullptr;
                AstNode* const innerPatternp = tagPatternp ? tagPatternp->patternp() : nullptr;
                AstVar* const newVarp = createCasePatternBinding(innerPatternp, isVoid, memberp,
                                                                 condp, fl, isUnpacked, unionp,
                                                                 tempVarp, stmtsp);
                if (newVarp) varDeclsp = AstNode::addNext<AstNode, AstNode>(varDeclsp, newVarp);

                // Create new case item
                AstCaseItem* const newItemp
                    = new AstCaseItem{itemp->fileline(), tagConstp, stmtsp};
                newCaseItemsp = AstNode::addNext<AstNode, AstNode>(newCaseItemsp, newItemp);
            }
        }

        // Create new case statement with tag extraction as expression
        AstCase* const newCasep
            = new AstCase{fl, VCaseType::CT_CASE, tagExprp, VN_AS(newCaseItemsp, CaseItem)};

        // Create C++ local scope with variable declarations, temp assign, and case
        AstCLocalScope* const scopep = new AstCLocalScope{fl, nullptr};
        scopep->addStmtsp(tempVarp);
        if (varDeclsp) scopep->addStmtsp(varDeclsp);
        scopep->addStmtsp(tempAssignp);
        scopep->addStmtsp(newCasep);

        // Replace original case
        casep->replaceWith(scopep);
        VL_DO_DANGLING(pushDeletep(casep), casep);

        ++m_statTaggedMatches;
    }

    // Transform: target = tagged MemberName (value)
    // For unpacked tagged unions, transforms into:
    //   target.__Vtag = tagIndex;
    //   target.MemberName = value;  // if not void
    void transformTaggedExprUnpacked(AstAssign* assignp, AstTaggedExpr* taggedp,
                                     AstUnionDType* unionp) {
        FileLine* const fl = taggedp->fileline();
        AstMemberDType* const memberp
            = VN_CAST(m_memberMap.findMember(unionp, taggedp->name()), MemberDType);
        UASSERT_OBJ(memberp, taggedp, "Member not found in tagged union");

        const int tagIndex = memberp->tagIndex();
        const bool isVoid = isVoidDType(memberp->subDTypep());

        // Get the target (LHS of assignment) and clone it
        AstNodeExpr* const targetp = assignp->lhsp();

        // Create: target.__Vtag = tagIndex
        AstStructSel* const tagSelp = new AstStructSel{fl, targetp->cloneTree(false), "__Vtag"};
        tagSelp->dtypeSetBitSized(32, VSigning::UNSIGNED);
        AstAssign* const tagAssignp = new AstAssign{
            fl, tagSelp, new AstConst{fl, AstConst::WidthedValue{}, 32, static_cast<uint32_t>(tagIndex)}};

        // Replace the original assignment with tag assignment
        assignp->replaceWith(tagAssignp);

        // If member is not void, add member assignment after tag assignment
        if (!isVoid && taggedp->exprp()) {
            AstStructSel* const memberSelp
                = new AstStructSel{fl, targetp->cloneTree(false), taggedp->name()};
            memberSelp->dtypep(memberp->subDTypep());
            // Clone the value expression to avoid dtype reference issues when original tree is
            // deleted
            AstNodeExpr* valuep = taggedp->exprp()->cloneTree(false);
            AstAssign* const memberAssignp = new AstAssign{fl, memberSelp, valuep};
            tagAssignp->addNextHere(memberAssignp);
        }

        VL_DO_DANGLING(pushDeletep(assignp), assignp);
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        m_modp = nodep;
        // Build cache of module-level vars for O(1) lookup in findPatternVar()
        const std::map<std::string, AstVar*> prevModVars = std::move(m_modVarsByBaseName);
        m_modVarsByBaseName.clear();
        for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                const std::string baseName = baseVarName(varp->name());
                // Only store first var with this base name (matches original behavior)
                if (m_modVarsByBaseName.find(baseName) == m_modVarsByBaseName.end()) {
                    m_modVarsByBaseName[baseName] = varp;
                }
            }
        }
        iterateChildren(nodep);
        m_modVarsByBaseName = std::move(prevModVars);
    }
    void visit(AstTaggedExpr* nodep) override {
        // Don't iterate children - we handle exprp directly in the transform
        // iterateChildren(nodep);

        // Skip transformation if this TaggedExpr is used as a pattern in a Matches expression
        // In that case, transformIfMatches() will handle it
        if (AstMatches* const matchesp = VN_CAST(nodep->backp(), Matches)) {
            if (matchesp->patternp() == nodep) {
                // This is a pattern, not an expression to be transformed
                // transformIfMatches() will handle it when processing the parent If
                return;
            }
        }

        // Get the union type from the expression's dtype
        AstNodeDType* const dtypep = nodep->dtypep();
        // V3Width should catch missing dtype first
        UASSERT_OBJ(dtypep, nodep, "Tagged expression without type context");
        AstUnionDType* const unionp = VN_CAST(dtypep->skipRefp(), UnionDType);
        // V3Width should catch non-tagged-union type first
        UASSERT_OBJ(unionp && unionp->isTagged(), nodep,
                    "Tagged expression used with non-tagged-union type");

        // For unpacked tagged unions, handle at assignment level
        // This includes explicitly unpacked unions and those with dynamic/array members
        if (!unionp->packed()) {
            // Find parent assignment
            AstAssign* assignp = VN_CAST(nodep->backp(), Assign);
            if (assignp && assignp->rhsp() == nodep) {
                transformTaggedExprUnpacked(assignp, nodep, unionp);
                ++m_statTaggedExprs;
                return;
            }
            // If not in simple assignment context, this is more complex
            // For now, emit an error for unsupported contexts
            nodep->v3warn(E_UNSUPPORTED, "Tagged expression in non-simple assignment context");
            return;
        }

        // Transform tagged union expression (packed unions - use bit operations)
        AstNodeExpr* const newp = transformTaggedExpr(nodep, unionp);
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);

        ++m_statTaggedExprs;
    }

    void visit(AstIf* nodep) override {
        // Check if this is an if with matches condition - let transformIfMatches validate the type
        if (AstMatches* const matchesp = VN_CAST(nodep->condp(), Matches)) {
            transformIfMatches(nodep, matchesp);
            return;
        }
        iterateChildren(nodep);
    }

    void visit(AstCase* nodep) override {
        // Check if this is a case matches - let transformCaseMatches validate the type
        if (nodep->caseMatches()) {
            transformCaseMatches(nodep);
            return;
        }
        iterateChildren(nodep);
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit TaggedVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~TaggedVisitor() override {
        V3Stats::addStat("Tagged, expressions transformed", m_statTaggedExprs);
        V3Stats::addStat("Tagged, matches transformed", m_statTaggedMatches);
    }
};

//######################################################################
// Tagged class functions

void V3Tagged::taggedAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { TaggedVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("tagged", 0, dumpTreeEitherLevel() >= 3);
}
