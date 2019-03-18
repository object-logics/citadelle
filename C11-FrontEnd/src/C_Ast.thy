(******************************************************************************
 * Generation of Language.C Grammar with ML Interface Binding
 *
 * Copyright (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)

theory C_Ast
  imports Main
begin

ML_file \<open>../generated/Ast_C.ML\<close>

ML\<open>
structure C_ast_simple = struct
  open C_ast_simple
  val Ident = Ident0
end
\<close>

section \<open>Language.C Haskell parsing in ML\<close>

ML \<open>val Position = C_ast_simple.position val NoPosition = C_ast_simple.noPosition val BuiltinPosition = C_ast_simple.builtinPosition val InternalPosition = C_ast_simple.internalPosition val Name = C_ast_simple.name val OnlyPos = C_ast_simple.onlyPos val NodeInfo = C_ast_simple.nodeInfo val AnonymousRef = C_ast_simple.anonymousRef val NamedRef = C_ast_simple.namedRef val CChar = C_ast_simple.cChar val CChars = C_ast_simple.cChars val DecRepr = C_ast_simple.decRepr val HexRepr = C_ast_simple.hexRepr val OctalRepr = C_ast_simple.octalRepr val FlagUnsigned = C_ast_simple.flagUnsigned val FlagLong = C_ast_simple.flagLong val FlagLongLong = C_ast_simple.flagLongLong val FlagImag = C_ast_simple.flagImag val CFloat = C_ast_simple.cFloat val Flags = C_ast_simple.flags val CInteger = C_ast_simple.cInteger val CAssignOp = C_ast_simple.cAssignOp val CMulAssOp = C_ast_simple.cMulAssOp val CDivAssOp = C_ast_simple.cDivAssOp val CRmdAssOp = C_ast_simple.cRmdAssOp val CAddAssOp = C_ast_simple.cAddAssOp val CSubAssOp = C_ast_simple.cSubAssOp val CShlAssOp = C_ast_simple.cShlAssOp val CShrAssOp = C_ast_simple.cShrAssOp val CAndAssOp = C_ast_simple.cAndAssOp val CXorAssOp = C_ast_simple.cXorAssOp val COrAssOp = C_ast_simple.cOrAssOp val CMulOp = C_ast_simple.cMulOp val CDivOp = C_ast_simple.cDivOp val CRmdOp = C_ast_simple.cRmdOp val CAddOp = C_ast_simple.cAddOp val CSubOp = C_ast_simple.cSubOp val CShlOp = C_ast_simple.cShlOp val CShrOp = C_ast_simple.cShrOp val CLeOp = C_ast_simple.cLeOp val CGrOp = C_ast_simple.cGrOp val CLeqOp = C_ast_simple.cLeqOp val CGeqOp = C_ast_simple.cGeqOp val CEqOp = C_ast_simple.cEqOp val CNeqOp = C_ast_simple.cNeqOp val CAndOp = C_ast_simple.cAndOp val CXorOp = C_ast_simple.cXorOp val COrOp = C_ast_simple.cOrOp val CLndOp = C_ast_simple.cLndOp val CLorOp = C_ast_simple.cLorOp val CPreIncOp = C_ast_simple.cPreIncOp val CPreDecOp = C_ast_simple.cPreDecOp val CPostIncOp = C_ast_simple.cPostIncOp val CPostDecOp = C_ast_simple.cPostDecOp val CAdrOp = C_ast_simple.cAdrOp val CIndOp = C_ast_simple.cIndOp val CPlusOp = C_ast_simple.cPlusOp val CMinOp = C_ast_simple.cMinOp val CCompOp = C_ast_simple.cCompOp val CNegOp = C_ast_simple.cNegOp val CAuto = C_ast_simple.cAuto val CRegister = C_ast_simple.cRegister val CStatic = C_ast_simple.cStatic val CExtern = C_ast_simple.cExtern val CTypedef = C_ast_simple.cTypedef val CThread = C_ast_simple.cThread val CInlineQual = C_ast_simple.cInlineQual val CNoreturnQual = C_ast_simple.cNoreturnQual val CStructTag = C_ast_simple.cStructTag val CUnionTag = C_ast_simple.cUnionTag val CIntConst = C_ast_simple.cIntConst val CCharConst = C_ast_simple.cCharConst val CFloatConst = C_ast_simple.cFloatConst val CStrConst = C_ast_simple.cStrConst val CStrLit = C_ast_simple.cStrLit val CFunDef = C_ast_simple.cFunDef val CDecl = C_ast_simple.cDecl val CStaticAssert = C_ast_simple.cStaticAssert val CDeclr = C_ast_simple.cDeclr val CPtrDeclr = C_ast_simple.cPtrDeclr val CArrDeclr = C_ast_simple.cArrDeclr val CFunDeclr = C_ast_simple.cFunDeclr val CNoArrSize = C_ast_simple.cNoArrSize val CArrSize = C_ast_simple.cArrSize val CLabel = C_ast_simple.cLabel val CCase = C_ast_simple.cCase val CCases = C_ast_simple.cCases val CDefault = C_ast_simple.cDefault val CExpr = C_ast_simple.cExpr val CCompound = C_ast_simple.cCompound val CIf = C_ast_simple.cIf val CSwitch = C_ast_simple.cSwitch val CWhile = C_ast_simple.cWhile val CFor = C_ast_simple.cFor val CGoto = C_ast_simple.cGoto val CGotoPtr = C_ast_simple.cGotoPtr val CCont = C_ast_simple.cCont val CBreak = C_ast_simple.cBreak val CReturn = C_ast_simple.cReturn val CAsm = C_ast_simple.cAsm val CAsmStmt = C_ast_simple.cAsmStmt val CAsmOperand = C_ast_simple.cAsmOperand val CBlockStmt = C_ast_simple.cBlockStmt val CBlockDecl = C_ast_simple.cBlockDecl val CNestedFunDef = C_ast_simple.cNestedFunDef val CStorageSpec = C_ast_simple.cStorageSpec val CTypeSpec = C_ast_simple.cTypeSpec val CTypeQual = C_ast_simple.cTypeQual val CFunSpec = C_ast_simple.cFunSpec val CAlignSpec = C_ast_simple.cAlignSpec val CVoidType = C_ast_simple.cVoidType val CCharType = C_ast_simple.cCharType val CShortType = C_ast_simple.cShortType val CIntType = C_ast_simple.cIntType val CLongType = C_ast_simple.cLongType val CFloatType = C_ast_simple.cFloatType val CDoubleType = C_ast_simple.cDoubleType val CSignedType = C_ast_simple.cSignedType val CUnsigType = C_ast_simple.cUnsigType val CBoolType = C_ast_simple.cBoolType val CComplexType = C_ast_simple.cComplexType val CInt128Type = C_ast_simple.cInt128Type val CSUType = C_ast_simple.cSUType val CEnumType = C_ast_simple.cEnumType val CTypeDef = C_ast_simple.cTypeDef val CTypeOfExpr = C_ast_simple.cTypeOfExpr val CTypeOfType = C_ast_simple.cTypeOfType val CAtomicType = C_ast_simple.cAtomicType val CConstQual = C_ast_simple.cConstQual val CVolatQual = C_ast_simple.cVolatQual val CRestrQual = C_ast_simple.cRestrQual val CAtomicQual = C_ast_simple.cAtomicQual val CAttrQual = C_ast_simple.cAttrQual val CNullableQual = C_ast_simple.cNullableQual val CNonnullQual = C_ast_simple.cNonnullQual val CAlignAsType = C_ast_simple.cAlignAsType val CAlignAsExpr = C_ast_simple.cAlignAsExpr val CStruct = C_ast_simple.cStruct val CEnum = C_ast_simple.cEnum val CInitExpr = C_ast_simple.cInitExpr val CInitList = C_ast_simple.cInitList val CArrDesig = C_ast_simple.cArrDesig val CMemberDesig = C_ast_simple.cMemberDesig val CRangeDesig = C_ast_simple.cRangeDesig val CAttr = C_ast_simple.cAttr val CComma = C_ast_simple.cComma val CAssign = C_ast_simple.cAssign val CCond = C_ast_simple.cCond val CBinary = C_ast_simple.cBinary val CCast = C_ast_simple.cCast val CUnary = C_ast_simple.cUnary val CSizeofExpr = C_ast_simple.cSizeofExpr val CSizeofType = C_ast_simple.cSizeofType val CAlignofExpr = C_ast_simple.cAlignofExpr val CAlignofType = C_ast_simple.cAlignofType val CComplexReal = C_ast_simple.cComplexReal val CComplexImag = C_ast_simple.cComplexImag val CIndex = C_ast_simple.cIndex val CCall = C_ast_simple.cCall val CMember = C_ast_simple.cMember val CVar = C_ast_simple.cVar val CConst = C_ast_simple.cConst val CCompoundLit = C_ast_simple.cCompoundLit val CGenericSelection = C_ast_simple.cGenericSelection val CStatExpr = C_ast_simple.cStatExpr val CLabAddrExpr = C_ast_simple.cLabAddrExpr val CBuiltinExpr = C_ast_simple.cBuiltinExpr val CBuiltinVaArg = C_ast_simple.cBuiltinVaArg val CBuiltinOffsetOf = C_ast_simple.cBuiltinOffsetOf val CBuiltinTypesCompatible = C_ast_simple.cBuiltinTypesCompatible val CDeclExt = C_ast_simple.cDeclExt val CFDefExt = C_ast_simple.cFDefExt val CAsmExt = C_ast_simple.cAsmExt val CTranslUnit = C_ast_simple.cTranslUnit\<close>

ML\<open>type class_Pos = Position.T * Position.T\<close>

ML\<open>
type NodeInfo = C_ast_simple.nodeInfo
type CStorageSpec = NodeInfo C_ast_simple.cStorageSpecifier
type CFunSpec = NodeInfo C_ast_simple.cFunctionSpecifier
type CConst = NodeInfo C_ast_simple.cConstant
type 'a CInitializerList = ('a C_ast_simple.cPartDesignator List.list * 'a C_ast_simple.cInitializer) List.list
type CTranslUnit = NodeInfo C_ast_simple.cTranslationUnit
type CExtDecl = NodeInfo C_ast_simple.cExternalDeclaration
type CFunDef = NodeInfo C_ast_simple.cFunctionDef
type CDecl = NodeInfo C_ast_simple.cDeclaration
type CDeclr = NodeInfo C_ast_simple.cDeclarator
type CDerivedDeclr = NodeInfo C_ast_simple.cDerivedDeclarator
type CArrSize = NodeInfo C_ast_simple.cArraySize
type CStat = NodeInfo C_ast_simple.cStatement
type CAsmStmt = NodeInfo C_ast_simple.cAssemblyStatement
type CAsmOperand = NodeInfo C_ast_simple.cAssemblyOperand
type CBlockItem = NodeInfo C_ast_simple.cCompoundBlockItem
type CDeclSpec = NodeInfo C_ast_simple.cDeclarationSpecifier
type CTypeSpec = NodeInfo C_ast_simple.cTypeSpecifier
type CTypeQual = NodeInfo C_ast_simple.cTypeQualifier
type CAlignSpec = NodeInfo C_ast_simple.cAlignmentSpecifier
type CStructUnion = NodeInfo C_ast_simple.cStructureUnion
type CEnum = NodeInfo C_ast_simple.cEnumeration
type CInit = NodeInfo C_ast_simple.cInitializer
type CInitList = NodeInfo CInitializerList
type CDesignator = NodeInfo C_ast_simple.cPartDesignator
type CAttr = NodeInfo C_ast_simple.cAttribute
type CExpr = NodeInfo C_ast_simple.cExpression
type CBuiltin = NodeInfo C_ast_simple.cBuiltinThing
type CStrLit = NodeInfo C_ast_simple.cStringLiteral
(**)
type CAssignOp = C_ast_simple.cAssignOp
(**)
type 'a Reversed = 'a
datatype CDeclrR = CDeclrR0 of C_ast_simple.ident C_ast_simple.optiona * NodeInfo C_ast_simple.cDerivedDeclarator list Reversed * NodeInfo C_ast_simple.cStringLiteral C_ast_simple.optiona * NodeInfo C_ast_simple.cAttribute list * NodeInfo
fun CDeclrR ide l s a n = CDeclrR0 (ide, l, s, a, n)
type 'a Maybe = 'a C_ast_simple.optiona
datatype 'a Located = Located of 'a * (C_ast_simple.position * (C_ast_simple.position * int))
type ClangCVersion = C_ast_simple.clangCVersion
type Ident = C_ast_simple.ident
type Position = C_ast_simple.position
type PosLength = Position * int
type Name = C_ast_simple.name
type Bool = bool
type CString = C_ast_simple.cString
type CChar = C_ast_simple.cChar
type CInteger = C_ast_simple.cInteger
type CFloat = C_ast_simple.cFloat
type CStructTag = C_ast_simple.cStructTag
type CUnaryOp = C_ast_simple.cUnaryOp
type 'a CStringLiteral = 'a C_ast_simple.cStringLiteral
type 'a CConstant = 'a C_ast_simple.cConstant
type ('a, 'b) Either = ('a, 'b) C_ast_simple.either
type CIntRepr = C_ast_simple.cIntRepr
type CIntFlag = C_ast_simple.cIntFlag
type Comment = C_ast_simple.comment
(**)
val reverse = rev
val Nothing = C_ast_simple.None
val Just = C_ast_simple.Some
val False = false
val True = true
(**)
val CDecl_flat = fn l1 => CDecl l1 o map (fn (a, b, c) => ((a, b), c))
fun flat3 (a, b, c) = ((a, b), c)
fun maybe def f = fn C_ast_simple.None => def | C_ast_simple.Some x => f x 
val id = I
fun flip f b a = f a b
val Reversed = I
(**)

val From_string = C_ast_simple.SS_base o C_ast_simple.ST
\<close>

end
