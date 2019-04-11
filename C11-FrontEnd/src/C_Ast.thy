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

ML_file \<open>../generated/c_ast.ML\<close>

ML\<open>
structure C_Ast = struct
  open C_Ast
  val Ident = Ident0
end
\<close>

section \<open>Language.C Haskell parsing in ML\<close>

ML \<open>val Position = C_Ast.position val NoPosition = C_Ast.noPosition val BuiltinPosition = C_Ast.builtinPosition val InternalPosition = C_Ast.internalPosition val Name = C_Ast.name val OnlyPos = C_Ast.onlyPos val NodeInfo = C_Ast.nodeInfo val AnonymousRef = C_Ast.anonymousRef val NamedRef = C_Ast.namedRef val CChar = C_Ast.cChar val CChars = C_Ast.cChars val DecRepr = C_Ast.decRepr val HexRepr = C_Ast.hexRepr val OctalRepr = C_Ast.octalRepr val FlagUnsigned = C_Ast.flagUnsigned val FlagLong = C_Ast.flagLong val FlagLongLong = C_Ast.flagLongLong val FlagImag = C_Ast.flagImag val CFloat = C_Ast.cFloat val Flags = C_Ast.flags val CInteger = C_Ast.cInteger val CAssignOp = C_Ast.cAssignOp val CMulAssOp = C_Ast.cMulAssOp val CDivAssOp = C_Ast.cDivAssOp val CRmdAssOp = C_Ast.cRmdAssOp val CAddAssOp = C_Ast.cAddAssOp val CSubAssOp = C_Ast.cSubAssOp val CShlAssOp = C_Ast.cShlAssOp val CShrAssOp = C_Ast.cShrAssOp val CAndAssOp = C_Ast.cAndAssOp val CXorAssOp = C_Ast.cXorAssOp val COrAssOp = C_Ast.cOrAssOp val CMulOp = C_Ast.cMulOp val CDivOp = C_Ast.cDivOp val CRmdOp = C_Ast.cRmdOp val CAddOp = C_Ast.cAddOp val CSubOp = C_Ast.cSubOp val CShlOp = C_Ast.cShlOp val CShrOp = C_Ast.cShrOp val CLeOp = C_Ast.cLeOp val CGrOp = C_Ast.cGrOp val CLeqOp = C_Ast.cLeqOp val CGeqOp = C_Ast.cGeqOp val CEqOp = C_Ast.cEqOp val CNeqOp = C_Ast.cNeqOp val CAndOp = C_Ast.cAndOp val CXorOp = C_Ast.cXorOp val COrOp = C_Ast.cOrOp val CLndOp = C_Ast.cLndOp val CLorOp = C_Ast.cLorOp val CPreIncOp = C_Ast.cPreIncOp val CPreDecOp = C_Ast.cPreDecOp val CPostIncOp = C_Ast.cPostIncOp val CPostDecOp = C_Ast.cPostDecOp val CAdrOp = C_Ast.cAdrOp val CIndOp = C_Ast.cIndOp val CPlusOp = C_Ast.cPlusOp val CMinOp = C_Ast.cMinOp val CCompOp = C_Ast.cCompOp val CNegOp = C_Ast.cNegOp val CAuto = C_Ast.cAuto val CRegister = C_Ast.cRegister val CStatic = C_Ast.cStatic val CExtern = C_Ast.cExtern val CTypedef = C_Ast.cTypedef val CThread = C_Ast.cThread val CInlineQual = C_Ast.cInlineQual val CNoreturnQual = C_Ast.cNoreturnQual val CStructTag = C_Ast.cStructTag val CUnionTag = C_Ast.cUnionTag val CIntConst = C_Ast.cIntConst val CCharConst = C_Ast.cCharConst val CFloatConst = C_Ast.cFloatConst val CStrConst = C_Ast.cStrConst val CStrLit = C_Ast.cStrLit val CFunDef = C_Ast.cFunDef val CDecl = C_Ast.cDecl val CStaticAssert = C_Ast.cStaticAssert val CDeclr = C_Ast.cDeclr val CPtrDeclr = C_Ast.cPtrDeclr val CArrDeclr = C_Ast.cArrDeclr val CFunDeclr = C_Ast.cFunDeclr val CNoArrSize = C_Ast.cNoArrSize val CArrSize = C_Ast.cArrSize val CLabel = C_Ast.cLabel val CCase = C_Ast.cCase val CCases = C_Ast.cCases val CDefault = C_Ast.cDefault val CExpr = C_Ast.cExpr val CCompound = C_Ast.cCompound val CIf = C_Ast.cIf val CSwitch = C_Ast.cSwitch val CWhile = C_Ast.cWhile val CFor = C_Ast.cFor val CGoto = C_Ast.cGoto val CGotoPtr = C_Ast.cGotoPtr val CCont = C_Ast.cCont val CBreak = C_Ast.cBreak val CReturn = C_Ast.cReturn val CAsm = C_Ast.cAsm val CAsmStmt = C_Ast.cAsmStmt val CAsmOperand = C_Ast.cAsmOperand val CBlockStmt = C_Ast.cBlockStmt val CBlockDecl = C_Ast.cBlockDecl val CNestedFunDef = C_Ast.cNestedFunDef val CStorageSpec = C_Ast.cStorageSpec val CTypeSpec = C_Ast.cTypeSpec val CTypeQual = C_Ast.cTypeQual val CFunSpec = C_Ast.cFunSpec val CAlignSpec = C_Ast.cAlignSpec val CVoidType = C_Ast.cVoidType val CCharType = C_Ast.cCharType val CShortType = C_Ast.cShortType val CIntType = C_Ast.cIntType val CLongType = C_Ast.cLongType val CFloatType = C_Ast.cFloatType val CDoubleType = C_Ast.cDoubleType val CSignedType = C_Ast.cSignedType val CUnsigType = C_Ast.cUnsigType val CBoolType = C_Ast.cBoolType val CComplexType = C_Ast.cComplexType val CInt128Type = C_Ast.cInt128Type val CSUType = C_Ast.cSUType val CEnumType = C_Ast.cEnumType val CTypeDef = C_Ast.cTypeDef val CTypeOfExpr = C_Ast.cTypeOfExpr val CTypeOfType = C_Ast.cTypeOfType val CAtomicType = C_Ast.cAtomicType val CConstQual = C_Ast.cConstQual val CVolatQual = C_Ast.cVolatQual val CRestrQual = C_Ast.cRestrQual val CAtomicQual = C_Ast.cAtomicQual val CAttrQual = C_Ast.cAttrQual val CNullableQual = C_Ast.cNullableQual val CNonnullQual = C_Ast.cNonnullQual val CAlignAsType = C_Ast.cAlignAsType val CAlignAsExpr = C_Ast.cAlignAsExpr val CStruct = C_Ast.cStruct val CEnum = C_Ast.cEnum val CInitExpr = C_Ast.cInitExpr val CInitList = C_Ast.cInitList val CArrDesig = C_Ast.cArrDesig val CMemberDesig = C_Ast.cMemberDesig val CRangeDesig = C_Ast.cRangeDesig val CAttr = C_Ast.cAttr val CComma = C_Ast.cComma val CAssign = C_Ast.cAssign val CCond = C_Ast.cCond val CBinary = C_Ast.cBinary val CCast = C_Ast.cCast val CUnary = C_Ast.cUnary val CSizeofExpr = C_Ast.cSizeofExpr val CSizeofType = C_Ast.cSizeofType val CAlignofExpr = C_Ast.cAlignofExpr val CAlignofType = C_Ast.cAlignofType val CComplexReal = C_Ast.cComplexReal val CComplexImag = C_Ast.cComplexImag val CIndex = C_Ast.cIndex val CCall = C_Ast.cCall val CMember = C_Ast.cMember val CVar = C_Ast.cVar val CConst = C_Ast.cConst val CCompoundLit = C_Ast.cCompoundLit val CGenericSelection = C_Ast.cGenericSelection val CStatExpr = C_Ast.cStatExpr val CLabAddrExpr = C_Ast.cLabAddrExpr val CBuiltinExpr = C_Ast.cBuiltinExpr val CBuiltinVaArg = C_Ast.cBuiltinVaArg val CBuiltinOffsetOf = C_Ast.cBuiltinOffsetOf val CBuiltinTypesCompatible = C_Ast.cBuiltinTypesCompatible val CDeclExt = C_Ast.cDeclExt val CFDefExt = C_Ast.cFDefExt val CAsmExt = C_Ast.cAsmExt val CTranslUnit = C_Ast.cTranslUnit\<close>

ML\<open>type class_Pos = Position.T * Position.T\<close>

ML\<open>
type NodeInfo = C_Ast.nodeInfo
type CStorageSpec = NodeInfo C_Ast.cStorageSpecifier
type CFunSpec = NodeInfo C_Ast.cFunctionSpecifier
type CConst = NodeInfo C_Ast.cConstant
type 'a CInitializerList = ('a C_Ast.cPartDesignator List.list * 'a C_Ast.cInitializer) List.list
type CTranslUnit = NodeInfo C_Ast.cTranslationUnit
type CExtDecl = NodeInfo C_Ast.cExternalDeclaration
type CFunDef = NodeInfo C_Ast.cFunctionDef
type CDecl = NodeInfo C_Ast.cDeclaration
type CDeclr = NodeInfo C_Ast.cDeclarator
type CDerivedDeclr = NodeInfo C_Ast.cDerivedDeclarator
type CArrSize = NodeInfo C_Ast.cArraySize
type CStat = NodeInfo C_Ast.cStatement
type CAsmStmt = NodeInfo C_Ast.cAssemblyStatement
type CAsmOperand = NodeInfo C_Ast.cAssemblyOperand
type CBlockItem = NodeInfo C_Ast.cCompoundBlockItem
type CDeclSpec = NodeInfo C_Ast.cDeclarationSpecifier
type CTypeSpec = NodeInfo C_Ast.cTypeSpecifier
type CTypeQual = NodeInfo C_Ast.cTypeQualifier
type CAlignSpec = NodeInfo C_Ast.cAlignmentSpecifier
type CStructUnion = NodeInfo C_Ast.cStructureUnion
type CEnum = NodeInfo C_Ast.cEnumeration
type CInit = NodeInfo C_Ast.cInitializer
type CInitList = NodeInfo CInitializerList
type CDesignator = NodeInfo C_Ast.cPartDesignator
type CAttr = NodeInfo C_Ast.cAttribute
type CExpr = NodeInfo C_Ast.cExpression
type CBuiltin = NodeInfo C_Ast.cBuiltinThing
type CStrLit = NodeInfo C_Ast.cStringLiteral
(**)
type CAssignOp = C_Ast.cAssignOp
(**)
type 'a Reversed = 'a
datatype CDeclrR = CDeclrR0 of C_Ast.ident C_Ast.optiona * NodeInfo C_Ast.cDerivedDeclarator list Reversed * NodeInfo C_Ast.cStringLiteral C_Ast.optiona * NodeInfo C_Ast.cAttribute list * NodeInfo
fun CDeclrR ide l s a n = CDeclrR0 (ide, l, s, a, n)
type 'a Maybe = 'a C_Ast.optiona
datatype 'a Located = Located of 'a * (C_Ast.position * (C_Ast.position * int))
type ClangCVersion = C_Ast.clangCVersion
type Ident = C_Ast.ident
type Position = C_Ast.position
type PosLength = Position * int
type Name = C_Ast.name
type Bool = bool
type CString = C_Ast.cString
type CChar = C_Ast.cChar
type CInteger = C_Ast.cInteger
type CFloat = C_Ast.cFloat
type CStructTag = C_Ast.cStructTag
type CUnaryOp = C_Ast.cUnaryOp
type 'a CStringLiteral = 'a C_Ast.cStringLiteral
type 'a CConstant = 'a C_Ast.cConstant
type ('a, 'b) Either = ('a, 'b) C_Ast.either
type CIntRepr = C_Ast.cIntRepr
type CIntFlag = C_Ast.cIntFlag
type Comment = C_Ast.comment
(**)
val reverse = rev
val Nothing = C_Ast.None
val Just = C_Ast.Some
val False = false
val True = true
(**)
val CDecl_flat = fn l1 => CDecl l1 o map (fn (a, b, c) => ((a, b), c))
fun flat3 (a, b, c) = ((a, b), c)
fun maybe def f = fn C_Ast.None => def | C_Ast.Some x => f x 
val id = I
fun flip f b a = f a b
val Reversed = I
(**)

val From_string = C_Ast.SS_base o C_Ast.ST
\<close>

end
