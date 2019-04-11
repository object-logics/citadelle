(* Generated from C_Model_ml.thy; DO NOT EDIT! *)

structure C_Ast : sig
  datatype string_b_a_s_e = ST of string | STa of char list
  datatype abr_string = SS_base of string_b_a_s_e | String_concatWith of abr_string * abr_string list
  datatype name = Name0 of int
  datatype cChar = CChar0 of char * bool | CChars0 of char list * bool
  datatype 'a flags = Flags0 of int
  datatype position = Position0 of int * abr_string * int * int | NoPosition0 | BuiltinPosition0 | InternalPosition0
  datatype nodeInfo = OnlyPos0 of position * (position * int) | NodeInfo0 of position * (position * int) * name
  datatype ident = Ident0 of abr_string * int * nodeInfo
  datatype cFloat = CFloat0 of abr_string
  datatype sUERef = AnonymousRef0 of name | NamedRef0 of ident
  datatype ('a, 'b) either = Left of 'a | Right of 'b
  datatype 'a optiona = None | Some of 'a
  datatype cString = CString0 of abr_string * bool
  datatype commentFormat = SingleLine | MultiLine
  datatype comment = Comment of position * abr_string * commentFormat
  datatype cIntFlag = FlagUnsigned0 | FlagLong0 | FlagLongLong0 | FlagImag0
  datatype cIntRepr = DecRepr0 | HexRepr0 | OctalRepr0
  datatype cInteger = CInteger0 of int * cIntRepr * cIntFlag flags
  datatype cUnaryOp = CPreIncOp0 | CPreDecOp0 | CPostIncOp0 | CPostDecOp0 | CAdrOp0 | CIndOp0 | CPlusOp0 | CMinOp0 | CCompOp0 | CNegOp0
  datatype cAssignOp = CAssignOp0 | CMulAssOp0 | CDivAssOp0 | CRmdAssOp0 | CAddAssOp0 | CSubAssOp0 | CShlAssOp0 | CShrAssOp0 | CAndAssOp0 | CXorAssOp0 | COrAssOp0
  datatype cBinaryOp = CMulOp0 | CDivOp0 | CRmdOp0 | CAddOp0 | CSubOp0 | CShlOp0 | CShrOp0 | CLeOp0 | CGrOp0 | CLeqOp0 | CGeqOp0 | CEqOp0 | CNeqOp0 | CAndOp0 | CXorOp0 | COrOp0 | CLndOp0 | CLorOp0
  datatype 'a cConstant = CIntConst0 of cInteger * 'a | CCharConst0 of cChar * 'a | CFloatConst0 of cFloat * 'a | CStrConst0 of cString * 'a
  datatype 'a cFunctionSpecifier = CInlineQual0 of 'a | CNoreturnQual0 of 'a
  datatype 'a cStorageSpecifier = CAuto0 of 'a | CRegister0 of 'a | CStatic0 of 'a | CExtern0 of 'a | CTypedef0 of 'a | CThread0 of 'a
  datatype cStructTag = CStructTag0 | CUnionTag0
  datatype 'a cStringLiteral = CStrLit0 of cString * 'a
  datatype 'a cArraySize = CNoArrSize0 of bool | CArrSize0 of bool * 'a cExpression
  and 'a cDerivedDeclarator = CPtrDeclr0 of 'a cTypeQualifier list * 'a | CArrDeclr0 of 'a cTypeQualifier list * 'a cArraySize * 'a | CFunDeclr0 of ((ident list), ('a cDeclaration list * bool)) either * 'a cAttribute list * 'a
  and 'a cDeclarator = CDeclr0 of ident optiona * 'a cDerivedDeclarator list * 'a cStringLiteral optiona * 'a cAttribute list * 'a
  and 'a cFunctionDef = CFunDef0 of 'a cDeclarationSpecifier list * 'a cDeclarator * 'a cDeclaration list * 'a cStatement * 'a
  and 'a cCompoundBlockItem = CBlockStmt0 of 'a cStatement | CBlockDecl0 of 'a cDeclaration | CNestedFunDef0 of 'a cFunctionDef
  and 'a cStatement = CLabel0 of ident * 'a cStatement * 'a cAttribute list * 'a | CCase0 of 'a cExpression * 'a cStatement * 'a | CCases0 of 'a cExpression * 'a cExpression * 'a cStatement * 'a | CDefault0 of 'a cStatement * 'a |
    CExpr0 of 'a cExpression optiona * 'a | CCompound0 of ident list * 'a cCompoundBlockItem list * 'a | CIf0 of 'a cExpression * 'a cStatement * 'a cStatement optiona * 'a | CSwitch0 of 'a cExpression * 'a cStatement * 'a |
    CWhile0 of 'a cExpression * 'a cStatement * bool * 'a | CFor0 of ('a cExpression optiona, 'a cDeclaration) either * 'a cExpression optiona * 'a cExpression optiona * 'a cStatement * 'a | CGoto0 of ident * 'a |
    CGotoPtr0 of 'a cExpression * 'a | CCont0 of 'a | CBreak0 of 'a | CReturn0 of 'a cExpression optiona * 'a | CAsm0 of 'a cAssemblyStatement * 'a
  and 'a cExpression = CComma0 of 'a cExpression list * 'a | CAssign0 of cAssignOp * 'a cExpression * 'a cExpression * 'a | CCond0 of 'a cExpression * 'a cExpression optiona * 'a cExpression * 'a |
    CBinary0 of cBinaryOp * 'a cExpression * 'a cExpression * 'a | CCast0 of 'a cDeclaration * 'a cExpression * 'a | CUnary0 of cUnaryOp * 'a cExpression * 'a | CSizeofExpr0 of 'a cExpression * 'a | CSizeofType0 of 'a cDeclaration * 'a
    | CAlignofExpr0 of 'a cExpression * 'a | CAlignofType0 of 'a cDeclaration * 'a | CComplexReal0 of 'a cExpression * 'a | CComplexImag0 of 'a cExpression * 'a | CIndex0 of 'a cExpression * 'a cExpression * 'a |
    CCall0 of 'a cExpression * 'a cExpression list * 'a | CMember0 of 'a cExpression * ident * bool * 'a | CVar0 of ident * 'a | CConst0 of 'a cConstant |
    CCompoundLit0 of 'a cDeclaration * ('a cPartDesignator list * 'a cInitializer) list * 'a | CGenericSelection0 of 'a cExpression * ('a cDeclaration optiona * 'a cExpression) list * 'a | CStatExpr0 of 'a cStatement * 'a |
    CLabAddrExpr0 of ident * 'a | CBuiltinExpr0 of 'a cBuiltinThing
  and 'a cAttribute = CAttr0 of ident * 'a cExpression list * 'a
  and 'a cTypeQualifier = CConstQual0 of 'a | CVolatQual0 of 'a | CRestrQual0 of 'a | CAtomicQual0 of 'a | CAttrQual0 of 'a cAttribute | CNullableQual0 of 'a | CNonnullQual0 of 'a
  and 'a cEnumeration = CEnum0 of ident optiona * ((ident * 'a cExpression optiona) list) optiona * 'a cAttribute list * 'a
  and 'a cPartDesignator = CArrDesig0 of 'a cExpression * 'a | CMemberDesig0 of ident * 'a | CRangeDesig0 of 'a cExpression * 'a cExpression * 'a
  and 'a cInitializer = CInitExpr0 of 'a cExpression * 'a | CInitList0 of ('a cPartDesignator list * 'a cInitializer) list * 'a
  and 'a cAssemblyOperand = CAsmOperand0 of ident optiona * 'a cStringLiteral * 'a cExpression * 'a
  and 'a cAssemblyStatement = CAsmStmt0 of 'a cTypeQualifier optiona * 'a cStringLiteral * 'a cAssemblyOperand list * 'a cAssemblyOperand list * 'a cStringLiteral list * 'a
  and 'a cAlignmentSpecifier = CAlignAsType0 of 'a cDeclaration * 'a | CAlignAsExpr0 of 'a cExpression * 'a
  and 'a cDeclarationSpecifier = CStorageSpec0 of 'a cStorageSpecifier | CTypeSpec0 of 'a cTypeSpecifier | CTypeQual0 of 'a cTypeQualifier | CFunSpec0 of 'a cFunctionSpecifier | CAlignSpec0 of 'a cAlignmentSpecifier
  and 'a cDeclaration = CDecl0 of 'a cDeclarationSpecifier list * (('a cDeclarator optiona * 'a cInitializer optiona) * 'a cExpression optiona) list * 'a | CStaticAssert0 of 'a cExpression * 'a cStringLiteral * 'a
  and 'a cBuiltinThing = CBuiltinVaArg0 of 'a cExpression * 'a cDeclaration * 'a | CBuiltinOffsetOf0 of 'a cDeclaration * 'a cPartDesignator list * 'a | CBuiltinTypesCompatible0 of 'a cDeclaration * 'a cDeclaration * 'a
  and 'a cStructureUnion = CStruct0 of cStructTag * ident optiona * ('a cDeclaration list) optiona * 'a cAttribute list * 'a
  and 'a cTypeSpecifier = CVoidType0 of 'a | CCharType0 of 'a | CShortType0 of 'a | CIntType0 of 'a | CLongType0 of 'a | CFloatType0 of 'a | CDoubleType0 of 'a | CSignedType0 of 'a | CUnsigType0 of 'a | CBoolType0 of 'a |
    CComplexType0 of 'a | CInt128Type0 of 'a | CSUType0 of 'a cStructureUnion * 'a | CEnumType0 of 'a cEnumeration * 'a | CTypeDef0 of ident * 'a | CTypeOfExpr0 of 'a cExpression * 'a | CTypeOfType0 of 'a cDeclaration * 'a |
    CAtomicType0 of 'a cDeclaration * 'a
  datatype clangCVersion = ClangCVersion0 of abr_string
  datatype 'a cExternalDeclaration = CDeclExt0 of 'a cDeclaration | CFDefExt0 of 'a cFunctionDef | CAsmExt0 of 'a cStringLiteral * 'a
  datatype 'a cTranslationUnit = CTranslUnit0 of 'a cExternalDeclaration list * 'a
  val fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val rev : 'a list -> 'a list
  val foldl : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
  val flatten : abr_string list -> abr_string
  val translation_unit : nodeInfo cTranslationUnit * (comment list * int list) -> unit
  val main : nodeInfo cTranslationUnit * (comment list * int list) -> unit
  val cIf : 'a cExpression -> 'a cStatement -> 'a cStatement optiona -> 'a -> 'a cStatement
  val cAsm : 'a cAssemblyStatement -> 'a -> 'a cStatement
  val cFor : ('a cExpression optiona, 'a cDeclaration) either -> 'a cExpression optiona -> 'a cExpression optiona -> 'a cStatement -> 'a -> 'a cStatement
  val cVar : ident -> 'a -> 'a cExpression
  val name : int -> name
  val foldl_one : ('a -> char -> 'a) -> 'a -> string -> 'a
  val foldlb : ('a -> char -> 'a) -> 'a -> string_b_a_s_e -> 'a
  val foldla : ('a -> char -> 'a) -> 'a -> abr_string -> 'a
  val cAttr : ident -> 'a cExpression list -> 'a -> 'a cAttribute
  val cAuto : 'a -> 'a cStorageSpecifier
  val cCall : 'a cExpression -> 'a cExpression list -> 'a -> 'a cExpression
  val cCase : 'a cExpression -> 'a cStatement -> 'a -> 'a cStatement
  val cCast : 'a cDeclaration -> 'a cExpression -> 'a -> 'a cExpression
  val cChar : char -> bool -> cChar
  val cCond : 'a cExpression -> 'a cExpression optiona -> 'a cExpression -> 'a -> 'a cExpression
  val cCont : 'a -> 'a cStatement
  val cDecl : 'a cDeclarationSpecifier list -> (('a cDeclarator optiona * 'a cInitializer optiona) * 'a cExpression optiona) list -> 'a -> 'a cDeclaration
  val cEnum : ident optiona -> ((ident * 'a cExpression optiona) list) optiona -> 'a cAttribute list -> 'a -> 'a cEnumeration
  val cEqOp : cBinaryOp
  val cExpr : 'a cExpression optiona -> 'a -> 'a cStatement
  val cGoto : ident -> 'a -> 'a cStatement
  val cGrOp : cBinaryOp
  val cLeOp : cBinaryOp
  val cOrOp : cBinaryOp
  val flags : int -> 'a flags
  val ident : abr_string -> int -> nodeInfo -> ident
  val cAddOp : cBinaryOp
  val cAdrOp : cUnaryOp
  val cAndOp : cBinaryOp
  val cBreak : 'a -> 'a cStatement
  val cCases : 'a cExpression -> 'a cExpression -> 'a cStatement -> 'a -> 'a cStatement
  val cChars : char list -> bool -> cChar
  val cComma : 'a cExpression list -> 'a -> 'a cExpression
  val cConst : 'a cConstant -> 'a cExpression
  val cDeclr : ident optiona -> 'a cDerivedDeclarator list -> 'a cStringLiteral optiona -> 'a cAttribute list -> 'a -> 'a cDeclarator
  val cDivOp : cBinaryOp
  val cFloat : abr_string -> cFloat
  val cGeqOp : cBinaryOp
  val cIndOp : cUnaryOp
  val cIndex : 'a cExpression -> 'a cExpression -> 'a -> 'a cExpression
  val cLabel : ident -> 'a cStatement -> 'a cAttribute list -> 'a -> 'a cStatement
  val cLeqOp : cBinaryOp
  val cLndOp : cBinaryOp
  val cLorOp : cBinaryOp
  val cMinOp : cUnaryOp
  val cMulOp : cBinaryOp
  val cNegOp : cUnaryOp
  val cNeqOp : cBinaryOp
  val cRmdOp : cBinaryOp
  val cShlOp : cBinaryOp
  val cShrOp : cBinaryOp
  val cSubOp : cBinaryOp
  val cUnary : cUnaryOp -> 'a cExpression -> 'a -> 'a cExpression
  val cWhile : 'a cExpression -> 'a cStatement -> bool -> 'a -> 'a cStatement
  val cXorOp : cBinaryOp
  val to_list : abr_string -> char list
  val cAsmExt : 'a cStringLiteral -> 'a -> 'a cExternalDeclaration
  val cAssign : cAssignOp -> 'a cExpression -> 'a cExpression -> 'a -> 'a cExpression
  val cBinary : cBinaryOp -> 'a cExpression -> 'a cExpression -> 'a -> 'a cExpression
  val cCompOp : cUnaryOp
  val cExtern : 'a -> 'a cStorageSpecifier
  val cFunDef : 'a cDeclarationSpecifier list -> 'a cDeclarator -> 'a cDeclaration list -> 'a cStatement -> 'a -> 'a cFunctionDef
  val cMember : 'a cExpression -> ident -> bool -> 'a -> 'a cExpression
  val cPlusOp : cUnaryOp
  val cReturn : 'a cExpression optiona -> 'a -> 'a cStatement
  val cSUType : 'a cStructureUnion -> 'a -> 'a cTypeSpecifier
  val cStatic : 'a -> 'a cStorageSpecifier
  val cStrLit : cString -> 'a -> 'a cStringLiteral
  val cString : abr_string -> bool -> cString
  val cStruct : cStructTag -> ident optiona -> ('a cDeclaration list) optiona -> 'a cAttribute list -> 'a -> 'a cStructureUnion
  val cSwitch : 'a cExpression -> 'a cStatement -> 'a -> 'a cStatement
  val cThread : 'a -> 'a cStorageSpecifier
  val decRepr : cIntRepr
  val hexRepr : cIntRepr
  val onlyPos : position -> position * int -> nodeInfo
  val cArrSize : bool -> 'a cExpression -> 'a cArraySize
  val cAsmStmt : 'a cTypeQualifier optiona -> 'a cStringLiteral -> 'a cAssemblyOperand list -> 'a cAssemblyOperand list -> 'a cStringLiteral list -> 'a -> 'a cAssemblyStatement
  val cDeclExt : 'a cDeclaration -> 'a cExternalDeclaration
  val cDefault : 'a cStatement -> 'a -> 'a cStatement
  val cFDefExt : 'a cFunctionDef -> 'a cExternalDeclaration
  val cFunSpec : 'a cFunctionSpecifier -> 'a cDeclarationSpecifier
  val cGotoPtr : 'a cExpression -> 'a -> 'a cStatement
  val cIntType : 'a -> 'a cTypeSpecifier
  val cInteger : int -> cIntRepr -> cIntFlag flags -> cInteger
  val cOrAssOp : cAssignOp
  val cTypeDef : ident -> 'a -> 'a cTypeSpecifier
  val cTypedef : 'a -> 'a cStorageSpecifier
  val flagImag : cIntFlag
  val flagLong : cIntFlag
  val namedRef : ident -> sUERef
  val nodeInfo : position -> position * int -> name -> nodeInfo
  val position : int -> abr_string -> int -> int -> position
  val cAddAssOp : cAssignOp
  val cAndAssOp : cAssignOp
  val cArrDeclr : 'a cTypeQualifier list -> 'a cArraySize -> 'a -> 'a cDerivedDeclarator
  val cArrDesig : 'a cExpression -> 'a -> 'a cPartDesignator
  val cAssignOp : cAssignOp
  val cAttrQual : 'a cAttribute -> 'a cTypeQualifier
  val cBoolType : 'a -> 'a cTypeSpecifier
  val cCharType : 'a -> 'a cTypeSpecifier
  val cCompound : ident list -> 'a cCompoundBlockItem list -> 'a -> 'a cStatement
  val cDivAssOp : cAssignOp
  val cEnumType : 'a cEnumeration -> 'a -> 'a cTypeSpecifier
  val cFunDeclr : ((ident list), ('a cDeclaration list * bool)) either -> 'a cAttribute list -> 'a -> 'a cDerivedDeclarator
  val cInitExpr : 'a cExpression -> 'a -> 'a cInitializer
  val cInitList : ('a cPartDesignator list * 'a cInitializer) list -> 'a -> 'a cInitializer
  val cIntConst : cInteger -> 'a -> 'a cConstant
  val cLongType : 'a -> 'a cTypeSpecifier
  val cMulAssOp : cAssignOp
  val cPreDecOp : cUnaryOp
  val cPreIncOp : cUnaryOp
  val cPtrDeclr : 'a cTypeQualifier list -> 'a -> 'a cDerivedDeclarator
  val cRegister : 'a -> 'a cStorageSpecifier
  val cRmdAssOp : cAssignOp
  val cShlAssOp : cAssignOp
  val cShrAssOp : cAssignOp
  val cStatExpr : 'a cStatement -> 'a -> 'a cExpression
  val cStrConst : cString -> 'a -> 'a cConstant
  val cSubAssOp : cAssignOp
  val cTypeQual : 'a cTypeQualifier -> 'a cDeclarationSpecifier
  val cTypeSpec : 'a cTypeSpecifier -> 'a cDeclarationSpecifier
  val cUnionTag : cStructTag
  val cVoidType : 'a -> 'a cTypeSpecifier
  val cXorAssOp : cAssignOp
  val octalRepr : cIntRepr
  val cAlignSpec : 'a cAlignmentSpecifier -> 'a cDeclarationSpecifier
  val cBlockDecl : 'a cDeclaration -> 'a cCompoundBlockItem
  val cBlockStmt : 'a cStatement -> 'a cCompoundBlockItem
  val cCharConst : cChar -> 'a -> 'a cConstant
  val cConstQual : 'a -> 'a cTypeQualifier
  val cFloatType : 'a -> 'a cTypeSpecifier
  val cNoArrSize : bool -> 'a cArraySize
  val cPostDecOp : cUnaryOp
  val cPostIncOp : cUnaryOp
  val cRestrQual : 'a -> 'a cTypeQualifier
  val cShortType : 'a -> 'a cTypeSpecifier
  val cStructTag : cStructTag
  val cUnsigType : 'a -> 'a cTypeSpecifier
  val cVolatQual : 'a -> 'a cTypeQualifier
  val noPosition : position
  val cAsmOperand : ident optiona -> 'a cStringLiteral -> 'a cExpression -> 'a -> 'a cAssemblyOperand
  val cAtomicQual : 'a -> 'a cTypeQualifier
  val cAtomicType : 'a cDeclaration -> 'a -> 'a cTypeSpecifier
  val cDoubleType : 'a -> 'a cTypeSpecifier
  val cFloatConst : cFloat -> 'a -> 'a cConstant
  val cInlineQual : 'a -> 'a cFunctionSpecifier
  val cInt128Type : 'a -> 'a cTypeSpecifier
  val cRangeDesig : 'a cExpression -> 'a cExpression -> 'a -> 'a cPartDesignator
  val cSignedType : 'a -> 'a cTypeSpecifier
  val cSizeofExpr : 'a cExpression -> 'a -> 'a cExpression
  val cSizeofType : 'a cDeclaration -> 'a -> 'a cExpression
  val cTranslUnit : 'a cExternalDeclaration list -> 'a -> 'a cTranslationUnit
  val cTypeOfExpr : 'a cExpression -> 'a -> 'a cTypeSpecifier
  val cTypeOfType : 'a cDeclaration -> 'a -> 'a cTypeSpecifier
  val anonymousRef : name -> sUERef
  val cAlignAsExpr : 'a cExpression -> 'a -> 'a cAlignmentSpecifier
  val cAlignAsType : 'a cDeclaration -> 'a -> 'a cAlignmentSpecifier
  val cAlignofExpr : 'a cExpression -> 'a -> 'a cExpression
  val cAlignofType : 'a cDeclaration -> 'a -> 'a cExpression
  val cBuiltinExpr : 'a cBuiltinThing -> 'a cExpression
  val cComplexImag : 'a cExpression -> 'a -> 'a cExpression
  val cComplexReal : 'a cExpression -> 'a -> 'a cExpression
  val cComplexType : 'a -> 'a cTypeSpecifier
  val cCompoundLit : 'a cDeclaration -> ('a cPartDesignator list * 'a cInitializer) list -> 'a -> 'a cExpression
  val cLabAddrExpr : ident -> 'a -> 'a cExpression
  val cMemberDesig : ident -> 'a -> 'a cPartDesignator
  val cNonnullQual : 'a -> 'a cTypeQualifier
  val cStorageSpec : 'a cStorageSpecifier -> 'a cDeclarationSpecifier
  val flagLongLong : cIntFlag
  val flagUnsigned : cIntFlag
  val cBuiltinVaArg : 'a cExpression -> 'a cDeclaration -> 'a -> 'a cBuiltinThing
  val cNestedFunDef : 'a cFunctionDef -> 'a cCompoundBlockItem
  val cNoreturnQual : 'a -> 'a cFunctionSpecifier
  val cNullableQual : 'a -> 'a cTypeQualifier
  val cStaticAssert : 'a cExpression -> 'a cStringLiteral -> 'a -> 'a cDeclaration
  val clangCVersion : abr_string -> clangCVersion
  val builtinPosition : position
  val cBuiltinOffsetOf : 'a cDeclaration -> 'a cPartDesignator list -> 'a -> 'a cBuiltinThing
  val internalPosition : position
  val cGenericSelection : 'a cExpression -> ('a cDeclaration optiona * 'a cExpression) list -> 'a -> 'a cExpression
  val cBuiltinTypesCompatible : 'a cDeclaration -> 'a cDeclaration -> 'a -> 'a cBuiltinThing
end = struct

datatype string_b_a_s_e = ST of string | STa of char list;

datatype abr_string = SS_base of string_b_a_s_e | String_concatWith of abr_string * abr_string list;

datatype name = Name0 of int;

datatype cChar = CChar0 of char * bool | CChars0 of char list * bool;

datatype 'a flags = Flags0 of int;

datatype position = Position0 of int * abr_string * int * int | NoPosition0 | BuiltinPosition0 | InternalPosition0;

datatype nodeInfo = OnlyPos0 of position * (position * int) | NodeInfo0 of position * (position * int) * name;

datatype ident = Ident0 of abr_string * int * nodeInfo;

datatype cFloat = CFloat0 of abr_string;

datatype sUERef = AnonymousRef0 of name | NamedRef0 of ident;

datatype ('a, 'b) either = Left of 'a | Right of 'b;

datatype 'a optiona = None | Some of 'a;

datatype cString = CString0 of abr_string * bool;

datatype commentFormat = SingleLine | MultiLine;

datatype comment = Comment of position * abr_string * commentFormat;

datatype cIntFlag = FlagUnsigned0 | FlagLong0 | FlagLongLong0 | FlagImag0;

datatype cIntRepr = DecRepr0 | HexRepr0 | OctalRepr0;

datatype cInteger = CInteger0 of int * cIntRepr * cIntFlag flags;

datatype cUnaryOp = CPreIncOp0 | CPreDecOp0 | CPostIncOp0 | CPostDecOp0 | CAdrOp0 | CIndOp0 | CPlusOp0 | CMinOp0 | CCompOp0 | CNegOp0;

datatype cAssignOp = CAssignOp0 | CMulAssOp0 | CDivAssOp0 | CRmdAssOp0 | CAddAssOp0 | CSubAssOp0 | CShlAssOp0 | CShrAssOp0 | CAndAssOp0 | CXorAssOp0 | COrAssOp0;

datatype cBinaryOp = CMulOp0 | CDivOp0 | CRmdOp0 | CAddOp0 | CSubOp0 | CShlOp0 | CShrOp0 | CLeOp0 | CGrOp0 | CLeqOp0 | CGeqOp0 | CEqOp0 | CNeqOp0 | CAndOp0 | CXorOp0 | COrOp0 | CLndOp0 | CLorOp0;

datatype 'a cConstant = CIntConst0 of cInteger * 'a | CCharConst0 of cChar * 'a | CFloatConst0 of cFloat * 'a | CStrConst0 of cString * 'a;

datatype 'a cFunctionSpecifier = CInlineQual0 of 'a | CNoreturnQual0 of 'a;

datatype 'a cStorageSpecifier = CAuto0 of 'a | CRegister0 of 'a | CStatic0 of 'a | CExtern0 of 'a | CTypedef0 of 'a | CThread0 of 'a;

datatype cStructTag = CStructTag0 | CUnionTag0;

datatype 'a cStringLiteral = CStrLit0 of cString * 'a;

datatype 'a cArraySize = CNoArrSize0 of bool | CArrSize0 of bool * 'a cExpression
and 'a cDerivedDeclarator = CPtrDeclr0 of 'a cTypeQualifier list * 'a | CArrDeclr0 of 'a cTypeQualifier list * 'a cArraySize * 'a | CFunDeclr0 of ((ident list), ('a cDeclaration list * bool)) either * 'a cAttribute list * 'a
and 'a cDeclarator = CDeclr0 of ident optiona * 'a cDerivedDeclarator list * 'a cStringLiteral optiona * 'a cAttribute list * 'a
and 'a cFunctionDef = CFunDef0 of 'a cDeclarationSpecifier list * 'a cDeclarator * 'a cDeclaration list * 'a cStatement * 'a
and 'a cCompoundBlockItem = CBlockStmt0 of 'a cStatement | CBlockDecl0 of 'a cDeclaration | CNestedFunDef0 of 'a cFunctionDef
and 'a cStatement = CLabel0 of ident * 'a cStatement * 'a cAttribute list * 'a | CCase0 of 'a cExpression * 'a cStatement * 'a | CCases0 of 'a cExpression * 'a cExpression * 'a cStatement * 'a | CDefault0 of 'a cStatement * 'a |
  CExpr0 of 'a cExpression optiona * 'a | CCompound0 of ident list * 'a cCompoundBlockItem list * 'a | CIf0 of 'a cExpression * 'a cStatement * 'a cStatement optiona * 'a | CSwitch0 of 'a cExpression * 'a cStatement * 'a |
  CWhile0 of 'a cExpression * 'a cStatement * bool * 'a | CFor0 of ('a cExpression optiona, 'a cDeclaration) either * 'a cExpression optiona * 'a cExpression optiona * 'a cStatement * 'a | CGoto0 of ident * 'a |
  CGotoPtr0 of 'a cExpression * 'a | CCont0 of 'a | CBreak0 of 'a | CReturn0 of 'a cExpression optiona * 'a | CAsm0 of 'a cAssemblyStatement * 'a
and 'a cExpression = CComma0 of 'a cExpression list * 'a | CAssign0 of cAssignOp * 'a cExpression * 'a cExpression * 'a | CCond0 of 'a cExpression * 'a cExpression optiona * 'a cExpression * 'a |
  CBinary0 of cBinaryOp * 'a cExpression * 'a cExpression * 'a | CCast0 of 'a cDeclaration * 'a cExpression * 'a | CUnary0 of cUnaryOp * 'a cExpression * 'a | CSizeofExpr0 of 'a cExpression * 'a | CSizeofType0 of 'a cDeclaration * 'a |
  CAlignofExpr0 of 'a cExpression * 'a | CAlignofType0 of 'a cDeclaration * 'a | CComplexReal0 of 'a cExpression * 'a | CComplexImag0 of 'a cExpression * 'a | CIndex0 of 'a cExpression * 'a cExpression * 'a |
  CCall0 of 'a cExpression * 'a cExpression list * 'a | CMember0 of 'a cExpression * ident * bool * 'a | CVar0 of ident * 'a | CConst0 of 'a cConstant |
  CCompoundLit0 of 'a cDeclaration * ('a cPartDesignator list * 'a cInitializer) list * 'a | CGenericSelection0 of 'a cExpression * ('a cDeclaration optiona * 'a cExpression) list * 'a | CStatExpr0 of 'a cStatement * 'a |
  CLabAddrExpr0 of ident * 'a | CBuiltinExpr0 of 'a cBuiltinThing
and 'a cAttribute = CAttr0 of ident * 'a cExpression list * 'a
and 'a cTypeQualifier = CConstQual0 of 'a | CVolatQual0 of 'a | CRestrQual0 of 'a | CAtomicQual0 of 'a | CAttrQual0 of 'a cAttribute | CNullableQual0 of 'a | CNonnullQual0 of 'a
and 'a cEnumeration = CEnum0 of ident optiona * ((ident * 'a cExpression optiona) list) optiona * 'a cAttribute list * 'a
and 'a cPartDesignator = CArrDesig0 of 'a cExpression * 'a | CMemberDesig0 of ident * 'a | CRangeDesig0 of 'a cExpression * 'a cExpression * 'a
and 'a cInitializer = CInitExpr0 of 'a cExpression * 'a | CInitList0 of ('a cPartDesignator list * 'a cInitializer) list * 'a
and 'a cAssemblyOperand = CAsmOperand0 of ident optiona * 'a cStringLiteral * 'a cExpression * 'a
and 'a cAssemblyStatement = CAsmStmt0 of 'a cTypeQualifier optiona * 'a cStringLiteral * 'a cAssemblyOperand list * 'a cAssemblyOperand list * 'a cStringLiteral list * 'a
and 'a cAlignmentSpecifier = CAlignAsType0 of 'a cDeclaration * 'a | CAlignAsExpr0 of 'a cExpression * 'a
and 'a cDeclarationSpecifier = CStorageSpec0 of 'a cStorageSpecifier | CTypeSpec0 of 'a cTypeSpecifier | CTypeQual0 of 'a cTypeQualifier | CFunSpec0 of 'a cFunctionSpecifier | CAlignSpec0 of 'a cAlignmentSpecifier
and 'a cDeclaration = CDecl0 of 'a cDeclarationSpecifier list * (('a cDeclarator optiona * 'a cInitializer optiona) * 'a cExpression optiona) list * 'a | CStaticAssert0 of 'a cExpression * 'a cStringLiteral * 'a
and 'a cBuiltinThing = CBuiltinVaArg0 of 'a cExpression * 'a cDeclaration * 'a | CBuiltinOffsetOf0 of 'a cDeclaration * 'a cPartDesignator list * 'a | CBuiltinTypesCompatible0 of 'a cDeclaration * 'a cDeclaration * 'a
and 'a cStructureUnion = CStruct0 of cStructTag * ident optiona * ('a cDeclaration list) optiona * 'a cAttribute list * 'a
and 'a cTypeSpecifier = CVoidType0 of 'a | CCharType0 of 'a | CShortType0 of 'a | CIntType0 of 'a | CLongType0 of 'a | CFloatType0 of 'a | CDoubleType0 of 'a | CSignedType0 of 'a | CUnsigType0 of 'a | CBoolType0 of 'a |
  CComplexType0 of 'a | CInt128Type0 of 'a | CSUType0 of 'a cStructureUnion * 'a | CEnumType0 of 'a cEnumeration * 'a | CTypeDef0 of ident * 'a | CTypeOfExpr0 of 'a cExpression * 'a | CTypeOfType0 of 'a cDeclaration * 'a |
  CAtomicType0 of 'a cDeclaration * 'a;

datatype clangCVersion = ClangCVersion0 of abr_string;

datatype 'a cExternalDeclaration = CDeclExt0 of 'a cDeclaration | CFDefExt0 of 'a cFunctionDef | CAsmExt0 of 'a cStringLiteral * 'a;

datatype 'a cTranslationUnit = CTranslUnit0 of 'a cExternalDeclaration list * 'a;

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun rev xs = fold (fn a => fn b => a :: b) xs [];

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

fun flatten x = String_concatWith (SS_base (ST ""), x);

fun translation_unit uu = ();

fun main x = translation_unit x;

fun cIf x = (fn a => fn b => fn c => CIf0 (x, a, b, c));

fun cAsm x = (fn a => CAsm0 (x, a));

fun cFor x = (fn a => fn b => fn c => fn d => CFor0 (x, a, b, c, d));

fun cVar x = (fn a => CVar0 (x, a));

fun name x = Name0 x;

fun foldl_one f accu s = foldl f accu (String.explode s);

fun foldlb f accu = (fn a => (case a of ST aa => foldl_one f accu aa | STa aa => foldl f accu aa));

fun foldla f accu e = (case e of SS_base a => foldlb f accu a | String_concatWith (abr, a) => (case a of [] => accu | x :: aa => foldl (fn accua => foldla f (foldla f accua abr)) (foldla f accu x) aa));

fun cAttr x = (fn a => fn b => CAttr0 (x, a, b));

fun cAuto x = CAuto0 x;

fun cCall x = (fn a => fn b => CCall0 (x, a, b));

fun cCase x = (fn a => fn b => CCase0 (x, a, b));

fun cCast x = (fn a => fn b => CCast0 (x, a, b));

fun cChar x = (fn a => CChar0 (x, a));

fun cCond x = (fn a => fn b => fn c => CCond0 (x, a, b, c));

fun cCont x = CCont0 x;

fun cDecl x = (fn a => fn b => CDecl0 (x, a, b));

fun cEnum x = (fn a => fn b => fn c => CEnum0 (x, a, b, c));

val cEqOp : cBinaryOp = CEqOp0;

fun cExpr x = (fn a => CExpr0 (x, a));

fun cGoto x = (fn a => CGoto0 (x, a));

val cGrOp : cBinaryOp = CGrOp0;

val cLeOp : cBinaryOp = CLeOp0;

val cOrOp : cBinaryOp = COrOp0;

fun flags x = Flags0 x;

fun ident x = (fn a => fn b => Ident0 (x, a, b));

val cAddOp : cBinaryOp = CAddOp0;

val cAdrOp : cUnaryOp = CAdrOp0;

val cAndOp : cBinaryOp = CAndOp0;

fun cBreak x = CBreak0 x;

fun cCases x = (fn a => fn b => fn c => CCases0 (x, a, b, c));

fun cChars x = (fn a => CChars0 (x, a));

fun cComma x = (fn a => CComma0 (x, a));

fun cConst x = CConst0 x;

fun cDeclr x = (fn a => fn b => fn c => fn d => CDeclr0 (x, a, b, c, d));

val cDivOp : cBinaryOp = CDivOp0;

fun cFloat x = CFloat0 x;

val cGeqOp : cBinaryOp = CGeqOp0;

val cIndOp : cUnaryOp = CIndOp0;

fun cIndex x = (fn a => fn b => CIndex0 (x, a, b));

fun cLabel x = (fn a => fn b => fn c => CLabel0 (x, a, b, c));

val cLeqOp : cBinaryOp = CLeqOp0;

val cLndOp : cBinaryOp = CLndOp0;

val cLorOp : cBinaryOp = CLorOp0;

val cMinOp : cUnaryOp = CMinOp0;

val cMulOp : cBinaryOp = CMulOp0;

val cNegOp : cUnaryOp = CNegOp0;

val cNeqOp : cBinaryOp = CNeqOp0;

val cRmdOp : cBinaryOp = CRmdOp0;

val cShlOp : cBinaryOp = CShlOp0;

val cShrOp : cBinaryOp = CShrOp0;

val cSubOp : cBinaryOp = CSubOp0;

fun cUnary x = (fn a => fn b => CUnary0 (x, a, b));

fun cWhile x = (fn a => fn b => fn c => CWhile0 (x, a, b, c));

val cXorOp : cBinaryOp = CXorOp0;

fun to_list s = rev (foldla (fn l => fn c => c :: l) [] s);

fun cAsmExt x = (fn a => CAsmExt0 (x, a));

fun cAssign x = (fn a => fn b => fn c => CAssign0 (x, a, b, c));

fun cBinary x = (fn a => fn b => fn c => CBinary0 (x, a, b, c));

val cCompOp : cUnaryOp = CCompOp0;

fun cExtern x = CExtern0 x;

fun cFunDef x = (fn a => fn b => fn c => fn d => CFunDef0 (x, a, b, c, d));

fun cMember x = (fn a => fn b => fn c => CMember0 (x, a, b, c));

val cPlusOp : cUnaryOp = CPlusOp0;

fun cReturn x = (fn a => CReturn0 (x, a));

fun cSUType x = (fn a => CSUType0 (x, a));

fun cStatic x = CStatic0 x;

fun cStrLit x = (fn a => CStrLit0 (x, a));

fun cString x = (fn a => CString0 (x, a));

fun cStruct x = (fn a => fn b => fn c => fn d => CStruct0 (x, a, b, c, d));

fun cSwitch x = (fn a => fn b => CSwitch0 (x, a, b));

fun cThread x = CThread0 x;

val decRepr : cIntRepr = DecRepr0;

val hexRepr : cIntRepr = HexRepr0;

fun onlyPos x = (fn a => OnlyPos0 (x, a));

fun cArrSize x = (fn a => CArrSize0 (x, a));

fun cAsmStmt x = (fn a => fn b => fn c => fn d => fn e => CAsmStmt0 (x, a, b, c, d, e));

fun cDeclExt x = CDeclExt0 x;

fun cDefault x = (fn a => CDefault0 (x, a));

fun cFDefExt x = CFDefExt0 x;

fun cFunSpec x = CFunSpec0 x;

fun cGotoPtr x = (fn a => CGotoPtr0 (x, a));

fun cIntType x = CIntType0 x;

fun cInteger x = (fn a => fn b => CInteger0 (x, a, b));

val cOrAssOp : cAssignOp = COrAssOp0;

fun cTypeDef x = (fn a => CTypeDef0 (x, a));

fun cTypedef x = CTypedef0 x;

val flagImag : cIntFlag = FlagImag0;

val flagLong : cIntFlag = FlagLong0;

fun namedRef x = NamedRef0 x;

fun nodeInfo x = (fn a => fn b => NodeInfo0 (x, a, b));

fun position x = (fn a => fn b => fn c => Position0 (x, a, b, c));

val cAddAssOp : cAssignOp = CAddAssOp0;

val cAndAssOp : cAssignOp = CAndAssOp0;

fun cArrDeclr x = (fn a => fn b => CArrDeclr0 (x, a, b));

fun cArrDesig x = (fn a => CArrDesig0 (x, a));

val cAssignOp : cAssignOp = CAssignOp0;

fun cAttrQual x = CAttrQual0 x;

fun cBoolType x = CBoolType0 x;

fun cCharType x = CCharType0 x;

fun cCompound x = (fn a => fn b => CCompound0 (x, a, b));

val cDivAssOp : cAssignOp = CDivAssOp0;

fun cEnumType x = (fn a => CEnumType0 (x, a));

fun cFunDeclr x = (fn a => fn b => CFunDeclr0 (x, a, b));

fun cInitExpr x = (fn a => CInitExpr0 (x, a));

fun cInitList x = (fn a => CInitList0 (x, a));

fun cIntConst x = (fn a => CIntConst0 (x, a));

fun cLongType x = CLongType0 x;

val cMulAssOp : cAssignOp = CMulAssOp0;

val cPreDecOp : cUnaryOp = CPreDecOp0;

val cPreIncOp : cUnaryOp = CPreIncOp0;

fun cPtrDeclr x = (fn a => CPtrDeclr0 (x, a));

fun cRegister x = CRegister0 x;

val cRmdAssOp : cAssignOp = CRmdAssOp0;

val cShlAssOp : cAssignOp = CShlAssOp0;

val cShrAssOp : cAssignOp = CShrAssOp0;

fun cStatExpr x = (fn a => CStatExpr0 (x, a));

fun cStrConst x = (fn a => CStrConst0 (x, a));

val cSubAssOp : cAssignOp = CSubAssOp0;

fun cTypeQual x = CTypeQual0 x;

fun cTypeSpec x = CTypeSpec0 x;

val cUnionTag : cStructTag = CUnionTag0;

fun cVoidType x = CVoidType0 x;

val cXorAssOp : cAssignOp = CXorAssOp0;

val octalRepr : cIntRepr = OctalRepr0;

fun cAlignSpec x = CAlignSpec0 x;

fun cBlockDecl x = CBlockDecl0 x;

fun cBlockStmt x = CBlockStmt0 x;

fun cCharConst x = (fn a => CCharConst0 (x, a));

fun cConstQual x = CConstQual0 x;

fun cFloatType x = CFloatType0 x;

fun cNoArrSize x = CNoArrSize0 x;

val cPostDecOp : cUnaryOp = CPostDecOp0;

val cPostIncOp : cUnaryOp = CPostIncOp0;

fun cRestrQual x = CRestrQual0 x;

fun cShortType x = CShortType0 x;

val cStructTag : cStructTag = CStructTag0;

fun cUnsigType x = CUnsigType0 x;

fun cVolatQual x = CVolatQual0 x;

val noPosition : position = NoPosition0;

fun cAsmOperand x = (fn a => fn b => fn c => CAsmOperand0 (x, a, b, c));

fun cAtomicQual x = CAtomicQual0 x;

fun cAtomicType x = (fn a => CAtomicType0 (x, a));

fun cDoubleType x = CDoubleType0 x;

fun cFloatConst x = (fn a => CFloatConst0 (x, a));

fun cInlineQual x = CInlineQual0 x;

fun cInt128Type x = CInt128Type0 x;

fun cRangeDesig x = (fn a => fn b => CRangeDesig0 (x, a, b));

fun cSignedType x = CSignedType0 x;

fun cSizeofExpr x = (fn a => CSizeofExpr0 (x, a));

fun cSizeofType x = (fn a => CSizeofType0 (x, a));

fun cTranslUnit x = (fn a => CTranslUnit0 (x, a));

fun cTypeOfExpr x = (fn a => CTypeOfExpr0 (x, a));

fun cTypeOfType x = (fn a => CTypeOfType0 (x, a));

fun anonymousRef x = AnonymousRef0 x;

fun cAlignAsExpr x = (fn a => CAlignAsExpr0 (x, a));

fun cAlignAsType x = (fn a => CAlignAsType0 (x, a));

fun cAlignofExpr x = (fn a => CAlignofExpr0 (x, a));

fun cAlignofType x = (fn a => CAlignofType0 (x, a));

fun cBuiltinExpr x = CBuiltinExpr0 x;

fun cComplexImag x = (fn a => CComplexImag0 (x, a));

fun cComplexReal x = (fn a => CComplexReal0 (x, a));

fun cComplexType x = CComplexType0 x;

fun cCompoundLit x = (fn a => fn b => CCompoundLit0 (x, a, b));

fun cLabAddrExpr x = (fn a => CLabAddrExpr0 (x, a));

fun cMemberDesig x = (fn a => CMemberDesig0 (x, a));

fun cNonnullQual x = CNonnullQual0 x;

fun cStorageSpec x = CStorageSpec0 x;

val flagLongLong : cIntFlag = FlagLongLong0;

val flagUnsigned : cIntFlag = FlagUnsigned0;

fun cBuiltinVaArg x = (fn a => fn b => CBuiltinVaArg0 (x, a, b));

fun cNestedFunDef x = CNestedFunDef0 x;

fun cNoreturnQual x = CNoreturnQual0 x;

fun cNullableQual x = CNullableQual0 x;

fun cStaticAssert x = (fn a => fn b => CStaticAssert0 (x, a, b));

fun clangCVersion x = ClangCVersion0 x;

val builtinPosition : position = BuiltinPosition0;

fun cBuiltinOffsetOf x = (fn a => fn b => CBuiltinOffsetOf0 (x, a, b));

val internalPosition : position = InternalPosition0;

fun cGenericSelection x = (fn a => fn b => CGenericSelection0 (x, a, b));

fun cBuiltinTypesCompatible x = (fn a => fn b => CBuiltinTypesCompatible0 (x, a, b));

end; (*struct C_Ast*)
