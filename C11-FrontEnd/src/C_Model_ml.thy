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

theory C_Model_ml
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


type text_range = Symbol_Pos.text * Position.T
type ml_source_range = ML_Lex.token Antiquote.antiquote list * Position.range

datatype 'ml_source_range antiq_stack0 = Setup of 'ml_source_range
                                       | Hook of Symbol_Pos.T list (* length = number of tokens to advance *) * Symbol_Pos.T list (* length = number of steps back in stack *) * 'ml_source_range

fun map_antiq_stack f = fn Setup x => Setup (f x)
                         | Hook (l1, l2, x) => Hook (l1, l2, f x)

type antiq_stack = ml_source_range antiq_stack0 list

datatype antiq_hol = Invariant of string (* term *)
                   | Fnspec of text_range (* ident *) * string (* term *)
                   | Relspec of string (* term *)
                   | Modifies of (bool (* true: [*] *) * text_range) list
                   | Dont_translate
                   | Auxupd of string (* term *)
                   | Ghostupd of string (* term *)
                   | Spec of string (* term *)
                   | End_spec of string (* term *)
                   | Calls of text_range list
                   | Owned_by of text_range

structure C_Env = struct

type tyidents = (Position.T list * serial) Symtab.table

type env_lang = { tyidents : tyidents
                , scopes : tyidents list
                , namesupply : int }
(* NOTE: The distinction between type variable or identifier can not be solely made
         during the lexing process.
         Another pass on the parsed tree is required. *)

type reports = Position.report_text list

type env_tree = { context : Context.generic
                , reports : reports }

type rule_static = (env_lang -> env_tree -> env_lang * env_tree) option

datatype rule_type = Void
                   | Shift
                   | Reduce of int

type ('LrTable_state, 'svalue0, 'pos) rule_ml =
  { rule_pos : 'pos * 'pos
  , rule_type : rule_type
  , rule_env_lang : env_lang
  , rule_static : rule_static
  , rule_antiq : ((int * ('LrTable_state * ('svalue0 * 'pos * 'pos)))
                  * (Position.range * ML_Lex.token Antiquote.antiquote list)) list }

datatype 'a tree = Tree of 'a * 'a tree list

type 'class_Pos rule_output0 = { output_pos : 'class_Pos option
                               , output_env : rule_static }

type rule_output = class_Pos rule_output0

type T = { env_lang : env_lang
         , env_tree : env_tree
         , rule_output : rule_output
         , rule_input : class_Pos list * int
         , stream_hook : (Symbol_Pos.T list * Symbol_Pos.T list * Position.range * ML_Lex.token Antiquote.antiquote list) list list }

(**)

fun map_env_lang f {env_lang, env_tree, rule_output, rule_input, stream_hook} =
  {env_lang = f env_lang, env_tree = env_tree, rule_output = rule_output, rule_input = rule_input, stream_hook = stream_hook}

fun map_env_tree f {env_lang, env_tree, rule_output, rule_input, stream_hook} =
  {env_lang = env_lang, env_tree = f env_tree, rule_output = rule_output, rule_input = rule_input, stream_hook = stream_hook}

fun map_rule_output f {env_lang, env_tree, rule_output, rule_input, stream_hook} =
  {env_lang = env_lang, env_tree = env_tree, rule_output = f rule_output, rule_input = rule_input, stream_hook = stream_hook}

fun map_rule_input f {env_lang, env_tree, rule_output, rule_input, stream_hook} =
  {env_lang = env_lang, env_tree = env_tree, rule_output = rule_output, rule_input = f rule_input, stream_hook = stream_hook}

fun map_stream_hook f {env_lang, env_tree, rule_output, rule_input, stream_hook} =
  {env_lang = env_lang, env_tree = env_tree, rule_output = rule_output, rule_input = rule_input, stream_hook = f stream_hook}

(**)

fun map_output_pos f {output_pos, output_env} =
  {output_pos = f output_pos, output_env = output_env}

fun map_output_env f {output_pos, output_env} =
  {output_pos = output_pos, output_env = f output_env}

(**)

fun map_tyidents f {tyidents, scopes, namesupply} =
  {tyidents = f tyidents, scopes = scopes, namesupply = namesupply}

fun map_scopes f {tyidents, scopes, namesupply} =
  {tyidents = tyidents, scopes = f scopes, namesupply = namesupply}

fun map_namesupply f {tyidents, scopes, namesupply} =
  {tyidents = tyidents, scopes = scopes, namesupply = f namesupply}

(**)

fun map_context f {context, reports} =
  {context = f context, reports = reports}

fun map_reports f {context, reports} =
  {context = context, reports = f reports}

(**)

val empty_env_lang : env_lang = {tyidents = Symtab.make [], scopes = [], namesupply = 0(*"mlyacc_of_happy"*)}
fun empty_env_tree context : env_tree = {context = context, reports = []}
val empty_rule_output : rule_output = {output_pos = NONE, output_env = NONE}
fun make env_lang env_tree = {env_lang = env_lang, env_tree = env_tree, rule_output = empty_rule_output, rule_input = ([], 0), stream_hook = []}
fun string_of (env_lang : env_lang) = 
  let fun dest tab = Symtab.dest tab |> map #1
  in @{make_string} ( ("tyidents", dest (#tyidents env_lang))
                    , ("scopes", map dest (#scopes env_lang))
                    , ("namesupply", #namesupply env_lang)) end

(**)

val encode_positions =
     map (Position.dest
       #> (fn pos => ((#line pos, #offset pos, #end_offset pos), #props pos)))
  #> let open XML.Encode in list (pair (triple int int int) properties) end
  #> YXML.string_of_body
  
val decode_positions =
     YXML.parse_body
  #> let open XML.Decode in list (pair (triple int int int) properties) end
  #> map ((fn ((line, offset, end_offset), props) =>
           {line = line, offset = offset, end_offset = end_offset, props = props})
          #> Position.make)

end

structure C_Env' =
struct

fun map_tyidents f = C_Env.map_env_lang (C_Env.map_tyidents f)
fun map_scopes f = C_Env.map_env_lang (C_Env.map_scopes f)
fun map_namesupply f = C_Env.map_env_lang (C_Env.map_namesupply f)

(**)

fun get_tyidents t = #env_lang t |> #tyidents
fun get_scopes t = #env_lang t |> #scopes
fun get_namesupply t = #env_lang t |> #namesupply

(**)

fun map_output_pos f = C_Env.map_rule_output (C_Env.map_output_pos f)
fun map_output_env f = C_Env.map_rule_output (C_Env.map_output_env f)

(**)

fun get_output_pos (t : C_Env.T) = #rule_output t |> #output_pos

(**)

fun map_context f = C_Env.map_env_tree (C_Env.map_context f)
fun map_reports f = C_Env.map_env_tree (C_Env.map_reports f)

(**)

fun get_reports (t : C_Env.T) = #env_tree t |> #reports

end

signature HSK_C_PARSER =
sig
  type arg = C_Env.T
  type 'a p (* name of the monad, similar as the one declared in Parser.y *) = arg -> 'a * arg

  (**)
  val return : 'a -> 'a p
  val bind : 'a p -> ('a -> 'b p) -> 'b p
  val bind' : 'b p -> ('b -> unit p) -> 'b p
  val >> : unit p * 'a p -> 'a p

  (**)
  val report : Position.T list -> ('a -> Markup.T list) -> 'a -> C_Env.reports -> C_Env.reports
  val markup_tvar : bool -> Position.T list -> string * serial -> Markup.T list

  (* Language.C.Data.RList *)
  val empty : 'a list Reversed
  val singleton : 'a -> 'a list Reversed
  val snoc : 'a list Reversed -> 'a -> 'a list Reversed
  val rappend : 'a list Reversed -> 'a list -> 'a list Reversed
  val rappendr : 'a list Reversed -> 'a list Reversed -> 'a list Reversed
  val rmap : ('a -> 'b) -> 'a list Reversed -> 'b list Reversed

  (* Language.C.Data.Position *)
  val posOf : 'a -> Position
  val posOf' : bool -> class_Pos -> Position * int
  val make_comment : Symbol_Pos.T list -> Symbol_Pos.T list -> Symbol_Pos.T list -> Position.range -> Comment

  (* Language.C.Data.Node *)
  val mkNodeInfo' : Position -> PosLength -> Name -> NodeInfo
  val decode : NodeInfo -> (class_Pos, string) Either
  val decode_error' : NodeInfo -> Position.range

  (* Language.C.Data.Ident *)
  val mkIdent : Position * int -> string -> Name -> Ident
  val internalIdent : string -> Ident

  (* Language.C.Syntax.AST *)
  val liftStrLit : 'a CStringLiteral -> 'a CConstant

  (* Language.C.Syntax.Constants *)
  val concatCStrings : CString list -> CString

  (* Language.C.Parser.ParserMonad *)
  val getNewName : Name p
  val isTypeIdent : string -> arg -> bool
  val enterScope : unit p
  val leaveScope : unit p
  val getCurrentPosition : Position p

  (* Language.C.Parser.Tokens *)
  val CTokCLit : CChar -> (CChar -> 'a) -> 'a
  val CTokILit : CInteger -> (CInteger -> 'a) -> 'a
  val CTokFLit : CFloat -> (CFloat -> 'a) -> 'a
  val CTokSLit : CString -> (CString -> 'a) -> 'a

  (* Language.C.Parser.Parser *)
  val reverseList : 'a list -> 'a list Reversed
  val L : 'a -> int -> 'a Located p
  val unL : 'a Located -> 'a
  val withNodeInfo : int -> (NodeInfo -> 'a) -> 'a p
  val withNodeInfo_CExtDecl : CExtDecl -> (NodeInfo -> 'a) -> 'a p
  val withNodeInfo_CExpr : CExpr list Reversed -> (NodeInfo -> 'a) -> 'a p
  val withLength : NodeInfo -> (NodeInfo -> 'a) -> 'a p
  val reverseDeclr : CDeclrR -> CDeclr
  val withAttribute : int -> CAttr list -> (NodeInfo -> CDeclrR) -> CDeclrR p
  val withAttributePF : int -> CAttr list -> (NodeInfo -> CDeclrR -> CDeclrR) -> (CDeclrR -> CDeclrR) p
  val appendObjAttrs : CAttr list -> CDeclr -> CDeclr
  val withAsmNameAttrs : CStrLit Maybe * CAttr list -> CDeclrR -> CDeclrR p
  val appendDeclrAttrs : CAttr list -> CDeclrR -> CDeclrR
  val ptrDeclr : CDeclrR -> CTypeQual list -> NodeInfo -> CDeclrR
  val funDeclr : CDeclrR -> (Ident list, (CDecl list * Bool)) Either -> CAttr list -> NodeInfo -> CDeclrR
  val arrDeclr : CDeclrR -> CTypeQual list -> Bool -> Bool -> CExpr Maybe -> NodeInfo -> CDeclrR
  val liftTypeQuals : CTypeQual list Reversed -> CDeclSpec list
  val liftCAttrs : CAttr list -> CDeclSpec list
  val addTrailingAttrs : CDeclSpec list Reversed -> CAttr list -> CDeclSpec list Reversed
  val emptyDeclr : CDeclrR
  val mkVarDeclr : Ident -> NodeInfo -> CDeclrR
  val doDeclIdent : CDeclSpec list -> CDeclrR -> unit p
  val doFuncParamDeclIdent : CDeclr -> unit p
end

structure Hsk_c_parser : HSK_C_PARSER =
struct
(******************************************************************************
 * Language.C
 * https://hackage.haskell.org/package/language-c
 *
 * Copyright (c) 1999-2017 Manuel M T Chakravarty
 *                         Duncan Coutts
 *                         Benedikt Huber
 * Portions Copyright (c) 1989,1990 James A. Roskind
 *
 *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *
 *
 * Language.C.Comments
 * https://hackage.haskell.org/package/language-c-comments
 *
 * Copyright (c) 2010-2014 Geoff Hulette
*)
  open C_ast_simple
  type arg = C_Env.T
  type 'a p = arg -> 'a * arg

  (**)
  val To_string0 = String.implode o to_list
  fun reverse l = rev l

  fun report [] _ _ = I
    | report ps markup x =
        let val ms = markup x
        in fold (fn p => fold (fn m => cons ((p, m), "")) ms) ps end

  fun markup_tvar def ps (name, id) =
    let 
      fun markup_elem name = (name, (name, []): Markup.T);
      val (tvarN, tvar) = markup_elem "C tvar";
      val entity = Markup.entity tvarN name
    in
      tvar ::
      (if def then I else cons (Markup.keyword_properties Markup.ML_keyword3))
        (map (fn pos => Markup.properties (Position.entity_properties_of def id pos) entity) ps)
    end

  (**)
  val return = pair
  fun bind f g = f #-> g
  fun bind' f g = bind f (fn r => bind (g r) (fn () => return r))
  fun a >> b = a #> b o #2
  fun sequence_ f = fn [] => return ()
                     | x :: xs => f x >> sequence_ f xs

  (* Language.C.Data.RList *)
  val empty = []
  fun singleton x = [x]
  fun snoc xs x = x :: xs
  fun rappend xs ys = rev ys @ xs
  fun rappendr xs ys = ys @ xs
  val rmap = map
  val viewr = fn [] => error "viewr: empty RList"
               | x :: xs => (xs, x)

  (* Language.C.Data.Position *)
  val nopos = NoPosition
  fun posOf _ = NoPosition
  fun posOf' mk_range =
    (if mk_range then Position.range else I)
    #> (fn (pos1, pos2) =>
          let val {offset = offset, end_offset = end_offset, ...} = Position.dest pos1
          in (Position offset (From_string (C_Env.encode_positions [pos1, pos2])) 0 0, end_offset - offset) end)
  fun posOf'' node env =
    let val (stack, len) = #rule_input env
        val (mk_range, (pos1a, pos1b)) = case node of Left i => (true, nth stack (len - i - 1))
                                                    | Right range => (false, range)
        val (pos2a, pos2b) = nth stack 0
    in ( (posOf' mk_range (pos1a, pos1b) |> #1, posOf' true (pos2a, pos2b))
       , C_Env'.map_output_pos (K (SOME (pos1a, pos2b))) env) end
  val posOf''' = posOf'' o Left
  val internalPos = InternalPosition
  fun make_comment body_begin body body_end range =
    Comment ( posOf' false range |> #1
            , From_string (Symbol_Pos.implode (body_begin @ body @ body_end))
            , case body_end of [] => SingleLine | _ => MultiLine)

  (* Language.C.Data.Node *)
  val undefNode = OnlyPos nopos (nopos, ~1)
  fun mkNodeInfoOnlyPos pos = OnlyPos pos (nopos, ~1)
  fun mkNodeInfo pos name = NodeInfo pos (nopos, ~1) name
  val mkNodeInfo' = NodeInfo
  val decode =
   (fn OnlyPos0 range => range
     | NodeInfo0 (pos1, (pos2, len2), _) => (pos1, (pos2, len2)))
   #> (fn (Position0 (_, s1, _, _), (Position0 (_, s2, _, _), _)) =>
            (case (C_Env.decode_positions (To_string0 s1), C_Env.decode_positions (To_string0 s2))
             of ([pos1, _], [_, pos2]) => Left (Position.range (pos1, pos2))
              | _ => Right "Expecting 2 elements")
        | _ => Right "Invalid position")
  fun decode_error' x = case decode x of Left x => x | Right msg => error msg
  fun decode_error x = Right (decode_error' x)
  val nameOfNode = fn OnlyPos0 _ => NONE
                    | NodeInfo0 (_, _, name) => SOME name

  (* Language.C.Data.Ident *)
  local
    val bits7 = Integer.pow 7 2
    val bits14 = Integer.pow 14 2
    val bits21 = Integer.pow 21 2
    val bits28 = Integer.pow 28 2
    fun quad s = case s of
      [] => 0
    | c1 :: [] => ord c1
    | c1 :: c2 :: [] => ord c2 * bits7 + ord c1
    | c1 :: c2 :: c3 :: [] => ord c3 * bits14 + ord c2 * bits7 + ord c1
    | c1 :: c2 :: c3 :: c4 :: s => ((ord c4 * bits21
                                     + ord c3 * bits14
                                     + ord c2 * bits7
                                     + ord c1)
                                    mod bits28)
                                   + (quad s mod bits28)
    fun internalIdent0 pos s = Ident (From_string s, quad (Symbol.explode s), pos)
  in
  fun mkIdent (pos, len) s name = internalIdent0 (mkNodeInfo' pos (pos, len) name) s
  val internalIdent = internalIdent0 (mkNodeInfoOnlyPos internalPos)
  end

  (* Language.C.Syntax.AST *)
  fun liftStrLit (CStrLit0 (str, at)) = CStrConst str at

  (* Language.C.Syntax.Constants *)
  fun concatCStrings cs = CString0 (flatten (map (fn CString0 (s,_) => s) cs), exists (fn CString0 (_, b) => b) cs)

  (* Language.C.Parser.ParserMonad *)
  fun getNewName env =
    (Name (C_Env'.get_namesupply env), C_Env'.map_namesupply (fn x => x + 1) env)
  fun addTypedef (Ident0 (i, _, node)) env =
    let val (pos1, _) = decode_error' node
        val id = serial ()
        val name = To_string0 i
        val pos = [pos1]
    in ((), env |> C_Env'.map_tyidents (Symtab.update (name, (pos, id)))
                |> C_Env'.map_reports (report pos (markup_tvar true pos) (name, id))) end
  fun shadowTypedef (Ident0 (i, _, _)) env =
    ((), C_Env'.map_tyidents (Symtab.delete_safe (To_string0 i)) env)
  fun isTypeIdent s0 = Symtab.exists (fn (s1, _) => s0 = s1) o C_Env'.get_tyidents
  fun enterScope env =
    ((), C_Env'.map_scopes (cons (C_Env'.get_tyidents env)) env)
  fun leaveScope env = 
    case C_Env'.get_scopes env of [] => error "leaveScope: already in global scope"
                               | tyidents :: scopes => ((), env |> C_Env'.map_scopes (K scopes)
                                                                |> C_Env'.map_tyidents (K tyidents))
  val getCurrentPosition = return NoPosition

  (* Language.C.Parser.Tokens *)
  fun CTokCLit x f = x |> f
  fun CTokILit x f = x |> f
  fun CTokFLit x f = x |> f
  fun CTokSLit x f = x |> f

  (* Language.C.Parser.Parser *)
  fun reverseList x = rev x
  fun L a i = posOf''' i #>> curry Located a
  fun unL (Located (a, _)) = a
  fun withNodeInfo00 (pos1, (pos2, len2)) mkAttrNode name =
    return (mkAttrNode (NodeInfo pos1 (pos2, len2) name))
  fun withNodeInfo0 x = x |> bind getNewName oo withNodeInfo00
  fun withNodeInfo0' node mkAttrNode env = let val (range, env) = posOf'' node env
                                           in withNodeInfo0 range mkAttrNode env end
  fun withNodeInfo x = x |> withNodeInfo0' o Left
  fun withNodeInfo' x = x |> withNodeInfo0' o decode_error
  fun withNodeInfo_CExtDecl x = x |>
    withNodeInfo' o (fn CDeclExt0 (CDecl0 (_, _, node)) => node
                      | CDeclExt0 (CStaticAssert0 (_, _, node)) => node
                      | CFDefExt0 (CFunDef0 (_, _, _, _, node)) => node
                      | CAsmExt0 (_, node) => node)
  val get_node_CExpr =
    fn CComma0 (_, a) => a | CAssign0 (_, _, _, a) => a | CCond0 (_, _, _, a) => a |
    CBinary0 (_, _, _, a) => a | CCast0 (_, _, a) => a | CUnary0 (_, _, a) => a | CSizeofExpr0 (_, a) => a | CSizeofType0 (_, a) => a | CAlignofExpr0 (_, a) => a | CAlignofType0 (_, a) => a | CComplexReal0 (_, a) => a | CComplexImag0 (_, a) => a | CIndex0 (_, _, a) => a |
    CCall0 (_, _, a) => a | CMember0 (_, _, _, a) => a | CVar0 (_, a) => a | CConst0 c => (case c of
    CIntConst0 (_, a) => a | CCharConst0 (_, a) => a | CFloatConst0 (_, a) => a | CStrConst0 (_, a) => a) |
    CCompoundLit0 (_, _, a) => a | CGenericSelection0 (_, _, a) => a | CStatExpr0 (_, a) => a |
    CLabAddrExpr0 (_, a) => a | CBuiltinExpr0 cBuiltinThing => (case cBuiltinThing
     of CBuiltinVaArg0 (_, _, a) => a
     | CBuiltinOffsetOf0 (_, _, a) => a
     | CBuiltinTypesCompatible0 (_, _, a) => a)
  fun withNodeInfo_CExpr x = x |> withNodeInfo' o get_node_CExpr o hd
  fun withLength node mkAttrNode =
    bind (posOf'' (decode_error node)) (fn range => 
      withNodeInfo00 range mkAttrNode (case nameOfNode node of NONE => error "nameOfNode"
                                                             | SOME name => name))
  fun reverseDeclr (CDeclrR0 (ide, reversedDDs, asmname, cattrs, at)) = CDeclr ide (rev reversedDDs) asmname cattrs at
  fun appendDeclrAttrs newAttrs (CDeclrR0 (ident, l, asmname, cattrs, at)) =
    case l of
      [] => CDeclrR ident empty asmname (cattrs @ newAttrs) at
    | x :: xs =>
      let val appendAttrs = fn CPtrDeclr0 (typeQuals, at) => CPtrDeclr (typeQuals @ map CAttrQual newAttrs) at
                             | CArrDeclr0 (typeQuals, arraySize, at) => CArrDeclr (typeQuals @ map CAttrQual newAttrs) arraySize at
                             | CFunDeclr0 (parameters, cattrs, at) => CFunDeclr parameters (cattrs @ newAttrs) at
      in CDeclrR ident (appendAttrs x :: xs) asmname cattrs at
      end
  fun withAttribute node cattrs mkDeclrNode =
    bind (posOf''' node) (fn (pos, _) =>
    bind getNewName (fn name =>
        let val attrs = mkNodeInfo pos name
            val newDeclr = appendDeclrAttrs cattrs (mkDeclrNode attrs)
        in return newDeclr end))
  fun withAttributePF node cattrs mkDeclrCtor =
    bind (posOf''' node) (fn (pos, _) =>
    bind getNewName (fn name =>
        let val attrs = mkNodeInfo pos name
            val newDeclr = appendDeclrAttrs cattrs o mkDeclrCtor attrs
        in return newDeclr end))
  fun appendObjAttrs newAttrs (CDeclr0 (ident, indirections, asmname, cAttrs, at)) =
    CDeclr ident indirections asmname (cAttrs @ newAttrs) at
  fun appendObjAttrsR newAttrs (CDeclrR0 (ident, indirections, asmname, cAttrs, at)) =
    CDeclrR ident indirections asmname (cAttrs @ newAttrs) at
  fun setAsmName mAsmName (CDeclrR0 (ident, indirections, oldName, cattrs, at)) =
    case (case (mAsmName, oldName)
          of (None, None) => Right None
           | (None, oldname as Some _) => Right oldname
           | (newname as Some _, None) => Right newname
           | (Some n1, Some n2) => Left (n1, n2))
    of
      Left (n1, n2) => let fun showName (CStrLit0 (CString0 (s, _), _)) = To_string0 s
                       in error ("Duplicate assembler name: " ^ showName n1 ^ " " ^ showName n2) end
    | Right newName => return (CDeclrR ident indirections newName cattrs at)
  fun withAsmNameAttrs (mAsmName, newAttrs) declr = setAsmName mAsmName (appendObjAttrsR newAttrs declr)
  fun ptrDeclr (CDeclrR0 (ident, derivedDeclrs, asmname, cattrs, dat)) tyquals at =
    CDeclrR ident (snoc derivedDeclrs (CPtrDeclr tyquals at)) asmname cattrs dat
  fun funDeclr (CDeclrR0 (ident, derivedDeclrs, asmname, dcattrs, dat)) params cattrs at =
    CDeclrR ident (snoc derivedDeclrs (CFunDeclr params cattrs at)) asmname dcattrs dat
  fun arrDeclr (CDeclrR0 (ident, derivedDeclrs, asmname, cattrs, dat)) tyquals var_sized static_size size_expr_opt at =
    CDeclrR ident
            (snoc
               derivedDeclrs
               (CArrDeclr tyquals (case size_expr_opt of
                                     Some e => CArrSize static_size e
                                   | None => CNoArrSize var_sized) at))
            asmname
            cattrs
            dat
  val liftTypeQuals = map CTypeQual o reverse
  val liftCAttrs = map (CTypeQual o CAttrQual)
  fun addTrailingAttrs declspecs new_attrs =
    case viewr declspecs of
      (specs_init, CTypeSpec0 (CSUType0 (CStruct0 (tag, name, Some def, def_attrs, su_node), node))) =>
        snoc specs_init (CTypeSpec (CSUType (CStruct tag name (Just def) (def_attrs @ new_attrs) su_node) node))
    | (specs_init, CTypeSpec0 (CEnumType0 (CEnum0 (name, Some def, def_attrs, e_node), node))) => 
        snoc specs_init (CTypeSpec (CEnumType (CEnum name (Just def) (def_attrs @ new_attrs) e_node) node))
    | _ => rappend declspecs (liftCAttrs new_attrs)
  val emptyDeclr = CDeclrR Nothing empty Nothing [] undefNode
  fun mkVarDeclr ident = CDeclrR (Some ident) empty Nothing []
  fun doDeclIdent declspecs (CDeclrR0 (mIdent, _, _, _, _)) =
    case mIdent of None => return ()
                 | Some ident =>
                     if exists (fn CStorageSpec0 (CTypedef0 _) => true | _ => false) declspecs
                     then addTypedef ident
                     else shadowTypedef ident
  val doFuncParamDeclIdent =
    fn CDeclr0 (_, (CFunDeclr0 (Right (params, _), _, _) :: _), _, _, _) =>
        sequence_
          shadowTypedef
          (maps (fn CDecl0 (_,l,_) => maps (fn ((Some (CDeclr0 (Some mIdent, _, _, _, _)),_),_) => [mIdent]
                                             | _ => [])
                                           l
                  | _ => [])
                params)
     | _ => return ()
end

structure List = struct
  open List
  val reverse = rev
end

datatype ('a, 'b) either = Left of 'a | Right of 'b
type ('LrTable_state, 'a, 'Position_T) stack_elem0 = 'LrTable_state * ('a * 'Position_T * 'Position_T)
type ('LrTable_state, 'a, 'Position_T) stack0 = ('LrTable_state, 'a, 'Position_T) stack_elem0 list
type cString = CString
type cChar = CChar
type cInteger = CInteger
type cFloat = CFloat
type ident = Ident
type 'a monad = 'a Hsk_c_parser.p
val return = Hsk_c_parser.return
\<close>

section \<open>Loading of Generated Grammar\<close>

ML_file "../copied_from_git/mlton/lib/mlyacc-lib/base.sig"
ML_file "../copied_from_git/mlton/lib/mlyacc-lib/join.sml"
ML_file "../copied_from_git/mlton/lib/mlyacc-lib/lrtable.sml"
ML_file "../copied_from_git/mlton/lib/mlyacc-lib/stream.sml"
(*ML\<open>val foldl = List.foldl val foldr = List.foldr\<close>
  ML_file "../copied_from_git/mlton/lib/mlyacc-lib/parser2.sml"*)
ML_file "../copied_from_git/mlton/lib/mlyacc-lib/parser1.sml"
ML_file "../generated/language_c.grm.sig"

ML\<open>
structure MlyValueM' = struct
open Hsk_c_parser
val To_string0 = String.implode o C_ast_simple.to_list
fun update_env f x = pair () ##> C_Env'.map_output_env (K (SOME (f x)))

val specifier3 : (CDeclSpec list) -> unit monad = update_env (fn l => fn env_lang => fn env_tree =>
  ( env_lang
  , fold
      let open C_ast_simple
      in fn CTypeSpec0 (CTypeDef0 (Ident0 (i, _, node), _)) =>
            let val name = To_string0 i
                val pos1 = [decode_error' node |> #1]
            in case Symtab.lookup (#tyidents env_lang) name of
                 NONE => I
               | SOME (pos0, id) => C_Env.map_reports (report pos1 (markup_tvar false pos0) (name, id)) end
          | _ => I
      end
      l
      env_tree))
val declaration_specifier3 : (CDeclSpec list) -> unit monad = specifier3
val type_specifier3 : (CDeclSpec list) -> unit monad = specifier3
end

structure MlyValueM = struct
  open MlyValueM
  open MlyValueM'
end
\<close>

ML_file "../generated/language_c.grm.sml"

ML\<open>
structure StrictCLrVals = StrictCLrValsFun(structure Token = LrParser1.Token)
\<close>

ML\<open>
local open StrictCLrVals.Tokens in
  fun token_of_string error ty_ClangCVersion ty_cChar ty_cFloat ty_cInteger ty_cString ty_ident ty_string a1 a2 = fn
     "(" => x28 (ty_string, a1, a2)
    | ")" => x29 (ty_string, a1, a2)
    | "[" => x5b (ty_string, a1, a2)
    | "]" => x5d (ty_string, a1, a2)
    | "->" => x2d_x3e (ty_string, a1, a2)
    | "." => x2e (ty_string, a1, a2)
    | "!" => x21 (ty_string, a1, a2)
    | "~" => x7e (ty_string, a1, a2)
    | "++" => x2b_x2b (ty_string, a1, a2)
    | "--" => x2d_x2d (ty_string, a1, a2)
    | "+" => x2b (ty_string, a1, a2)
    | "-" => x2d (ty_string, a1, a2)
    | "*" => x2a (ty_string, a1, a2)
    | "/" => x2f (ty_string, a1, a2)
    | "%" => x25 (ty_string, a1, a2)
    | "&" => x26 (ty_string, a1, a2)
    | "<<" => x3c_x3c (ty_string, a1, a2)
    | ">>" => x3e_x3e (ty_string, a1, a2)
    | "<" => x3c (ty_string, a1, a2)
    | "<=" => x3c_x3d (ty_string, a1, a2)
    | ">" => x3e (ty_string, a1, a2)
    | ">=" => x3e_x3d (ty_string, a1, a2)
    | "==" => x3d_x3d (ty_string, a1, a2)
    | "!=" => x21_x3d (ty_string, a1, a2)
    | "^" => x5e (ty_string, a1, a2)
    | "|" => x7c (ty_string, a1, a2)
    | "&&" => x26_x26 (ty_string, a1, a2)
    | "||" => x7c_x7c (ty_string, a1, a2)
    | "?" => x3f (ty_string, a1, a2)
    | ":" => x3a (ty_string, a1, a2)
    | "=" => x3d (ty_string, a1, a2)
    | "+=" => x2b_x3d (ty_string, a1, a2)
    | "-=" => x2d_x3d (ty_string, a1, a2)
    | "*=" => x2a_x3d (ty_string, a1, a2)
    | "/=" => x2f_x3d (ty_string, a1, a2)
    | "%=" => x25_x3d (ty_string, a1, a2)
    | "&=" => x26_x3d (ty_string, a1, a2)
    | "^=" => x5e_x3d (ty_string, a1, a2)
    | "|=" => x7c_x3d (ty_string, a1, a2)
    | "<<=" => x3c_x3c_x3d (ty_string, a1, a2)
    | ">>=" => x3e_x3e_x3d (ty_string, a1, a2)
    | "," => x2c (ty_string, a1, a2)
    | ";" => x3b (ty_string, a1, a2)
    | "{" => x7b (ty_string, a1, a2)
    | "}" => x7d (ty_string, a1, a2)
    | "..." => x2e_x2e_x2e (ty_string, a1, a2)
    | x => let 
    val alignof = alignof (ty_string, a1, a2)
    val alignas = alignas (ty_string, a1, a2)
    val atomic = x5f_Atomic (ty_string, a1, a2)
    val asm = asm (ty_string, a1, a2)
    val auto = auto (ty_string, a1, a2)
    val break = break (ty_string, a1, a2)
    val bool = x5f_Bool (ty_string, a1, a2)
    val case0 = case0 (ty_string, a1, a2)
    val char = char (ty_string, a1, a2)
    val const = const (ty_string, a1, a2)
    val continue = continue (ty_string, a1, a2)
    val complex = x5f_Complex (ty_string, a1, a2)
    val default = default (ty_string, a1, a2)
    val do0 = do0 (ty_string, a1, a2)
    val double = double (ty_string, a1, a2)
    val else0 = else0 (ty_string, a1, a2)
    val enum = enum (ty_string, a1, a2)
    val extern = extern (ty_string, a1, a2)
    val float = float (ty_string, a1, a2)
    val for0 = for0 (ty_string, a1, a2)
    val generic = x5f_Generic (ty_string, a1, a2)
    val goto = goto (ty_string, a1, a2)
    val if0 = if0 (ty_string, a1, a2)
    val inline = inline (ty_string, a1, a2)
    val int = int (ty_string, a1, a2)
    val int128 = x5f_x5f_int_x31_x32_x38 (ty_string, a1, a2)
    val long = long (ty_string, a1, a2)
    val label = x5f_x5f_label_x5f_x5f (ty_string, a1, a2)
    val noreturn = x5f_Noreturn (ty_string, a1, a2)
    val nullable = x5f_Nullable (ty_string, a1, a2)
    val nonnull = x5f_Nonnull (ty_string, a1, a2)
    val register = register (ty_string, a1, a2)
    val restrict = restrict (ty_string, a1, a2)
    val return0 = return0 (ty_string, a1, a2)
    val short = short (ty_string, a1, a2)
    val signed = signed (ty_string, a1, a2)
    val sizeof = sizeof (ty_string, a1, a2)
    val static = static (ty_string, a1, a2)
    val staticassert = x5f_Static_assert (ty_string, a1, a2)
    val struct0 = struct0 (ty_string, a1, a2)
    val switch = switch (ty_string, a1, a2)
    val typedef = typedef (ty_string, a1, a2)
    val typeof = typeof (ty_string, a1, a2)
    val thread = x5f_x5f_thread (ty_string, a1, a2)
    val union = union (ty_string, a1, a2)
    val unsigned = unsigned (ty_string, a1, a2)
    val void = void (ty_string, a1, a2)
    val volatile = volatile (ty_string, a1, a2)
    val while0 = while0 (ty_string, a1, a2)
    val cchar = cchar (ty_cChar, a1, a2)
    val cint = cint (ty_cInteger, a1, a2)
    val cfloat = cfloat (ty_cFloat, a1, a2)
    val cstr = cstr (ty_cString, a1, a2)
    val ident = ident (ty_ident, a1, a2)
    val tyident = tyident (ty_ident, a1, a2)
    val attribute = x5f_x5f_attribute_x5f_x5f (ty_string, a1, a2)
    val extension = x5f_x5f_extension_x5f_x5f (ty_string, a1, a2)
    val real = x5f_x5f_real_x5f_x5f (ty_string, a1, a2)
    val imag = x5f_x5f_imag_x5f_x5f (ty_string, a1, a2)
    val builtinvaarg = x5f_x5f_builtin_va_arg (ty_string, a1, a2)
    val builtinoffsetof = x5f_x5f_builtin_offsetof (ty_string, a1, a2)
    val builtintypescompatiblep = x5f_x5f_builtin_types_compatible_p (ty_string, a1, a2)
    val clangcversion = clangcversion (ty_ClangCVersion, a1, a2)
    in case x of
      "_Alignas" => alignas
    | "_Alignof" => alignof
    | "__alignof" => alignof
    | "alignof" => alignof
    | "__alignof__" => alignof
    | "__asm" => asm
    | "asm" => asm
    | "__asm__" => asm
    | "_Atomic" => atomic
    | "__attribute" => attribute
    | "__attribute__" => attribute
    | "auto" => auto
    | "_Bool" => bool
    | "break" => break
    | "__builtin_offsetof" => builtinoffsetof
    | "__builtin_types_compatible_p" => builtintypescompatiblep
    | "__builtin_va_arg" => builtinvaarg
    | "case" => case0
    | "char" => char
    | "_Complex" => complex
    | "__complex__" => complex
    | "__const" => const
    | "const" => const
    | "__const__" => const
    | "continue" => continue
    | "default" => default
    | "do" => do0
    | "double" => double
    | "else" => else0
    | "enum" => enum
    | "__extension__" => extension
    | "extern" => extern
    | "float" => float
    | "for" => for0
    | "_Generic" => generic
    | "goto" => goto
    | "if" => if0
    | "__imag" => imag
    | "__imag__" => imag
    | "__inline" => inline
    | "inline" => inline
    | "__inline__" => inline
    | "int" => int
    | "__int128" => int128
    | "__label__" => label
    | "long" => long
    | "_Nonnull" => nonnull
    | "__nonnull" => nonnull
    | "_Noreturn" => noreturn
    | "_Nullable" => nullable
    | "__nullable" => nullable
    | "__real" => real
    | "__real__" => real
    | "register" => register
    | "__restrict" => restrict
    | "restrict" => restrict
    | "__restrict__" => restrict
    | "return" => return0
    | "short" => short
    | "__signed" => signed
    | "signed" => signed
    | "__signed__" => signed
    | "sizeof" => sizeof
    | "static" => static
    | "_Static_assert" => staticassert
    | "struct" => struct0
    | "switch" => switch
    | "__thread" => thread
    | "_Thread_local" => thread
    | "typedef" => typedef
    | "__typeof" => typeof
    | "typeof" => typeof
    | "__typeof__" => typeof
    | "union" => union
    | "unsigned" => unsigned
    | "void" => void
    | "__volatile" => volatile
    | "volatile" => volatile
    | "__volatile__" => volatile
    | "while" => while0
    | _ => error
    end
end
\<close>

end
