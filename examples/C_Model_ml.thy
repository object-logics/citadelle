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
 *
 *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *
 *
 * Securify & Orca
 *
 * Copyright (c) 2016-2017 Nanyang Technological University, Singapore
 *               2017-2018 Virginia Tech, USA
 *
 *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *
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
  imports C_Model_core
begin

section \<open>Convert\<close>

definition translation_unit :: "CTranslUnit \<times> Comment list \<times> integer list \<Rightarrow> unit" where
          "translation_unit _ = ()"

section \<open>Run\<close>

definition "main = translation_unit"

declare [[default_code_width = 236]]

code_reserved SML Ident error

meta_command' \<comment>\<open>\<^theory_text>\<open>code_reflect' open C_ast_simple functions main String.to_list S.flatten\<close>\<close> \<open>
let
  open META
  fun meta_command {shallow, deep = _, syntax_print = _} =
    [(META_semi_theories o Theories_one o Theory_code_reflect)
      (Code_reflect
        ( true
        , From.string "C_ast_simple"
        , map From.string [ "main", "String.to_list", "S.flatten" ]
         @ (shallow
            |> hd
            |> fst
            |> d_hsk_constr
            |> map (flattenb (From.string "C_Model_core.") o to_String))))]
in meta_command
end
\<close>

ML\<open>
structure C_ast_simple = struct
  open C_ast_simple
  val Ident = Ident0
end
\<close>

section \<open>CTranslation\<close>

ML\<open>val foldl = List.foldl val foldr = List.foldr\<close>

ML_file "mlton/lib/mlyacc-lib/base.sig"
ML_file "mlton/lib/mlyacc-lib/join.sml"
ML_file "mlton/lib/mlyacc-lib/lrtable.sml"
ML_file "mlton/lib/mlyacc-lib/stream.sml"
(*ML_file "mlton/lib/mlyacc-lib/parser2.sml"*)
ML_file "mlton/lib/mlyacc-lib/parser1.sml"

ML\<open>open C_ast_simple\<close>

meta_command'\<open>
let
  open META
  fun b s = SML_basic [s]
  fun meta_command {shallow, deep = _, syntax_print = _} =
    [(META_semi_theories o Theories_one o Theory_ML o SMLa o SML_top)
      (shallow
       |> hd
       |> fst
       |> d_hsk_constr
       |> map_filter
            (fn s =>
              let val s' = s |> to_String |> To_string0 in
              if List.exists (fn s0 => s0 = s') ["Ident", "ClangCVersion", "CString"] then NONE
              else
                  SOME
                    (SML_val_fun
                      ( SOME Sval
                      , SML_rewrite ( b (to_String s)
                                    , From.string "="
                                    , b (case String.explode s' of
                                           c :: s => Char.toLower c :: s |> String.implode |> From.string))))
              end))]
in meta_command
end
\<close>

ML\<open>
type NodeInfo = nodeInfo
type CStorageSpec = NodeInfo cStorageSpecifier
type CFunSpec = NodeInfo cFunctionSpecifier
type CConst = NodeInfo cConstant
type 'a CInitializerList = ('a cPartDesignator List.list * 'a cInitializer) List.list
type CTranslUnit = NodeInfo cTranslationUnit
type CExtDecl = NodeInfo cExternalDeclaration
type CFunDef = NodeInfo cFunctionDef
type CDecl = NodeInfo cDeclaration
type CDeclr = NodeInfo cDeclarator
type CDerivedDeclr = NodeInfo cDerivedDeclarator
type CArrSize = NodeInfo cArraySize
type CStat = NodeInfo cStatement
type CAsmStmt = NodeInfo cAssemblyStatement
type CAsmOperand = NodeInfo cAssemblyOperand
type CBlockItem = NodeInfo cCompoundBlockItem
type CDeclSpec = NodeInfo cDeclarationSpecifier
type CTypeSpec = NodeInfo cTypeSpecifier
type CTypeQual = NodeInfo cTypeQualifier
type CAlignSpec = NodeInfo cAlignmentSpecifier
type CStructUnion = NodeInfo cStructureUnion
type CEnum = NodeInfo cEnumeration
type CInit = NodeInfo cInitializer
type CInitList = NodeInfo CInitializerList
type CDesignator = NodeInfo cPartDesignator
type CAttr = NodeInfo cAttribute
type CExpr = NodeInfo cExpression
type CBuiltin = NodeInfo cBuiltinThing
type CStrLit = NodeInfo cStringLiteral
(**)
type CAssignOp = cAssignOp
(**)
type 'a Reversed = 'a
datatype CDeclrR = CDeclrR0 of ident optiona * NodeInfo cDerivedDeclarator list Reversed * NodeInfo cStringLiteral optiona * NodeInfo cAttribute list * NodeInfo
fun CDeclrR ide l s a n = CDeclrR0 (ide, l, s, a, n)
type 'a Maybe = 'a optiona
datatype 'a Located = Located of 'a * position
type ClangCVersion = clangCVersion
type Ident = ident
type Bool = bool
type CString = cString
type CStructTag = cStructTag
type CUnaryOp = cUnaryOp
(**)
val reverse = rev
val Nothing = None
val Just = Some
val False = false
val True = true
fun L a b = Located (a, b)
(**)
val CDecl_flat = fn l1 => CDecl l1 o map (fn (a, b, c) => ((a, b), c))
fun flat3 (a, b, c) = ((a, b), c)
fun maybe def f = fn None => def | Some x => f x 
val id = I
fun flip f b a = f a b
val Reversed = I
(**)

val From_string = SS_base o ST
type c_env = {tyidents : Symtab.set, scopes : Symtab.set list, namesupply : int}

signature HSK_C_PARSER =
sig
  type arg = c_env
  type 'a p (* name of the monad, similar as the one declared in Parser.y *) = arg -> 'a * arg
  type posLength = position * int

  (**)
  val return : 'a -> 'a p
  val bind : 'a p -> ('a -> 'b p) -> 'b p
  val >> : unit p * 'a p -> 'a p

  (* Language.C.Data.RList *)
  val empty : 'a list Reversed
  val singleton : 'a -> 'a list Reversed
  val snoc : 'a list Reversed -> 'a -> 'a list Reversed
  val rappend : 'a list Reversed -> 'a list -> 'a list Reversed
  val rappendr : 'a list Reversed -> 'a list Reversed -> 'a list Reversed
  val rmap : ('a -> 'b) -> 'a list Reversed -> 'b list Reversed

  (* Language.C.Data.Position *)
  val posOf : 'a -> position

  (* Language.C.Data.Node *)
  val mkNodeInfo' : position -> posLength -> name -> nodeInfo

  (* Language.C.Data.Ident *)
  val internalIdent : string -> ident

  (* Language.C.Syntax.AST *)
  val liftStrLit : 'a cStringLiteral -> 'a cConstant

  (* Language.C.Syntax.Constants *)
  val concatCStrings : CString list -> CString

  (* Language.C.Parser.ParserMonad *)
  val getNewName : name p
  val isTypeIdent : string -> arg -> bool
  val enterScope : unit p
  val leaveScope : unit p
  val getCurrentPosition : position p

  (* Language.C.Parser.Tokens *)
  val CTokCLit : cChar -> (cChar -> 'a) -> 'a
  val CTokILit : cInteger -> (cInteger -> 'a) -> 'a
  val CTokFLit : cFloat -> (cFloat -> 'a) -> 'a
  val CTokSLit : cString -> (cString -> 'a) -> 'a

  (* Language.C.Parser.Parser *)
  val reverseList : 'a list -> 'a list Reversed
  val unL : 'a Located -> 'a
  val withNodeInfo : 'node -> (NodeInfo -> 'a) -> 'a p
  val withLength : NodeInfo -> (NodeInfo -> 'a) -> 'a p
  val reverseDeclr : CDeclrR -> CDeclr
  val withAttribute : 'node -> CAttr list -> (NodeInfo -> CDeclrR) -> CDeclrR p
  val withAttributePF : 'node -> CAttr list -> (NodeInfo -> CDeclrR -> CDeclrR) -> (CDeclrR -> CDeclrR) p
  val appendObjAttrs : CAttr list -> CDeclr -> CDeclr
  val withAsmNameAttrs : CStrLit Maybe * CAttr list -> CDeclrR -> CDeclrR p
  val appendDeclrAttrs : CAttr list -> CDeclrR -> CDeclrR
  val ptrDeclr : CDeclrR -> CTypeQual list -> NodeInfo -> CDeclrR
  val funDeclr : CDeclrR -> (Ident list, (CDecl list * Bool)) either -> CAttr list -> NodeInfo -> CDeclrR
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
  type arg = c_env
  type 'a p = arg -> 'a * arg
  type posLength = position * int

  (**)
  val To_string0 = String.implode o to_list
  fun reverse l = rev l

  (**)
  val return = pair
  fun bind f g = f #-> g
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
  val internalPos = InternalPosition

  (* Language.C.Data.Node *)
  val undefNode = OnlyPos nopos (nopos, ~1)
  fun mkNodeInfoOnlyPos pos = OnlyPos pos (nopos, ~1)
  fun mkNodeInfo pos name = NodeInfo pos (nopos, ~1) name
  val mkNodeInfo' = NodeInfo

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
  in
  fun internalIdent s = Ident (From_string s, quad (Symbol.explode s), mkNodeInfoOnlyPos internalPos)
  end

  (* Language.C.Syntax.AST *)
  fun liftStrLit (CStrLit0 (str, at)) = CStrConst str at

  (* Language.C.Syntax.Constants *)
  fun concatCStrings cs = CString0 (flatten (map (fn CString0 (s,_) => s) cs), exists (fn CString0 (_, b) => b) cs)

  (* Language.C.Parser.ParserMonad *)
  fun getNewName {tyidents, scopes, namesupply} =
    (Name namesupply, {tyidents = tyidents, scopes = scopes, namesupply = namesupply + 1})
  fun addTypedef (Ident0 (i,_,_)) {tyidents, scopes, namesupply} =
    ((), {tyidents = Symtab.update (To_string0 i, ()) tyidents, scopes = scopes, namesupply = namesupply})
  fun shadowTypedef (Ident0 (i,_,_)) {tyidents, scopes, namesupply} =
    ((), {tyidents = Symtab.delete_safe (To_string0 i) tyidents, scopes = scopes, namesupply = namesupply})
  fun isTypeIdent s0 {tyidents, ...} = Symtab.exists (fn (s1, _) => s0 = s1) tyidents
  fun enterScope {tyidents, scopes, namesupply} = ((), {tyidents = tyidents, scopes = tyidents :: scopes, namesupply = namesupply})
  fun leaveScope {scopes, namesupply, ...} = 
    case scopes of [] => error "leaveScope: already in global scope"
                 | tyidents :: scopes => ((), {tyidents = tyidents, scopes = scopes, namesupply = namesupply})
  val getCurrentPosition = return NoPosition

  (* Language.C.Parser.Tokens *)
  fun CTokCLit x f = x |> f
  fun CTokILit x f = x |> f
  fun CTokFLit x f = x |> f
  fun CTokSLit x f = x |> f

  (* Language.C.Parser.Parser *)
  fun reverseList x = rev x
  fun unL (Located (a, _)) = a
  fun withNodeInfo _ f = return (f (OnlyPos NoPosition (NoPosition, 0)))
  fun withLength x f = return (f x)
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
    bind
      getNewName
      (fn name =>
        let val attrs = mkNodeInfo (posOf node) name
            val newDeclr = appendDeclrAttrs cattrs (mkDeclrNode attrs)
        in return newDeclr end)
  fun withAttributePF node cattrs mkDeclrCtor =
    bind
      getNewName
      (fn name =>
        let val attrs = mkNodeInfo (posOf node) name
            val newDeclr = appendDeclrAttrs cattrs o mkDeclrCtor attrs
        in return newDeclr end)
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
\<close>

ML_file "../doc/language_c.grm.sig"
ML_file "../doc/language_c.grm.sml"

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
