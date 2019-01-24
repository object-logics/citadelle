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

meta_command' \<comment>\<open>\<^theory_text>\<open>code_reflect' open C_ast_simple functions main\<close>\<close> \<open>
let
  open META
  fun meta_command {shallow, deep = _, syntax_print = _} =
    [(META_semi_theories o Theories_one o Theory_code_reflect)
      (Code_reflect
        ( true
        , From.string "C_ast_simple"
        , map From.string [ "main" ]
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
ML_file "mlton/lib/mlyacc-lib/parser2.sml"

ML\<open>
structure SourcePos = struct
  datatype t = T of {column: int, file: string, line: int}
end
\<close>

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
type CDeclrR = CDeclr
type 'a Reversed = 'a
type 'a Maybe = 'a optiona
datatype 'a Located = Located of 'a * position
datatype ClangCVersion = ClangCVersion
type Ident = ident
type Bool = bool
type CString = cString
type CStructTag = cStructTag
type CUnaryOp = cUnaryOp
(**)
fun reverse x = x
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
signature HSK_C_PARSER = sig
  type arg
  type 'a p (* name of the monad, similar as Parser.y (in uppercase) *) = arg -> 'a * arg
  type posLength = position * int
  val return : 'a -> 'a p
  val bind : 'a p -> ('a -> 'b p) -> 'b p
  val >> : unit p * 'a p -> 'a p
  val getNewName : name p
  val getCurrentPosition : position p
  val mkNodeInfo' : position -> posLength -> name -> nodeInfo
  val withNodeInfo : 'node -> (NodeInfo -> 'a) -> 'a p
  val withLength : NodeInfo -> (NodeInfo -> 'a) -> 'a p
  val empty : 'a list Reversed
  val snoc : 'a list Reversed -> 'a -> 'a list Reversed
  val leaveScope : unit p
  val enterScope : unit p
  val liftCAttrs : CAttr list -> CDeclSpec list
  val liftTypeQuals : CTypeQual list Reversed -> CDeclSpec list
  val reverseDeclr : CDeclrR -> CDeclr
  val doFuncParamDeclIdent : CDeclr -> unit p
  val rappendr : 'a list Reversed -> 'a list Reversed -> 'a list Reversed
  val singleton : 'a -> 'a list Reversed
  val withAsmNameAttrs : CStrLit Maybe * CAttr list -> CDeclrR -> CDeclrR p
  val doDeclIdent : CDeclSpec list -> CDeclrR -> unit p
  val reverseList : 'a list -> 'a list Reversed
  val rmap : ('a -> 'b) -> 'a list Reversed -> 'b list Reversed
  val rappend : 'a list Reversed -> 'a list -> 'a list Reversed
  val addTrailingAttrs : CDeclSpec list Reversed -> CAttr list -> CDeclSpec list Reversed
  val unL : 'a Located -> 'a
  val posOf : 'a -> position
  val appendObjAttrs : CAttr list -> CDeclr -> CDeclr
  val mkVarDeclr : Ident -> NodeInfo -> CDeclrR
  val ptrDeclr : CDeclrR -> CTypeQual list -> NodeInfo -> CDeclrR
  val withAttribute : 'node -> CAttr list -> (NodeInfo -> CDeclrR) -> CDeclrR p
  val appendDeclrAttrs : CAttr list -> CDeclrR -> CDeclrR
  val funDeclr : CDeclrR -> (Ident list, (CDecl list * Bool)) either -> CAttr list -> NodeInfo -> CDeclrR
  val emptyDeclr : CDeclrR
  val arrDeclr : CDeclrR -> CTypeQual list -> Bool -> Bool -> CExpr Maybe -> NodeInfo -> CDeclrR
  val withAttributePF : 'node -> CAttr list -> (NodeInfo -> CDeclrR -> CDeclrR) -> (CDeclrR -> CDeclrR) p
  val liftStrLit : 'a cStringLiteral -> 'a cConstant
  val CTokILit : string -> (cInteger -> 'a) -> 'a
  val CTokCLit : string -> (cChar -> 'a) -> 'a
  val CTokFLit : string -> (cFloat -> 'a) -> 'a
  val CTokSLit : string -> (cString -> 'a) -> 'a
  val concatCStrings : CString list -> CString
  val internalIdent : string -> ident
end

structure Hsk_c_parser : HSK_C_PARSER = struct
  type arg = unit
  type 'a p = arg -> 'a * arg
  type posLength = position * int
  type position = unit
  val return = pair
  val getNewName = return (Name 0)
  fun bind f g = f #-> g
  val getCurrentPosition = return NoPosition
  fun mkNodeInfo' _ _ _ = OnlyPos NoPosition (NoPosition, 0)
  fun withNodeInfo _ f = return (f (OnlyPos NoPosition (NoPosition, 0)))
  fun withLength x f = return (f x)
  val empty = []
  fun snoc xs x = x :: xs
  val leaveScope = return ()
  val enterScope = return ()
  fun a >> b = b
  fun liftCAttrs _ = []
  fun liftTypeQuals _ = []
  fun reverseDeclr x = x
  fun doFuncParamDeclIdent _ = return ()
  fun rappendr _ x = x
  fun singleton x = [x]
  fun withAsmNameAttrs _ x = return x
  fun doDeclIdent _ _ = return ()
  val reverseList = rev
  val rmap = map
  fun rappend l _ = l
  fun addTrailingAttrs l _ = l
  fun unL (Located (a, _)) = a
  fun posOf _ = NoPosition
  fun appendObjAttrs _ = I
  fun mkVarDeclr _ _ = error ""
  fun ptrDeclr x _ _ = x
  fun withAttribute _ _ _ = return (error "")
  fun appendDeclrAttrs _ = I
  fun funDeclr x _ _ _ = x
  val undefNode = OnlyPos NoPosition (NoPosition, 0)
  val emptyDeclr = CDeclr Nothing empty Nothing [] undefNode
  fun arrDeclr x _ _ _ _ _ = x
  fun withAttributePF _ _ _ = return I
  fun liftStrLit _ = error ""
  fun CTokILit _ = error ""
  fun CTokCLit _ = error ""
  fun CTokFLit _ = error ""
  fun CTokSLit _ = error ""
  fun concatCStrings _ = error ""
  fun internalIdent _ = error ""
end

structure List = struct
  open List
  val reverse = rev
end
\<close>

ML_file "mlyacc_output/a.grm.sig"
ML_file "mlyacc_output/a.grm.sml"

end
