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

theory C_Model_ml_lex
  imports C_Model_ml
begin

section \<open>Instantiation of the Parser with the Lexer\<close>

ML\<open>
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

section \<open>\<close>

text\<open>The parser consists of a generic module @{file "../copied_from_git/mlton/lib/mlyacc-lib/base.sig"}, 
which interprets a automata-like format generated from smlyacc.\<close>

ML\<open>
type 'a stack_elem = (LrTable.state, 'a, Position.T) stack_elem0

fun map_svalue0 f (st, (v, pos1, pos2)) = (st, (f v, pos1, pos2))

structure Stack_Data_Lang = Generic_Data
  (type T = (LrTable.state, StrictCLrVals.Tokens.svalue0, Position.T) stack0 * C_Env.env_lang
   val empty = ([], C_Env.empty_env_lang)
   val extend = I
   val merge = #2)

structure Stack_Data_Tree = Generic_Data
  (type T = C_Env.reports
   val empty = []
   val extend = I
   val merge = #2)

structure StrictCLex : ARG_LEXER1 =
struct
structure Tokens = StrictCLrVals.Tokens
structure UserDeclarations =
struct
  type ('a,'b) token = ('a, 'b) Tokens.token
  type pos = Position.T
  type arg = Tokens.arg
  type svalue0 = Tokens.svalue0
  type svalue = arg -> svalue0 * arg
  type token0 = C_Lex.token
  type state = StrictCLrVals.ParserData.LrTable.state
end

type stack = (UserDeclarations.state, UserDeclarations.svalue0, UserDeclarations.pos) stack0
           * (Position.range * ML_Lex.token Antiquote.antiquote list) list list
           * (UserDeclarations.pos * UserDeclarations.pos) list
           * (UserDeclarations.state, UserDeclarations.svalue0, UserDeclarations.pos) C_Env.rule_ml C_Env.tree list

fun makeLexer input =
  let val s = Synchronized.var "input"
                (input 1024
                 |> map_filter (fn Right (C_Lex.Token (_, (C_Lex.Space, _))) => NONE
                                 | Right (C_Lex.Token (_, (C_Lex.Comment _, _))) => NONE
                                 | Right (C_Lex.Token (_, (C_Lex.Directive _, _))) => NONE
                                 | Right (C_Lex.Token s) => SOME (Right s)
                                 | Left ml => SOME (Left ml)))
      fun drain ((stack, stack_ml, stack_pos, stack_tree), arg) =
        let val (arg, stack_ml) =
              case #stream_hook arg
              of l :: ls =>
                ( C_Env.map_stream_hook (K ls) arg
                , fold_rev (fn (_, syms, range, ants) => fn stack_ml =>
                             let
                               val () =
                                 if length stack_ml = 1 orelse length stack_ml - length syms = 1 then
                                   warning ("Unevaluated code as the hook is pointing to an internal initial value" ^ Position.here (range |> Position.range_position))
                                 else ()
                               val () =
                                 if length stack_ml - length syms <= 0 then
                                   error ("Maximum depth reached (" ^ Int.toString (length syms - length stack_ml + 1) ^ " in excess)" ^ Position.here (Symbol_Pos.range syms |> Position.range_position))
                                 else ()
                             in nth_map (length syms) (fn xs => (range, ants) :: xs) stack_ml end)
                           l
                           stack_ml)
               | [] => (arg, stack_ml)
            fun return0 x = (x, ((stack, stack_ml, stack_pos, stack_tree), arg))
        in
          case Synchronized.change_result s (fn [] => (NONE, []) | x :: xs => (SOME x, xs))
          of SOME (Left l_antiq) =>
              drain
                ( (stack, stack_ml, stack_pos, stack_tree)
                , fold (fn Setup (ants, range) =>
                          (fn arg =>
                             C_Env'.map_context
                               let val setup = "setup" in
                                 I #> Stack_Data_Lang.put (stack, #env_lang arg)
                                   #> ML_Context.expression
                                        range
                                        setup
                                        "Stack_Data_Lang.T -> Context.generic -> Context.generic"
                                        ("fn context => " ^ setup ^ " (Stack_Data_Lang.get context) context")
                                        ants
                               end
                               arg)
                         | Hook (syms_shift, syms, (ants, range)) =>
                           C_Env.map_stream_hook
                               (fn stream_hook => 
                                case
                                   fold (fn _ => fn (eval1, eval2) =>
                                       (case eval2 of e2 :: eval2 => (e2, eval2)
                                                    | [] => ([], []))
                                       |>> (fn e1 => e1 :: eval1))
                                     syms_shift
                                     ([], stream_hook)
                                of (eval1, eval2) => fold cons
                                                          eval1
                                                          (case eval2 of e :: es => ((syms_shift, syms, range, ants) :: e) :: es
                                                                       | [] => [[(syms_shift, syms, range, ants)]])))
                       l_antiq
                       arg)
           | NONE => 
              let val () =
                    fold (uncurry
                           (fn pos => 
                             fold_rev (fn (syms, _, _, _) => fn () =>
                                        let val () = error ("Maximum depth reached (" ^ Int.toString (pos + 1) ^ " in excess)" ^ Position.here (Symbol_Pos.range syms |> Position.range_position))
                                        in () end)))
                         (map_index I (#stream_hook arg))
                         ()
              in return0 (Tokens.x25_eof (Position.none, Position.none)) end
           | SOME (Right ((pos1, pos2), (C_Lex.Char (b, [c]), _))) =>
              return0 (StrictCLrVals.Tokens.cchar (CChar (String.sub (c,0)) b, pos1, pos2))
           | SOME (Right ((pos1, pos2), (C_Lex.Char (b, _), _))) => error "to do"
           | SOME (Right ((pos1, pos2), (C_Lex.String (b, s), _))) =>
              return0 (StrictCLrVals.Tokens.cstr (C_ast_simple.CString0 (From_string (implode s), b), pos1, pos2))
           | SOME (Right ((pos1, pos2), (C_Lex.Integer (i, repr, flag), _))) =>
              return0 (StrictCLrVals.Tokens.cint
                        ( CInteger i repr
                            (C_Lex.read_bin (fold (fn flag => map (fn (bit, flag0) => (if flag = flag0 then "1" else bit, flag0)))
                                                  flag
                                                  ([FlagUnsigned, FlagLong, FlagLongLong, FlagImag] |> rev |> map (pair "0"))
                                             |> map #1)
                             |> Flags)
                        , pos1
                        , pos2))
           | SOME (Right ((pos1, pos2), (C_Lex.Ident, s))) => 
              let val (name, arg) = Hsk_c_parser.getNewName arg
                  val ident0 = Hsk_c_parser.mkIdent (Hsk_c_parser.posOf' false (pos1, pos2)) s name
              in ( (if Hsk_c_parser.isTypeIdent s arg then
                      StrictCLrVals.Tokens.tyident (ident0, pos1, pos2)
                    else
                      StrictCLrVals.Tokens.ident (ident0, pos1, pos2))
                 , ((stack, stack_ml, stack_pos, stack_tree), arg))
              end
           | SOME (Right ((pos1, pos2), (_, s))) => 
                       token_of_string (Tokens.error (pos1, pos2))
                                       (C_ast_simple.ClangCVersion0 (From_string s))
                                       (CChar #"0" false)
                                       (CFloat (From_string s))
                                       (CInteger 0 DecRepr (Flags 0))
                                       (C_ast_simple.CString0 (From_string s, false))
                                       (C_ast_simple.Ident (From_string s, 0, OnlyPos NoPosition (NoPosition, 0)))
                                       s
                                       pos1
                                       pos2
                                       s
                       |> return0
        end
  in drain
  end
end
\<close>
text\<open>This is where the instatiation of the Parser Functor with the Lexer actually happens ...\<close>
ML\<open>
structure StrictCParser =
  JoinWithArg1(structure LrParser = LrParser1
               structure ParserData = StrictCLrVals.ParserData
               structure Lex = StrictCLex)

structure P = struct

open C_Env

fun exec_tree msg write (Tree ({rule_pos = (p1, p2), rule_type, rule_env_lang = env_lang, rule_static, rule_antiq}, l_tree)) =
  write
    (fn _ =>
      let val (s1, s2) =
        case rule_type of Void => ("VOID", NONE)
                        | Shift => ("SHIFT", NONE)
                        | Reduce i => ("REDUCE " ^ Int.toString i, SOME (MlyValue.string_reduce i ^ " " ^ MlyValue.type_reduce i))
      in msg ^ s1 ^ " " ^ Position.here p1 ^ " " ^ Position.here p2 ^ (case s2 of SOME s2 => " " ^ s2 | NONE => "") end)
  #> (case rule_static of SOME rule_static => rule_static env_lang | NONE => pair env_lang)
  #-> (fn env_lang =>
        fold (fn ((rule, stack0), (range, ants)) =>
               let val stack = ([stack0], env_lang)
                   val hook = "hook"
               in C_Env.map_context
                   (I #> Stack_Data_Lang.put stack
                      #> ML_Context.expression
                           range
                           hook
                           (MlyValue.type_reduce rule ^ " stack_elem -> C_Env.env_lang -> Context.generic -> Context.generic")
                           ("fn context => \
                              \let val (stack, env_lang) = Stack_Data_Lang.get context \
                              \in " ^ hook ^ " (stack |> hd |> map_svalue0 MlyValue.reduce" ^ Int.toString rule ^ ") env_lang end context")
                           ants)
               end)
             rule_antiq)
  #> fold (exec_tree (msg ^ " ") write) l_tree

fun exec_tree' l env_tree = env_tree
  |> C_Env.map_context (Stack_Data_Tree.put [])
  |> fold (exec_tree "" let val ctxt = Context.proof_of (#context env_tree)
                        in if Config.get ctxt C_Options.parser_trace andalso Context_Position.is_visible ctxt
                           then fn f => tap (tracing o f) else K I end)
          l
  |> (fn env_tree =>
       env_tree |> C_Env.map_reports (append (Stack_Data_Tree.get (#context env_tree))))

fun uncurry_context f = uncurry (map_env_tree o f)

fun parse env_lang err accept s =
 make env_lang
 #> StrictCParser.makeLexer (fn _ => s)
 #> StrictCParser.parse
      ( 0
      , uncurry_context (fn (stack, _, _, stack_tree) =>
          let val range_pos = I #> Position.range #> Position.range_position
          in tap (fn _ => Position.reports_text [( ( range_pos (case hd stack of (_, (_, pos1, pos2)) => (pos1, pos2))
                                                   , Markup.bad ())
                                                 , "")])
             #> exec_tree' (rev stack_tree)
             #> err stack (range_pos (case stack_tree of Tree ({rule_pos, ...}, _) :: _ => rule_pos | _ => (Position.none, Position.none)))
          end)
      , Position.none
      , uncurry_context (fn (stack, _, _, stack_tree) =>
          exec_tree' stack_tree
          #> accept (stack |> hd |> map_svalue0 MlyValue.reduce0))
      , fn (stack, arg) => arg |> map_rule_input (K stack)
                               |> map_rule_output (K empty_rule_output)
      , fn arg => (#rule_output arg, arg)
      , #env_lang)
 #> snd
 #> #env_tree
end
\<close>

section \<open>The Construction of an C-Context (analogously to the standard ML context)\<close>

ML\<open>
(*  Title:      Pure/Isar/token.ML
    Author:     Markus Wenzel, TU Muenchen

Outer token syntax for Isabelle/Isar.
*)

structure C_Token =
struct

(** tokens **)

(* token kind *)

val delimited_kind = member (op =) [Token.String, Token.Alt_String, Token.Verbatim, Token.Cartouche, Token.Comment];

(* datatype token *)

datatype T = Token of (Symbol_Pos.text * Position.range) * (Token.kind * Symbol_Pos.T list);

(* position *)

fun pos_of (Token ((_, (pos, _)), _)) = pos;
fun end_pos_of (Token ((_, (_, pos)), _)) = pos;

fun range_of (toks as tok :: _) =
      let val pos' = end_pos_of (List.last toks)
      in Position.range (pos_of tok, pos') end
  | range_of [] = Position.no_range;


(* stopper *)

fun mk_eof pos = Token (("", (pos, Position.none)), (Token.EOF, []));
val eof = mk_eof Position.none;

fun is_eof (Token (_, (Token.EOF, _))) = true
  | is_eof _ = false;

val not_eof = not o is_eof;

val stopper =
  Scan.stopper (fn [] => eof | toks => mk_eof (end_pos_of (List.last toks))) is_eof;


(* kind of token *)

fun kind_of (Token (_, (k, _))) = k;
fun is_kind k (Token (_, (k', _))) = k = k';

val is_command = is_kind Token.Command;
val is_ident = is_kind Token.Ident;
val is_sym_ident = is_kind Token.Sym_Ident;

val is_stack1 = fn Token (_, (Token.Sym_Ident, l)) => forall (fn (s, _) => s = "+") l
                 | _ => false;

val is_stack2 = fn Token (_, (Token.Sym_Ident, l)) => forall (fn (s, _) => s = "@") l
                 | _ => false;

val is_modifies_star = fn Token (_, (Token.Sym_Ident, l)) => Symbol_Pos.content l = "[*]"
                        | _ => false;

val is_colon = fn Token (_, (Token.Keyword, [(":", _)])) => true
                | _ => false;

fun is_proper (Token (_, (Token.Space, _))) = false
  | is_proper (Token (_, (Token.Comment, _))) = false
  | is_proper _ = true;

val is_improper = not o is_proper;

fun is_error' (Token (_, (Token.Error msg, _))) = SOME msg
  | is_error' _ = NONE;


(* token content *)

fun content_of (Token (_, (_, x))) = Symbol_Pos.content x;
fun content_of' (Token (_, (_, x))) = x;

fun input_of (Token ((source, range), (kind, _))) =
  Input.source (delimited_kind kind) source range;

fun inner_syntax_of tok =
  let val x = content_of tok
  in if YXML.detect x then x else Syntax.implode_input (input_of tok) end;


(* markup reports *)

local

val token_kind_markup =
 fn Token.Var => (Markup.var, "")
  | Token.Type_Ident => (Markup.tfree, "")
  | Token.Type_Var => (Markup.tvar, "")
  | Token.String => (Markup.string, "")
  | Token.Alt_String => (Markup.alt_string, "")
  | Token.Verbatim => (Markup.verbatim, "")
  | Token.Cartouche => (Markup.cartouche, "")
  | Token.Comment => (Markup.ML_comment, "")
  | Token.Error msg => (Markup.bad (), msg)
  | _ => (Markup.empty, "");

fun keyword_reports tok = map (fn markup => ((pos_of tok, markup), ""));

fun command_markups keywords x =
  if Keyword.is_theory_end keywords x then [Markup.keyword2 |> Markup.keyword_properties]
  else
    (if Keyword.is_proof_asm keywords x then [Markup.keyword3]
     else if Keyword.is_improper keywords x then [Markup.keyword1, Markup.improper]
     else [Markup.keyword1])
    |> map Markup.command_properties;

in

fun keyword_markup (important, keyword) x =
  if important orelse Symbol.is_ascii_identifier x then keyword else Markup.delimiter;

fun completion_report tok =
  if is_kind Token.Keyword tok
  then map (fn m => ((pos_of tok, m), "")) (Completion.suppress_abbrevs (content_of tok))
  else [];

fun reports keywords tok =
  if is_command tok then
    keyword_reports tok (command_markups keywords (content_of tok))
  else if is_stack1 tok orelse is_stack2 tok then
    keyword_reports tok [Markup.keyword2 |> Markup.keyword_properties]
  else if is_kind Token.Keyword tok then
    keyword_reports tok
      [keyword_markup (false, Markup.keyword2 |> Markup.keyword_properties) (content_of tok)]
  else
    let val (m, text) = token_kind_markup (kind_of tok)
    in [((pos_of tok, m), text)] end;

fun markups keywords = map (#2 o #1) o reports keywords;

end;


(* unparse *)

fun unparse (Token (_, (kind, x))) =
  let val x = Symbol_Pos.content x
  in case kind of
    Token.String => Symbol_Pos.quote_string_qq x
  | Token.Alt_String => Symbol_Pos.quote_string_bq x
  | Token.Verbatim => enclose "{*" "*}" x
  | Token.Cartouche => cartouche x
  | Token.Comment => enclose "(*" "*)" x
  | Token.EOF => ""
  | _ => x
  end;

fun text_of tok =
  let
    val k = Token.str_of_kind (kind_of tok);
    val ms = markups Keyword.empty_keywords tok;
    val s = unparse tok;
  in
    if s = "" then (k, "")
    else if size s < 40 andalso not (exists_string (fn c => c = "\n") s)
    then (k ^ " " ^ Markup.markups ms s, "")
    else (k, Markup.markups ms s)
  end;






(** scanners **)

open Basic_Symbol_Pos;

val err_prefix = "C outer lexical error: ";


(* scan cartouche *)

val scan_cartouche =
  Symbol_Pos.scan_pos --
    ((Symbol_Pos.scan_cartouche err_prefix >> Symbol_Pos.cartouche_content) -- Symbol_Pos.scan_pos);


(* scan space *)

fun space_symbol (s, _) = Symbol.is_blank s andalso s <> "\n";

val scan_space =
  Scan.many1 space_symbol @@@ Scan.optional ($$$ "\n") [] ||
  Scan.many space_symbol @@@ $$$ "\n";


(* scan comment *)

val scan_comment =
  Symbol_Pos.scan_pos -- (Symbol_Pos.scan_comment_body err_prefix -- Symbol_Pos.scan_pos);



(** token sources **)

fun source_proper src = src |> Source.filter is_proper;
fun source_improper src = src |> Source.filter is_improper;

local

fun token_leq ((_, syms1), (_, syms2)) = length syms1 <= length syms2;

fun token k ss =
  Token ((Symbol_Pos.implode ss, Symbol_Pos.range ss), (k, ss));

fun token_range k (pos1, (ss, pos2)) =
  Token (Symbol_Pos.implode_range (pos1, pos2) ss, (k, ss));

val keywords = Scan.make_lexicon (map raw_explode ["setup", "hook", "INVARIANT", "INV", "FNSPEC", "RELSPEC", "MODIFIES", "DONT_TRANSLATE", "AUXUPD", "GHOSTUPD", "SPEC", "END-SPEC", "CALLS", "OWNED_BY"])

val scan_token = Scanner.!!! "bad input"
  (Symbol_Pos.scan_string_qq err_prefix >> token_range Token.String ||
    scan_cartouche >> token_range Token.Cartouche ||
    scan_comment >> token_range Token.Comment ||
    scan_space >> token Token.Space ||
    (Scan.max token_leq
      (Scan.literal keywords >> pair Token.Command)
      (C_Lex.scan_ident >> pair Token.Ident ||
       $$$ ":" >> pair Token.Keyword ||
       Scan.repeats1 ($$$ "+") >> pair Token.Sym_Ident ||
       Scan.repeats1 ($$$ "@") >> pair Token.Sym_Ident ||
       $$$ "[" @@@ $$$ "*" @@@ $$$ "]" >> pair Token.Sym_Ident)) >> uncurry token);

fun recover msg =
  (Scan.one (Symbol.not_eof o Symbol_Pos.symbol) >> single)
  >> (single o token (Token.Error msg));

in

fun source' strict _ =
  let
    val scan_strict = Scan.bulk scan_token;
    val scan = if strict then scan_strict else Scan.recover scan_strict recover;
  in Source.source Symbol_Pos.stopper scan end;

fun source keywords pos src = Symbol_Pos.source pos src |> source' false keywords;
fun source_strict keywords pos src = Symbol_Pos.source pos src |> source' true keywords;


end;


(* explode *)

fun explode keywords pos =
  Symbol.explode #>
  Source.of_list #>
  source keywords pos #>
  Source.exhaust;





(** parsers **)



(* read antiquotation source *)

fun read_no_commands'0 keywords syms =
  Source.of_list syms
  |> source' false (Keyword.no_command_keywords keywords)
  |> source_improper
  |> Source.exhaust

fun read_no_commands' keywords scan syms =
  Source.of_list syms
  |> source' false (Keyword.no_command_keywords keywords)
  |> source_proper
  |> Source.source
       stopper
       (Scan.recover
         (Scan.bulk scan)
         (fn msg =>
           Scan.one (not o is_eof)
           >> (fn tok => [Right
                           let
                             val msg = case is_error' tok of SOME msg0 => msg0 ^ " (" ^ msg ^ ")"
                                                           | NONE => msg
                           in ( msg
                              , [((pos_of tok, Markup.bad ()), msg)]
                              , tok)
                           end])))
  |> Source.exhaust;

fun read_antiq' keywords scan = read_no_commands' keywords (scan >> Left);
end
\<close>

ML\<open>
(*  Title:      Pure/Isar/parse.ML
    Author:     Markus Wenzel, TU Muenchen

Generic parsers for Isabelle/Isar outer syntax.
*)

structure C_Parse =
struct

(** error handling **)

(* group atomic parsers (no cuts!) *)

fun group s scan = scan || Scan.fail_with
  (fn [] => (fn () => s () ^ " expected,\nbut end-of-input was found")
    | tok :: _ =>
        (fn () =>
          (case C_Token.text_of tok of
            (txt, "") =>
              s () ^ " expected,\nbut " ^ txt ^ Position.here (C_Token.pos_of tok) ^
              " was found"
          | (txt1, txt2) =>
              s () ^ " expected,\nbut " ^ txt1 ^ Position.here (C_Token.pos_of tok) ^
              " was found:\n" ^ txt2)));


(* cut *)

fun cut kind scan =
  let
    fun get_pos [] = " (end-of-input)"
      | get_pos (tok :: _) = Position.here (C_Token.pos_of tok);

    fun err (toks, NONE) = (fn () => kind ^ get_pos toks)
      | err (toks, SOME msg) =
          (fn () =>
            let val s = msg () in
              if String.isPrefix kind s then s
              else kind ^ get_pos toks ^ ": " ^ s
            end);
  in Scan.!! err scan end;

fun !!! scan = cut "C outer syntax error" scan;
fun !!!! scan = cut "Corrupted C outer syntax in presentation" scan;

(** basic parsers **)

(* tokens *)

fun RESET_VALUE atom = (*required for all primitive parsers*)
  Scan.ahead (Scan.one (K true)) -- atom >> #2;


val not_eof = RESET_VALUE (Scan.one C_Token.not_eof);

fun input atom = Scan.ahead atom |-- not_eof >> C_Token.input_of;
fun inner_syntax atom = Scan.ahead atom |-- not_eof >> C_Token.inner_syntax_of;

fun kind k =
  group (fn () => Token.str_of_kind k)
    (RESET_VALUE (Scan.one (C_Token.is_kind k) >> C_Token.content_of));

val short_ident = kind Token.Ident;
val long_ident = kind Token.Long_Ident;
val sym_ident = kind Token.Sym_Ident;
val term_var = kind Token.Var;
val type_ident = kind Token.Type_Ident;
val type_var = kind Token.Type_Var;
val number = kind Token.Nat;
val string = kind Token.String;
val verbatim = kind Token.Verbatim;
val cartouche = kind Token.Cartouche;
val eof = kind Token.EOF;



(* names and embedded content *)


val embedded =
  group (fn () => "embedded content")
    (cartouche || string || short_ident || long_ident || sym_ident ||
      term_var || type_ident || type_var || number);

val text = group (fn () => "text") (embedded || verbatim);



(* embedded source text *)

val ML_source = input (group (fn () => "ML source") text);
val antiq_source = input (group (fn () => "Antiquotation source") text);

(* terms *)

val term = group (fn () => "term") (inner_syntax embedded);

end;
\<close>

ML\<open>
(*  Title:      Pure/ML/ml_context.ML
    Author:     Makarius

ML context and antiquotations.
*)

structure C_Context =
struct

(** ML antiquotations **)

datatype 'a antiq_language = Antiq_ML of Antiquote.antiq
                           | Antiq_stack of 'a antiq_stack0
                           | Antiq_HOL of antiq_hol
                           | Antiq_none of C_Lex.token

(* names for generated environment *)

structure Names = Proof_Data
(
  type T = string * Name.context;
  val init_names = ML_Syntax.reserved |> Name.declare "ML_context";
  fun init _ = ("Isabelle0", init_names);
);

fun struct_name ctxt = #1 (Names.get ctxt);
val struct_begin = (Names.map o apfst) (fn _ => "Isabelle" ^ serial_string ());

fun variant a ctxt =
  let
    val names = #2 (Names.get ctxt);
    val (b, names') = Name.variant (Name.desymbolize (SOME false) a) names;
    val ctxt' = (Names.map o apsnd) (K names') ctxt;
  in (b, ctxt') end;


(* decl *)

type decl = Proof.context -> string * string;  (*final context -> ML env, ML body*)

fun value_decl a s ctxt =
  let
    val (b, ctxt') = variant a ctxt;
    val env = "val " ^ b ^ " = " ^ s ^ ";\n";
    val body = struct_name ctxt ^ "." ^ b;
    fun decl (_: Proof.context) = (env, body);
  in (decl, ctxt') end;


(* theory data *)

structure Antiquotations = Theory_Data
(
  type T = (Token.src -> Proof.context -> decl * Proof.context) Name_Space.table;
  val empty : T = Name_Space.empty_table Markup.ML_antiquotationN;
  val extend = I;
  fun merge data : T = Name_Space.merge_tables data;
);

val get_antiquotations = Antiquotations.get o Proof_Context.theory_of;

fun check_antiquotation ctxt =
  #1 o Name_Space.check (Context.Proof ctxt) (get_antiquotations ctxt);

fun add_antiquotation name f thy = thy
  |> Antiquotations.map (Name_Space.define (Context.Theory thy) true (name, f) #> snd);

fun print_antiquotations verbose ctxt =
  Pretty.big_list "ML antiquotations:"
    (map (Pretty.mark_str o #1) (Name_Space.markup_table verbose ctxt (get_antiquotations ctxt)))
  |> Pretty.writeln;

fun apply_antiquotation src ctxt =
  let val (src', f) = Token.check_src ctxt get_antiquotations src
  in f src' ctxt end;


(* parsing and evaluation *)

local

val antiq =
  Parse.!!! ((Parse.token Parse.liberal_name ::: Parse.args) --| Scan.ahead Parse.eof);

fun make_env name visible =
  (ML_Lex.tokenize
    ("structure " ^ name ^ " =\nstruct\n\
     \val ML_context = Context_Position.set_visible " ^ Bool.toString visible ^
     " (Context.the_local_context ());\n"),
   ML_Lex.tokenize "end;");

fun reset_env name = ML_Lex.tokenize ("structure " ^ name ^ " = struct end");

fun eval_antiquotes (ants, pos) opt_context =
  let
    val visible =
      (case opt_context of
        SOME (Context.Proof ctxt) => Context_Position.is_visible ctxt
      | _ => true);
    val opt_ctxt = Option.map Context.proof_of opt_context;

    val ((ml_env, ml_body), opt_ctxt') =
      if forall (fn Antiquote.Text _ => true | _ => false) ants
      then (([], map (fn Antiquote.Text tok => tok) ants), opt_ctxt)
      else
        let
          fun tokenize range = apply2 (ML_Lex.tokenize #> map (ML_Lex.set_range range));

          fun expand_src range src ctxt =
            let val (decl, ctxt') = apply_antiquotation src ctxt
            in (decl #> tokenize range, ctxt') end;

          fun expand (Antiquote.Text tok) ctxt = (K ([], [tok]), ctxt)
            | expand (Antiquote.Control {name, range, body}) ctxt =
                expand_src range
                  (Token.make_src name (if null body then [] else [Token.read_cartouche body])) ctxt
            | expand (Antiquote.Antiq {range, body, ...}) ctxt =
                expand_src range
                  (Token.read_antiq (Thy_Header.get_keywords' ctxt) antiq (body, #1 range)) ctxt;

          val ctxt =
            (case opt_ctxt of
              NONE => error ("No context -- cannot expand ML antiquotations" ^ Position.here pos)
            | SOME ctxt => struct_begin ctxt);

          val (begin_env, end_env) = make_env (struct_name ctxt) visible;
          val (decls, ctxt') = fold_map expand ants ctxt;
          val (ml_env, ml_body) =
            decls |> map (fn decl => decl ctxt') |> split_list |> apply2 flat;
        in ((begin_env @ ml_env @ end_env, ml_body), SOME ctxt') end;
  in ((ml_env, ml_body), opt_ctxt') end;

fun scan_antiq ctxt explicit syms =
  let fun scan_stack is_stack = Scan.optional (Scan.one is_stack >> C_Token.content_of') []
      fun scan_cmd cmd scan =
        Scan.one (fn tok => C_Token.is_command tok andalso C_Token.content_of tok = cmd) |--
        Scan.option (Scan.one C_Token.is_colon) |--
        scan
      fun scan_cmd_hol cmd scan f =
        Scan.trace (Scan.one (fn tok => C_Token.is_command tok andalso C_Token.content_of tok = cmd) |--
                    Scan.option (Scan.one C_Token.is_colon) |--
                    scan)
        >> (I #>> Antiq_HOL o f)
      val scan_ident = Scan.one C_Token.is_ident >> (fn tok => (C_Token.content_of tok, C_Token.pos_of tok))
      val scan_sym_ident_not_stack = Scan.one (fn c => C_Token.is_sym_ident c andalso not (C_Token.is_stack1 c) andalso not (C_Token.is_stack2 c)) >> (fn tok => (C_Token.content_of tok, C_Token.pos_of tok))
      val keywords = Thy_Header.get_keywords' ctxt
  in ( C_Token.read_antiq'
         keywords
         (C_Parse.!!! (   Scan.trace
                            (scan_stack C_Token.is_stack1 --
                             scan_stack C_Token.is_stack2 --
                             scan_cmd "hook" C_Parse.ML_source) >> (I #>> (fn ((stack1, stack2), syms) => Antiq_stack (Hook (stack1, stack2, syms))))
                       || Scan.trace (scan_cmd "setup" C_Parse.ML_source) >> (I #>> (Antiq_stack o Setup))
                       || scan_cmd_hol "INVARIANT" C_Parse.term Invariant
                       || scan_cmd_hol "INV" C_Parse.term Invariant
                       || scan_cmd_hol "FNSPEC" (scan_ident --| Scan.option (Scan.one C_Token.is_colon) -- C_Parse.term) Fnspec
                       || scan_cmd_hol "RELSPEC" C_Parse.term Relspec
                       || scan_cmd_hol "MODIFIES" (Scan.repeat (   scan_sym_ident_not_stack >> pair true
                                                                || scan_ident >> pair false))
                                                  Modifies
                       || scan_cmd_hol "DONT_TRANSLATE" (Scan.succeed ()) (K Dont_translate)
                       || scan_cmd_hol "AUXUPD" C_Parse.term Auxupd
                       || scan_cmd_hol "GHOSTUPD" C_Parse.term Ghostupd
                       || scan_cmd_hol "SPEC" C_Parse.term Spec
                       || scan_cmd_hol "END-SPEC" C_Parse.term End_spec
                       || scan_cmd_hol "CALLS" (Scan.repeat scan_ident) Calls
                       || scan_cmd_hol "OWNED_BY" scan_ident Owned_by
                       || (if explicit
                           then Scan.trace C_Parse.antiq_source >> (I #>> (fn syms => Antiq_ML {start = Position.none, stop = Position.none, range = Input.range_of syms, body = Input.source_explode syms}))
                           else Scan.fail)))
         syms
     , C_Token.read_no_commands'0 keywords syms)
  end

fun print0 s =
  maps
    (fn C_Lex.Token (_, (t as C_Lex.Directive d, _)) =>
        (s ^ @{make_string} t) :: print0 (s ^ "  ") (C_Lex.token_list_of d)
      | C_Lex.Token (_, t) => 
        [case t of (C_Lex.Char _, _) => "Text Char"
                 | (C_Lex.String _, _) => "Text String"
                 | _ => let val t' = @{make_string} (#2 t)
                        in
                          if String.size t' <= 2 then @{make_string} (#1 t)
                          else
                            s ^ @{make_string} (#1 t) ^ " "
                              ^ (String.substring (t', 1, String.size t' - 2)
                                 |> Markup.markup Markup.intensify)
                        end])

val print = tracing o cat_lines o print0 ""

in

fun eval flags pos ants =
  let
    val non_verbose = ML_Compiler.verbose false flags;

    (*prepare source text*)
    val ((env, body), env_ctxt) = eval_antiquotes (ants, pos) (Context.get_generic_context ());
    val _ =
      (case env_ctxt of
        SOME ctxt =>
          if Config.get ctxt ML_Options.source_trace andalso Context_Position.is_visible ctxt
          then tracing (cat_lines [ML_Lex.flatten env, ML_Lex.flatten body])
          else ()
      | NONE => ());

    (*prepare environment*)
    val _ =
      Context.setmp_generic_context
        (Option.map (Context.Proof o Context_Position.set_visible false) env_ctxt)
        (fn () =>
          (ML_Compiler.eval non_verbose Position.none env; Context.get_generic_context ())) ()
      |> (fn NONE => () | SOME context' => Context.>> (ML_Env.inherit context'));

    (*eval body*)
    val _ = ML_Compiler.eval flags pos body;

    (*clear environment*)
    val _ =
      (case (env_ctxt, is_some (Context.get_generic_context ())) of
        (SOME ctxt, true) =>
          let
            val name = struct_name ctxt;
            val _ = ML_Compiler.eval non_verbose Position.none (reset_env name);
            val _ = Context.>> (ML_Env.forget_structure name);
          in () end
      | _ => ());
  in () end;

fun eval'0 env err accept flags pos ants {context, reports} =
  let val ctxt = Context.proof_of context
      val keywords = Thy_Header.get_keywords' ctxt

      val ants =
        maps (fn Left (pos, antiq as {explicit, body, ...}, cts) =>
                 let val (res, l_comm) = scan_antiq ctxt explicit body
                 in 
                   [ Left
                       ( antiq
                       , l_comm
                       , if forall (fn Right _ => true | _ => false) res then
                           let val (l_msg, res) = split_list (map_filter (fn Right (msg, l_report, l_tok) => SOME (msg, (l_report, l_tok)) | _ => NONE) res)
                               val (l_report, l_tok) = split_list res
                           in [(Antiq_none (C_Lex.Token (pos, ((C_Lex.Comment o Right o SOME) (explicit, cat_lines l_msg, if explicit then flat l_report else []), cts))), l_tok)] end
                         else
                           map (fn Left x => x
                                 | Right (msg, l_report, tok) =>
                                     (Antiq_none (C_Lex.Token (C_Token.range_of [tok], ((C_Lex.Comment o Right o SOME) (explicit, msg, l_report), C_Token.content_of tok))), [tok]))
                               res) ]
                 end
               | Right tok => [Right tok])
             ants

      fun map_ants f1 f2 = maps (fn Left x => f1 x | Right tok => f2 tok) ants
      fun map_ants' f1 = map_ants (fn (_, _, l) => maps f1 l) (K [])

      val ants_ml = map_ants' (fn (Antiq_ML a, _) => [Antiquote.Antiq a] | _ => [])
      val ants_stack =
        map_ants (single o Left o maps (fn (Antiq_stack x, _) =>
                                             [map_antiq_stack (fn src => (ML_Lex.read_source false src, Input.range_of src)) x]
                                         | _ => [])
                                o (fn (_, _, l) => l))
                 (single o Right)
      val ants_hol = map_ants (fn (a, _, l) => [Left (a, maps (fn (Antiq_HOL x, _) => [x] | _ => []) l)])
                              (fn C_Lex.Token (pos, (C_Lex.Directive l, _)) => [Right (pos, l)]
                                | _ => [])
      val ants_none = map_ants' (fn (Antiq_none x, _) => [x] | _ => [])

      val _ = Position.reports (Antiquote.antiq_reports ants_ml
                                @ maps (fn Left (_, _, [(Antiq_none _, _)]) => []
                                         | Left ({start, stop, range = (pos, _), ...}, _, _) =>
                                            (case stop of SOME stop => cons (stop, Markup.antiquote)
                                                        | NONE => I)
                                              [(start, Markup.antiquote),
                                               (pos, Markup.language_antiquotation)]
                                         | _ => [])
                                       ants);
      val _ = Position.reports_text (maps C_Lex.token_report ants_none
                                     @ maps (fn Left (_, _, [(Antiq_none _, _)]) => []
                                              | Left (_, l, ls) =>
                                                  maps (maps (C_Token.reports keywords)) (l :: map #2 ls)
                                              | _ => [])
                                            ants);
      val _ = C_Lex.check ants_none;

      val _ = ML_Context.eval (ML_Compiler.verbose false flags)
                              pos
                              (case ML_Lex.read "(,)" of [par_l, colon, par_r, space] =>
                                                           par_l ::
                                                           (ants_ml
                                                           |> separate colon)
                                                           @ [par_r, space]
                                                       | _ => [])
      val () = if Config.get ctxt C_Options.lexer_trace andalso Context_Position.is_visible ctxt
               then print (map_filter (fn Right x => SOME x | _ => NONE) ants_stack)
               else ()
  in P.parse env (err ants_hol) (accept ants_hol) ants_stack {context = context, reports = reports} end

fun eval' env err accept flags pos ants =
  Context.>> (C_Env.empty_env_tree
              #> eval'0 env err accept flags pos ants
              #> (fn {context, reports} =>
                   let val _ = Position.reports_text reports
                   in context end))

end;

fun eval_source env err accept flags source =
  eval' env err accept flags (Input.pos_of source) (C_Lex.read_source source);

fun eval_source' env err accept flags source =
  eval'0 env err accept flags (Input.pos_of source) (C_Lex.read_source source);

end
\<close>

end
