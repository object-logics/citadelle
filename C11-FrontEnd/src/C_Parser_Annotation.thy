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

theory C_Parser_Annotation
  imports C_Environment
begin

section \<open>The Construction of an C-Context (analogously to the standard ML context)\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/Isar/keyword.ML\<close>\<close> \<open>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      Pure/Isar/keyword.ML
    Author:     Makarius

Isar keyword classification.
*)

structure C_Keyword =
struct
val before_command = "before_command";
val quasi_command = "quasi_command";


type entry =
 {pos: Position.T,
  id: serial,
  kind: string,
  files: string list,  (*extensions of embedded files*)
  tags: string list};

fun check_spec pos ((kind, files), tags) : entry =
  {pos = pos, id = serial (), kind = kind, files = files, tags = tags};


(** keyword tables **)

(* type keywords *)

datatype keywords = Keywords of
 {minor: Scan.lexicon,
  major: Scan.lexicon,
  commands: entry Symtab.table};

fun minor_keywords (Keywords {minor, ...}) = minor;
fun major_keywords (Keywords {major, ...}) = major;

fun make_keywords (minor, major, commands) =
  Keywords {minor = minor, major = major, commands = commands};

fun map_keywords f (Keywords {minor, major, commands}) =
  make_keywords (f (minor, major, commands));



(* build keywords *)

val empty_keywords =
  make_keywords (Scan.empty_lexicon, Scan.empty_lexicon, Symtab.empty);

fun empty_keywords' minor =
  make_keywords (minor, Scan.empty_lexicon, Symtab.empty);

fun merge_keywords
  (Keywords {minor = minor1, major = major1, commands = commands1},
    Keywords {minor = minor2, major = major2, commands = commands2}) =
  make_keywords
   (Scan.merge_lexicons (minor1, minor2),
    Scan.merge_lexicons (major1, major2),
    Symtab.merge (K true) (commands1, commands2));

val add_keywords =
  fold (fn ((name, pos), spec as ((kind, _), _)) => map_keywords (fn (minor, major, commands) =>
    if kind = "" orelse kind = before_command orelse kind = quasi_command then
      let
        val minor' = Scan.extend_lexicon (Symbol.explode name) minor;
      in (minor', major, commands) end
    else
      let
        val entry = check_spec pos spec;
        val major' = Scan.extend_lexicon (Symbol.explode name) major;
        val commands' = Symtab.update (name, entry) commands;
      in (minor, major', commands') end));


(* keyword status *)

fun is_command (Keywords {commands, ...}) = Symtab.defined commands;


(* command keywords *)

fun lookup_command (Keywords {commands, ...}) = Symtab.lookup commands;

fun command_markup keywords name =
  lookup_command keywords name
  |> Option.map (fn {pos, id, ...} =>
      Markup.properties (Position.entity_properties_of false id pos)
        (Markup.entity Markup.command_keywordN name));
end
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/Isar/token.ML\<close>\<close> \<open>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      Pure/Isar/token.ML
    Author:     Markus Wenzel, TU Muenchen

Outer token syntax for Isabelle/Isar.
*)

structure C_Token =
struct

(** tokens **)

(* token kind *)


val delimited_kind =
  (fn Token.String => true
    | Token.Alt_String => true
    | Token.Verbatim => true
    | Token.Cartouche => true
    | Token.Comment _ => true
    | _ => false);


(* datatype token *)

(*The value slot assigns an (optional) internal value to a token,
  usually as a side-effect of special scanner setup (see also
  args.ML).  Note that an assignable ref designates an intermediate
  state of internalization -- it is NOT meant to persist.*)

datatype T = Token of (Symbol_Pos.text * Position.range) * (Token.kind * string) * slot

and slot =
  Slot |
  Value of value option |
  Assignable of value option Unsynchronized.ref

and value =
  Source of T list |
  Literal of bool * Markup.T |
  Name of Token.name_value * morphism |
  Typ of typ |
  Term of term |
  Fact of string option * thm list |  (*optional name for dynamic fact, i.e. fact "variable"*)
  Attribute of morphism -> attribute |
  Declaration of declaration |
  Files of Token.file Exn.result list;

type src = T list;


(* position *)

fun pos_of (Token ((_, (pos, _)), _, _)) = pos;
fun end_pos_of (Token ((_, (_, pos)), _, _)) = pos;

fun range_of (toks as tok :: _) =
      let val pos' = end_pos_of (List.last toks)
      in Position.range (pos_of tok, pos') end
  | range_of [] = Position.no_range;



(* stopper *)

fun mk_eof pos = Token (("", (pos, Position.none)), (Token.EOF, ""), Slot);
val eof = mk_eof Position.none;

fun is_eof (Token (_, (Token.EOF, _), _)) = true
  | is_eof _ = false;

val not_eof = not o is_eof;

val stopper =
  Scan.stopper (fn [] => eof | toks => mk_eof (end_pos_of (List.last toks))) is_eof;


(* kind of token *)

fun kind_of (Token (_, (k, _), _)) = k;
fun is_kind k (Token (_, (k', _), _)) = k = k';

val is_command = is_kind Token.Command;

fun keyword_with pred (Token (_, (Token.Keyword, x), _)) = pred x
  | keyword_with _ _ = false;

fun ident_with pred (Token (_, (Token.Ident, x), _)) = pred x
  | ident_with _ _ = false;

val is_ident = is_kind Token.Ident;
val is_sym_ident = is_kind Token.Sym_Ident;

fun content_of (Token (_, (_, x), _)) = x;
fun content_of' (Token (_, (_, _), Value (SOME (Source l)))) = map (fn Token ((_, (pos, _)), (_, x), _) => (x, pos)) l
  | content_of' _ = [];

val is_stack1 = fn Token (_, (Token.Sym_Ident, _), Value (SOME (Source l))) => forall (fn tok => content_of tok = "+") l
                 | _ => false;

val is_stack2 = fn Token (_, (Token.Sym_Ident, _), Value (SOME (Source l))) => forall (fn tok => content_of tok = "@") l
                 | _ => false;

val is_stack3 = fn Token (_, (Token.Sym_Ident, _), Value (SOME (Source l))) => forall (fn tok => content_of tok = "&") l
                 | _ => false;

val is_modifies_star = fn Token (_, (Token.Sym_Ident, _), Value (SOME (Source l))) => String.concat (map content_of l) = "[*]"
                        | _ => false;

val is_colon = fn Token (_, (Token.Keyword, _), Value (SOME (Source l))) => String.concat (map content_of l) = ":"
                | _ => false;

fun is_proper (Token (_, (Token.Space, _), _)) = false
  | is_proper (Token (_, (Token.Comment _, _), _)) = false
  | is_proper _ = true;

val is_improper = not o is_proper;

fun is_error' (Token (_, (Token.Error msg, _), _)) = SOME msg
  | is_error' _ = NONE;

(* blanks and newlines -- space tokens obey lines *)



(* token content *)

fun source_of (Token ((source, _), _, _)) = source;

fun input_of (Token ((source, range), (kind, _), _)) =
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
  | Token.Comment _ => (Markup.ML_comment, "")
  | Token.Error msg => (Markup.bad (), msg)
  | _ => (Markup.empty, "");

fun keyword_reports tok = map (fn markup => ((pos_of tok, markup), ""));

fun command_markups _ _ =
    [Markup.keyword1]
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
  else if is_stack1 tok orelse is_stack2 tok orelse is_stack3 tok then
    keyword_reports tok [Markup.keyword2 |> Markup.keyword_properties]
  else if is_kind Token.Keyword tok then
    keyword_reports tok
      [keyword_markup (false, Markup.keyword2 |> Markup.keyword_properties) (content_of tok)]
  else
    let
      val pos = pos_of tok;
      val (m, text) = token_kind_markup (kind_of tok);
      val delete = #2 (Symbol_Pos.explode_delete (source_of tok, pos));
    in ((pos, m), text) :: map (fn p => ((p, Markup.delete), "")) delete end;

fun markups keywords = map (#2 o #1) o reports keywords;

end;


(* unparse *)

fun unparse (Token (_, (kind, x), _)) =
  (case kind of
    Token.String => Symbol_Pos.quote_string_qq x
  | Token.Alt_String => Symbol_Pos.quote_string_bq x
  | Token.Verbatim => enclose "{*" "*}" x
  | Token.Cartouche => cartouche x
  | Token.Comment NONE => enclose "(*" "*)" x
  | Token.EOF => ""
  | _ => x);

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



(** associated values **)

(* inlined file content *)



(* access values *)



(* reports of value *)



(* name value *)



(* maxidx *)



(* fact values *)



(* transform *)



(* static binding *)

(*1st stage: initialize assignable slots*)
fun init_assignable tok =
  (case tok of
    Token (x, y, Slot) => Token (x, y, Assignable (Unsynchronized.ref NONE))
  | Token (_, _, Value _) => tok
  | Token (_, _, Assignable r) => (r := NONE; tok));

(*2nd stage: assign values as side-effect of scanning*)
fun assign v tok =
  (case tok of
    Token (x, y, Slot) => Token (x, y, Value v)
  | Token (_, _, Value _) => tok
  | Token (_, _, Assignable r) => (r := v; tok));

fun evaluate mk eval arg =
  let val x = eval arg in (assign (SOME (mk x)) arg; x) end;

(*3rd stage: static closure of final values*)
fun closure (Token (x, y, Assignable (Unsynchronized.ref v))) = Token (x, y, Value v)
  | closure tok = tok;


(* pretty *)



(* src *)







(** scanners **)

open Basic_Symbol_Pos;

val err_prefix = "Annotation lexical error: ";

val !!! = C_Scan.!!!;


(* scan stack *)

fun scan_stack is_stack = Scan.optional (Scan.one is_stack >> content_of') []


(* scan symbolic idents *)

val scan_symid =
  Scan.many1 (Symbol.is_symbolic_char o Symbol_Pos.symbol) ||
  Scan.one (Symbol.is_symbolic o Symbol_Pos.symbol) >> single;

fun is_symid str =
  (case try Symbol.explode str of
    SOME [s] => Symbol.is_symbolic s orelse Symbol.is_symbolic_char s
  | SOME ss => forall Symbol.is_symbolic_char ss
  | _ => false);

fun ident_or_symbolic "begin" = false
  | ident_or_symbolic ":" = true
  | ident_or_symbolic "::" = true
  | ident_or_symbolic s = Symbol_Pos.is_identifier s orelse is_symid s;


(* scan verbatim text *)

val scan_verb =
  $$$ "*" --| Scan.ahead (~$$ "}") ||
  Scan.one (fn (s, _) => s <> "*" andalso Symbol.not_eof s) >> single;

val scan_verbatim =
  Scan.ahead ($$ "{" -- $$ "*") |--
    !!! "unclosed verbatim text"
      ((Symbol_Pos.scan_pos --| $$ "{" --| $$ "*") --
        (Scan.repeats scan_verb -- ($$ "*" |-- $$ "}" |-- Symbol_Pos.scan_pos)));

val recover_verbatim =
  $$$ "{" @@@ $$$ "*" @@@ Scan.repeats scan_verb;


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
  Token ((Symbol_Pos.implode ss, Symbol_Pos.range ss), (k, Symbol_Pos.content ss), Slot);

fun token' (mk_value, k) ss =
  if mk_value then
    Token ( (Symbol_Pos.implode ss, Symbol_Pos.range ss)
          , (k, Symbol_Pos.content ss)
          , Value (SOME (Source (map (fn (s, pos) => Token (("", (pos, Position.none)), (k, s), Slot)) ss))))
  else
    token k ss;

fun token_range k (pos1, (ss, pos2)) =
  Token (Symbol_Pos.implode_range (pos1, pos2) ss, (k, Symbol_Pos.content ss), Slot);

fun pair_f x = pair (false, x)
fun pair_t x = pair (true, x)

fun scan_token keywords = !!! "bad input"
  (Symbol_Pos.scan_string_qq err_prefix >> token_range Token.String ||
    Symbol_Pos.scan_string_bq err_prefix >> token_range Token.Alt_String ||
    scan_verbatim >> token_range Token.Verbatim ||
    scan_cartouche >> token_range Token.Cartouche ||
    scan_comment >> token_range (Token.Comment NONE) ||
    Comment.scan >> (fn (k, ss) => token (Token.Comment (SOME k)) ss) ||
    scan_space >> token Token.Space ||
    (Scan.repeats1 ($$$ "+") >> pair_t Token.Sym_Ident ||
      Scan.repeats1 ($$$ "@") >> pair_t Token.Sym_Ident ||
      Scan.repeats1 ($$$ "&") >> pair_t Token.Sym_Ident ||
      Scan.max token_leq
        (Scan.max token_leq
          (Scan.literal (C_Keyword.major_keywords keywords) >> pair_f Token.Command)
          ($$$ ":" >> pair_t Token.Keyword ||
           Scan.literal (C_Keyword.minor_keywords keywords) >> pair_f Token.Keyword))
        (Lexicon.scan_longid >> pair_f Token.Long_Ident ||
          C_Lex.scan_ident >> pair_f Token.Ident ||
          Lexicon.scan_id >> pair_f Token.Ident ||
          Lexicon.scan_var >> pair_f Token.Var ||
          Lexicon.scan_tid >> pair_f Token.Type_Ident ||
          Lexicon.scan_tvar >> pair_f Token.Type_Var ||
          Symbol_Pos.scan_float >> pair_f Token.Float ||
          Symbol_Pos.scan_nat >> pair_f Token.Nat ||
          $$$ "[" @@@ $$$ "*" @@@ $$$ "]" >> pair_t Token.Sym_Ident ||
          scan_symid >> pair_f Token.Sym_Ident)) >> uncurry token');

fun recover msg =
  (Scan.one (Symbol.not_eof o Symbol_Pos.symbol) >> single)
  >> (single o token (Token.Error msg));

in

fun make_source keywords {strict} =
  let
    val scan_strict = Scan.bulk (scan_token keywords);
    val scan = if strict then scan_strict else Scan.recover scan_strict recover;
  in Source.source Symbol_Pos.stopper scan end;


end;


(* explode *)

fun tokenize keywords strict syms =
  Source.of_list syms |> make_source keywords strict |> Source.exhaust;

fun explode keywords pos text =
  Symbol_Pos.explode (text, pos) |> tokenize keywords {strict = false};

fun explode0 keywords = explode keywords Position.none;


(* print name in parsable form *)



(* make *)




(** parsers **)

type 'a parser = T list -> 'a * T list;
type 'a context_parser = Context.generic * T list -> 'a * (Context.generic * T list);


(* read body -- e.g. antiquotation source *)

fun read_with_commands'0 keywords syms =
  Source.of_list syms
  |> make_source keywords {strict = false}
  |> source_improper
  |> Source.exhaust

fun read_with_commands' keywords scan syms =
  Source.of_list syms
  |> make_source keywords {strict = false}
  |> source_proper
  |> Source.source
       stopper
       (Scan.recover
         (Scan.bulk scan)
         (fn msg =>
           Scan.one (not o is_eof)
           >> (fn tok => [C_Scan.Right
                           let
                             val msg = case is_error' tok of SOME msg0 => msg0 ^ " (" ^ msg ^ ")"
                                                           | NONE => msg
                           in ( msg
                              , [((pos_of tok, Markup.bad ()), msg)]
                              , tok)
                           end])))
  |> Source.exhaust;

fun read_antiq' keywords scan = read_with_commands' keywords (scan >> C_Scan.Left);

(* wrapped syntax *)

end;

type 'a c_parser = 'a C_Token.parser;
type 'a c_context_parser = 'a C_Token.context_parser;
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/Isar/parse.ML\<close>\<close> \<open>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      Pure/Isar/parse.ML
    Author:     Markus Wenzel, TU Muenchen

Generic parsers for Isabelle/Isar outer syntax.
*)

signature C_PARSE =
sig
  type T
  type 'a parser = T list -> 'a * T list
(**)
  val C_source: Input.source parser
(**)
  val group: (unit -> string) -> (T list -> 'a) -> T list -> 'a
  val !!! : (T list -> 'a) -> T list -> 'a
  val !!!! : (T list -> 'a) -> T list -> 'a
  val not_eof: T parser (*
  val token: 'a parser -> T parser *)
  val range: 'a parser -> ('a * Position.range) parser
  val position: 'a parser -> ('a * Position.T) parser
  val input: 'a parser -> Input.source parser
  val inner_syntax: 'a parser -> string parser
  val command: string parser (*
  val keyword: string parser *)
  val short_ident: string parser
  val long_ident: string parser
  val sym_ident: string parser (*
  val dots: string parser
  val minus: string parser *)
  val term_var: string parser
  val type_ident: string parser
  val type_var: string parser
  val number: string parser (*
  val float_number: string parser *)
  val string: string parser (*
  val alt_string: string parser *)
  val verbatim: string parser
  val cartouche: string parser
  val eof: string parser (*
  val command_name: string -> string parser *)
  val keyword_with: (string -> bool) -> string parser
  val keyword_markup: bool * Markup.T -> string -> string parser
  val keyword_improper: string -> string parser
  val $$$ : string -> string parser
  val reserved: string -> string parser (*
  val underscore: string parser
  val maybe: 'a parser -> 'a option parser
  val tag_name: string parser
  val tags: string list parser
  val opt_keyword: string -> bool parser
  val opt_bang: bool parser
  val begin: string parser
  val opt_begin: bool parser *)
  val nat: int parser (*
  val int: int parser
  val real: real parser
  val enum_positions: string -> 'a parser -> ('a list * Position.T list) parser
  val enum1_positions: string -> 'a parser -> ('a list * Position.T list) parser *)
  val enum: string -> 'a parser -> 'a list parser
  val enum1: string -> 'a parser -> 'a list parser (*
  val and_list: 'a parser -> 'a list parser
  val and_list1: 'a parser -> 'a list parser
  val enum': string -> 'a context_parser -> 'a list context_parser
  val enum1': string -> 'a context_parser -> 'a list context_parser
  val and_list': 'a context_parser -> 'a list context_parser
  val and_list1': 'a context_parser -> 'a list context_parser *)
  val list: 'a parser -> 'a list parser (*
  val list1: 'a parser -> 'a list parser
  val properties: Properties.T parser *)
  val name: string parser
  val binding: binding parser
  val embedded: string parser
  val text: string parser (*
  val path: string parser
  val session_name: string parser
  val theory_name: string parser
  val liberal_name: string parser
  val parname: string parser
  val parbinding: binding parser
  val class: string parser
  val sort: string parser
  val type_const: string parser
  val arity: (string * string list * string) parser
  val multi_arity: (string list * string list * string) parser
  val type_args: string list parser
  val type_args_constrained: (string * string option) list parser
  val typ: string parser
  val mixfix: mixfix parser
  val mixfix': mixfix parser
  val opt_mixfix: mixfix parser
  val opt_mixfix': mixfix parser
  val syntax_mode: Syntax.mode parser
  val where_: string parser
  val const_decl: (string * string * mixfix) parser
  val const_binding: (binding * string * mixfix) parser
  val params: (binding * string option * mixfix) list parser
  val vars: (binding * string option * mixfix) list parser
  val for_fixes: (binding * string option * mixfix) list parser *)
  val ML_source: Input.source parser (*
  val document_source: Input.source parser
  val const: string parser *)
  val term: string parser (*
  val prop: string parser
  val literal_fact: string parser
  val propp: (string * string list) parser
  val termp: (string * string list) parser
  val private: Position.T parser
  val qualified: Position.T parser
  val target: (string * Position.T) parser
  val opt_target: (string * Position.T) option parser
  val args: T list parser
  val args1: (string -> bool) -> T list parser
  val attribs: Token.src list parser
  val opt_attribs: Token.src list parser
  val thm_sel: Facts.interval list parser
  val thm: (Facts.ref * Token.src list) parser
  val thms1: (Facts.ref * Token.src list) list parser
  val option_name: string parser
  val option_value: string parser
  val options: ((string * Position.T) * (string * Position.T)) list parser *)
end;

structure C_Parse: C_PARSE =
struct
type T = C_Token.T
type 'a parser = T list -> 'a * T list
structure Token =
struct
  open Token
  open C_Token
end

(** error handling **)

(* group atomic parsers (no cuts!) *)

fun group s scan = scan || Scan.fail_with
  (fn [] => (fn () => s () ^ " expected,\nbut end-of-input was found")
    | tok :: _ =>
        (fn () =>
          (case Token.text_of tok of
            (txt, "") =>
              s () ^ " expected,\nbut " ^ txt ^ Position.here (Token.pos_of tok) ^
              " was found"
          | (txt1, txt2) =>
              s () ^ " expected,\nbut " ^ txt1 ^ Position.here (Token.pos_of tok) ^
              " was found:\n" ^ txt2)));


(* cut *)

fun cut kind scan =
  let
    fun get_pos [] = " (end-of-input)"
      | get_pos (tok :: _) = Position.here (Token.pos_of tok);

    fun err (toks, NONE) = (fn () => kind ^ get_pos toks)
      | err (toks, SOME msg) =
          (fn () =>
            let val s = msg () in
              if String.isPrefix kind s then s
              else kind ^ get_pos toks ^ ": " ^ s
            end);
  in Scan.!! err scan end;

fun !!! scan = cut "Annotation syntax error" scan;
fun !!!! scan = cut "Corrupted annotation syntax in presentation" scan;



(** basic parsers **)

(* tokens *)

fun RESET_VALUE atom = (*required for all primitive parsers*)
  Scan.ahead (Scan.one (K true)) -- atom >> (fn (arg, x) => (Token.assign NONE arg; x));


val not_eof = RESET_VALUE (Scan.one Token.not_eof);


fun range scan = (Scan.ahead not_eof >> (Token.range_of o single)) -- scan >> Library.swap;
fun position scan = (Scan.ahead not_eof >> Token.pos_of) -- scan >> Library.swap;
fun input atom = Scan.ahead atom |-- not_eof >> Token.input_of;
fun inner_syntax atom = Scan.ahead atom |-- not_eof >> Token.inner_syntax_of;

fun kind k =
  group (fn () => Token.str_of_kind k)
    (RESET_VALUE (Scan.one (Token.is_kind k) >> Token.content_of));

val command = kind Token.Command;
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


fun keyword_with pred = RESET_VALUE (Scan.one (Token.keyword_with pred) >> Token.content_of);

fun keyword_markup markup x =
  group (fn () => Token.str_of_kind Token.Keyword ^ " " ^ quote x)
    (Scan.ahead not_eof -- keyword_with (fn y => x = y))
  >> (fn (tok, x) => (Token.assign (SOME (Token.Literal markup)) tok; x));

val keyword_improper = keyword_markup (true, Markup.improper);
val $$$ = keyword_markup (false, Markup.quasi_keyword);

fun reserved x =
  group (fn () => "reserved identifier " ^ quote x)
    (RESET_VALUE (Scan.one (Token.ident_with (fn y => x = y)) >> Token.content_of));


val nat = number >> (#1 o Library.read_int o Symbol.explode);


(* enumerations *)


fun enum1 sep scan = scan ::: Scan.repeat ($$$ sep |-- !!! scan);
fun enum sep scan = enum1 sep scan || Scan.succeed [];

fun list scan = enum "," scan;


(* names and embedded content *)

val name =
  group (fn () => "name")
    (short_ident || long_ident || sym_ident || number || string);

val binding = position name >> Binding.make;

val embedded =
  group (fn () => "embedded content")
    (cartouche || string || short_ident || long_ident || sym_ident ||
      term_var || type_ident || type_var || number);

val text = group (fn () => "text") (embedded || verbatim);






(* type classes *)







(* types *)





(* mixfix annotations *)















(* syntax mode *)



(* fixes *)







(* embedded source text *)

val ML_source = input (group (fn () => "ML source") text);


(* terms *)

val term = group (fn () => "term") (inner_syntax embedded);


(* patterns *)



(* target information *)



(* arguments within outer syntax *)









(* attributes *)



(* theorem references *)





(* options *)




(**)

val C_source = input (group (fn () => "C source") text);
end;
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/Thy/thy_header.ML\<close>\<close> \<open>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      Pure/Thy/thy_header.ML
    Author:     Makarius

Static theory header information.
*)

structure C_Thy_Header =
struct
val bootstrap_keywords =
  C_Keyword.empty_keywords' (Keyword.minor_keywords (Thy_Header.get_keywords @{theory}))

(* theory data *)

structure Data = Theory_Data
(
  type T = C_Keyword.keywords;
  val empty = bootstrap_keywords;
  val extend = I;
  val merge = C_Keyword.merge_keywords;
);

val add_keywords = Data.map o C_Keyword.add_keywords;

val get_keywords = Data.get;
val get_keywords' = get_keywords o Proof_Context.theory_of;

end
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/Isar/outer_syntax.ML\<close>\<close> \<open>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      Pure/Isar/outer_syntax.ML
    Author:     Markus Wenzel, TU Muenchen

Isabelle/Isar outer syntax.
*)

structure C_Annotation  =
struct

(** outer syntax **)

(* errors *)

fun err_command msg name ps =
  error (msg ^ quote (Markup.markup Markup.keyword1 name) ^ Position.here_list ps);

fun err_dup_command name ps =
  err_command "Duplicate annotation syntax command " name ps;


(* command parsers *)

datatype command_parser =
  Parser of Symbol_Pos.T list * (bool * Symbol_Pos.T list) -> C_Transition.eval_time c_parser;

datatype command = Command of
 {comment: string,
  command_parser: command_parser,
  pos: Position.T,
  id: serial};

fun eq_command (Command {id = id1, ...}, Command {id = id2, ...}) = id1 = id2;

fun new_command comment command_parser pos =
  Command {comment = comment, command_parser = command_parser, pos = pos, id = serial ()};

fun command_pos (Command {pos, ...}) = pos;

fun command_markup def (name, Command {pos, id, ...}) =
  Markup.properties (Position.entity_properties_of def id pos)
    (Markup.entity Markup.commandN name);



(* theory data *)

structure Data = Theory_Data
(
  type T = command Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data : T =
    data |> Symtab.join (fn name => fn (cmd1, cmd2) =>
      if eq_command (cmd1, cmd2) then raise Symtab.SAME
      else err_dup_command name [command_pos cmd1, command_pos cmd2]);
);

val get_commands = Data.get;
val dest_commands = get_commands #> Symtab.dest #> sort_by #1;
val lookup_commands = Symtab.lookup o get_commands;


(* maintain commands *)

fun add_command name cmd thy =
    let
      val _ =
        C_Keyword.is_command (C_Thy_Header.get_keywords thy) name orelse
          err_command "Undeclared outer syntax command " name [command_pos cmd];
      val _ =
        (case lookup_commands thy name of
          NONE => ()
        | SOME cmd' => err_dup_command name [command_pos cmd, command_pos cmd']);
      val _ =
        Context_Position.report_generic (Context.the_generic_context ())
          (command_pos cmd) (command_markup true (name, cmd));
    in Data.map (Symtab.update (name, cmd)) thy end;

fun delete_command (name, pos) thy =
    let
      val _ =
        C_Keyword.is_command (C_Thy_Header.get_keywords thy) name orelse
          err_command "Undeclared outer syntax command " name [pos];
    in Data.map (Symtab.delete name) thy end;


(* implicit theory setup *)

type command_keyword = string * Position.T;

fun raw_command0 (name, pos) comment command_parser =
  C_Thy_Header.add_keywords [((name, pos), ((Keyword.thy_decl, []), [name]))]
  #> add_command name (new_command comment command_parser pos);

fun raw_command (name, pos) comment command_parser =
  let val setup = add_command name (new_command comment command_parser pos)
  in Context.>> (Context.mapping setup (Local_Theory.background_theory setup)) end;

fun command (name, pos) comment parse =
  raw_command (name, pos) comment (Parser parse);

fun command' (name, pos) comment parse =
  raw_command0 (name, pos) comment (Parser parse);



(** toplevel parsing **)

(* parse commands *)

local
fun scan_stack' f b = Scan.one f >> (pair b o C_Token.content_of')
in
val before_command =
  C_Token.scan_stack C_Token.is_stack1
  -- Scan.optional (   scan_stack' C_Token.is_stack2 false
                    || scan_stack' C_Token.is_stack3 true)
                   (pair false [])
end

fun parse_command thy =
  Scan.ahead (before_command |-- C_Parse.position C_Parse.command) :|-- (fn (name, pos) =>
    let val command_tags = before_command --| C_Parse.command;
    in
      case lookup_commands thy name of
        SOME (cmd as Command {command_parser = Parser parse, ...}) =>
          C_Parse.!!! (command_tags :|-- parse)
          >> (pair [((pos, command_markup false (name, cmd)), "")])
      | NONE =>
          Scan.fail_with (fn _ => fn _ =>
            let
              val msg = "undefined command ";
            in msg ^ quote (Markup.markup Markup.keyword1 name) end)
    end)
end
\<close>

end
