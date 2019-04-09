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

theory C_Annotation
  imports C_Parser
begin

section \<open>The Construction of an C-Context (analogously to the standard ML context)\<close>

ML\<open>
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

fun major_keywords (Keywords {major, ...}) = major;

fun make_keywords (minor, major, commands) =
  Keywords {minor = minor, major = major, commands = commands};

fun map_keywords f (Keywords {minor, major, commands}) =
  make_keywords (f (minor, major, commands));



(* build keywords *)

val empty_keywords =
  make_keywords (Scan.empty_lexicon, Scan.empty_lexicon, Symtab.empty);

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

ML\<open>
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

val is_stack3 = fn Token (_, (Token.Sym_Ident, l)) => forall (fn (s, _) => s = "&") l
                 | _ => false;

val is_modifies_star = fn Token (_, (Token.Sym_Ident, l)) => Symbol_Pos.content l = "[*]"
                        | _ => false;

val is_colon = fn Token (_, (Token.Keyword, [(":", _)])) => true
                | _ => false;

fun is_proper (Token (_, (Token.Space, _))) = false
  | is_proper (Token (_, (Token.Comment _, _))) = false
  | is_proper _ = true;

val is_improper = not o is_proper;

fun is_error' (Token (_, (Token.Error msg, _))) = SOME msg
  | is_error' _ = NONE;


(* token content *)

fun content_of (Token (_, (_, x))) = Symbol_Pos.content x;
fun content_of' (Token (_, (_, x))) = x;
fun source_of (Token ((source, _), _)) = source;

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

fun unparse (Token (_, (kind, x))) =
  let val x = Symbol_Pos.content x
  in case kind of
    Token.String => Symbol_Pos.quote_string_qq x
  | Token.Alt_String => Symbol_Pos.quote_string_bq x
  | Token.Verbatim => enclose "{*" "*}" x
  | Token.Cartouche => cartouche x
  | Token.Comment NONE => enclose "(*" "*)" x
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

fun scan_stack is_stack = Scan.optional (Scan.one is_stack >> content_of') []

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

fun scan_token keywords = Scanner.!!! "bad input"
  (Symbol_Pos.scan_string_qq err_prefix >> token_range Token.String ||
    scan_cartouche >> token_range Token.Cartouche ||
    scan_comment >> token_range (Token.Comment NONE) ||
    Comment.scan >> (fn (k, ss) => token (Token.Comment (SOME k)) ss) ||
    scan_space >> token Token.Space ||
    (Scan.max token_leq
      (Scan.literal (C_Keyword.major_keywords keywords) >> pair Token.Command)
      (C_Lex.scan_ident >> pair Token.Ident ||
       $$$ ":" >> pair Token.Keyword ||
       Scan.repeats1 ($$$ "+") >> pair Token.Sym_Ident ||
       Scan.repeats1 ($$$ "@") >> pair Token.Sym_Ident ||
       Scan.repeats1 ($$$ "&") >> pair Token.Sym_Ident ||
       $$$ "[" @@@ $$$ "*" @@@ $$$ "]" >> pair Token.Sym_Ident)) >> uncurry token);

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





(** parsers **)

type 'a parser = T list -> 'a * T list;
type 'a context_parser = Context.generic * T list -> 'a * (Context.generic * T list);


(* read antiquotation source *)

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
           >> (fn tok => [Right
                           let
                             val msg = case is_error' tok of SOME msg0 => msg0 ^ " (" ^ msg ^ ")"
                                                           | NONE => msg
                           in ( msg
                              , [((pos_of tok, Markup.bad ()), msg)]
                              , tok)
                           end])))
  |> Source.exhaust;

fun read_antiq' keywords scan = read_with_commands' keywords (scan >> Left);
end

type 'a c_parser = 'a C_Token.parser;
type 'a c_context_parser = 'a C_Token.context_parser;
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

fun range scan = (Scan.ahead not_eof >> (C_Token.range_of o single)) -- scan >> Library.swap;
fun position scan = (Scan.ahead not_eof >> C_Token.pos_of) -- scan >> Library.swap;
fun input atom = Scan.ahead atom |-- not_eof >> C_Token.input_of;
fun inner_syntax atom = Scan.ahead atom |-- not_eof >> C_Token.inner_syntax_of;

fun kind k =
  group (fn () => Token.str_of_kind k)
    (RESET_VALUE (Scan.one (C_Token.is_kind k) >> C_Token.content_of));

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



(* names and embedded content *)


val embedded =
  group (fn () => "embedded content")
    (cartouche || string || short_ident || long_ident || sym_ident ||
      term_var || type_ident || type_var || number);

val text = group (fn () => "text") (embedded || verbatim);



(* embedded source text *)

val ML_source = input (group (fn () => "ML source") text);

(* terms *)

val term = group (fn () => "term") (inner_syntax embedded);

end;
\<close>

ML\<open>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      Pure/Thy/thy_header.ML
    Author:     Makarius

Static theory header information.
*)

structure C_Thy_Header =
struct
val bootstrap_keywords = C_Keyword.empty_keywords

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

ML\<open>
(*  Title:      Pure/Isar/outer_syntax.ML
    Author:     Frederic Tuong, Univ. Paris-Saclay
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
  err_command "Duplicate C outer syntax command " name ps;


(* command parsers *)

datatype command_parser =
  Parser of Symbol_Pos.T list * (bool * Symbol_Pos.T list) -> eval_time c_parser;

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

ML\<open>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      Pure/ML/ml_context.ML
    Author:     Makarius

ML context and antiquotations.
*)

structure C_Context =
struct

(** ML antiquotations **)


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

type env_direct = env_directives * C_Env.env_tree

structure Directives = Generic_Data
  (type T = (Position.T list
             * serial
             * (C_Lex.token_kind_directive
                -> env_direct
                -> int option (* result path of conditional directive to choose *)
                   * antiq_language list (* nested annotations from the input *)
                   * env_direct (*NOTE: remove the possibility of returning a too modified env?*)))
            Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = #2);

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

fun scan_antiq context syms =
  let val keywords = C_Thy_Header.get_keywords' (Context.proof_of context)
  in ( C_Token.read_antiq'
         keywords
         (C_Parse.!!! (Scan.trace (C_Annotation.parse_command (Context.theory_of context))
                       >> (I #>> Antiq_stack)))
         syms
     , C_Token.read_with_commands'0 keywords syms)
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

fun markup_directive_command def ps (name, id) =
  let 
    fun markup_elem name = (name, (name, []): Markup.T);
    val (varN, var) = markup_elem "directive command";
    val entity = Markup.entity varN name
  in
    var ::
    ((if def then I else cons (Markup.keyword_properties Markup.keyword1)))
      (map (fn pos => Markup.properties (Position.entity_properties_of def id pos) entity) ps)
  end

fun directive_update (name, pos) f tab =
  let val pos = [pos]
      val id = serial ()
      val _ = markup_directive_command true pos (name, id)
  in Symtab.update (name, (pos, id, f)) tab end

fun markup_directive_define def in_direct ps (name, id) =
  let 
    fun markup_elem name = (name, (name, []): Markup.T);
    val (varN, var) = markup_elem "directive define";
    val entity = Markup.entity varN name
  in
    var ::
    (cons (Markup.keyword_properties (if def orelse in_direct then Markup.operator else Markup.antiquote)))
      (map (fn pos => Markup.properties (Position.entity_properties_of def id pos) entity) ps)
  end

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

fun eval'0 env err accept ants {context, reports_text} =
  let fun scan_comment tag pos (antiq as {explicit, body, ...}) cts =
           let val (res, l_comm) = scan_antiq context body
           in 
             Left
                 ( tag
                 , antiq
                 , l_comm
                 , if forall (fn Right _ => true | _ => false) res then
                     let val (l_msg, res) = split_list (map_filter (fn Right (msg, l_report, l_tok) => SOME (msg, (l_report, l_tok)) | _ => NONE) res)
                         val (l_report, l_tok) = split_list res
                     in [(Antiq_none (C_Lex.Token (pos, ((C_Lex.Comment o Right o SOME) (explicit, cat_lines l_msg, if explicit then flat l_report else []), cts))), l_tok)] end
                   else
                     map (fn Left x => x
                           | Right (msg, l_report, tok) =>
                               (Antiq_none (C_Lex.Token (C_Token.range_of [tok], ((C_Lex.Comment o Right o SOME) (explicit, msg, l_report), C_Token.content_of tok))), [tok]))
                         res)
           end

      val ants = map (fn C_Lex.Token (pos, (C_Lex.Comment (Left antiq), cts)) =>
                          scan_comment Comment_language pos antiq cts
                       | tok => Right tok)
                     ants

      fun map_ants f1 f2 = maps (fn Left x => f1 x | Right tok => f2 tok)

      val ants_none = map_ants (fn (_, _, _, l) => maps (fn (Antiq_none x, _) => [x] | _ => []) l) (K []) ants

      val _ = Position.reports (maps (fn Left (_, _, _, [(Antiq_none _, _)]) => []
                                       | Left (_, {start, stop, range = (pos, _), ...}, _, _) =>
                                          (case stop of SOME stop => cons (stop, Markup.antiquote)
                                                      | NONE => I)
                                            [(start, Markup.antiquote),
                                             (pos, Markup.language_antiquotation)]
                                       | _ => [])
                                     ants);
      val _ = Position.reports_text (maps C_Lex.token_report ants_none
                                     @ maps (fn Left (_, _, _, [(Antiq_none _, _)]) => []
                                              | Left (_, _, l, ls) =>
                                                  maps (fn (Antiq_stack (pos, _), _) => pos | _ => []) ls
                                                  @ maps (maps (C_Token.reports ())) (l :: map #2 ls)
                                              | _ => [])
                                            ants);
      val _ = C_Lex.check ants_none;

      val ((ants, {context, reports_text}), env) =
        C_Env_Ext.map_env_directives'
          (fn env_dir =>
            let val (ants, (env_dir, env_tree)) =
              fold_map
                let
                  fun subst_directive tok (range1 as (pos1, _)) name (env_dir, env_tree) =
                    case Symtab.lookup env_dir name of
                      NONE => (Right (Left tok), (env_dir, env_tree))
                    | SOME (pos0, id, toks) =>
                        let val _ = Position.reports [(pos1, Markup.language_antiquotation)]
                        in
                          ( Right (Right (pos1, map (C_Lex.set_range range1) toks))
                          , (env_dir, C_Env.map_reports_text (Hsk_c_parser.report [pos1] (markup_directive_define false false pos0) (name, id)) env_tree))
                        end
                in
                 fn Left (tag, antiq, toks, l_antiq) =>
                      fold_map (fn antiq as (Antiq_stack (_, Lexing (_, exec)), _) =>
                                     apsnd (stack_exec0 (exec Comment_language)) #> pair antiq
                                 | (Antiq_stack (rep, Parsing (syms, (range, env1, _, skip, exec))), toks) =>
                                     (fn env as (env_dir, _) =>
                                       ((Antiq_stack (rep, Parsing (syms, (range, env1, env_dir, skip, exec))), toks), env))
                                 | antiq => pair antiq)
                               l_antiq
                      #> apfst (fn l_antiq => Left (tag, antiq, toks, l_antiq))
                  | Right tok =>
                  case tok of
                    C_Lex.Token (_, (C_Lex.Directive dir, _)) =>
                      (case C_Lex.directive_first_cmd_of dir of
                         NONE => I
                       | SOME dir_tok =>
                         apsnd (C_Env.map_reports_text (append (map (fn tok => ((C_Lex.pos_of tok, Markup.antiquote), "")) (C_Lex.directive_tail_cmds_of dir))))
                         #>
                         let val name = C_Lex.content_of dir_tok
                             val pos1 = C_Lex.pos_of dir_tok
                         in
                           case Symtab.lookup (Directives.get context) name of
                             NONE => apsnd (C_Env.map_reports_text (cons ((pos1, Markup.antiquote), "")))
                           | SOME (pos0, id, exec) =>
                               apsnd (C_Env.map_reports_text (Hsk_c_parser.report [pos1] (markup_directive_command false pos0) (name, id)))
                               #> exec dir
                               #> (fn (_, _, env) => env)
                         end)
                      #> tap
                           (fn _ =>
                             app (fn C_Lex.Token ((pos, _), (C_Lex.Comment (Left _), _)) =>
                                     (Position.reports_text [((pos, Markup.ML_comment), "")];
                                      (* not yet implemented *)
                                      warning ("Ignored annotation in directive" ^ Position.here pos))
                                   | _ => ())
                                 (C_Lex.token_list_of dir))
                      #> pair (Right (Left tok))
                  | C_Lex.Token (pos, (C_Lex.Keyword, cts)) => subst_directive tok pos cts
                  | C_Lex.Token (pos, (C_Lex.Ident, cts)) => subst_directive tok pos cts
                  | _ => pair (Right (Left tok))
                end
                ants
                (env_dir, {context = context, reports_text = reports_text})
            in ((ants, env_tree), env_dir) end)
          env

      val ants_stack =
        map_ants (single o Left o (fn (_, a, _, l) => (a, maps (single o #1) l)))
                 (map Right o (fn Left tok => [tok] | Right (_, toks) => toks))
                 ants
      val _ = Position.reports_text (maps (fn Right (Left tok) => C_Lex.token_report tok
                                            | Right (Right (pos, [])) => [((pos, Markup.intensify), "")]
                                            | _ => [])
                                          ants);
      val ctxt = Context.proof_of context
      val () = if Config.get ctxt C_Options.lexer_trace andalso Context_Position.is_visible ctxt
               then print (map_filter (fn Right x => SOME x | _ => NONE) ants_stack)
               else ()
  in P.parse env err accept ants_stack {context = context, reports_text = reports_text} end

fun eval' env err accept ants =
  Context.>> (C_Env_Ext.context_map
               let val tap_report = tap (Position.reports_text o #reports_text)
                                    #> (C_Env.empty_env_tree o #context)
               in eval'0 env
                         (fn env_lang => fn stack => fn pos => tap_report #> err env_lang stack pos)
                         (fn env_lang => fn stack => accept env_lang stack #> tap_report)
                         ants
               end)
end;

fun eval_source env err accept source =
  eval' env err accept (C_Lex.read_source source);

fun eval_source' env err accept source =
  eval'0 env err accept (C_Lex.read_source source);

end
\<close>

section \<open>\<close>
subsection \<open>\<close>

ML\<open>
local
fun expression range name constraint body ants context = context |>
  ML_Context.exec let val verbose = Config.get (Context.proof_of context) C_Options.ML_verbose
                  in fn () =>
    ML_Context.eval (ML_Compiler.verbose verbose ML_Compiler.flags) (#1 range)
     (ML_Lex.read "Context.put_generic_context (SOME (let val " @ ML_Lex.read_set_range range name @
      ML_Lex.read (": " ^ constraint ^ " =") @ ants @
      ML_Lex.read ("in " ^ body ^ " end (Context.the_generic_context ())));")) end;

structure C_Toplevel =
struct
val theory = Context.map_theory
val generic_theory = I
end

structure Isar_Cmd0 = 
struct
fun ML source =  ML_Context.exec (fn () =>
                    ML_Context.eval_source (ML_Compiler.verbose true ML_Compiler.flags) source) #>
                  Local_Theory.propagate_ml_env
end

structure C_Isar_Cmd = 
struct
fun setup src =
 fn NONE =>
    let val setup = "setup"
    in expression
        (Input.range_of src)
        setup
        "stack_data -> stack_data_elem -> C_Env.env_lang -> Context.generic -> Context.generic"
        ("fn context => \
           \let val (stack, env_lang) = Stack_Data_Lang.get context \
           \in " ^ setup ^ " stack (stack |> hd) env_lang end context")
        (ML_Lex.read_source false src) end
  | SOME rule => 
    let val hook = "hook"
    in expression
        (Input.range_of src)
        hook
        ("stack_data -> " ^ MlyValue.type_reduce rule ^ " stack_elem -> C_Env.env_lang -> Context.generic -> Context.generic")
        ("fn context => \
           \let val (stack, env_lang) = Stack_Data_Lang.get context \
           \in " ^ hook ^ " stack (stack |> hd |> map_svalue0 MlyValue.reduce" ^ Int.toString rule ^ ") env_lang end context")
        (ML_Lex.read_source false src)
    end

end

fun command0 f dir name =
  C_Annotation.command' name ""
    (fn (stack1, (to_delay, stack2)) =>
      C_Parse.range C_Parse.ML_source >>
        (fn (src, range) =>
          Parsing ((stack1, stack2), (range, dir, Symtab.empty, to_delay, K (f src)))))

fun command f dir name =
  C_Annotation.command' name ""
    (fn (stack1, (to_delay, stack2)) =>
      C_Parse.range C_Parse.ML_source >>
        (fn (src, range) =>
          Parsing ((stack1, stack2), (range, dir, Symtab.empty, to_delay, f src))))

in
val _ = Theory.setup (   command (C_Toplevel.generic_theory oo C_Isar_Cmd.setup) Bottom_up ("\<approx>setup", \<^here>)
                      #> command (C_Toplevel.generic_theory oo C_Isar_Cmd.setup) Top_down ("\<approx>setup\<Down>", \<^here>)
                      #> command0 (C_Toplevel.theory o Isar_Cmd.setup) Bottom_up ("setup", \<^here>)
                      #> command0 (C_Toplevel.theory o Isar_Cmd.setup) Top_down ("setup\<Down>", \<^here>)
                      #> command0 (C_Toplevel.generic_theory o Isar_Cmd0.ML) Bottom_up ("ML", \<^here>)
                      #> command0 (C_Toplevel.generic_theory o Isar_Cmd0.ML) Top_down ("ML\<Down>", \<^here>))
end

\<close>

subsection \<open>\<close>

ML\<open>
val _ =
  Theory.setup
  (Context.theory_map
    (C_Context.Directives.map
      (C_Context.directive_update ("define", \<^here>)
        (fn C_Lex.Define (_, C_Lex.Group1 ([], [tok3]), NONE, C_Lex.Group1 ([], toks)) =>
            (fn (env_dir, env_tree) =>
              ( NONE
              , []
              , let val name = C_Lex.content_of tok3
                    val id = serial ()
                    val pos = [C_Lex.pos_of tok3]
                in
                  ( Symtab.update (name, (pos, id, toks)) env_dir
                  , C_Env.map_reports_text (Hsk_c_parser.report pos (C_Context.markup_directive_define true false pos) (name, id))
                                           env_tree)
                end))
         | C_Lex.Define (_, C_Lex.Group1 ([], [tok3]), SOME (C_Lex.Group1 (_ :: toks_bl, _)), _) =>
             tap (fn _ => (* not yet implemented *)
                          warning ("Ignored functional macro directive" ^ Position.here (Position.range_position (C_Lex.pos_of tok3, C_Lex.end_pos_of (List.last toks_bl)))))
             #> (fn env => (NONE, [], env))
         | _ => fn env => (NONE, [], env))
       #>
       C_Context.directive_update ("undef", \<^here>)
        (fn C_Lex.Undef (C_Lex.Group2 (_, _, [tok])) =>
            (fn (env_dir, env_tree) =>
              ( NONE
              , []
              , let val name = C_Lex.content_of tok
                    val pos1 = C_Lex.pos_of tok
                in case Symtab.lookup env_dir name of
                     NONE => (env_dir, C_Env.map_reports_text (cons ((pos1, Markup.intensify), "")) env_tree)
                   | SOME (pos0, id, _) =>
                       ( Symtab.delete name env_dir
                       , C_Env.map_reports_text (Hsk_c_parser.report [pos1] (C_Context.markup_directive_define false true pos0) (name, id))
                                                env_tree)
                end))
         | _ => fn env => (NONE, [], env)))))
\<close>

end
