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
  imports C_Ast
begin

section\<open> Basic Scanning Combinators from Isabelle \<close>

ML\<open>
datatype ('a, 'b) either = Left of 'a | Right of 'b

structure Scanner =
struct
open Basic_Symbol_Pos;

val err_prefix = "C lexical error: ";

fun !!! msg = Symbol_Pos.!!! (fn () => err_prefix ^ msg);
fun opt x = Scan.optional x [];
fun opt'' x = Scan.optional (x >> K true) false;
fun one f = Scan.one (f o Symbol_Pos.symbol)
fun many f = Scan.many (f o Symbol_Pos.symbol)
fun many1 f = Scan.many1 (f o Symbol_Pos.symbol)
val one' = Scan.single o one
fun scan_full mem msg scan =
  scan --| (Scan.ahead (one' (not o mem)) || !!! msg Scan.fail)
fun this_string s =
  (fold (fn s0 => uncurry (fn acc => one (fn s1 => s0 = s1) >> (fn x => x :: acc)))
        (Symbol.explode s)
   o pair [])
  >> rev
val one_not_eof = Scan.one (Symbol.not_eof o #1)
fun unless_eof scan = Scan.unless scan one_not_eof >> single
val repeats_one_not_eof = Scan.repeats o unless_eof
val newline =   $$$ "\n"
             || $$$ "\^M" @@@ $$$ "\n"
             || $$$ "\^M"
val repeats_until_nl = repeats_one_not_eof newline
end
\<close>

section \<open>Instantiation of the Scanner with C Lexems \<close>

text\<open>Basically copied and modified from files in Pure General of Isabelle.\<close>
ML\<open>
(*  Title:      Pure/General/symbol.ML
    Author:     Makarius

Generalized characters with infinitely many named symbols.
*)

structure C_Symbol =
struct
fun is_ascii_quasi "_" = true
  | is_ascii_quasi "$" = true
  | is_ascii_quasi _ = false;

fun is_identletter s =
  Symbol.is_ascii_letter s orelse is_ascii_quasi s

fun is_ascii_oct s =
  Symbol.is_char s andalso Char.ord #"0" <= ord s andalso ord s <= Char.ord #"7";

fun is_ascii_digit1 s =
  Symbol.is_char s andalso Char.ord #"1" <= ord s andalso ord s <= Char.ord #"9";

fun is_ascii_letdig s =
  Symbol.is_ascii_letter s orelse Symbol.is_ascii_digit s orelse is_ascii_quasi s;

fun is_ascii_identifier s =
  size s > 0 andalso forall_string is_ascii_letdig s;

val is_ascii_blank_no_line =
  fn " " => true | "\t" => true | "\^K" => true | "\f" => true
    | _ => false;
end
\<close>

ML\<open>
(*  Title:      Pure/General/symbol_pos.ML
    Author:     Makarius

Symbols with explicit position information.
*)

structure C_Symbol_Pos =
struct
val !!! = Scanner.!!!
val $$ = Symbol_Pos.$$
val $$$ = Symbol_Pos.$$$
val ~$$$ = Symbol_Pos.~$$$

(* scan string literals *)

local

val char_code =
  Scan.one (Symbol.is_ascii_digit o Symbol_Pos.symbol) --
  Scan.one (Symbol.is_ascii_digit o Symbol_Pos.symbol) --
  Scan.one (Symbol.is_ascii_digit o Symbol_Pos.symbol) :|--
  (fn (((a, pos), (b, _)), (c, _)) =>
    let val (n, _) = Library.read_int [a, b, c]
    in if n <= 255 then Scan.succeed [(chr n, pos)] else Scan.fail end);

fun scan_str_inline q =
  $$$ "\\" |-- !!! "bad escape character in string"
    ($$$ q || $$$ "\\" || char_code) ||
  Scan.unless Scanner.newline
              (Scan.one (fn (s, _) => s <> q andalso s <> "\\" andalso Symbol.not_eof s)) >> single;

fun scan_strs_inline q =
  Scan.ahead ($$ q) |--
    !!! "unclosed string literal within the same line"
      ((Symbol_Pos.scan_pos --| $$$ q) -- (Scan.repeats (scan_str_inline q) -- ($$$ q |-- Symbol_Pos.scan_pos)));

in

val scan_string_qq_inline = scan_strs_inline "\"";
val scan_string_bq_inline = scan_strs_inline "`";

end;

(* nested text cartouches *)

fun scan_cartouche_depth stop =
  Scan.repeat1 (Scan.depend (fn (depth: int option) =>
    (case depth of
      SOME d =>
        $$ Symbol.open_ >> pair (SOME (d + 1)) ||
          (if d > 0 then
            Scan.unless stop
                        (Scan.one (fn (s, _) => s <> Symbol.close andalso Symbol.not_eof s))
            >> pair depth ||
            $$ Symbol.close >> pair (if d = 1 then NONE else SOME (d - 1))
          else Scan.fail)
    | NONE => Scan.fail)));

fun scan_cartouche msg stop =
  Scan.ahead ($$ Symbol.open_) |--
    !!! ("unclosed text cartouche within " ^ msg)
      (Scan.provide is_none (SOME 0) (scan_cartouche_depth stop));

fun scan_cartouche_multi stop = scan_cartouche "the comment delimiter" stop;
val scan_cartouche_inline = scan_cartouche "the same line" Scanner.newline;

(* C-style comments *)

local
val par_l = "/"
val par_r = "/"

val scan_body1 = $$$ "*" --| Scan.ahead (~$$$ par_r)
val scan_body2 = Scan.one (fn (s, _) => s <> "*" andalso Symbol.not_eof s) >> single
val scan_cmt =
  Scan.depend (fn (d: int) => $$$ par_l @@@ $$$ "*" >> pair (d + 1)) ||
  Scan.depend (fn 0 => Scan.fail | d => $$$ "*" @@@ $$$ par_r >> pair (d - 1)) ||
  Scan.lift scan_body1 ||
  Scan.lift scan_body2;

val scan_cmts = Scan.pass 0 (Scan.repeats scan_cmt);

in

val scan_comment =
  Scan.ahead ($$ par_l -- $$ "*") |--
    !!! "unclosed comment"
      ($$$ par_l @@@ $$$ "*" @@@ scan_cmts @@@ $$$ "*" @@@ $$$ par_r)
  || $$$ "/" @@@ $$$ "/" @@@ Scanner.repeats_until_nl;

val scan_comment_no_nest =
  Scan.ahead ($$ par_l -- $$ "*") |--
    !!! "unclosed comment"
      ($$$ par_l @@@ $$$ "*" @@@ Scan.repeats (scan_body1 || scan_body2) @@@ $$$ "*" @@@ $$$ par_r)
  || $$$ "/" @@@ $$$ "/" @@@ Scanner.repeats_until_nl;

val recover_comment =
  $$$ par_l @@@ $$$ "*" @@@ Scan.repeats (scan_body1 || scan_body2);

end
end
\<close>

ML\<open>
(*  Title:      Pure/General/antiquote.ML
    Author:     Makarius

Antiquotations within plain text.
*)

structure C_Antiquote =
struct

(* datatype antiquote *)

type antiq = { explicit: bool
             , start: Position.T
             , stop: Position.T option
             , range: Position.range
             , body: Symbol_Pos.T list
             , body_begin: Symbol_Pos.T list
             , body_end: Symbol_Pos.T list }

(* scan *)

open Basic_Symbol_Pos;

local

val err_prefix = "Antiquotation lexical error: ";

val par_l = "/"
val par_r = "/"

val scan_body1 = $$$ "*" --| Scan.ahead (~$$$ par_r)
val scan_body2 = Scan.one (fn (s, _) => s <> "*" andalso Symbol.not_eof s) >> single

val scan_antiq_body_multi =
  Scan.trace (Symbol_Pos.scan_string_qq err_prefix || Symbol_Pos.scan_string_bq err_prefix) >> #2 ||
  C_Symbol_Pos.scan_cartouche_multi ($$$ "*" @@@ $$$ par_r) ||
  scan_body1 ||
  scan_body2;

val scan_antiq_body_multi_recover =
  scan_body1 ||
  scan_body2;

val scan_antiq_body_inline =
  Scan.trace (C_Symbol_Pos.scan_string_qq_inline || C_Symbol_Pos.scan_string_bq_inline) >> #2 ||
  C_Symbol_Pos.scan_cartouche_inline ||
  Scanner.unless_eof Scanner.newline;

val scan_antiq_body_inline_recover =
  Scanner.unless_eof Scanner.newline;

fun control_name sym = (case Symbol.decode sym of Symbol.Control name => name);

fun scan_antiq_multi scan =
  Symbol_Pos.scan_pos
  -- (Scan.trace ($$ par_l |-- $$ "*" |-- scan)
      -- Symbol_Pos.scan_pos
      -- Symbol_Pos.!!! (fn () => err_prefix ^ "missing closing antiquotation")
                        (Scan.repeats scan_antiq_body_multi
                         -- Symbol_Pos.scan_pos
                         -- ($$$ "*" @@@ $$$ par_r)
                         -- Symbol_Pos.scan_pos))

fun scan_antiq_multi_recover scan =
  Symbol_Pos.scan_pos -- ($$ par_l |-- $$ "*" |-- scan -- Symbol_Pos.scan_pos --
      (Scan.repeats scan_antiq_body_multi_recover -- Symbol_Pos.scan_pos -- ($$ "*" |-- $$ par_r |-- Symbol_Pos.scan_pos)))

fun scan_antiq_inline scan =
  (Symbol_Pos.scan_pos -- Scan.trace ($$ "/" |-- $$ "/" |-- scan)
  -- Symbol_Pos.scan_pos
  -- Scan.repeats scan_antiq_body_inline -- Symbol_Pos.scan_pos)

fun scan_antiq_inline_recover scan =
  (Symbol_Pos.scan_pos --| $$ "/" --| $$ "/" -- scan
  -- Symbol_Pos.scan_pos
  -- Scan.repeats scan_antiq_body_inline_recover -- Symbol_Pos.scan_pos)

in

val scan_control =
  Scan.option (Scan.one (Symbol.is_control o Symbol_Pos.symbol)) --
  Symbol_Pos.scan_cartouche err_prefix >>
    (fn (opt_control, body) =>
      let
        val (name, range) =
          (case opt_control of
            SOME (sym, pos) => ((control_name sym, pos), Symbol_Pos.range ((sym, pos) :: body))
          | NONE => (("cartouche", #2 (hd body)), Symbol_Pos.range body));
      in {name = name, range = range, body = body} end) ||
  Scan.one (Symbol.is_control o Symbol_Pos.symbol) >>
    (fn (sym, pos) =>
      {name = (control_name sym, pos), range = Symbol_Pos.range [(sym, pos)], body = []});

val scan_antiq =
  scan_antiq_multi ($$$ "@" >> K true || scan_body1 >> K false)
  >> (fn (pos1, (((explicit, body_begin), pos2), (((body, pos3), body_end), pos4))) =>
      {explicit = explicit,
       start = Position.range_position (pos1, pos2),
       stop = SOME (Position.range_position (pos3, pos4)),
       range = Position.range (pos1, pos4),
       body = body,
       body_begin = body_begin,
       body_end = body_end}) ||
  scan_antiq_inline ($$$ "@" >> K true || $$$ "*" >> K false)
  >> (fn ((((pos1, (explicit, body_begin)), pos2), body), pos3) => 
      {explicit = explicit,
       start = Position.range_position (pos1, pos2),
       stop = NONE,
       range = Position.range (pos1, pos3),
       body = body,
       body_begin = body_begin,
       body_end = []})

val scan_antiq_recover =
  scan_antiq_multi_recover ($$$ "@" >> K true || scan_body1 >> K false) >> (fn (_, ((explicit, _), _)) => explicit) ||
  scan_antiq_inline_recover ($$$ "@" >> K true || $$$ "*" >> K false) >> (fn ((((_, explicit), _), _), _) => explicit)

end;

end;
\<close>

ML\<open>
(*  Title:      Pure/ML/ml_options.ML
    Author:     Makarius

ML configuration options.
*)

structure C_Options =
struct

(* source trace *)

val lexer_trace = Attrib.setup_config_bool @{binding C_lexer_trace} (fn _ => false);
val parser_trace = Attrib.setup_config_bool @{binding C_parser_trace} (fn _ => false);

end
\<close>

ML\<open>
(*  Title:      Pure/ML/ml_lex.ML
    Author:     Makarius

Lexical syntax for Isabelle/ML and Standard ML.
*)

structure C_Lex =
struct

open Scanner;

(** keywords **)

val keywords =
 ["(",
  ")",
  "[",
  "]",
  "->",
  ".",
  "!",
  "~",
  "++",
  "--",
  "+",
  "-",
  "*",
  "/",
  "%",
  "&",
  "<<",
  ">>",
  "<",
  "<=",
  ">",
  ">=",
  "==",
  "!=",
  "^",
  "|",
  "&&",
  "||",
  "?",
  ":",
  "=",
  "+=",
  "-=",
  "*=",
  "/=",
  "%=",
  "&=",
  "^=",
  "|=",
  "<<=",
  ">>=",
  ",",
  ";",
  "{",
  "}",
  "...",
  (**)
  "_Alignas",
  "_Alignof",
  "__alignof",
  "alignof",
  "__alignof__",
  "__asm",
  "asm",
  "__asm__",
  "_Atomic",
  "__attribute",
  "__attribute__",
  "auto",
  "_Bool",
  "break",
  "__builtin_offsetof",
  "__builtin_types_compatible_p",
  "__builtin_va_arg",
  "case",
  "char",
  "_Complex",
  "__complex__",
  "__const",
  "const",
  "__const__",
  "continue",
  "default",
  "do",
  "double",
  "else",
  "enum",
  "__extension__",
  "extern",
  "float",
  "for",
  "_Generic",
  "goto",
  "if",
  "__imag",
  "__imag__",
  "__inline",
  "inline",
  "__inline__",
  "int",
  "__int128",
  "__label__",
  "long",
  "_Nonnull",
  "__nonnull",
  "_Noreturn",
  "_Nullable",
  "__nullable",
  "__real",
  "__real__",
  "register",
  "__restrict",
  "restrict",
  "__restrict__",
  "return",
  "short",
  "__signed",
  "signed",
  "__signed__",
  "sizeof",
  "static",
  "_Static_assert",
  "struct",
  "switch",
  "__thread",
  "_Thread_local",
  "typedef",
  "__typeof",
  "typeof",
  "__typeof__",
  "union",
  "unsigned",
  "void",
  "__volatile",
  "volatile",
  "__volatile__",
  "while"];

val keywords2 =
 ["__asm",
  "asm",
  "__asm__",
  "extern"];

val keywords3 =
 ["_Bool",
  "char",
  "double",
  "float",
  "int",
  "__int128",
  "long",
  "short",
  "__signed",
  "signed",
  "__signed__",
  "unsigned",
  "void"];

val lexicon = Scan.make_lexicon (map raw_explode keywords);



(** tokens **)

(* datatype token *)

datatype token_kind =
  Keyword | Ident | Type_ident | GnuC | ClangC |
  (**)
  Char of bool * Symbol.symbol list |
  Integer of int * CIntRepr * CIntFlag list |
  Float |
  String of bool * Symbol.symbol list |
  File of bool * Symbol.symbol list |
  (**)
  Space | Comment of (C_Antiquote.antiq, (bool * string * ((Position.T * Markup.T) * string) list) option) either | Sharp of int |
  (**)
  Error of string * token_group | Directive of token_kind_directive | EOF

and token_kind_directive = Inline of token_group (* a not yet analyzed directive *)
                         | Include of token_group
                         | Define of token_group (* define *)
                                   * token_group (* name *)
                                   * token_group option (* functional arguments *)
                                   * token_group (* rewrite body *)
                         | Undef of token_group (* name *)
                         | Conditional of token_group (* if *)
                                        * token_group list (* elif *)
                                        * token_group option (* else *)
                                        * token_group (* endif *)

and token_group = Group1 of token list (* spaces and comments filtered from the directive *)
                          * token list (* directive: raw data *)
                | Group2 of token list (* spaces and comments filtered from the directive *)
                          * token list (* directive: function *)
                          * token list (* directive: arguments (same line) *)
                | Group3 of (  Position.range (* full directive (with blanks) *)
                             * token list (* spaces and comments filtered from the directive *)
                             * token list (* directive: function *)
                             * token list (* directive: arguments (same line) *))
                          * (Position.range * token list) (* C code or directive: arguments (following lines) *)

and token = Token of Position.range * (token_kind * string);


(* position *)

fun set_range range (Token (_, x)) = Token (range, x);
fun range_of (Token (range, _)) = range;

val pos_of = #1 o range_of;
val end_pos_of = #2 o range_of;


(* stopper *)

fun mk_eof pos = Token ((pos, Position.none), (EOF, ""));
val eof = mk_eof Position.none;

fun is_eof (Token (_, (EOF, _))) = true
  | is_eof _ = false;

val stopper =
  Scan.stopper (fn [] => eof | toks => mk_eof (end_pos_of (List.last toks))) is_eof;

val one_not_eof = Scan.one (not o is_eof)

(* token content *)

fun kind_of (Token (_, (k, _))) = k;

val group_list_of = fn
   Inline g => [g]
 | Include g => [g]
 | Define (g1, g2, o_g3, g4) => flat [[g1], [g2], the_list o_g3, [g4]]
 | Undef g => [g]
 | Conditional (g1, gs2, o_g3, g4) => flat [[g1], gs2, the_list o_g3, [g4]]

fun content_of (Token (_, (_, x))) = x;
fun token_leq (tok, tok') = content_of tok <= content_of tok';

fun is_keyword (Token (_, (Keyword, _))) = true
  | is_keyword _ = false;

fun is_ident (Token (_, (Ident, _))) = true
  | is_ident _ = false;

fun is_delimiter (Token (_, (Keyword, x))) = not (C_Symbol.is_ascii_identifier x)
  | is_delimiter _ = false;

(* range *)

val range_list_of0 =
 fn [] => Position.no_range
  | toks as tok1 :: _ => Position.range (pos_of tok1, end_pos_of (List.last toks))
    (* WARNING the use of:
       fn tok2 => List.last (Symbol_Pos.explode (content_of tok2, pos_of tok2)) |-> Position.advance
       would not return an accurate position if for example several
       "backslash newlines" are present in the symbol *)

fun range_list_of toks = (range_list_of0 toks, toks)
fun range_list_of' toks1 toks2 = (range_list_of0 toks1, toks2)

local
fun cmp_pos x2 x1 = Position.distance_of (pos_of x2) (pos_of x1) < 0

fun merge_pos xs = case xs of (xs1, []) => xs1
                            | ([], xs2) => xs2
                            | (x1 :: xs1, x2 :: xs2) =>
                                let val (x, xs) = (if cmp_pos x2 x1 then (x1, (xs1, x2 :: xs2)) else (x2, (x1 :: xs1, xs2)))
                                in x :: merge_pos xs end
in
fun merge_blank toks_bl xs1 xs2 =
  let val cmp_tok2 = cmp_pos (List.last xs1)
  in ( range_list_of (merge_pos (xs1, filter cmp_tok2 toks_bl))
     , range_list_of (merge_pos (xs2, filter_out cmp_tok2 toks_bl)))
  end
end

val token_list_of = 
  let fun merge_blank' toks_bl xs1 xs2 =
    let val ((_, l1), (_, l2)) = merge_blank toks_bl xs1 xs2
    in [l1, l2] end
  in group_list_of
    #> maps (fn
        Group1 (toks_bl, []) => [toks_bl]
      | Group1 (toks_bl, xs1) => merge_blank' toks_bl xs1 []
      | Group2 (toks_bl, xs1, xs2) => merge_blank' toks_bl xs1 xs2
      | Group3 ((_, toks_bl, xs1, xs2), (_, xs3)) => flat [merge_blank' toks_bl xs1 xs2, [xs3]])
    #> flat
  end

local
  fun warn0 pos l s =
    if exists (not o Symbol.is_printable) l then
      app (fn (s, pos) =>
            if Symbol.is_printable s
            then ()
            else Output.information ("Not printable character " ^ @{make_string} (ord s, s) ^ Position.here pos))
                                    (Symbol_Pos.explode (s, pos))
    else ()
in
val warn = fn
    Token ((pos, _), (Char (_, l), s)) => warn0 pos l s
  | Token ((pos, _), (String (_, l), s)) => warn0 pos l s
  | Token ((pos, _), (File (_, l), s)) => warn0 pos l s
  | Token (_, (Comment (Right (SOME (explicit, msg, _))), _)) => (if explicit then warning else tracing) msg
  | Token ((pos, _), (Directive (Inline _), _)) => warning ("Ignored directive" ^ Position.here pos)
  | Token (_, (Directive (kind as Conditional _), _)) => 
      app (fn Token (_, (Error (msg, _), _)) => warning msg | _ => ())
          (token_list_of kind)
  | _ => ();
end

fun check_error tok =
  case kind_of tok of
    Error (msg, _) => SOME msg
  | _ => NONE;

(* markup *)

local

val token_kind_markup0 =
 fn Char _ => (Markup.ML_char, "")
  | Integer _ => (Markup.ML_numeral, "")
  | Float => (Markup.ML_numeral, "")
  | ClangC => (Markup.ML_numeral, "")
  | String _ => (Markup.ML_string, "")
  | File _ => (Markup.ML_string, "")
  | Sharp _ => (Markup.antiquote, "")
  | Error (msg, _) => (Markup.bad (), msg)
  | _ => (Markup.empty, "");

fun token_report' escape_directive (tok as Token ((pos, _), (kind, x))) =
  if escape_directive andalso (is_keyword tok orelse is_ident tok) then
    [((pos, Markup.antiquote), "")]
  else if is_keyword tok then
    let
      val (markup, txt) = if is_delimiter tok then (Markup.ML_delimiter, "")
        else if member (op =) keywords2 x then (Markup.ML_keyword2 |> Markup.keyword_properties, "")
        else if member (op =) keywords3 x then (Markup.ML_keyword3 |> Markup.keyword_properties, "")
        else (Markup.ML_keyword1 |> Markup.keyword_properties, "");
    in [((pos, markup), txt)] end
  else
    case kind of
     Directive (tokens as Inline _) =>
       ((pos, Markup.antiquoted), "") :: maps token_report0 (token_list_of tokens)
   | Directive (Include (Group2 (toks_bl, toks1, toks2))) =>
       ((pos, Markup.antiquoted), "")
       :: flat [ maps token_report1 toks1
               , maps token_report0 toks2
               , maps token_report0 toks_bl ]
   | Directive (Define (Group1 (toks_bl1, toks1), Group1 (toks_bl2, toks2), toks3, Group1 (toks_bl4, toks4))) =>
       let val (toks_bl3, toks3) = case toks3 of SOME (Group1 x) => x | _ => ([], [])
       in ((pos, Markup.antiquoted), "")
         :: ((range_list_of0 toks4 |> #1, Markup.intensify), "")
         :: flat [ maps token_report1 toks1
                 , maps token_report0 toks2
                 , maps token_report0 toks3
                 , maps token_report0 toks4
                 , maps token_report0 toks_bl1
                 , maps token_report0 toks_bl2
                 , map (fn tok => ((pos_of tok, Markup.antiquote), "")) toks_bl3
                 , maps token_report0 toks_bl4 ] end
   | Directive (Undef (Group2 (toks_bl, toks1, toks2))) =>
       ((pos, Markup.antiquoted), "")
       :: flat [ maps token_report1 toks1
               , maps token_report0 toks2
               , maps token_report0 toks_bl ]
   | Directive (Conditional (c1, cs2, c3, c4)) =>
       maps (fn Group3 (((pos, _), toks_bl, toks1, toks2), ((pos3, _), toks3)) => 
                ((pos, Markup.antiquoted), "")
                :: ((pos3, Markup.intensify), "")
                :: flat [ maps token_report1 toks1
                        , maps token_report0 toks2
                        , maps token_report0 toks3
                        , maps token_report0 toks_bl ]
              | _ => error "Only expecting Group3")
            (flat [[c1], cs2, the_list c3, [c4]])
   | Error (msg, Group2 (toks_bl, toks1, toks2)) =>
        ((range_list_of0 toks1 |> #1, Markup.bad ()), msg)
        :: ((pos, Markup.antiquoted), "")
        :: flat [ maps token_report1 toks1
                , maps token_report0 toks2
                , maps token_report0 toks_bl ]
   | Error (msg, Group3 ((_, toks_bl, toks1, toks2), _)) =>
        ((range_list_of0 toks1 |> #1, Markup.bad ()), msg)
        :: ((pos, Markup.antiquoted), "")
        :: flat [ maps token_report1 toks1
                , maps token_report0 toks2
                , maps token_report0 toks_bl ]
   | Comment (Right c) => ((pos, Markup.ML_comment), "") :: (case c of NONE => [] | SOME (_, _, l) => l)
   | x => [let val (markup, txt) = token_kind_markup0 x in ((pos, markup), txt) end]

and token_report0 tok = token_report' false tok
and token_report1 tok = token_report' true tok

in
val token_report = token_report0
end;


(** scanners **)

(* identifiers *)

val scan_ident =
      one C_Symbol.is_identletter
  ::: many (fn s => C_Symbol.is_identletter s orelse Symbol.is_ascii_digit s);


(* numerals *)

fun read_bin s = #1 (read_radix_int 2 s)
fun read_oct s = #1 (read_radix_int 8 s)
fun read_dec s = #1 (read_int s)
val read_hex =
  let fun conv_ascii c1 c0 = String.str (Char.chr (Char.ord #"9" + Char.ord c1 - Char.ord c0 + 1))
  in map (fn s => let val c = String.sub (s, 0) in
                  if c >= #"A" andalso c <= #"F" then
                    conv_ascii c #"A"
                  else if c >= #"a" andalso c <= #"f" then
                    conv_ascii c #"a"
                  else s
                  end)
  #> read_radix_int 16
  #> #1
  end

local
open C_ast_simple
val many_digit = many Symbol.is_ascii_digit
val many1_digit = many1 Symbol.is_ascii_digit
val many_hex = many Symbol.is_ascii_hex
val many1_hex = many1 Symbol.is_ascii_hex

val scan_suffix_ll = ($$$ "l" @@@ $$$ "l" || $$$ "L" @@@ $$$ "L") >> K [FlagLongLong]
fun scan_suffix_gnu flag = ($$$ "i" || $$$ "j") >> K [flag]
val scan_suffix_int = 
  let val u = ($$$ "u" || $$$ "U") >> K [FlagUnsigned]
      val l = ($$$ "l" || $$$ "L") >> K [FlagLong] in
      u @@@ scan_suffix_ll
   || scan_suffix_ll @@@ opt u
   || u @@@ opt l
   || l @@@ opt u
  end

val scan_suffix_gnu_int0 = scan_suffix_gnu FlagImag
val scan_suffix_gnu_int = scan_full (member (op =) (raw_explode "uUlLij"))
                                    "Invalid integer constant suffix"
                                    (   scan_suffix_int @@@ opt scan_suffix_gnu_int0
                                     || scan_suffix_gnu_int0 @@@ opt scan_suffix_int)

fun scan_intgnu x =
  x -- opt scan_suffix_gnu_int
  >> (fn ((s1', read, repr), l) => (read (map (Symbol_Pos.content o single) s1'), repr, l))

val scan_intoct = scan_intgnu ($$ "0" |-- (   many (fn x => x = "0")
                                              >> (fn xs => (xs, read_dec, DecRepr))
                                           || many C_Symbol.is_ascii_oct
                                              >> (fn xs => (xs, read_oct, OctalRepr))))
val scan_intdec = scan_intgnu (one C_Symbol.is_ascii_digit1 -- many Symbol.is_ascii_digit
                               >> (fn (x, xs) => (x :: xs, read_dec, DecRepr)))
val scan_inthex = scan_intgnu (($$ "0" -- ($$ "x" || $$ "X")) |-- many1_hex
                               >> (fn xs2 => (xs2, read_hex, HexRepr)))

(**)

fun scan_signpart a A = ($$$ a || $$$ A) @@@ opt ($$$ "+" || $$$ "-") @@@ many1_digit
val scan_exppart = scan_signpart "e" "E"

val scan_suffix_float = $$$ "f" || $$$ "F" || $$$ "l" || $$$ "L"
val scan_suffix_gnu_float0 = Scan.trace (scan_suffix_gnu ()) >> #2
val scan_suffix_gnu_float = scan_full (member (op =) (raw_explode "fFlLij"))
                                      "Invalid float constant suffix"
                                      (   scan_suffix_float @@@ opt scan_suffix_gnu_float0
                                       || scan_suffix_gnu_float0 @@@ opt scan_suffix_float)

val scan_hex_pref = $$$ "0" @@@ $$$ "x"

val scan_hexmant = many_hex @@@ $$$ "." @@@ many1_hex
                || many1_hex @@@ $$$ "."
val scan_floatdec =
      (       (   many_digit @@@ $$$ "." @@@ many1_digit
               || many1_digit @@@ $$$ ".")
          @@@ opt scan_exppart
       || many1_digit @@@ scan_exppart)
  @@@ opt scan_suffix_gnu_float

val scan_floathex = scan_hex_pref @@@ (scan_hexmant || many1_hex) @@@ scan_signpart "p" "P" @@@ opt scan_suffix_gnu_float
val scan_floatfail = scan_hex_pref @@@ scan_hexmant
in
val scan_int = scan_inthex
            || scan_intoct
            || scan_intdec
             
val scan_float = scan_floatdec
              || scan_floathex
              || scan_floatfail >> !!! "Hexadecimal floating constant requires an exponent" Scan.fail

val scan_clangversion = many1_digit @@@ $$$ "." @@@ many1_digit @@@ $$$ "." @@@ many1_digit

end;


(* chars and strings *)

val scan_blanks1 = many1 Symbol.is_ascii_blank

local
val escape_char = [ ("n", #"\n")
                  , ("t", #"\t")
                  , ("v", #"\v")
                  , ("b", #"\b")
                  , ("r", #"\r")
                  , ("f", #"\f")
                  , ("a", #"\a")
                  , ("e", #"\^[")
                  , ("E", #"\^[")
                  , ("\\", #"\\")
                  , ("?", #"?")
                  , ("'", #"'")
                  , ("\"", #"\"") ]
fun scan_escape s0 =
  let val oct = one' C_Symbol.is_ascii_oct
      val hex = one' Symbol.is_ascii_hex
      fun read_oct' l = [chr (read_oct (map Symbol_Pos.content l))]
  in one' (member (op =) (raw_explode (s0 ^ String.concat (map #1 escape_char))))
     >> (fn i =>
          [case AList.lookup (op =) escape_char (Symbol_Pos.content i) of
             NONE => s0
           | SOME c => String.str c])
  || oct -- oct -- oct >> (fn ((o1, o2), o3) => read_oct' [o1, o2, o3])
  || oct -- oct >> (fn (o1, o2) => read_oct' [o1, o2])
  || oct >> (read_oct' o single)
  || $$ "x" |-- many1 Symbol.is_ascii_hex
     >> (fn xs => [chr (read_hex (map (Symbol_Pos.content o single) xs))])
  || $$ "u" |-- hex -- hex -- hex -- hex
     >> (fn (((x1, x2), x3), x4) =>
          [chr (read_hex (map Symbol_Pos.content [x1, x2, x3, x4]))])
  || $$ "U" |-- hex -- hex -- hex -- hex -- hex -- hex -- hex -- hex
     >> (fn (((((((x1, x2), x3), x4), x5), x6), x7), x8) =>
          [chr (read_hex (map Symbol_Pos.content [x1, x2, x3, x4, x5, x6, x7, x8]))])
  end

fun scan_str s0 =
     Scan.one (fn (s, _) => Symbol.not_eof s andalso s <> s0 andalso s <> "\\")
     >> (fn s => [#1 s])
  || $$ "\\" |-- !!! "bad escape character" (scan_escape s0);

fun scan_gap xs = ($$ "\\" -- scan_blanks1 -- $$ "\\" >> K []) xs;

fun scan_string0 s0 msg repeats =
  opt'' ($$ "L") --
    (Scan.ahead ($$ s0) |--
      !!! ("unclosed " ^ msg ^ " literal")
        ($$ s0 |-- repeats (scan_gap || scan_str s0) --| $$ s0))

fun recover_string0 s0 repeats =
  opt ($$$ "L") @@@ $$$ s0 @@@ repeats (scan_gap || Scan.permissive (Scan.trace (scan_str s0) >> #2));
in

val scan_char = scan_string0 "'" "char" Scan.repeats1
val scan_string = scan_string0 "\"" "string" Scan.repeats
val scan_file =
  let fun scan s_l s_r =
    Scan.ahead ($$ s_l) |--
        !!! ("unclosed file literal")
          ($$ s_l |-- Scan.repeats (Scan.one (fn (s, _) => Symbol.not_eof s andalso s <> s_r) >> (fn s => [#1 s])) --| $$ s_r)
  in
     scan "\"" "\"" >> pair false
  || scan "<" ">" >> pair true
  end

val recover_char = recover_string0 "'" Scan.repeats1
val recover_string = recover_string0 "\"" Scan.repeats

end;

(* scan tokens *)

fun check input =
  case fold (fn tok =>
              let val () = warn tok
              in case check_error tok of SOME s => cons s | NONE => I end)
            input
            []
  of [] => ()
   | l => error (cat_lines (rev l))

local

fun token k ss = Token (Symbol_Pos.range ss, (k, Symbol_Pos.content ss));
fun scan_token f1 f2 = Scan.trace f1 >> (fn (v, s) => token (f2 v) s)

val comments =
     Scan.recover
       (scan_token C_Antiquote.scan_antiq (Comment o Left))
       (fn msg => Scan.ahead C_Antiquote.scan_antiq_recover
                  -- C_Symbol_Pos.scan_comment_no_nest
                  >> (fn (explicit, res) => token (Comment (Right (SOME (explicit, msg, [])))) res)
               || Scan.fail_with (fn _ => fn _ => msg))
  || C_Symbol_Pos.scan_comment_no_nest >> token (Comment (Right NONE))

fun scan_fragment blanks =
     scan_token scan_char Char
  || scan_token scan_string String
  || blanks >> token Space
  || comments
  || Scan.max token_leq (Scan.literal lexicon >> token Keyword)
                        (   scan_clangversion >> token ClangC
                         || scan_float >> token Float
                         || scan_token scan_int Integer
                         || scan_ident >> token Ident)

(* scan tokens, directive part *)

val scan_directive =
  let val many1_no_eol = many1 C_Symbol.is_ascii_blank_no_line
      val blanks = Scan.repeat (many1_no_eol >> token Space || comments)
      val f_filter = fn Token (_, (Space, _)) => true
                      | Token (_, (Comment _, _)) => true
                      | Token (_, (Error _, _)) => true
                      | _ => false in
        ($$$ "#" >> (single o token (Sharp 1)))
    @@@ (   (   blanks @@@ (scan_ident >> token Ident >> single)
            @@@ blanks @@@ (scan_token scan_file File >> single)
            @@@ blanks) --| Scan.ahead newline
         || Scan.repeat (   $$$ "#" @@@ $$$ "#" >> token (Sharp 2)
                         || $$$ "#" >> token (Sharp 1)
                         || scan_fragment many1_no_eol))
    >> (fn tokens => Inline (Group1 (filter f_filter tokens, filter_out f_filter tokens)))
  end

local
fun !!! text scan =
  let
    fun get_pos [] = " (end-of-input)"
      | get_pos (t :: _) = Position.here (pos_of t);

    fun err (syms, msg) = fn () =>
      err_prefix ^ text ^ get_pos syms ^
      (case msg of NONE => "" | SOME m => "\n" ^ m ());
  in Scan.!! err scan end

val pos_here_of = Position.here o pos_of

fun one_directive f =
  Scan.one (fn Token (_, (Directive (Inline (Group1 (_, Token (_, (Sharp 1, _)) :: Token (_, s) :: _))), _)) => f s
             | _ => false)

val get_cond = fn Token (pos, (Directive (Inline (Group1 (toks_bl, tok1 :: tok2 :: toks))), _)) =>
                    (fn t3 => Group3 ((pos, toks_bl, [tok1, tok2], toks), range_list_of t3))
                | _ => error "Inline directive expected"

val one_start_cond = one_directive (fn (Keyword, "if") => true
                                     | (Ident, "ifdef") => true
                                     | (Ident, "ifndef") => true
                                     | _ => false)
val one_elif = one_directive (fn (Ident, "elif") => true | _ => false)
val one_else = one_directive (fn (Keyword, "else") => true | _ => false)
val one_endif = one_directive (fn (Ident, "endif") => true | _ => false)

val not_cond =
  Scan.unless
    (one_start_cond || one_elif || one_else || one_endif)
    (one_not_eof
     >> (fn Token (pos, ( Directive (Inline (Group1 ( toks_bl
                                                    , (tok1 as Token (_, (Sharp _, _)))
                                                      :: (tok2 as Token (_, (Ident, "include")))
                                                      :: toks)))
                        , s)) =>
              Token (pos, ( case toks of [Token (_, (File _, _))] =>
                              Directive (Include (Group2 (toks_bl, [tok1, tok2], toks)))
                            | _ => Error ("Expecting at least and at most one file" ^ Position.here (end_pos_of tok2), Group2 (toks_bl, [tok1, tok2], toks))
                          , s))
          | Token (pos, ( Directive (Inline (Group1 ( toks_bl
                                                    , (tok1 as Token (_, (Sharp _, _)))
                                                      :: (tok2 as Token (_, (Ident, "define")))
                                                      :: toks)))
                        , s)) =>
             Token (pos, ( case toks of
                            (tok3 as Token (_, (Ident, _))) :: toks =>
                            (case
                               case toks of
                                 (tok3' as Token (pos, (Keyword, "("(*)*)))) :: toks => 
                                   if Position.offset_of (end_pos_of tok3) = Position.offset_of (pos_of tok3')
                                   then let fun take_prefix' toks_bl toks_acc pos = fn
                                               (tok1 as Token (_, (Ident, _))) :: (tok2 as Token (pos2, (Keyword, key))) :: toks =>
                                                 if key = ","
                                                 then take_prefix' (tok2 :: toks_bl) (tok1 :: toks_acc) pos2 toks
                                                 else if key = (*( *)")" then Left (rev (tok2 :: toks_bl), rev (tok1 :: toks_acc), toks)
                                                 else Right ("Expecting a colon delimiter or a closing parenthesis" ^ Position.here (#1 pos2))
                                             | Token (pos1, (Ident, _)) :: _ => Right ("Expecting a colon delimiter or a closing parenthesis" ^ Position.here (#2 pos1))
                                             | _ => Right ("Expecting an identifier" ^ Position.here (#2 pos))
                                        in case
                                            case toks of
                                              (tok1 as Token (_, (Ident, _))) :: (tok2 as Token (_, (Keyword, (*( *)")"))) :: toks => Left ([tok2], [tok1], toks)
                                            | _ => take_prefix' [] [] pos toks
                                           of Left (toks_bl, toks_acc, toks) => Left (SOME (Group1 (tok3' :: toks_bl, toks_acc)), Group1 ([], toks))
                                            | Right x => Right x
                                        end
                                   else Left (NONE, Group1 ([], tok3' :: toks))
                               | _ => Left (NONE, Group1 ([], toks))
                             of Left (gr1, gr2) =>
                                  Directive (Define (Group1 (toks_bl, [tok1, tok2]), Group1 ([], [tok3]), gr1, gr2))
                              | Right msg => Error (msg, Group2 (toks_bl, [tok1, tok2], tok3 :: toks)))
                           | _ => Error ("Expecting at least one identifier" ^ Position.here (end_pos_of tok2), Group2 (toks_bl, [tok1, tok2], toks))
                         , s))
          | Token (pos, ( Directive (Inline (Group1 ( toks_bl
                                                    , (tok1 as Token (_, (Sharp _, _)))
                                                      :: (tok2 as Token (_, (Ident, "undef")))
                                                      :: toks)))
                        , s)) =>
              Token (pos, ( case toks of
                              [Token (_, (Ident, _))] => Directive (Undef (Group2 (toks_bl, [tok1, tok2], toks)))
                            | _ => Error ("Expecting at least and at most one identifier" ^ Position.here (end_pos_of tok2), Group2 (toks_bl, [tok1, tok2], toks))
                          , s))
          | x => x))

fun scan_cond xs = xs |>
  (one_start_cond -- scan_cond_list
   -- Scan.repeat (one_elif -- scan_cond_list)
   -- Scan.option (one_else -- scan_cond_list)
   -- Scan.recover one_endif
                   (fn msg =>
                     Scan.fail_with
                       (fn toks => fn () =>
                         case toks of
                           tok :: _ => "can be closed here" ^ Position.here (pos_of tok)
                         | _ => msg))
    >> (fn (((t_if, t_elif), t_else), t_endif) =>
         Token ( Position.no_range
               , ( Directive
                     (Conditional
                       let fun t_body x = x |-> get_cond
                       in
                       ( t_body t_if
                       , map t_body t_elif
                       , Option.map t_body t_else
                       , t_body (t_endif, []))
                       end)
                 , ""))))

and scan_cond_list xs = xs |> Scan.repeat (not_cond || scan_cond)

val scan_directive_cond0 =
     not_cond
  || Scan.ahead ( one_start_cond |-- scan_cond_list
                 |-- Scan.repeat (one_elif -- scan_cond_list)
                 |-- one_else --| scan_cond_list -- (one_elif || one_else))
     :-- (fn (tok1, tok2) => !!! ( "directive" ^ pos_here_of tok2
                                 ^ " not expected after" ^ pos_here_of tok1
                                 ^ ", detected at")
                                 Scan.fail)
     >> #2
  || (Scan.ahead one_start_cond |-- !!! "unclosed directive" scan_cond)
  || (Scan.ahead one_not_eof |-- !!! "missing or ambiguous beginning of conditional" Scan.fail)

fun scan_directive_recover msg =
     not_cond
  || one_not_eof >> (fn tok as Token (pos, (_, s)) => Token (pos, (Error (msg, get_cond tok []), s)))

in

val scan_directive_cond =
  Scan.recover
    (Scan.bulk scan_directive_cond0)
    (fn msg => scan_directive_recover msg >> single)

end

(* scan tokens, main *)

val scan_ml = scan_token scan_directive Directive
           || scan_fragment scan_blanks1;

fun recover msg =
 (recover_char ||
  recover_string ||
  Symbol_Pos.recover_cartouche ||
  C_Symbol_Pos.recover_comment ||
  one' Symbol.not_eof)
  >> token (Error (msg, Group1 ([], [])));

fun gen_read pos text =
  let
    val syms = Symbol_Pos.explode (text, pos);

    val termination =
      if null syms then []
      else
        let
          val pos1 = List.last syms |-> Position.advance;
          val pos2 = Position.advance Symbol.space pos1;
        in [Token (Position.range (pos1, pos2), (Space, Symbol.space))] end;

    val backslash1 = $$$ "\\" @@@ many C_Symbol.is_ascii_blank_no_line @@@ Scanner.newline
    val backslash2 = Scan.one (not o Symbol_Pos.is_eof)

    val input0 =
      Source.of_list syms
      |> Source.source Symbol_Pos.stopper (Scan.bulk (backslash1 >> SOME || backslash2 >> K NONE))
      |> Source.map_filter I
      |> Source.exhaust
      |> map (Symbol_Pos.range #> Position.range_position)

    val input1 =
      Source.of_list syms
      |> Source.source Symbol_Pos.stopper (Scan.bulk (backslash1 >> K NONE || backslash2 >> SOME))
      |> Source.map_filter I
      |> Source.source Symbol_Pos.stopper
                       (Scan.recover (Scan.bulk (!!! "bad input" scan_ml)) (fn msg => recover msg >> single))
      |> Source.source stopper scan_directive_cond
      |> Source.exhaust
      |> (fn input => input @ termination);

    fun get_antiq tok = case tok of
        Token (pos, (Comment (Left antiq), cts)) => [Left (pos, antiq, cts)]
      | Token (_, (Directive l, _)) =>
          maps (get_antiq #> map_filter (fn Left x => SOME (Left x) | _ => NONE)) (token_list_of l)
          @ [Right tok]
      | _ => [Right tok]

    val _ = app (fn pos => Output.information ("Backslash newline" ^ Position.here pos)) input0
    val _ = Position.reports_text ( map (fn pos => ((pos, Markup.intensify), "")) input0
                                  @ maps token_report input1);
    val _ = check input1;
  in maps get_antiq input1
end;

in

fun read_source source =
  let
    val pos = Input.pos_of source;
    val _ =
      if Position.is_reported_range pos
      then Position.report pos (Markup.language' {name = "C", symbols = false, antiquotes = true} (Input.is_delimited source))
      else ();
  in gen_read pos (Input.text_of source) end;

end;

end;
\<close>

end
