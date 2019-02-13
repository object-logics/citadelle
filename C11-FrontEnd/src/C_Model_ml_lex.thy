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

theory C_Model_ml_lex
  imports C_Model_ml
begin

section\<open> Basic Scanning Combinators from Isabelle \<close>

ML\<open>
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

val scan_cartouche_depth_inline = scan_cartouche_depth Scanner.newline

fun scan_cartouche_multi stop =
  Scan.ahead ($$ Symbol.open_) |--
    !!! "unclosed text cartouche within the comment delimiter"
      (Scan.provide is_none (SOME 0) (scan_cartouche_depth stop));

val scan_cartouche_inline =
  Scan.ahead ($$ Symbol.open_) |--
    !!! "unclosed text cartouche within the same line"
      (Scan.provide is_none (SOME 0) scan_cartouche_depth_inline);

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

type antiq = {start1: Position.T, start2: Position.T, stop: Position.T, range: Position.range, head: antiq_head, body: Symbol_Pos.T list};
datatype 'a antiquote = Text of 'a | Control of Antiquote.control | Antiq of Antiquote.antiq | ML_source of antiq;

(* scan *)

open Basic_Symbol_Pos;

local

val err_prefix = "Antiquotation lexical error: ";

val par_l = "/"
val par_r = "/"

val scan_body1 = $$$ "*" --| Scan.ahead (~$$$ par_r)
val scan_body2 = Scan.one (fn (s, _) => s <> "*" andalso Symbol.not_eof s) >> single

val many_blank = Scanner.many Symbol.is_ascii_blank

val scan_antiq_body_multi =
  Scan.trace (Symbol_Pos.scan_string_qq err_prefix || Symbol_Pos.scan_string_bq err_prefix) >> #2 ||
  C_Symbol_Pos.scan_cartouche_multi ($$$ "*" @@@ $$$ par_r) ||
  scan_body1 ||
  scan_body2;

val scan_antiq_body_inline =
  Scan.trace (C_Symbol_Pos.scan_string_qq_inline || C_Symbol_Pos.scan_string_bq_inline) >> #2 ||
  C_Symbol_Pos.scan_cartouche_inline ||
  Scanner.unless_eof Scanner.newline;

fun control_name sym = (case Symbol.decode sym of Symbol.Control name => name);

fun scan_antiq_multi scan =
  Symbol_Pos.scan_pos -- ($$ par_l |-- $$ "*" |-- scan -- Symbol_Pos.scan_pos --
    Symbol_Pos.!!! (fn () => err_prefix ^ "missing closing antiquotation")
      (Scan.repeats scan_antiq_body_multi -- Symbol_Pos.scan_pos -- ($$ "*" |-- $$ par_r |-- Symbol_Pos.scan_pos)))

fun scan_antiq_inline scan =
  (Symbol_Pos.scan_pos --| $$ "/" --| $$ "/" -- scan
  -- Symbol_Pos.scan_pos
  -- Scan.repeats scan_antiq_body_inline -- Symbol_Pos.scan_pos)

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
  let val sym = $$ "@" in
  scan_antiq_multi sym
  >> (fn (pos1, ((_, pos2), ((body, pos3), pos4))) =>
      {start = Position.range_position (pos1, pos2),
       stop = Position.range_position (pos3, pos4),
       range = Position.range (pos1, pos4),
       body = body}) ||
  scan_antiq_inline sym
  >> (fn ((((pos1, _), pos2), body), pos3) => 
      {start = Position.range_position (pos1, pos2),
       stop = Position.range_position (pos3, pos3),
       range = Position.range (pos1, pos3),
       body = body})
  end

val scan_ml_source =
  let val sym = $$ "@" |-- many_blank |--
                Symbol_Pos.scan_pos --
                (Scanner.this_string "setup" >> K Setup
                 || (Scan.repeat ($$ "@") --| many_blank --| Scanner.this_string "hook") >> Hook)
                --| Scanner.many Symbol.is_ascii_blank in
  scan_antiq_multi sym
  >> (fn (pos1, (((pos1', head), pos2), ((body, pos3), pos4))) =>
      {start1 = Position.range_position (pos1, pos1'),
       start2 = Position.range_position (pos1', pos2),
       stop = Position.range_position (pos3, pos4),
       range = Position.range (pos1, pos4),
       head = head,
       body = body}) ||
  scan_antiq_inline sym
  >> (fn ((((pos1, (pos1', head)), pos2), body), pos3) => 
      {start1 = Position.range_position (pos1, pos1'),
       start2 = Position.range_position (pos1', pos2),
       stop = Position.range_position (pos3, pos3),
       range = Position.range (pos1, pos3),
       head = head,
       body = body})

  end

end;

end;
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
  Integer of int * cIntRepr * cIntFlag list |
  Float |
  String of bool * Symbol.symbol list |
  File of bool * Symbol.symbol list |
  (**)
  Space | Comment of unit C_Antiquote.antiquote | Sharp of int |
  (**)
  Error of string * token_group | Directive of token_kind_directive | EOF

and token_kind_directive = Inline of token list (* spaces and comments firstly filtered *)
                                   * token_group
                         | Include of token_group
                         | Conditional of token_group (* if *)
                                        * token_group list (* elif *)
                                        * token_group option (* else *)
                                        * token_group (* endif *)

and token_group = Group0 of token list (* not yet analyzed *)
                | Group1 of (Position.range * token list) (* function *)
                | Group2 of (Position.range * token list) (* function *)
                          * (Position.range * token list) (* arguments (same line) *)
                | Group3 of (Position.range * token list) (* function *)
                          * (Position.range * token list) (* arguments (same line) *)
                          * (Position.range * token list) (* arguments (following lines) *)

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
   Inline (g0, g) => [Group0 g0, g] (* WARNING: positions may not be sorted in increase order *)
 | Include g => [g]
 | Conditional (c1, cs2, c3, c4) => flat [[c1], cs2, the_list c3, [c4]]

fun content_of (Token (_, (_, x))) = x;
fun token_leq (tok, tok') = content_of tok <= content_of tok';

fun is_keyword (Token (_, (Keyword, _))) = true
  | is_keyword _ = false;

fun is_ident (Token (_, (Ident, _))) = true
  | is_ident _ = false;

fun is_delimiter (Token (_, (Keyword, x))) = not (C_Symbol.is_ascii_identifier x)
  | is_delimiter _ = false;

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
  | _ => ();
end

val token_list_of = group_list_of #> maps (fn
    Group0 l => l
  | Group1 (_, l) => l
  | Group2 ((_, l1), (_, l2)) => flat [l1, l2]
  | Group3 ((_, l1), (_, l2), (_, l3)) => flat [l1, l2, l3])

fun check_error tok =
  case kind_of tok of
    Error (msg, _) => SOME msg
  | _ => NONE;

(* range *)

val range_list_of0 =
 fn [] => Position.no_range
  | toks as tok1 :: _ => Position.range (pos_of tok1, end_pos_of (List.last toks))
    (* WARNING the use of:
       fn tok2 => List.last (Symbol_Pos.explode (content_of tok2, pos_of tok2)) |-> Position.advance
       would not return an accurate position if for example several
       "backslash newlines" are present in the symbol *)

fun range_list_of toks = (range_list_of0 toks, toks)

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

(* markup *)

local

val token_kind_markup0 =
 fn Char _ => (Markup.ML_char, "")
  | Integer _ => (Markup.ML_numeral, "")
  | Float => (Markup.ML_numeral, "")
  | ClangC => (Markup.ML_numeral, "")
  | String _ => (Markup.ML_string, "")
  | File _ => (Markup.ML_string, "")
  | Comment (C_Antiquote.Text ()) => (Markup.ML_comment, "")
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
   | Directive (Include (Group2 (((pos1, _), toks1), ((pos2, _), toks2)))) =>
       ((pos1, Markup.antiquoted), "")
       :: ((pos2, Markup.antiquoted), "")
       :: flat [ maps token_report1 toks1
               , maps token_report0 toks2 ]
   | Directive (Conditional (c1, cs2, c3, c4)) =>
       maps (fn Group3 (((pos1, _), toks1), ((pos2, _), toks2), ((pos3, _), toks3)) => 
                ((pos1, Markup.antiquoted), "")
                :: ((pos2, Markup.antiquoted), "")
                :: ((pos3, Markup.intensify), "")
                :: flat [ maps token_report1 toks1
                        , maps token_report0 toks2
                        , maps token_report0 toks3]
              | _ => error "Only expecting Group3")
            (flat [[c1], cs2, the_list c3, [c4]])
   | Error (msg, Group3 (((pos1, _), toks1), (_, toks2), _)) =>
        ((pos1, Markup.bad ()), msg)
        :: ((pos, Markup.antiquoted), "")
        :: flat [ maps token_report1 toks1
                , maps token_report0 toks2]
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

val scan_intoct = scan_intgnu ((* NOTE: 0 is lexed as octal integer constant, and readCOctal takes care of this*)
                               $$ "0" |-- many C_Symbol.is_ascii_oct
                               >> (fn xs => (xs, read_oct, OctalRepr)))
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

local

fun token k ss = Token (Symbol_Pos.range ss, (k, Symbol_Pos.content ss));
fun scan_token f1 f2 = Scan.trace f1 >> (fn (v, s) => token (f2 v) s)

val comments =
  let fun scan_anti f1 f2 = scan_token f1 (Comment o f2) in
     scan_anti C_Antiquote.scan_ml_source C_Antiquote.ML_source
  || scan_anti C_Antiquote.scan_control C_Antiquote.Control
  || scan_anti C_Antiquote.scan_antiq C_Antiquote.Antiq
  || C_Symbol_Pos.scan_comment_no_nest >> token (Comment (C_Antiquote.Text ()))
  end

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
    @@@ (      blanks @@@ (scan_ident >> token Ident >> single)
            @@@ blanks @@@ (scan_token scan_file File >> single)
            @@@ blanks
         || Scan.repeat (   $$$ "#" @@@ $$$ "#" >> token (Sharp 2)
                         || $$$ "#" >> token (Sharp 1)
                         || scan_fragment many1_no_eol))
    >> (fn tokens => Inline (filter f_filter tokens, Group0 (filter_out f_filter tokens)))
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
  Scan.one (fn Token (_, (Directive (Inline (_, Group0 (Token (_, (Sharp 1, _)):: Token (_, s) :: _))), _)) => f s
             | _ => false)

val get_cond = fn Token (_, (Directive (Inline (toks_bl, Group0 (tok1 :: tok2 :: toks))), _)) =>
 (fn t3 => let val (t1, t2) = merge_blank toks_bl [tok1, tok2] toks
           in Group3 (t1, t2, range_list_of t3) end)
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
     >> (fn Token (pos, (Directive ( Inline ( toks_bl
                                            , Group0 ((tok1 as Token (_, (Sharp _, _)))
                                                   :: (tok2 as Token (_, (Ident, "include")))
                                                   :: (toks as [Token (_, (File _, _))]))))
                                 , s)) =>
              Token (pos, (Directive (Include (Group2 (merge_blank toks_bl [tok1, tok2] toks))), s))
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

val scan_ml =
 (scan_directive
  >> (fn tokens =>
        let val tokens' = token_list_of tokens in
          Token ( range_list_of0 tokens'
                , (Directive tokens, String.concatWith "" (map content_of tokens')))
        end)
  || scan_fragment scan_blanks1);

fun recover msg =
 (recover_char ||
  recover_string ||
  Symbol_Pos.recover_cartouche ||
  C_Symbol_Pos.recover_comment ||
  one' Symbol.not_eof)
  >> token (Error (msg, Group0 []));

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

    fun check tok =
      let val () = warn tok
      in case check_error tok of SOME s => cons s | NONE => I end

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
        Token (_, (Comment (C_Antiquote.Control c), _)) => [Antiquote.Control c]
      | Token (_, (Comment (C_Antiquote.Antiq a), _)) => [Antiquote.Antiq a]
      | Token (_, (Directive l, _)) => maps get_antiq (token_list_of l)
      | _ => []

    fun get_ml tok = case tok of
        Token (_, (Comment (C_Antiquote.ML_source {start1, start2, stop, range = (pos, _), ...}), _)) =>
                                          [(start1, Markup.antiquote),
                                           (start2, Markup.keyword1),
                                           (stop, Markup.antiquote),
                                           (pos, Markup.language_antiquotation)]
      | Token (_, (Directive l, _)) => maps get_ml (token_list_of l)
      | _ => []

    fun filter_ml tok = case tok of
        Token (_, (Comment (C_Antiquote.ML_source {head = head, body = body, ...}), _)) => [(head, body)]
      | Token (_, (Directive l, _)) => maps filter_ml (token_list_of l)
      | _ => []

    fun read_ml0 (head, body) =
                  body
                  |> Token.read_no_commands (Thy_Header.get_keywords' @{context}) Parse.ML_source
                  |> map (fn source => Left (head, Input.range_of source, ML_Lex.read_source false source))

    fun read_ml tok = case tok of
        Token (_, (Comment (C_Antiquote.ML_source {head = head, body = body, ...}), _)) => (read_ml0 (head, body))
      | Token (_, (Directive _, _)) => maps read_ml0 (filter_ml tok) @ [Right tok]
      | _ => [Right tok]

    val input' = maps get_antiq input1;

    val _ = Position.reports (Antiquote.antiq_reports input' @ maps get_ml input1);
    val _ = app (fn pos => Output.information ("Backslash newline" ^ Position.here pos)) input0
    val _ = Position.reports_text ( map (fn pos => ((pos, Markup.intensify), "")) input0
                                  @ maps token_report input1);
    val _ = case fold check input1 [] of [] => ()
                                       | l => error (String.concatWith "\n" (rev l));
  in (maps read_ml input1, input')
end;

in

fun read_source source =
  let
    val pos = Input.pos_of source;
    val _ =
      if Position.is_reported_range pos
      then Position.report pos (Markup.language_ML (Input.is_delimited source))
      else ();
  in gen_read pos (Input.text_of source) end;

end;

end;
\<close>

section \<open>Instantiation of the Parser with the Lexer\<close>
text\<open>The parser consists of a generic module @{file "../mlton/lib/mlyacc-lib/base.sig"}, 
which interprets a automata-like format generated from smlyacc.\<close>

ML\<open>
type 'a stack_elem = (LrTable.state * ('a * Position.T * Position.T))

fun map_svalue0 f (st, (v, pos1, pos2)) = (st, (f v, pos1, pos2))

structure Stack_Data = Theory_Data
  (type T = StrictCLrVals.Tokens.svalue0 stack_elem list
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

fun makeLexer input =
  let val s = Synchronized.var "input"
                (input 1024
                 |> map_filter (fn Right (C_Lex.Token (_, (C_Lex.Space, _))) => NONE
                                 | Right (C_Lex.Token (_, (C_Lex.Comment _, _))) => NONE
                                 | Right (C_Lex.Token (_, (C_Lex.Directive _, _))) => NONE
                                 | Right (C_Lex.Token s) => SOME (Right s)
                                 | Left ml => SOME (Left ml)))
      fun drain ((stack, stack_ml), arg as {tyidents, scopes, namesupply, context}) =
        let fun return0 x = (x, ((stack, stack_ml), {tyidents = tyidents, scopes = scopes, namesupply = namesupply, context = context}))
        in
          case Synchronized.change_result s (fn [] => (NONE, []) | x :: xs => (SOME x, xs))
          of SOME (Left (Setup, range, ants)) =>
               let val setup = "setup" in
                 context
                 |> Context.map_theory (Stack_Data.put stack)
                 |> ML_Context.expression
                      range
                      setup
                      "Stack_Data.T -> theory -> theory"
                      ("Context.map_theory (fn thy => " ^ setup ^ " (Stack_Data.get thy) thy)")
                      ants
                 |> (fn context => drain ((stack, stack_ml), {tyidents = tyidents, scopes = scopes, namesupply = namesupply, context = context}))
               end
           | SOME (Left (Hook syms, range, ants)) =>
               drain ( ( stack
                       , let
                           val () =
                             if length stack_ml = 1 orelse length stack_ml - length syms = 1 then
                               warning ("Unevaluated code as the hook is pointing to an internal initial value" ^ Position.here (range |> Position.range_position))
                             else ()
                           val () =
                             if length stack_ml - length syms <= 0 then
                               error ("Maximum depth reached (" ^ Int.toString (length syms - length stack_ml + 1) ^ " in excess)" ^ Position.here (Symbol_Pos.range syms |> Position.range_position))
                             else ()
                         in nth_map (length syms) (fn xs => (range, ants) :: xs) stack_ml end)
                     , arg)
           | NONE => return0 (Tokens.x25_eof (Position.none, Position.none))
           | SOME (Right ((pos1, pos2), (C_Lex.Char (b, [c]), _))) =>
              return0 (StrictCLrVals.Tokens.cchar (CChar (String.sub (c,0)) b, pos1, pos2))
           | SOME (Right ((pos1, pos2), (C_Lex.Char (b, _), _))) => error "to do"
           | SOME (Right ((pos1, pos2), (C_Lex.String (b, s), _))) =>
              return0 (StrictCLrVals.Tokens.cstr (CString0 (From_string (implode s), b), pos1, pos2))
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
              let val ty_ident = Ident (From_string s, 0, OnlyPos NoPosition (NoPosition, 0))
              in return0 (if Hsk_c_parser.isTypeIdent s arg then
                            (Position.reports_text [((pos1, Markup.ML_keyword3 |> Markup.keyword_properties), "")];
                            StrictCLrVals.Tokens.tyident (ty_ident, pos1, pos2))
                          else
                            StrictCLrVals.Tokens.ident (ty_ident, pos1, pos2))
              end
           | SOME (Right ((pos1, pos2), (_, s))) => 
                       token_of_string (Tokens.error (pos1, pos2))
                                       (ClangCVersion0 (From_string s))
                                       (CChar #"0" false)
                                       (CFloat (From_string s))
                                       (CInteger 0 DecRepr (Flags 0))
                                       (CString0 (From_string s, false))
                                       (Ident (From_string s, 0, OnlyPos NoPosition (NoPosition, 0)))
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
  fun parse s context =
   {tyidents = Symtab.make [], scopes = [], namesupply = 0(*"mlyacc_of_happy"*), context = context}
   |> StrictCParser.makeLexer (fn _ => s)
   |> StrictCParser.parse
        ( 0
        , fn (stack, pos1, pos2) =>
            let val range_pos = I #> Position.range #> Position.range_position
                val () = Position.reports_text [( ( range_pos (case hd stack of (_, (_, pos1, pos2)) => (pos1, pos2))
                                                  , Markup.bad ())
                                                , "")]
            in Scan.error (Symbol_Pos.!!! (K "Syntax error") Scan.fail)
                          [("", range_pos (pos1, pos2))]
            end
        , Position.none
        , fn (((rule, stack0), (range, ants)), {tyidents, scopes, namesupply, context}) =>
               let val stack = [stack0]
                   val hook = "hook" in
                 context
                 |> Context.map_theory (Stack_Data.put stack)
                 |> ML_Context.expression
                      range
                      hook
                      (MlyValue.type_reduce rule ^ " stack_elem -> theory -> theory")
                      ("Context.map_theory (fn thy => " ^ hook ^ " (Stack_Data.get thy |> hd |> map_svalue0 MlyValue.reduce" ^ Int.toString rule ^ ") thy)")
                      ants
                 |> (fn context => {tyidents = tyidents, scopes = scopes, namesupply = namesupply, context = context})
               end
        , fn (_, arg) => arg)
   ||> (fn (_, {context = context, ...}) => context)
end
\<close>

section \<open>The Construction of an C-Context (analogously to the standard ML context)\<close>

ML\<open>
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

end;

fun eval' flags pos (ants, ants') =
  let val _ = ML_Context.eval flags pos (case ML_Lex.read "(,)" of
                              [par_l, colon, par_r, space] =>
                                par_l ::
                                (ants'
                                |> separate colon)
                                @ [par_r, space]
                              | _ => [])
      fun print s ants =
            app
              (fn C_Lex.Token (_, (t as C_Lex.Directive d, _)) =>
                  let val _ = Output.state (s ^ @{make_string} t)
                  in print (s ^ "  ") (C_Lex.token_list_of d) end
                | C_Lex.Token (_, t) => 
                  (case t of (C_Lex.Char _, _) => writeln "Text Char"
                           | (C_Lex.String _, _) => writeln "Text String"
                           | _ => let val t' = @{make_string} (#2 t)
                                  in
                                    if String.size t' <= 2 then Output.state (@{make_string} (#1 t))
                                    else
                                      Output.state (s ^ @{make_string} (#1 t) ^ " "
                                                   ^ (String.substring (t', 1, String.size t' - 2)
                                                      |> Markup.markup Markup.intensify))
                                  end))
              ants
      val _ = print "" (maps (fn Right x => [x] | _ => []) ants)
      val (_, context) = P.parse ants (Context.the_generic_context ())
  in Context.put_generic_context (SOME context)
  end

fun eval_source flags source =
  eval' flags (Input.pos_of source) (C_Lex.read_source source);

end
\<close>

end
