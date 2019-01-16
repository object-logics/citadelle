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
  imports Main
  keywords "C_lex" :: thy_decl
begin

ML\<open>
(*  Title:      Pure/ML/ml_lex.ML
    Author:     Makarius

Lexical syntax for Isabelle/ML and Standard ML.
*)

structure C_Lex =
struct

(** keywords **)

val keywords =
 ["#", "(", ")", ",", "->", "...", ":", ":>", ";", "=", "=>", "[",
  "]", "_", "{", "|", "}", "abstype", "and", "andalso", "as", "case",
  "datatype", "do", "else", "end", "eqtype", "exception", "fn", "fun",
  "functor", "handle", "if", "in", "include", "infix", "infixr",
  "let", "local", "nonfix", "of", "op", "open", "orelse", "raise",
  "rec", "sharing", "sig", "signature", "struct", "structure", "then",
  "type", "val", "where", "while", "with", "withtype"];

val keywords2 =
 ["and", "case", "do", "else", "end", "if", "in", "let", "local", "of",
  "sig", "struct", "then", "while", "with"];

val keywords3 =
 ["handle", "open", "raise"];

val lexicon = Scan.make_lexicon (map raw_explode keywords);



(** tokens **)

(* datatype token *)

datatype token_kind =
  Keyword | Ident | Long_Ident | Type_Var | Word | Int | Real | Char | String |
  Space | Comment | Error of string | EOF;

datatype token = Token of Position.range * (token_kind * string);


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


(* token content *)

fun kind_of (Token (_, (k, _))) = k;

fun content_of (Token (_, (_, x))) = x;
fun token_leq (tok, tok') = content_of tok <= content_of tok';

fun is_keyword (Token (_, (Keyword, _))) = true
  | is_keyword _ = false;

fun is_delimiter (Token (_, (Keyword, x))) = not (Symbol.is_ascii_identifier x)
  | is_delimiter _ = false;

fun is_regular (Token (_, (Error _, _))) = false
  | is_regular (Token (_, (EOF, _))) = false
  | is_regular _ = true;

fun is_improper (Token (_, (Space, _))) = true
  | is_improper (Token (_, (Comment, _))) = true
  | is_improper _ = false;

fun warn tok =
  (case tok of
    Token (_, (Keyword, ":>")) =>
      warning ("Opaque signature matching (:>) fails to work with ML pretty printing --\n\
        \prefer non-opaque matching (:) possibly with abstype" ^
        Position.here (pos_of tok))
  | _ => ());

fun check_content_of tok =
  (case kind_of tok of
    Error msg => error msg
  | _ => content_of tok);


(* flatten *)

fun flatten_content (tok :: (toks as tok' :: _)) =
      Symbol.escape (check_content_of tok) ::
        (if is_improper tok orelse is_improper tok' then flatten_content toks
         else Symbol.space :: flatten_content toks)
  | flatten_content toks = map (Symbol.escape o check_content_of) toks;

val flatten = implode o flatten_content;


(* markup *)

local

fun token_kind_markup SML =
 fn Type_Var => (Markup.ML_tvar, "")
  | Word => (Markup.ML_numeral, "")
  | Int => (Markup.ML_numeral, "")
  | Real => (Markup.ML_numeral, "")
  | Char => (Markup.ML_char, "")
  | String => (if SML then Markup.SML_string else Markup.ML_string, "")
  | Comment => (if SML then Markup.SML_comment else Markup.ML_comment, "")
  | Error msg => (Markup.bad (), msg)
  | _ => (Markup.empty, "");

in

fun token_report SML (tok as Token ((pos, _), (kind, x))) =
  let
    val (markup, txt) =
      if not (is_keyword tok) then token_kind_markup SML kind
      else if is_delimiter tok then (Markup.ML_delimiter, "")
      else if member (op =) keywords2 x then (Markup.ML_keyword2 |> Markup.keyword_properties, "")
      else if member (op =) keywords3 x then (Markup.ML_keyword3 |> Markup.keyword_properties, "")
      else (Markup.ML_keyword1 |> Markup.keyword_properties, "");
  in ((pos, markup), txt) end;

end;



(** scanners **)

open Basic_Symbol_Pos;

val err_prefix = "SML lexical error: ";

fun !!! msg = Symbol_Pos.!!! (fn () => err_prefix ^ msg);


(* identifiers *)

local

val scan_letdigs =
  Scan.many (Symbol.is_ascii_letdig o Symbol_Pos.symbol);

val scan_alphanumeric =
  Scan.one (Symbol.is_ascii_letter o Symbol_Pos.symbol) ::: scan_letdigs;

val scan_symbolic =
  Scan.many1 (member (op =) (raw_explode "!#$%&*+-/:<=>?@\\^`|~") o Symbol_Pos.symbol);

in

val scan_ident = scan_alphanumeric || scan_symbolic;

val scan_long_ident =
  Scan.repeats1 (scan_alphanumeric @@@ $$$ ".") @@@ (scan_ident || $$$ "=");

val scan_type_var = $$$ "'" @@@ scan_letdigs;

end;


(* numerals *)

local

val scan_dec = Scan.many1 (Symbol.is_ascii_digit o Symbol_Pos.symbol);
val scan_hex = Scan.many1 (Symbol.is_ascii_hex o Symbol_Pos.symbol);
val scan_sign = Scan.optional ($$$ "~") [];
val scan_decint = scan_sign @@@ scan_dec;
val scan_exp = ($$$ "E" || $$$ "e") @@@ scan_decint;

in

val scan_word =
  $$$ "0" @@@ $$$ "w" @@@ $$$ "x" @@@ scan_hex ||
  $$$ "0" @@@ $$$ "w" @@@ scan_dec;

val scan_int = scan_sign @@@ ($$$ "0" @@@ $$$ "x" @@@ scan_hex || scan_dec);

val scan_rat = scan_decint @@@ Scan.optional ($$$ "/" @@@ scan_dec) [];

val scan_real =
  scan_decint @@@ $$$ "." @@@ scan_dec @@@ Scan.optional scan_exp [] ||
  scan_decint @@@ scan_exp;

end;


(* chars and strings *)

val scan_blanks1 = Scan.many1 (Symbol.is_ascii_blank o Symbol_Pos.symbol);

local

val scan_escape =
  Scan.one (member (op =) (raw_explode "\"\\abtnvfr") o Symbol_Pos.symbol) >> single ||
  $$$ "^" @@@
    (Scan.one (fn (s, _) => Char.ord #"@" <= ord s andalso ord s <= Char.ord #"_") >> single) ||
  Scan.one (Symbol.is_ascii_digit o Symbol_Pos.symbol) --
    Scan.one (Symbol.is_ascii_digit o Symbol_Pos.symbol) --
    Scan.one (Symbol.is_ascii_digit o Symbol_Pos.symbol) >> (fn ((a, b), c) => [a, b, c]);

val scan_str =
  Scan.one (fn (s, _) => Symbol.not_eof s andalso s <> "\"" andalso s <> "\\" andalso
    (not (Symbol.is_char s) orelse Symbol.is_printable s)) >> single ||
  $$$ "\\" @@@ !!! "bad escape character in string" scan_escape;

val scan_gap = $$$ "\\" @@@ scan_blanks1 @@@ $$$ "\\";
val scan_gaps = Scan.repeats scan_gap;

in

val scan_char =
  $$$ "#" @@@ $$$ "\"" @@@ scan_gaps @@@ scan_str @@@ scan_gaps @@@ $$$ "\"";

val recover_char =
  $$$ "#" @@@ $$$ "\"" @@@ scan_gaps @@@ Scan.optional (Scan.permissive scan_str @@@ scan_gaps) [];

val scan_string =
  Scan.ahead ($$ "\"") |--
    !!! "unclosed string literal"
      ($$$ "\"" @@@ Scan.repeats (scan_gap || scan_str) @@@ $$$ "\"");

val recover_string =
  $$$ "\"" @@@ Scan.repeats (scan_gap || Scan.permissive scan_str);

end;


(* rat antiquotation *)

val rat_name = Symbol_Pos.explode ("Pure.rat ", Position.none);

val scan_rat_antiq =
  Symbol_Pos.scan_pos -- ($$ "@" |-- Symbol_Pos.scan_pos -- scan_rat) -- Symbol_Pos.scan_pos
    >> (fn ((pos1, (pos2, body)), pos3) =>
      {start = Position.range_position (pos1, pos2),
       stop = Position.none,
       range = Position.range (pos1, pos3),
       body = rat_name @ body});


(* scan tokens *)

local

fun token k ss = Token (Symbol_Pos.range ss, (k, Symbol_Pos.content ss));

val scan_ml =
 (scan_char >> token Char ||
  scan_string >> token String ||
  scan_blanks1 >> token Space ||
  Symbol_Pos.scan_comment err_prefix >> token Comment ||
  Scan.max token_leq
   (Scan.literal lexicon >> token Keyword)
   (scan_word >> token Word ||
    scan_real >> token Real ||
    scan_int >> token Int ||
    scan_long_ident >> token Long_Ident ||
    scan_ident >> token Ident ||
    scan_type_var >> token Type_Var));

val scan_sml = scan_ml >> Antiquote.Text;

val scan_ml_antiq =
  Antiquote.scan_control >> Antiquote.Control ||
  Antiquote.scan_antiq >> Antiquote.Antiq ||
  scan_rat_antiq >> Antiquote.Antiq ||
  scan_ml >> Antiquote.Text;

fun recover msg =
 (recover_char ||
  recover_string ||
  Symbol_Pos.recover_cartouche ||
  Symbol_Pos.recover_comment ||
  Scan.one (Symbol.not_eof o Symbol_Pos.symbol) >> single)
  >> (single o token (Error msg));

fun gen_read SML pos text =
  let
    val syms =
      Symbol_Pos.explode (text, pos)
      |> SML ? maps (fn (s, p) => raw_explode s |> map (rpair p));

    val termination =
      if null syms then []
      else
        let
          val pos1 = List.last syms |-> Position.advance;
          val pos2 = Position.advance Symbol.space pos1;
        in [Antiquote.Text (Token (Position.range (pos1, pos2), (Space, Symbol.space)))] end;

    val scan = if SML then scan_sml else scan_ml_antiq;
    fun check (Antiquote.Text tok) = (check_content_of tok; if SML then () else warn tok)
      | check _ = ();
    val input =
      Source.of_list syms
      |> Source.source Symbol_Pos.stopper
        (Scan.recover (Scan.bulk (!!! "bad input" scan))
          (fn msg => recover msg >> map Antiquote.Text))
      |> Source.exhaust;
    val _ = Position.reports (Antiquote.antiq_reports input);
    val _ =
      Position.reports_text (maps (fn Antiquote.Text t => [token_report SML t] | _ => []) input);
    val _ = List.app check input;
  in input @ termination end;

in

fun source src =
  Symbol_Pos.source (Position.line 1) src
  |> Source.source Symbol_Pos.stopper (Scan.recover (Scan.bulk (!!! "bad input" scan_ml)) recover);

val tokenize = Symbol.explode #> Source.of_list #> source #> Source.exhaust;

val read_pos = gen_read false;

val read = read_pos Position.none;

fun read_set_range range =
  read #> map (fn Antiquote.Text tok => Antiquote.Text (set_range range tok) | antiq => antiq);

fun read_source SML source =
  let
    val pos = Input.pos_of source;
    val language = if SML then Markup.language_SML else Markup.language_ML;
    val _ =
      if Position.is_reported_range pos
      then Position.report pos (language (Input.is_delimited source))
      else ();
  in gen_read SML pos (Input.text_of source) end;

end;

end;
\<close>

ML\<open>
structure C_Context =
struct
fun eval_source source =
  app
    (fn s =>
      writeln
        (@{make_string}
          (case s of Antiquote.Text (C_Lex.Token t) => Antiquote.Text (#2 t)
                   | Antiquote.Control c => Antiquote.Control c
                   | Antiquote.Antiq a => Antiquote.Antiq a)))
    (C_Lex.read_source false source)
end

structure C_Outer_Syntax =
struct
val _ =
  Outer_Syntax.command @{command_keyword C_lex} ""
    (Parse.ML_source >> (fn source =>
      Toplevel.generic_theory
        (ML_Context.exec (fn () =>
            C_Context.eval_source source) #>
          Local_Theory.propagate_ml_env)))
end
\<close>

end
