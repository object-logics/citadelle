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
  keywords "C_lex" :: thy_decl
begin

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
infixr 5 @@@@;

structure Scanner =
struct
open Basic_Symbol_Pos;

val err_prefix = "C lexical error: ";

fun !!! msg = Symbol_Pos.!!! (fn () => err_prefix ^ msg);
fun opt x = Scan.optional x [];
fun opt' x = Scan.optional x ([], []);
fun opt'' x = Scan.optional (x >> rpair true) ([], false);
fun one f = Scan.one (f o Symbol_Pos.symbol)
fun many f = Scan.many (f o Symbol_Pos.symbol)
fun many1 f = Scan.many1 (f o Symbol_Pos.symbol)
val one' = Scan.single o one
fun scan_full mem msg scan =
  scan --| (Scan.ahead (one' (not o mem)) || !!! msg Scan.fail)
fun (scan1 @@@@ scan2) = scan1 -- scan2 >> (fn ((l11, l12), (l21, l22)) => (l11 @ l21, l12 @ l22))
fun $$$$ x = $$$ x >> rpair []
fun flat' l = let val (l1, l2) = map_split I l in (flat l1, flat l2) end
fun repeats' scan = Scan.repeat scan >> flat'
fun repeats1' scan = Scan.repeat1 scan >> flat'
fun repeats_one_not_eof scan =
  Scan.repeats (Scan.unless scan
                            (Scan.one (fn (s, _) => Symbol.not_eof s) >> single))
val newline =   $$$ "\n"
             || $$$ "\^M" @@@ $$$ "\n"
             || $$$ "\^M"
val repeats_until_nl = repeats_one_not_eof newline
end
\<close>

ML\<open>
(*  Title:      Pure/General/symbol_pos.ML
    Author:     Makarius

Symbols with explicit position information.
*)

structure C_Symbol_Pos =
struct
val !!! = Symbol_Pos.!!!
val $$ = Symbol_Pos.$$
val $$$ = Symbol_Pos.$$$
val ~$$$ = Symbol_Pos.~$$$

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

fun scan_comment err_prefix =
  Scan.ahead ($$ par_l -- $$ "*") |--
    !!! (fn () => err_prefix ^ "unclosed comment")
      ($$$ par_l @@@ $$$ "*" @@@ scan_cmts @@@ $$$ "*" @@@ $$$ par_r)
  || $$$ "/" @@@ $$$ "/" @@@ Scanner.repeats_until_nl;

fun scan_comment_no_nest err_prefix =
  Scan.ahead ($$ par_l -- $$ "*") |--
    !!! (fn () => err_prefix ^ "unclosed comment")
      ($$$ par_l @@@ $$$ "*" @@@ Scan.repeats (scan_body1 || scan_body2) @@@ $$$ "*" @@@ $$$ par_r)
  || $$$ "/" @@@ $$$ "/" @@@ Scanner.repeats_until_nl;

end
end
\<close>

ML\<open>
(*  Title:      Pure/ML/ml_lex.ML
    Author:     Makarius

Lexical syntax for Isabelle/ML and Standard ML.
*)

structure C_Lex =
struct

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
  (**)
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

fun is_delimiter (Token (_, (Keyword, x))) = not (C_Symbol.is_ascii_identifier x)
  | is_delimiter _ = false;

val warn = K ();

fun check_content_of tok =
  (case kind_of tok of
    Error msg => error msg
  | _ => content_of tok);

(* markup *)

local

val token_kind_markup =
 fn Char _ => (Markup.ML_char, "")
  | Integer _ => (Markup.ML_numeral, "")
  | Float => (Markup.ML_numeral, "")
  | ClangC => (Markup.ML_numeral, "")
  | String _ => (Markup.ML_string, "")
  | Comment => (Markup.ML_comment, "")
  | Error msg => (Markup.bad (), msg)
  | _ => (Markup.empty, "");

in

fun token_report (tok as Token ((pos, _), (kind, x))) =
  let
    val (markup, txt) =
      if not (is_keyword tok) then token_kind_markup kind
      else if is_delimiter tok then (Markup.ML_delimiter, "")
      else if member (op =) keywords2 x then (Markup.ML_keyword2 |> Markup.keyword_properties, "")
      else if member (op =) keywords3 x then (Markup.ML_keyword3 |> Markup.keyword_properties, "")
      else (Markup.ML_keyword1 |> Markup.keyword_properties, "");
  in ((pos, markup), txt) end;

end;


(** scanners **)
open Scanner;

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

val scan_suffix_ll = ($$$ "l" @@@ $$$ "l" || $$$ "L" @@@ $$$ "L") >> rpair [FlagLongLong]
fun scan_suffix_gnu flag = ($$$ "i" || $$$ "j") >> rpair [flag]
val scan_suffix_int = 
  let val u = ($$$ "u" || $$$ "U") >> rpair [FlagUnsigned]
      val l = ($$$ "l" || $$$ "L") >> rpair [FlagLong] in
      u @@@@ scan_suffix_ll
   || scan_suffix_ll @@@@ opt' u
   || u @@@@ opt' l
   || l @@@@ opt' u
  end

val scan_suffix_gnu_int0 = scan_suffix_gnu FlagImag
val scan_suffix_gnu_int = scan_full (member (op =) (raw_explode "uUlLij"))
                                    "Invalid integer constant suffix"
                                    (   scan_suffix_int @@@@ opt' scan_suffix_gnu_int0
                                     || scan_suffix_gnu_int0 @@@@ opt' scan_suffix_int)

fun scan_intgnu x =
  x -- opt' scan_suffix_gnu_int
  >> (fn ((s1, s1', read, repr), (s2, l)) => (s1 @ s2, (read (map (Symbol_Pos.content o single) s1'), repr, l)))

val scan_intoct = scan_intgnu ((* NOTE: 0 is lexed as octal integer constant, and readCOctal takes care of this*)
                               $$ "0" -- many C_Symbol.is_ascii_oct
                               >> (fn (x, xs) => (x :: xs, xs, read_oct, OctalRepr)))
val scan_intdec = scan_intgnu (one C_Symbol.is_ascii_digit1 -- many Symbol.is_ascii_digit
                               >> (fn (x, xs) => let val xs = x :: xs in (xs, xs, read_dec, DecRepr) end))
val scan_inthex = scan_intgnu (($$$ "0" @@@ ($$$ "x" || $$$ "X")) -- many1_hex
                               >> (fn (xs1, xs2) => (xs1 @ xs2, xs2, read_hex, HexRepr)))

(**)

fun scan_signpart a A = ($$$ a || $$$ A) @@@ opt ($$$ "+" || $$$ "-") @@@ many1_digit
val scan_exppart = scan_signpart "e" "E"

val scan_suffix_float = $$$ "f" || $$$ "F" || $$$ "l" || $$$ "L"
val scan_suffix_gnu_float0 = scan_suffix_gnu () >> #1
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
      fun read_oct' l = (List.concat l, [chr (read_oct (map Symbol_Pos.content l))])
  in one' (member (op =) (raw_explode (s0 ^ String.concat (map #1 escape_char))))
     >> (fn i =>
          (i, [case AList.lookup (op =) escape_char (Symbol_Pos.content i) of
                 NONE => s0
               | SOME c => String.str c]))
  || oct -- oct -- oct >> (fn ((o1, o2), o3) => read_oct' [o1, o2, o3])
  || oct -- oct >> (fn (o1, o2) => read_oct' [o1, o2])
  || oct >> (read_oct' o single)
  || $$ "x" -- many1 Symbol.is_ascii_hex
     >> (fn (x, xs) => (x :: xs, [chr (read_hex (map (Symbol_Pos.content o single) xs))]))
  || $$$ "u" -- hex -- hex -- hex -- hex
     >> (fn ((((x, x1), x2), x3), x4) =>
          (List.concat [x, x1, x2, x3, x4], [chr (read_hex (map Symbol_Pos.content [x1, x2, x3, x4]))]))
  || $$$ "U" -- hex -- hex -- hex -- hex -- hex -- hex -- hex -- hex
     >> (fn ((((((((x, x1), x2), x3), x4), x5), x6), x7), x8) =>
          ( List.concat [x, x1, x2, x3, x4, x5, x6, x7, x8]
          , [chr (read_hex (map Symbol_Pos.content [x1, x2, x3, x4, x5, x6, x7, x8]))]))
  end

fun scan_str s0 =
     Scan.one (fn (s, _) => Symbol.not_eof s andalso s <> s0 andalso s <> "\\")
     >> (fn s => ([s], [#1 s]))
  || $$$$ "\\" @@@@ !!! "bad escape character" (scan_escape s0);

val scan_gap = $$$ "\\" @@@ scan_blanks1 @@@ $$$ "\\";

fun scan_string0 s0 msg repeats =
  opt'' ($$$ "L") --
    (Scan.ahead ($$ s0) |--
      !!! ("unclosed " ^ msg ^ " literal")
        ($$$$ s0 @@@@ repeats (scan_gap >> rpair [] || scan_str s0) @@@@ $$$$ s0))
  >> (fn ((s1, v1), (s2, v2)) => (s1 @ s2, (v1, v2)))

fun recover_string0 s0 repeats =
  opt ($$$ "L") @@@ $$$ s0 @@@ repeats (scan_gap || Scan.permissive (scan_str s0 >> #1));
in

val scan_char = scan_string0 "'" "char" repeats1'
val scan_string = scan_string0 "\"" "string" repeats'

val recover_char = recover_string0 "'" Scan.repeats1
val recover_string = recover_string0 "\"" Scan.repeats

end;

(* scan tokens *)

local

fun token k ss = Token (Symbol_Pos.range ss, (k, Symbol_Pos.content ss));
fun token' f (s, v) = token (f v) s;

val scan_ml =
 (scan_char >> token' Char ||
  scan_string >> token' String ||
  scan_blanks1 >> token Space ||
  C_Symbol_Pos.scan_comment_no_nest err_prefix >> token Comment ||
  Scan.max token_leq
   (Scan.literal lexicon >> token Keyword)
   (scan_clangversion >> token ClangC ||
    scan_float >> token Float ||
    scan_int >> token' Integer ||
    scan_ident >> token Ident));

val scan_ml_antiq =
  Antiquote.scan_control >> Antiquote.Control ||
  Antiquote.scan_antiq >> Antiquote.Antiq ||
  scan_ml >> Antiquote.Text;

fun recover msg =
 (recover_char ||
  recover_string ||
  Symbol_Pos.recover_cartouche ||
  Symbol_Pos.recover_comment ||
  one' Symbol.not_eof)
  >> (single o token (Error msg));

fun gen_read pos text =
  let
    val syms = Symbol_Pos.explode (text, pos);

    val termination =
      if null syms then []
      else
        let
          val pos1 = List.last syms |-> Position.advance;
          val pos2 = Position.advance Symbol.space pos1;
        in [Antiquote.Text (Token (Position.range (pos1, pos2), (Space, Symbol.space)))] end;

    fun check (Antiquote.Text tok) = (check_content_of tok; warn tok)
      | check _ = ();
    val input =
      Source.of_list syms
      |> Source.source Symbol_Pos.stopper
                       (Scan.bulk (   ($$$ "\\" @@@ many C_Symbol.is_ascii_blank_no_line) --| Scanner.newline
                                      >> (fn l => (Output.information ("Backslash newline" ^ Position.here (Symbol_Pos.range l |> Position.range_position)); NONE))
                                   || Scan.one (K true) >> SOME))
      |> Source.map_filter I
      |> Source.source Symbol_Pos.stopper
        (Scan.recover (Scan.bulk (!!! "bad input" scan_ml_antiq))
          (fn msg => recover msg >> map Antiquote.Text))
      |> Source.exhaust;
    val _ = Position.reports (Antiquote.antiq_reports input);
    val _ =
      Position.reports_text (maps (fn Antiquote.Text t => [token_report t] | _ => []) input);
    val _ = List.app check input;
  in input @ termination end;

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

ML\<open>
(*  Title:      Pure/ML/ml_context.ML
    Author:     Makarius

ML context and antiquotations.
*)

structure C_Context =
struct
fun eval_source source =
  app
    (fn Antiquote.Text (C_Lex.Token t) => 
        (case #2 t of (C_Lex.Char _, _) => writeln "Text Char"
                    | (C_Lex.String _, _) => writeln "Text String"
                    | _ => writeln (@{make_string} (Antiquote.Text (#2 t))))
      | Antiquote.Control c => writeln (@{make_string} (Antiquote.Control c))
      | Antiquote.Antiq a => writeln (@{make_string} (Antiquote.Antiq a)))
    (C_Lex.read_source source)
end
\<close>

ML\<open>
(*  Title:      Pure/ML/ml_file.ML
    Author:     Makarius

Commands to load ML files.
*)

structure ML_File =
struct

fun command SML debug files = Toplevel.generic_theory (fn gthy =>
  let
    val [{src_path, lines, digest, pos}: Token.file] = files (Context.theory_of gthy);
    val provide = Resources.provide (src_path, digest);
    val source = Input.source true (cat_lines lines) (pos, pos);
    val flags =
      {SML = SML, exchange = false, redirect = true, verbose = true,
        debug = debug, writeln = writeln, warning = warning};
  in
    gthy
    |> ML_Context.exec (fn () => ML_Context.eval_source flags source)
    |> Local_Theory.propagate_ml_env
    |> Context.mapping provide (Local_Theory.background_theory provide)
  end);

val ML = command false;
val SML = command true;

end;
\<close>

ML\<open>

structure C_Outer_Syntax =
struct
val _ =
  Outer_Syntax.command @{command_keyword C_lex} ""
    (Parse.input (Parse.group (fn () => "C source") Parse.text) >> (fn source =>
      Toplevel.generic_theory
        (ML_Context.exec (fn () =>
            C_Context.eval_source source) #>
          Local_Theory.propagate_ml_env)))
end
\<close>

C_lex \<comment> \<open>\<^url>\<open>https://gcc.gnu.org/onlinedocs/cpp/Initial-processing.html\<close>\<close> \<open>
/* inside /* inside */ int a = "outside";
// inside // inside until end of line
int a = "outside";
/* inside
  // inside
inside
*/ int a = "outside";
// inside /* inside until end of line
int a = "outside";
\<close>

C_lex \<comment> \<open>\<^url>\<open>https://gcc.gnu.org/onlinedocs/cpp/Initial-processing.html\<close>\<close> \<open>
/\
*
*/
@{abc\
def} // break of line activated everywhere (also in antiquotations)
i\    
n\                
t a = "/* //  /\ 
*\
fff */\
";
\<close>

end
