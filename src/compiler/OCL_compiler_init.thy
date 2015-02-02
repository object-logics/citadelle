(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_init.thy ---
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013-2015 Université Paris-Sud, France
 *               2013-2015 IRT SystemX, France
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
(* $Id:$ *)

header{* Part ... *}

theory OCL_compiler_init
imports "~~/src/HOL/Library/Code_Char"
        OCL_compiler_static
  keywords (* hol syntax *)
           "fun_sorry" "fun_quick"
           "definition\<acute>"
           :: thy_decl
begin

section{* ... *}

type_notation natural ("nat")
definition "Succ x = x + 1"

datatype string\<^sub>b\<^sub>a\<^sub>s\<^sub>e = ST String.literal
                   | ST' "char list"

datatype abr_string = (* NOTE operations in this datatype must not decrease the size of the string *)
                      SS_base string\<^sub>b\<^sub>a\<^sub>s\<^sub>e
                    | String_concatWith abr_string "abr_string list"

syntax "_string1" :: "_ \<Rightarrow> abr_string" ("\<langle>(_)\<rangle>")
translations "\<langle>x\<rangle>" \<rightleftharpoons> "CONST SS_base (CONST ST (CONST STR x))"

syntax "_string2" :: "_ \<Rightarrow> String.literal" ("\<prec>(_)\<succ>")
translations "\<prec>x\<succ>" \<rightleftharpoons> "CONST STR x"

syntax "_string3" :: "_ \<Rightarrow> abr_string" ("\<lless>(_)\<ggreater>")
translations "\<lless>x\<ggreater>" \<rightleftharpoons> "CONST SS_base (CONST ST' x)"

syntax "_char1" :: "_ \<Rightarrow> abr_string" ("\<degree>(_)\<degree>")
translations "\<degree>x\<degree>" \<rightleftharpoons> "CONST SS_base (CONST ST' ((CONST Cons) x (CONST Nil)))"

syntax "_char2" :: "_ \<Rightarrow> String.literal" ("\<ordmasculine>(_)\<ordmasculine>")
translations "\<ordmasculine>x\<ordmasculine>" \<rightleftharpoons> "CONST STR ((CONST Cons) x (CONST Nil))"

type_notation abr_string ("string")

section{* ... *}

ML {*
  local
    val mk_nib =
      Syntax.const o Lexicon.mark_const o
        fst o Term.dest_Const o HOLogic.mk_nibble;

    fun mk_char (s, _) accu =
        fold
          (fn c => fn l =>
               Syntax.const @{const_syntax Cons}
             $ (Syntax.const @{const_syntax Char} $ mk_nib (c div 16) $ mk_nib (c mod 16))
             $ l)
          (rev (map Char.ord (String.explode s)))
          accu;

    fun mk_string [] = Const (@{const_syntax Nil}, @{typ "char list"})
      | mk_string (s :: ss) = mk_char s (mk_string ss);

  in
    fun string_tr f content args =
      let fun err () = raise TERM ("string_tr", args) in
        (case args of
          [(c as Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ p] =>
            (case Term_Position.decode_position p of
              SOME (pos, _) => c $ f (mk_string (content (s, pos))) $ p
            | NONE => err ())
        | _ => err ())
      end;
  end;
*}

syntax "_cartouche_string" :: "cartouche_position \<Rightarrow> _"  ("_")
parse_translation {*
  [( @{syntax_const "_cartouche_string"}
   , let val cartouche_type = Attrib.setup_config_string @{binding cartouche_type} (K "char list") in
       fn ctxt =>
         string_tr
           (case Config.get ctxt cartouche_type of
              "char list" => I
            | "String.literal" => (fn x => Syntax.const @{const_syntax STR} $ x)
            | "abr_string" => (fn x => Syntax.const @{const_syntax SS_base}
                                       $ (Syntax.const @{const_syntax ST}
                                          $ (Syntax.const @{const_syntax STR}
                                             $ x)))
            | s => error ("Unregistered return type for the cartouche: \"" ^ s ^ "\""))
           (Symbol_Pos.cartouche_content o Symbol_Pos.explode)
     end)]
*}

declare[[cartouche_type = "abr_string"]]

section{* ... *}

ML{* 
local
val constdef = Scan.option Parse_Spec.constdecl -- (Parse_Spec.opt_thm_name ":" -- Parse.inner_syntax Parse.cartouche);
in
val _ =
  Outer_Syntax.local_theory' @{command_spec "definition\<acute>"} "constant definition"
    (constdef >> (fn args => #2 oo Specification.definition_cmd args));
end
*}

subsection{* ... *}

definition "List_mapi f l = rev (fst (foldl (\<lambda>(l,cpt) x. (f cpt x # l, Succ cpt)) ([], 0::nat) l))"
definition "List_iter f = foldl (\<lambda>_. f) ()"
definition "List_maps f x = List_flatten (List_map f x)"
definition List_append (infixr "@@@@" 65) where "List_append a b = List_flatten [a, b]"
definition "List_filter f l = rev (foldl (\<lambda>l x. if f x then x # l else l) [] l)"
definition "rev_map f = foldl (\<lambda>l x. f x # l) []"
definition "fold_list f l accu =
  (let (l, accu) = List.fold (\<lambda>x (l, accu). let (x, accu) = f x accu in (x # l, accu)) l ([], accu) in
   (rev l, accu))"
definition "char_escape = Char Nibble0 Nibble9"
definition "List_assoc x1 l = List.fold (\<lambda>(x2, v). \<lambda>None \<Rightarrow> if x1 = x2 then Some v else None | x \<Rightarrow> x) l None"
definition "List_split l = (List_map fst l, List_map snd l)"
definition "List_upto i j =
 (let to_i = \<lambda>n. int_of_integer (integer_of_natural n) in
  List_map (natural_of_integer o integer_of_int) (upto (to_i i) (to_i j)))"
definition "List_split_at f l =
 (let f = \<lambda>x. \<not> f x in
  (takeWhile f l, case dropWhile f l of [] \<Rightarrow> (None, []) | x # xs \<Rightarrow> (Some x, xs)))"
definition "List_take reverse lg l = reverse (snd (List_split (takeWhile (\<lambda>(n, _). n < lg) (enumerate 0 (reverse l)))))"
definition "List_take_last = List_take rev"
definition "List_take_first = List_take id"
datatype ('a, 'b) nsplit = Nsplit_text 'a
                         | Nsplit_sep 'b
definition "List_replace_gen f_res l c0 lby =
 (let Nsplit_text = \<lambda>l lgen. if l = [] then lgen else Nsplit_text l # lgen in
  case List.fold
         (\<lambda> c1 (l, lgen).
           if c0 c1 then
             (lby, Nsplit_sep c1 # Nsplit_text l lgen)
           else
             (c1 # l, lgen))
         (rev l)
         ([], [])
  of (l, lgen) \<Rightarrow> f_res (Nsplit_text l lgen))"
definition "List_nsplit_f l c0 = List_replace_gen id l c0 []"
definition "List_replace = List_replace_gen (List_flatten o List_map (\<lambda> Nsplit_text l \<Rightarrow> l | _ \<Rightarrow> []))"

fun List_map_find_aux where
   "List_map_find_aux accu f l = (\<lambda> [] \<Rightarrow> []
                         | x # xs \<Rightarrow> (case f x of Some x \<Rightarrow> List.fold (\<lambda>x xs. x # xs) (x # accu) xs
                                                | None \<Rightarrow> List_map_find_aux (x # accu) f xs)) l"
definition "List_map_find = List_map_find_aux []"

definition "flatten = String_concatWith \<open>\<close>"
definition String_flatten (infixr "@@" 65) where "String_flatten a b = flatten [a, b]"
definition "String_make n c = \<lless>List_map (\<lambda>_. c) (List_upto 1 n)\<ggreater>"
definition "ST0 c = \<lless>[c]\<ggreater>"
definition "ST0_base c = ST' [c]"

definition "String\<^sub>b\<^sub>a\<^sub>s\<^sub>e_map_gen replace g = (\<lambda> ST s \<Rightarrow> replace \<open>\<close> (Some s) \<open>\<close>
                                           | ST' s \<Rightarrow> flatten (List_map g s))"
fun String_map_gen where
   "String_map_gen replace g e =
     (\<lambda> SS_base s \<Rightarrow> String\<^sub>b\<^sub>a\<^sub>s\<^sub>e_map_gen replace g s
      | String_concatWith abr l \<Rightarrow> String_concatWith (String_map_gen replace g abr) (List.map (String_map_gen replace g) l)) e"

definition "String_foldl_one f accu s = foldl f accu (String.explode s)"
definition "String\<^sub>b\<^sub>a\<^sub>s\<^sub>e_foldl f accu = (\<lambda> ST s \<Rightarrow> String_foldl_one f accu s
                                      | ST' s \<Rightarrow> foldl f accu s)"
fun String_foldl where
   "String_foldl f accu e =
     (\<lambda> SS_base s \<Rightarrow> String\<^sub>b\<^sub>a\<^sub>s\<^sub>e_foldl f accu s
      | String_concatWith abr l \<Rightarrow>
        (case l of [] \<Rightarrow> accu
                 | x # xs \<Rightarrow> foldl (\<lambda>accu. String_foldl f (String_foldl f accu abr)) (String_foldl f accu x) xs)) e"

definition "replace_chars f s1 s s2 =
  s1 @@ (case s of None \<Rightarrow> \<open>\<close> | Some s \<Rightarrow> flatten (List_map f (String.explode s))) @@ s2"

definition "String_map f = String_map_gen (replace_chars (\<lambda>c. \<degree>f c\<degree>)) (\<lambda>x. \<degree>f x\<degree>)"
definition "String_replace_chars f = String_map_gen (replace_chars (\<lambda>c. f c)) f"
definition "String_all f = String_foldl (\<lambda>b s. b & f s) True"
definition "String_length = String_foldl (\<lambda>n _. Suc n) 0"
definition "String_to_list s = rev (String_foldl (\<lambda>l c. c # l) [] s)"
definition "String\<^sub>b\<^sub>a\<^sub>s\<^sub>e_to_list = (\<lambda> ST s \<Rightarrow> String.explode s | ST' l \<Rightarrow> l)"
definition "String_to_String\<^sub>b\<^sub>a\<^sub>s\<^sub>e = (\<lambda> SS_base s \<Rightarrow> s | s \<Rightarrow> ST' (String_to_list s))"
definition "String\<^sub>b\<^sub>a\<^sub>s\<^sub>e_to_String = SS_base"
definition "String\<^sub>b\<^sub>a\<^sub>s\<^sub>e_is_empty = (\<lambda> ST s \<Rightarrow> s = STR ''''
                                  | ST' s \<Rightarrow> s = [])"
fun String_is_empty where
   "String_is_empty e = (\<lambda> SS_base s \<Rightarrow> String\<^sub>b\<^sub>a\<^sub>s\<^sub>e_is_empty s | String_concatWith _ l \<Rightarrow> list_all String_is_empty l) e"

definition "String_equal s1 s2 = (String_to_list s1 = String_to_list s2)"

(* *)

definition "List_assoc' x l = List_assoc (String_to_list x) (List_map (map_prod String\<^sub>b\<^sub>a\<^sub>s\<^sub>e_to_list id) l)"
syntax "_list_assoc" :: "string \<Rightarrow> (string\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<times> 'a) list \<Rightarrow> 'a option" ("List.assoc")
translations "List.assoc" \<rightleftharpoons> "CONST List_assoc'"

definition "List_member' l x = List.member (List_map String\<^sub>b\<^sub>a\<^sub>s\<^sub>e_to_list l) (String_to_list x)"
syntax "_list_member" :: "string\<^sub>b\<^sub>a\<^sub>s\<^sub>e list \<Rightarrow> string \<Rightarrow> bool" ("List'_member")
translations "List_member" \<rightleftharpoons> "CONST List_member'"

definition "flatten_base l = String_to_String\<^sub>b\<^sub>a\<^sub>s\<^sub>e (flatten (List_map String\<^sub>b\<^sub>a\<^sub>s\<^sub>e_to_String l))"

section{* Preliminaries *}

subsection{* Misc. (to be removed) *}

(* Syntactic errors in target languages can appear during extraction,
   so we explicitly output parenthesis around expressions
   (by enclosing them in a 'id' scope for instance) *)

syntax "_Let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l" :: "[letbinds, 'a] \<Rightarrow> 'a" ("(let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l (_)/ in (_))" [0, 10] 10)
translations "_Let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l (_binds b bs) e" \<rightleftharpoons> "_Let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l b (_Let bs e)"
             "let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l x = a in e" \<rightleftharpoons> "CONST id (CONST Let a (%x. e))"

syntax  "_case_syntax\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l" :: "['a, cases_syn] => 'b"  ("(case\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l _ of/ _)" 10)
translations "case\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l v of w => x" \<rightleftharpoons> "CONST id (_case_syntax v (_case1 w x))"
             "case\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l v of w => x | y => z" \<rightleftharpoons> "CONST id (_case_syntax v (_case2 (_case1 w x) (_case1 y z)))"

syntax "_Lambda\<^sub>S\<^sub>c\<^sub>a\<^sub>l\<^sub>a" :: "[pttrn, bool] \<Rightarrow> 'a"  ("(3\<lambda>\<^sub>S\<^sub>c\<^sub>a\<^sub>l\<^sub>a _./ _)" [0, 10] 10)
       "_Lambda\<^sub>S\<^sub>c\<^sub>a\<^sub>l\<^sub>a" :: "[pttrn, pttrn, bool] \<Rightarrow> 'a"  ("(3\<lambda>\<^sub>S\<^sub>c\<^sub>a\<^sub>l\<^sub>a _ _./ _)" [0, 0, 10] 10)
translations "\<lambda>\<^sub>S\<^sub>c\<^sub>a\<^sub>l\<^sub>a x y. P" \<rightleftharpoons> "CONST id (%x y. P)"
             "\<lambda>\<^sub>S\<^sub>c\<^sub>a\<^sub>l\<^sub>a x. P" \<rightleftharpoons> "CONST id (%x. P)"

subsection{* Infra-structure that skip lengthy termination proofs *}

ML{*
structure Fun_quick = struct
val quick_dirty = false
  (* false: "fun_quick" behaves as "fun"
     true: "fun_quick" behaves as "fun", but it proves completeness and termination with "sorry" *)

val proof_by_patauto = Proof.global_terminal_proof
  ( ( Method.Then
        ( Method.no_combinator_info
        , [ Method.Basic (fn ctxt => SIMPLE_METHOD (Pat_Completeness.pat_completeness_tac ctxt 1) )
          , Method.Basic (fn ctxt => SIMPLE_METHOD (auto_tac (ctxt addsimps [])))])
    , (Position.none, Position.none))
  , NONE)
val proof_by_sorry = Proof.global_skip_proof true

fun mk_fun quick_dirty cmd_spec tac =
  Outer_Syntax.local_theory' cmd_spec
    "define general recursive functions (short version)"
    (Function_Common.function_parser
      (if quick_dirty then
         Function_Common.FunctionConfig { sequential=true, default=NONE
                                        , domintros=false, partials=true}
       else
         Function_Fun.fun_config)
      >> (if quick_dirty then
            fn ((config, fixes), statements) => fn b => fn ctxt =>
            ctxt |> Function.function_cmd fixes statements config b
                 |> tac
                 |> Function.termination_cmd NONE
                 |> proof_by_sorry
          else
            fn ((config, fixes), statements) => Function_Fun.add_fun_cmd fixes statements config))

val () = mk_fun quick_dirty @{command_spec "fun_quick"} proof_by_sorry
val () = mk_fun true @{command_spec "fun_sorry"} proof_by_patauto
end
*}

section{* ...  *}

subsection{* ... *}

definition "wildcard = \<open>_\<close>"

definition "escape_unicode c = flatten [\<degree>Char Nibble5 NibbleC\<degree>, \<open><\<close>, c, \<open>>\<close>]"

definition "lowercase_of_str = String_map (\<lambda>c. let n = nat_of_char c in if n < 97 then char_of_nat (n + 32) else c)"
definition "uppercase_of_str = String_map (\<lambda>c. let n = nat_of_char c in if n < 97 then c else char_of_nat (n - 32))"
definition "number_of_str = String_replace_chars (\<lambda>c. escape_unicode ([\<open>zero\<close>, \<open>one\<close>, \<open>two\<close>, \<open>three\<close>, \<open>four\<close>, \<open>five\<close>, \<open>six\<close>, \<open>seven\<close>, \<open>eight\<close>, \<open>nine\<close>] ! (nat_of_char c - 48)))"
definition "nat_raw_of_str = List_map (\<lambda>i. char_of_nat (nat_of_char (Char Nibble3 Nibble0) + i))"
fun_quick nat_of_str_aux where
   "nat_of_str_aux l (n :: Nat.nat) = (if n < 10 then n # l else nat_of_str_aux (n mod 10 # l) (n div 10))"
definition "nat_of_str n = \<lless>nat_raw_of_str (nat_of_str_aux [] n)\<ggreater>"
definition "natural_of_str = nat_of_str o nat_of_natural"
definition "add_0 n =
 (let n = nat_of_char n in
  flatten (List_map (\<lambda>_. \<open>0\<close>) (upt 0 (if n < 10 then 2 else if n < 100 then 1 else 0)))
  @@ nat_of_str n)"
definition "is_letter n = (n \<ge> CHR ''A'' & n \<le> CHR ''Z'' | n \<ge> CHR ''a'' & n \<le> CHR ''z'')"
definition "is_digit n = (n \<ge> CHR ''0'' & n \<le> CHR ''9'')"
definition "is_special = List.member '' <>^_=-./(){}''"
definition "base255_of_str = String_replace_chars (\<lambda>c. if is_letter c then \<degree>c\<degree> else add_0 c)"
definition "isub_of_str = String_replace_chars (\<lambda>c.
  if is_letter c | is_digit c then escape_unicode \<open>^sub\<close> @@ \<degree>c\<degree> else add_0 c)"
definition "isup_of_str = String_replace_chars (\<lambda>c.
  if is_letter c then escape_unicode \<lless>[char_of_nat (nat_of_char c - 32)]\<ggreater> else add_0 c)"
definition "text_of_str str =
 (let s = \<open>c\<close>
    ; ap = \<open> # \<close> in
  flatten [ \<open>(let \<close>, s, \<open> = char_of_nat in \<close>
          , String_replace_chars (\<lambda>c.
                                    if is_letter c then
                                      let g = \<langle>[Char Nibble2 Nibble7]\<rangle> in
                                      flatten [\<open>CHR \<close>,  g,g,\<degree>c\<degree>,g,g,  ap]
                                    else
                                      flatten [s, \<open> \<close>,  add_0 c, ap])
                                 str
          , \<open>[])\<close>])"
definition "text2_of_str = String_replace_chars (\<lambda>c. escape_unicode \<degree>c\<degree>)"

definition "textstr_of_str f_flatten f_char f_str str =
 (let str0 = String_to_list str
    ; f_letter = \<lambda>c. is_letter c | is_digit c | is_special c
    ; s = \<open>c\<close>
    ; g = \<langle>[Char Nibble2 Nibble7]\<rangle>
    ; f_text = \<lambda> Nsplit_text l \<Rightarrow> flatten [f_str (flatten [\<open>STR \<close>,  g,g,\<lless>l\<ggreater>,g,g  ])]
               | Nsplit_sep c \<Rightarrow> flatten [f_char c]
    ; str = case List_nsplit_f str0 (Not o f_letter) of
              [] \<Rightarrow> flatten [f_str (flatten [\<open>STR \<close>,  g,g,g,g  ])]
            | [x] \<Rightarrow> f_text x
            | l \<Rightarrow> flatten (List_map (\<lambda>x. \<open>(\<close> @@ f_text x @@ \<open>) # \<close>) l) @@ \<open>[]\<close> in
  if list_all f_letter str0 then
    str
  else
    f_flatten (flatten [ \<open>(\<close>, str, \<open>)\<close> ]))"

definition "mk_constr_name name = (\<lambda> x. flatten [isub_of_str name, \<open>_\<close>, isub_of_str x])"
definition "mk_dot s1 s2 = flatten [\<open>.\<close>, s1, s2]"
definition "mk_dot_par_gen dot l_s = flatten [dot, \<open>(\<close>, case l_s of [] \<Rightarrow> \<open>\<close> | x # xs \<Rightarrow> flatten [x, flatten (List_map (\<lambda>s. \<open>, \<close> @@ s) xs) ], \<open>)\<close>]"
definition "mk_dot_par dot s = mk_dot_par_gen dot [s]"
definition "mk_dot_comment s1 s2 s3 = mk_dot s1 (flatten [s2, \<open> /*\<close>, s3, \<open>*/\<close>])"

definition "hol_definition s = flatten [s, \<open>_def\<close>]"
definition "hol_split s = flatten [s, \<open>.split\<close>]"

subsection{* ... *}

definition "unicode_AA = escape_unicode \<open>AA\<close>"
definition "unicode_acute = escape_unicode \<open>acute\<close>"
definition "unicode_alpha = escape_unicode \<open>alpha\<close>"
definition "unicode_and = escape_unicode \<open>and\<close>"
definition "unicode_And = escape_unicode \<open>And\<close>"
definition "unicode_bottom = escape_unicode \<open>bottom\<close>"
definition "unicode_circ = escape_unicode \<open>circ\<close>"
definition "unicode_delta = escape_unicode \<open>delta\<close>"
definition "unicode_doteq = escape_unicode \<open>doteq\<close>"
definition "unicode_equiv = escape_unicode \<open>equiv\<close>"
definition "unicode_exists = escape_unicode \<open>exists\<close>"
definition "unicode_forall = escape_unicode \<open>forall\<close>"
definition "unicode_in = escape_unicode \<open>in\<close>"
definition "unicode_lambda = escape_unicode \<open>lambda\<close>"
definition "unicode_lceil = escape_unicode \<open>lceil\<close>"
definition "unicode_lfloor = escape_unicode \<open>lfloor\<close>"
definition "unicode_longrightarrow = escape_unicode \<open>longrightarrow\<close>"
definition "unicode_Longrightarrow = escape_unicode \<open>Longrightarrow\<close>"
definition "unicode_mapsto = escape_unicode \<open>mapsto\<close>"
definition "unicode_noteq = escape_unicode \<open>noteq\<close>"
definition "unicode_not = escape_unicode \<open>not\<close>"
definition "unicode_or = escape_unicode \<open>or\<close>"
definition "unicode_rceil = escape_unicode \<open>rceil\<close>"
definition "unicode_rfloor = escape_unicode \<open>rfloor\<close>"
definition "unicode_Rightarrow = escape_unicode \<open>Rightarrow\<close>"
definition "unicode_subseteq = escape_unicode \<open>subseteq\<close>"
definition "unicode_tau = escape_unicode \<open>tau\<close>"
definition "unicode_times = escape_unicode \<open>times\<close>"
definition "unicode_triangleq = escape_unicode \<open>triangleq\<close>"
definition "unicode_Turnstile = escape_unicode \<open>Turnstile\<close>"
definition "unicode_upsilon = escape_unicode \<open>upsilon\<close>"

end
