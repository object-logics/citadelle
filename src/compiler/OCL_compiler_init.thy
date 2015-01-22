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
imports OCL_compiler_static
  keywords (* hol syntax *)
           "fun_sorry" "fun_quick"
           :: thy_decl
begin

section{* ... *}

syntax "_string1" :: "'a \<Rightarrow> 'a" ("\<langle>(_)\<rangle>")
translations "\<langle>x\<rangle>" \<rightleftharpoons> "CONST id x"

syntax "_string2" :: "'a \<Rightarrow> 'a" ("\<prec>(_)\<succ>")
translations "\<prec>x\<succ>" \<rightleftharpoons> "CONST STR x"

syntax "_string3" :: "'a \<Rightarrow> 'a" ("\<lless>(_)\<ggreater>")
translations "\<lless>x\<ggreater>" \<rightleftharpoons> "CONST id x"

syntax "_char1" :: "'a \<Rightarrow> 'a list" ("\<degree>(_)\<degree>")
translations "\<degree>x\<degree>" \<rightleftharpoons> "CONST Cons x (CONST Nil)"

syntax "_char2" :: "'a \<Rightarrow> _" ("\<ordmasculine>(_)\<ordmasculine>")
translations "\<ordmasculine>x\<ordmasculine>" \<rightleftharpoons> "CONST STR (CONST Cons x (CONST Nil))"

section{* ... *}

type_synonym nat = natural
definition "Succ x = x + 1"

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
definition "Option_bind f = (\<lambda> None \<Rightarrow> None | Some x \<Rightarrow> f x)"
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
definition "List_replace_gen f_res l c0 lby =
 (case List.fold (\<lambda>c1 (l,lgen). if c1 = c0 then (lby, l # lgen) else (c1 # l, lgen)) (rev l) ([], [])
  of (l, lgen) \<Rightarrow> f_res (l # lgen))"
definition "List_nsplit l c0 = List_replace_gen id l c0 []"
definition "List_replace = List_replace_gen List_flatten"

definition "flatten = List_flatten"
definition String_flatten (infixr "@@" 65) where "String_flatten (a::char list) b = flatten [a, b]"
definition Stringl_flatten (infixr "@@@" 65) where "Stringl_flatten (a::String.literal list) b = flatten [a, b]"
definition "String_concatWith s =
 (\<lambda> [] \<Rightarrow> \<langle>''''\<rangle>
  | x # xs \<Rightarrow> flatten (flatten ([x] # List_map (\<lambda>s0. [s, s0]) xs)))"

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
        [ Method.Basic (fn ctxt => SIMPLE_METHOD (Pat_Completeness.pat_completeness_tac ctxt 1) )
        , Method.Basic (fn ctxt => SIMPLE_METHOD (auto_tac (ctxt addsimps [])))]
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

definition "wildcard = \<langle>''_''\<rangle>"

definition "escape_unicode c = flatten [\<degree>Char Nibble5 NibbleC\<degree>, \<langle>''<''\<rangle>, c, \<langle>''>''\<rangle>]"

definition "lowercase_of_str = List_map (\<lambda>c. let n = nat_of_char c in if n < 97 then char_of_nat (n + 32) else c)"
definition "uppercase_of_str = List_map (\<lambda>c. let n = nat_of_char c in if n < 97 then c else char_of_nat (n - 32))"
definition "number_of_str = flatten o List_map (\<lambda>c. escape_unicode ([\<langle>''zero''\<rangle>, \<langle>''one''\<rangle>, \<langle>''two''\<rangle>, \<langle>''three''\<rangle>, \<langle>''four''\<rangle>, \<langle>''five''\<rangle>, \<langle>''six''\<rangle>, \<langle>''seven''\<rangle>, \<langle>''eight''\<rangle>, \<langle>''nine''\<rangle>] ! (nat_of_char c - 48)))"
definition "nat_raw_of_str = List_map (\<lambda>i. char_of_nat (nat_of_char (Char Nibble3 Nibble0) + i))"
fun_quick nat_of_str_aux where
   "nat_of_str_aux l (n :: Nat.nat) = (if n < 10 then n # l else nat_of_str_aux (n mod 10 # l) (n div 10))"
definition "nat_of_str n = \<langle>nat_raw_of_str (nat_of_str_aux [] n)\<rangle>"
definition "natural_of_str = nat_of_str o nat_of_natural"
definition "add_0 n = flatten [ flatten (List_map (\<lambda>_. \<langle>''0''\<rangle>) (upt 0 (if n < 10 then 2 else if n < 100 then 1 else 0)))
          , nat_of_str n ]"
definition "is_letter n = (n \<ge> 65 & n < 91 | n \<ge> 97 & n < 123)"
definition "is_digit n = (n \<ge> 48 & n < 58)"
definition "base255_of_str_gen f0 f = flatten o List_map (\<lambda>c. let n = nat_of_char c in
  if is_letter n then f0 c else f (add_0 n))"
definition "base255_of_str = base255_of_str_gen (\<lambda>c. \<degree>c\<degree>) id"
definition "isub_of_str = flatten o List_map (\<lambda>c. let n = nat_of_char c in
  if is_letter n | is_digit n then escape_unicode \<langle>''^sub''\<rangle> @@ \<degree>c\<degree> else add_0 n)"
definition "isup_of_str = flatten o List_map (\<lambda>c. let n = nat_of_char c in
  if is_letter n then escape_unicode \<langle>[char_of_nat (nat_of_char c - 32)]\<rangle> else add_0 n)"
definition "text_of_str str =
 (let s = \<langle>''c''\<rangle>
    ; ap = \<langle>'' # ''\<rangle> in
  flatten [ \<langle>''(let ''\<rangle>, s, \<langle>'' = char_of_nat in ''\<rangle>
          , base255_of_str_gen
              (\<lambda>c.
                let g = \<langle>[Char Nibble2 Nibble7]\<rangle> in
                flatten [\<langle>''CHR ''\<rangle>,  g,g,\<degree>c\<degree>,g,g,  ap])
              (\<lambda>c. flatten [s, \<langle>'' ''\<rangle>, c, ap]) str
          , \<langle>''[])''\<rangle>])"
definition "text2_of_str = flatten o List_map (\<lambda>c. escape_unicode \<degree>c\<degree>)"

definition "mk_constr_name name = (\<lambda> x. flatten [isub_of_str name, \<langle>''_''\<rangle>, isub_of_str x])"
definition "mk_dot s1 s2 = flatten [\<langle>''.''\<rangle>, s1, s2]"
definition "mk_dot_par_gen dot l_s = flatten [dot, \<langle>''(''\<rangle>, case l_s of [] \<Rightarrow> \<langle>''''\<rangle> | x # xs \<Rightarrow> flatten [x, flatten (List_map (\<lambda>s. \<langle>'', ''\<rangle> @@ s) xs) ], \<langle>'')''\<rangle>]"
definition "mk_dot_par dot s = mk_dot_par_gen dot [s]"
definition "mk_dot_comment s1 s2 s3 = mk_dot s1 (flatten [s2, \<langle>'' /*''\<rangle>, s3, \<langle>''*/''\<rangle>])"

definition "hol_definition s = flatten [s, \<langle>''_def''\<rangle>]"
definition "hol_split s = flatten [s, \<langle>''.split''\<rangle>]"

subsection{* ... *}

definition "unicode_AA = escape_unicode \<langle>''AA''\<rangle>"
definition "unicode_acute = escape_unicode \<langle>''acute''\<rangle>"
definition "unicode_alpha = escape_unicode \<langle>''alpha''\<rangle>"
definition "unicode_and = escape_unicode \<langle>''and''\<rangle>"
definition "unicode_And = escape_unicode \<langle>''And''\<rangle>"
definition "unicode_bottom = escape_unicode \<langle>''bottom''\<rangle>"
definition "unicode_circ = escape_unicode \<langle>''circ''\<rangle>"
definition "unicode_delta = escape_unicode \<langle>''delta''\<rangle>"
definition "unicode_doteq = escape_unicode \<langle>''doteq''\<rangle>"
definition "unicode_equiv = escape_unicode \<langle>''equiv''\<rangle>"
definition "unicode_exists = escape_unicode \<langle>''exists''\<rangle>"
definition "unicode_forall = escape_unicode \<langle>''forall''\<rangle>"
definition "unicode_in = escape_unicode \<langle>''in''\<rangle>"
definition "unicode_lambda = escape_unicode \<langle>''lambda''\<rangle>"
definition "unicode_lceil = escape_unicode \<langle>''lceil''\<rangle>"
definition "unicode_lfloor = escape_unicode \<langle>''lfloor''\<rangle>"
definition "unicode_longrightarrow = escape_unicode \<langle>''longrightarrow''\<rangle>"
definition "unicode_Longrightarrow = escape_unicode \<langle>''Longrightarrow''\<rangle>"
definition "unicode_mapsto = escape_unicode \<langle>''mapsto''\<rangle>"
definition "unicode_noteq = escape_unicode \<langle>''noteq''\<rangle>"
definition "unicode_not = escape_unicode \<langle>''not''\<rangle>"
definition "unicode_or = escape_unicode \<langle>''or''\<rangle>"
definition "unicode_rceil = escape_unicode \<langle>''rceil''\<rangle>"
definition "unicode_rfloor = escape_unicode \<langle>''rfloor''\<rangle>"
definition "unicode_Rightarrow = escape_unicode \<langle>''Rightarrow''\<rangle>"
definition "unicode_subseteq = escape_unicode \<langle>''subseteq''\<rangle>"
definition "unicode_tau = escape_unicode \<langle>''tau''\<rangle>"
definition "unicode_times = escape_unicode \<langle>''times''\<rangle>"
definition "unicode_triangleq = escape_unicode \<langle>''triangleq''\<rangle>"
definition "unicode_Turnstile = escape_unicode \<langle>''Turnstile''\<rangle>"
definition "unicode_upsilon = escape_unicode \<langle>''upsilon''\<rangle>"

end
