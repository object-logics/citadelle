(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_init.thy ---
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013-2014 Universite Paris-Sud, France
 *               2013-2014 IRT SystemX, France
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
        "~~/src/HOL/Library/RBT"
        "~~/src/HOL/Library/Char_ord"
        "~~/src/HOL/Library/List_lexord"
  keywords (* hol syntax *)
           "fun_sorry" "fun_quick"
           :: thy_decl
begin

section{* ... *}

type_synonym nat = natural

section{* Preliminaries Compiler *}

subsection{* Oid-Management *}

definition "Succ x = x + 1"

datatype internal_oid = Oid nat
datatype internal_oids = Oids nat (* start *)
                              nat (* oid for assoc (incremented from start) *)
                              nat (* oid for inh (incremented from start) *)

definition "oidInit = (\<lambda> Oid n \<Rightarrow> Oids n n n)"

definition "oidSucAssoc = (\<lambda> Oids n1 n2 n3 \<Rightarrow> Oids n1 (Succ n2) (Succ n3))"
definition "oidSucInh = (\<lambda> Oids n1 n2 n3 \<Rightarrow> Oids n1 n2 (Succ n3))"
definition "oidGetAssoc = (\<lambda> Oids _ n _ \<Rightarrow> Oid n)"
definition "oidGetInh = (\<lambda> Oids _ _ n \<Rightarrow> Oid n)"

definition "oidReinitAll = (\<lambda>Oids n1 _ _ \<Rightarrow> Oids n1 n1 n1)"
definition "oidReinitInh = (\<lambda>Oids n1 n2 _ \<Rightarrow> Oids n1 n2 n2)"


subsection{* RBT Miscellaneous *}

subsection{* ... *} (* optimized data-structure version *)

datatype opt_attr_type = OptInh | OptOwn
datatype opt_ident = OptIdent nat

instantiation internal_oid :: linorder
begin
 definition "n_of_internal_oid = (\<lambda> Oid n \<Rightarrow> n)"
 definition "n \<le> m \<longleftrightarrow> n_of_internal_oid n \<le> n_of_internal_oid m"
 definition "n < m \<longleftrightarrow> n_of_internal_oid n < n_of_internal_oid m"
 instance
   apply(default)
   apply (metis less_eq_internal_oid_def less_imp_le less_internal_oid_def not_less)
   apply (metis less_eq_internal_oid_def order_refl)
   apply (metis less_eq_internal_oid_def order.trans)
   apply(simp add: less_eq_internal_oid_def n_of_internal_oid_def, case_tac x, case_tac y, simp)
 by (metis le_cases less_eq_internal_oid_def)
end

instantiation opt_ident :: linorder
begin
 definition "n_of_opt_ident = (\<lambda> OptIdent n \<Rightarrow> n)"
 definition "n \<le> m \<longleftrightarrow> n_of_opt_ident n \<le> n_of_opt_ident m"
 definition "n < m \<longleftrightarrow> n_of_opt_ident n < n_of_opt_ident m"
 instance
 apply(default)
 apply (metis less_eq_opt_ident_def less_imp_le less_opt_ident_def not_less)
 apply (metis less_eq_opt_ident_def order_refl)
   apply (metis less_eq_opt_ident_def order.trans)
   apply(simp add: less_eq_opt_ident_def n_of_opt_ident_def, case_tac x, case_tac y, simp)
 by (metis le_cases less_eq_opt_ident_def)
end

subsection{* ... *}

definition "List_mapi f l = rev (fst (foldl (\<lambda>(l,cpt) x. (f cpt x # l, Succ cpt)) ([], 0::nat) l))"
definition "List_iter f = foldl (\<lambda>_. f) ()"
definition "List_maps f x = flatten (List_map f x)"
definition List_append (infixr "@@" 65) where "List_append a b = flatten [a, b]"
definition "List_filter f l = rev (foldl (\<lambda>l x. if f x then x # l else l) [] l)"
definition "rev_map f = foldl (\<lambda>l x. f x # l) []"
definition "fold_list f l accu =
  (let (l, accu) = List.fold (\<lambda>x (l, accu). let (x, accu) = f x accu in (x # l, accu)) l ([], accu) in
   (rev l, accu))"
definition "char_escape = Char Nibble0 Nibble9"
definition "modify_def v k f rbt =
  (case lookup rbt k of None \<Rightarrow> insert k (f v) rbt
                      | Some _ \<Rightarrow> map_entry k f rbt)"
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
definition "List_replace = List_replace_gen flatten"
definition "lookup2 rbt = (\<lambda>(x1, x2). Option_bind (\<lambda>rbt. lookup rbt x2) (lookup rbt x1))"
definition "insert2 = (\<lambda>(x1, x2) v. modify_def empty x1 (insert x2 v))"

definition "String_concatWith s =
 (\<lambda> [] \<Rightarrow> ''''
  | x # xs \<Rightarrow> flatten (flatten ([x] # List_map (\<lambda>s0. [s, s0]) xs)))"

section{* Preliminaries *}

subsection{* Misc. (to be removed) *}
definition "bug_ocaml_extraction = id"
definition "bug_scala_extraction = id"
  (* In this theory, this identifier can be removed everywhere it is used.
     However without this, there is a syntax error when the code is extracted to OCaml. *)

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

definition "wildcard = ''_''"

definition "escape_unicode c = flatten [[Char Nibble5 NibbleC], ''<'', c, ''>'']"

definition "isub_of_str = flatten o List_map (\<lambda>c. escape_unicode ''^sub'' @@ [c])"
definition "isup_of_str = flatten o List_map (\<lambda>c. escape_unicode [char_of_nat (nat_of_char c - 32)])"
definition "lowercase_of_str = List_map (\<lambda>c. let n = nat_of_char c in if n < 97 then char_of_nat (n + 32) else c)"
definition "uppercase_of_str = List_map (\<lambda>c. let n = nat_of_char c in if n < 97 then c else char_of_nat (n - 32))"
definition "number_of_str = flatten o List_map (\<lambda>c. escape_unicode ([''zero'', ''one'', ''two'', ''three'', ''four'', ''five'', ''six'', ''seven'', ''eight'', ''nine''] ! (nat_of_char c - 48)))"
definition "nat_raw_of_str = List_map (\<lambda>i. char_of_nat (nat_of_char (Char Nibble3 Nibble0) + i))"
fun_quick nat_of_str_aux where
   "nat_of_str_aux l (n :: Nat.nat) = (if n < 10 then n # l else nat_of_str_aux (n mod 10 # l) (n div 10))"
definition "nat_of_str n = nat_raw_of_str (nat_of_str_aux [] n)"
definition "natural_of_str = nat_of_str o nat_of_natural"

definition "mk_constr_name name = (\<lambda> x. flatten [isub_of_str name, ''_'', isub_of_str x])"
definition "mk_dot s1 s2 = flatten [''.'', s1, s2]"
definition "mk_dot_par_gen dot l_s = flatten [dot, ''('', case l_s of [] \<Rightarrow> '''' | x # xs \<Rightarrow> flatten [x, flatten (List_map (\<lambda>s. '', '' @@ s) xs) ], '')'']"
definition "mk_dot_par dot s = mk_dot_par_gen dot [s]"
definition "mk_dot_comment s1 s2 s3 = mk_dot s1 (flatten [s2, '' /*'', s3, ''*/''])"

definition "hol_definition s = flatten [s, ''_def'']"
definition "hol_split s = flatten [s, ''.split'']"

subsection{* ... *}

definition "ty_boolean = ''Boolean''"

definition "unicode_AA = escape_unicode ''AA''"
definition "unicode_alpha = escape_unicode ''alpha''"
definition "unicode_and = escape_unicode ''and''"
definition "unicode_And = escape_unicode ''And''"
definition "unicode_bottom = escape_unicode ''bottom''"
definition "unicode_circ = escape_unicode ''circ''"
definition "unicode_delta = escape_unicode ''delta''"
definition "unicode_doteq = escape_unicode ''doteq''"
definition "unicode_equiv = escape_unicode ''equiv''"
definition "unicode_exists = escape_unicode ''exists''"
definition "unicode_forall = escape_unicode ''forall''"
definition "unicode_in = escape_unicode ''in''"
definition "unicode_lambda = escape_unicode ''lambda''"
definition "unicode_lceil = escape_unicode ''lceil''"
definition "unicode_lfloor = escape_unicode ''lfloor''"
definition "unicode_longrightarrow = escape_unicode ''longrightarrow''"
definition "unicode_Longrightarrow = escape_unicode ''Longrightarrow''"
definition "unicode_mapsto = escape_unicode ''mapsto''"
definition "unicode_noteq = escape_unicode ''noteq''"
definition "unicode_not = escape_unicode ''not''"
definition "unicode_or = escape_unicode ''or''"
definition "unicode_rceil = escape_unicode ''rceil''"
definition "unicode_rfloor = escape_unicode ''rfloor''"
definition "unicode_Rightarrow = escape_unicode ''Rightarrow''"
definition "unicode_subseteq = escape_unicode ''subseteq''"
definition "unicode_tau = escape_unicode ''tau''"
definition "unicode_times = escape_unicode ''times''"
definition "unicode_triangleq = escape_unicode ''triangleq''"
definition "unicode_Turnstile = escape_unicode ''Turnstile''"
definition "unicode_upsilon = escape_unicode ''upsilon''"

definition "const_oclastype = ''OclAsType''"
definition "const_oclistypeof = ''OclIsTypeOf''"
definition "const_ocliskindof = ''OclIsKindOf''"
definition "const_mixfix dot_ocl name = (let t = \<lambda>s. Char Nibble2 Nibble7 # s in
                                         flatten [dot_ocl, t ''('', name, t '')''])"
definition "const_oid_of s = flatten [''oid_of_'', s]"
definition "dot_oclastype = ''.oclAsType''"
definition "dot_oclistypeof = ''.oclIsTypeOf''"
definition "dot_ocliskindof = ''.oclIsKindOf''"
definition "dot_astype = mk_dot_par dot_oclastype"
definition "dot_istypeof = mk_dot_par dot_oclistypeof"
definition "dot_iskindof = mk_dot_par dot_ocliskindof"

definition "var_in_pre_state = ''in_pre_state''"
definition "var_in_post_state = ''in_post_state''"
definition "var_reconst_basetype = ''reconst_basetype''"
definition "var_oid_uniq = ''oid''"
definition "var_eval_extract = ''eval_extract''"
definition "var_deref = ''deref''"
definition "var_deref_oid = ''deref_oid''"
definition "var_deref_assocs = ''deref_assocs''"
definition "var_deref_assocs_list = ''deref_assocs_list''"
definition "var_inst_assoc = ''inst_assoc''"
definition "var_select = ''select''"
definition "var_select_object = ''select_object''"
definition "var_select_object_set = ''select_object_set''"
definition "var_select_object_set_any = ''select_object_set_any''"
definition "var_choose = ''choose''"
definition "var_switch = ''switch''"
definition "var_assocs = ''assocs''"
definition "var_map_of_list = ''map_of_list''"
definition "var_at_when_hol_post = ''''"
definition "var_at_when_hol_pre = ''at_pre''"
definition "var_at_when_ocl_post = ''''"
definition "var_at_when_ocl_pre = ''@pre''"
definition "var_OclInt = ''OclInt''"

definition "update_D_accessor_rbt_pre f = (\<lambda>(l_pre, l_post). (f l_pre, l_post))"
definition "update_D_accessor_rbt_post f = (\<lambda>(l_pre, l_post). (l_pre, f l_post))"

end
