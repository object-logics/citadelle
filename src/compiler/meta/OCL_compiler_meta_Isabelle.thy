(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_meta_Isabelle.thy ---
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

theory  OCL_compiler_meta_Isabelle
imports OCL_compiler_meta_Pure
        OCL_compiler_meta_SML
begin

section{* Isabelle/HOL Meta-Model aka. AST definition of HOL *}
subsection{* type definition *}

datatype hol_'type = Ty_apply hol_'type "hol_'type list"
                   | Ty_apply_bin string (* binop *) hol_'type hol_'type
                   | Ty_apply_paren string (* left *) string (* right *) hol_'type
                   | Ty_base string

datatype hol_datatype = Datatype string (* name *)
                                 "(string (* name *) \<times> hol_'type list (* arguments *)) list" (* constructors *)

datatype hol_type_synonym = Type_synonym string (* name *)
                                           "string list" (* parametric variables *)
                                           hol_'type (* content *)

datatype hol_'expr = Expr_rewrite hol_'expr (* left *) string (* symb rewriting *) hol_'expr (* right *)
                   | Expr_basic "string list"
                   | Expr_oid string (* prefix *) internal_oid
                   | Expr_annot hol_'expr hol_'type
                   | Expr_bind0 string (* symbol *) hol_'expr (* arg *) hol_'expr
                   | Expr_function0 "hol_'expr (* value *) option" (* none: function *) "(hol_'expr (* pattern *) \<times> hol_'expr (* to return *)) list"
                   | Expr_applys00 hol_'expr "hol_'expr list"
                   | Expr_paren string (* left *) string (* right *) hol_'expr
                   | Expr_if_then_else hol_'expr hol_'expr hol_'expr
                   | Expr_inner0 "string list" (* simulate a pre-initialized context (de bruijn variables under "lam") *)
                                 pure_term (* usual continuation of inner syntax term *)

datatype hol_type_notation = Type_notation string (* name *)
                                           string (* content *)

datatype hol_instantiation = Instantiation string (* name *)
                                           string (* name in definition *)
                                           hol_'expr

datatype hol_defs = Defs_overloaded string (* name *) hol_'expr (* content *)

datatype hol_consts = Consts_raw string (* name *)
                                 hol_'type
                                 string (* ocl 'post' mixfix *)

datatype hol_definition = Definition hol_'expr
                        | Definition_abbrev string (* name *) "hol_'expr (* syntax extension *) \<times> nat (* priority *)" hol_'expr
                        | Definition_abbrev0 string (* name *) hol_'expr (* syntax extension *) hol_'expr

datatype hol_'ntheorem = Thm_str string (* represents a single thm *)
                       | Thm_strs string (* represents several thms *)
                       | Thm_THEN hol_'ntheorem hol_'ntheorem
                       | Thm_simplified hol_'ntheorem hol_'ntheorem
                       | Thm_symmetric hol_'ntheorem
                       | Thm_where hol_'ntheorem "(string \<times> hol_'expr) list"
                       | Thm_of hol_'ntheorem "hol_'expr list"
                       | Thm_OF hol_'ntheorem hol_'ntheorem

datatype hol_'ntheorems = Thms_single hol_'ntheorem
                        | Thms_mult hol_'ntheorem

type_synonym hol_'ntheorems_l = "hol_'ntheorems list"

datatype hol_lemmas = Lemmas_simp_opt
                                      bool (* True : simp *)
                                      string (* name *)
                                      "hol_'ntheorem list"
                    | Lemmas_simps string (* name *)
                                   "string (* thms *) list"

datatype hol_'tactic_simp = Simp_only hol_'ntheorems_l
                          | Simp_add_del_split hol_'ntheorems_l (* add *) hol_'ntheorems_l (* del *) hol_'ntheorems_l (* split *)

datatype hol_'tactic = Tact_rule0 "hol_'ntheorem option"
                     | Tact_drule hol_'ntheorem
                     | Tact_erule hol_'ntheorem
                     | Tact_intro "hol_'ntheorem list"
                     | Tact_elim hol_'ntheorem
                     | Tact_subst_l0 bool (* asm *)
                                     "string (* nat *) list" (* pos *)
                                     hol_'ntheorem
                     | Tact_insert hol_'ntheorems_l
                     | Tact_plus "hol_'tactic list"
                     | Tact_option "hol_'tactic list"
                     | Tact_or "hol_'tactic list"
                     | Tact_one hol_'tactic_simp
                     | Tact_all hol_'tactic_simp
                     | Tact_auto_simp_add_split hol_'ntheorems_l "string list"
                     | Tact_rename_tac "string list"
                     | Tact_case_tac hol_'expr
                     | Tact_blast "nat option"
                     | Tact_clarify
                     | Tact_metis0 "string list" (* e.g. "no_types" (override_type_encs) *)
                                   "hol_'ntheorem list"

datatype hol_'tactic_last = Tacl_done
                          | Tacl_by "hol_'tactic list"
                          | Tacl_sorry

datatype hol_'tac_apply_end = AppE "hol_'tactic list" (* apply_end (... ',' ...) *)

datatype hol_'tac_apply = App "hol_'tactic list" (* apply (... ',' ...) *)
                        | App_using0 hol_'ntheorems_l (* using ... *)
                        | App_unfolding0 hol_'ntheorems_l (* unfolding ... *)
                        | App_let hol_'expr (* name *) hol_'expr
                        | App_have0 string (* name *)
                                    bool (* true: add [simp] *)
                                    hol_'expr
                                    hol_'tactic_last
                        | App_fix_let "string list"
                                      "(hol_'expr (* name *) \<times> hol_'expr) list" (* let statements *) (* TODO merge recursively *)
                                      "hol_'expr list option" (* None => ?thesis
                                                                 Some l => "... ==> ..." *)
                                      "hol_'tac_apply_end list" (* qed apply_end ... *)

datatype hol_lemma = Lemma_by string (* name *) "hol_'expr list" (* specification to prove *)
                              "hol_'tactic list list" (* tactics : apply (... ',' ...) '\n' apply ... *)
                              hol_'tactic_last
                   | Lemma_by_assum string (* name *)
                                    "(string (* name *) \<times> bool (* true: add [simp] *) \<times> hol_'expr) list" (* specification to prove (assms) *)
                                    hol_'expr (* specification to prove (conclusion) *)
                                    "hol_'tac_apply list"
                                    hol_'tactic_last

datatype hol_axiomatization = Axiom string (* name *)
                                    hol_'expr

datatype hol_section = Section_title nat (* nesting level *)
                                     string (* content *)

datatype hol_text = Text string

datatype hol_ML = Ml sml_expr

datatype hol_thm = Thm "hol_'ntheorem list"

datatype hol_interpretation = Interpretation string (* name *)
                                             string (* locale name *)
                                             "hol_'expr list" (* locale param *)
                                             hol_'tactic_last

datatype hol_'t = Theory_dataty hol_datatype
                | Theory_ty_synonym hol_type_synonym
                | Theory_ty_notation hol_type_notation
                | Theory_instantiation_class hol_instantiation
                | Theory_defs_overloaded hol_defs
                | Theory_consts_class hol_consts
                | Theory_definition_hol hol_definition
                | Theory_lemmas_simp hol_lemmas
                | Theory_lemma_by hol_lemma
                | Theory_axiom hol_axiomatization
                | Theory_section_title hol_section
                | Theory_text hol_text
                | Theory_ml hol_ML
                | Theory_thm hol_thm
                | Theory_interpretation hol_interpretation

record hol_'thy_locale = 
  HolThyLocale_name :: string
  HolThyLocale_header :: "( (hol_'expr (* name *) \<times> hol_'type (* 'fix' statement *)) list
                          \<times> (string (* name *) \<times> hol_'expr (* 'assumes' statement *)) option (* None: no 'assumes' to generate *)) list"

datatype hol_'thy = H_thy_simple hol_'t
                  | H_thy_locale hol_'thy_locale "hol_'t list (* positioning comments can occur before and after this group of commands *) list"

section{* ... *}

definition "thm_OF s l = List.fold (\<lambda>x acc. Thm_OF acc x) l s"
definition "thm_simplified s l = List.fold (\<lambda>x acc. Thm_simplified acc x) l s"
definition "Opt s = Ty_apply (Ty_base \<open>option\<close>) [Ty_base s]"
definition "Raw = Ty_base"
definition "Type_synonym' n = Type_synonym n []"
definition "Type_synonym0 n l f = Type_synonym n l (f l)"
definition "Expr_annot' e s = Expr_annot e (Ty_base s)"
definition "wrap_oclty x = \<open>\<cdot>\<close> @@ x"
definition "Expr_annot_ocl e s = Expr_annot' e (wrap_oclty s)"
definition "Expr_lambdas s = Expr_bind0 \<open>\<lambda>\<close> (Expr_basic s)"
definition "Expr_lambda x = Expr_lambdas [x]"
definition "Expr_lambdas0 = Expr_bind0 \<open>\<lambda>\<close>"
definition "Expr_lam x f = Expr_lambdas0 (Expr_basic [x]) (f x)"
definition "Expr_some = Expr_paren \<open>\<lfloor>\<close> \<open>\<rfloor>\<close>"
definition "Expr_parenthesis (* mandatory parenthesis *) = Expr_paren \<open>(\<close> \<open>)\<close>"
definition "Expr_warning_parenthesis (* optional parenthesis that can be removed but a warning will be raised *) = Expr_parenthesis"
definition "Expr_pat b = Expr_basic [\<open>?\<close> @@ b]"
definition "Expr_And x f = Expr_bind0 \<open>\<And>\<close> (Expr_basic [x]) (f x)"
definition "Expr_exists x f = Expr_bind0 \<open>\<exists>\<close> (Expr_basic [x]) (f x)"
definition "Expr_binop = Expr_rewrite"
definition "expr_binop s l = (case rev l of x # xs \<Rightarrow> List.fold (\<lambda>x. Expr_binop x s) xs x)"
definition "expr_binop' s l = (case rev l of x # xs \<Rightarrow> List.fold (\<lambda>x. Expr_parenthesis o Expr_binop x s) xs x)"
definition "Expr_set l = (case l of [] \<Rightarrow> Expr_basic [\<open>{}\<close>] | _ \<Rightarrow> Expr_paren \<open>{\<close> \<open>}\<close> (expr_binop \<open>,\<close> l))"
definition "Expr_oclset l = (case l of [] \<Rightarrow> Expr_basic [\<open>Set{}\<close>] | _ \<Rightarrow> Expr_paren \<open>Set{\<close> \<open>}\<close> (expr_binop \<open>,\<close> l))"
definition "Expr_list l = (case l of [] \<Rightarrow> Expr_basic [\<open>[]\<close>] | _ \<Rightarrow> Expr_paren \<open>[\<close> \<open>]\<close> (expr_binop \<open>,\<close> l))"
definition "Expr_list' f l = Expr_list (List_map f l)"
definition "Expr_pair e1 e2 = Expr_parenthesis (Expr_binop e1 \<open>,\<close> e2)"
definition "Expr_pair' l = (case l of [] \<Rightarrow> Expr_basic [\<open>()\<close>] | _ \<Rightarrow> Expr_paren \<open>(\<close> \<open>)\<close> (expr_binop \<open>,\<close> l))"
definition' \<open>Expr_string s = Expr_basic [flatten [\<open>"\<close>, s, \<open>"\<close>]]\<close>
definition "Expr_applys0 e l = Expr_parenthesis (Expr_applys00 e (List_map Expr_parenthesis l))"
definition "Expr_applys e l = Expr_applys0 (Expr_parenthesis e) l"
definition "Expr_apply e = Expr_applys0 (Expr_basic [e])"
definition "Expr_preunary e1 e2 = Expr_applys00 e1 [e2]" (* no parenthesis and separated with one space *)
definition "Expr_postunary e1 e2 = Expr_applys00 e1 [e2]" (* no parenthesis and separated with one space *)
definition "Expr_case = Expr_function0 o Some"
definition "Expr_function = Expr_function0 None"
definition "Expr_inner = Expr_inner0 []"
definition "Lemmas_simp = Lemmas_simp_opt True"
definition "Lemmas_nosimp = Lemmas_simp_opt False"
definition "Consts_value = \<open>(_)\<close>"
definition "Consts_raw0 s l e o_arg = Consts_raw s l (String_replace_chars (\<lambda>c. if c = Char Nibble5 NibbleF then \<open>'_\<close> else \<degree>c\<degree>) e @@ (case o_arg of
         None \<Rightarrow> \<open>\<close>
       | Some arg \<Rightarrow>
           let ap = \<lambda>s. \<open>'(\<close> @@ s @@ \<open>')\<close> in
           ap (if arg = 0 then
                \<open>\<close>
              else
                Consts_value @@ (flatten (List_map (\<lambda>_. \<open>,\<close> @@ Consts_value) (List_upto 2 arg))))))"
definition "Ty_arrow = Ty_apply_bin \<open>\<Rightarrow>\<close>"
definition "Ty_times = Ty_apply_bin \<open>\<times>\<close>"
definition "Consts s l e = Consts_raw0 s (Ty_arrow (Ty_base \<open>'\<alpha>\<close>) l) e None"
definition "Simp_add_del l_a l_d = Simp_add_del_split l_a l_d []"
definition "Tact_subst_l = Tact_subst_l0 False"

definition "Tac_rule' = Tact_rule0 None"
definition "Tac_rule = Tact_rule0 o Some"
definition "Tac_drule = Tact_drule"
definition "Tac_erule = Tact_erule"
definition "Tac_intro = Tact_intro"
definition "Tac_elim = Tact_elim"
definition "Tac_subst_l0 = Tact_subst_l0"
definition "Tac_subst_l = Tact_subst_l"
definition "Tac_insert = Tact_insert o List_map Thms_single"
definition "Tac_plus = Tact_plus"
definition "Tac_option = Tact_option"
definition "Tac_or = Tact_or"
definition "tac_gen_simp = Simp_add_del [] []"
definition "tac_gen_simp_add2 l1 l2 = Simp_add_del (List_flatten [ List_map Thms_mult l1
                                                    , List_map (Thms_single o Thm_str) l2])
                                           []"
definition "tac_gen_simp_add_del l1 l2 = Simp_add_del (List_map (Thms_single o Thm_str) l1)
                                              (List_map (Thms_single o Thm_str) l2)"
definition "tac_gen_simp_add_del_split l1 l2 l3 = Simp_add_del_split (List_map Thms_single l1)
                                                             (List_map Thms_single l2)
                                                             (List_map Thms_single l3)"
definition "tac_gen_simp_add_split l1 l2 = Simp_add_del_split (List_map Thms_single l1)
                                                      []
                                                      (List_map Thms_single l2)"
definition "tac_gen_simp_only l = Simp_only (List_map Thms_single l)"
definition "tac_gen_simp_only' l = Simp_only (List_map Thms_mult l)"
definition "tac_gen_simp_add0 l = Simp_add_del (List_map Thms_single l) []"
definition "Tac_simp = Tact_one tac_gen_simp"
definition "Tac_simp_add2 l1 l2 = Tact_one (tac_gen_simp_add2 l1 l2)"
definition "Tac_simp_add_del l1 l2 = Tact_one (tac_gen_simp_add_del l1 l2)"
definition "Tac_simp_add_del_split l1 l2 l3 = Tact_one (tac_gen_simp_add_del_split l1 l2 l3)"
definition "Tac_simp_add_split l1 l2 = Tact_one (tac_gen_simp_add_split l1 l2)"
definition "Tac_simp_only l = Tact_one (tac_gen_simp_only l)"
definition "Tac_simp_only' l = Tact_one (tac_gen_simp_only' l)"
definition "Tac_simp_add0 l = Tact_one (tac_gen_simp_add0 l)"
definition "Tac_simp_add = Tac_simp_add2 []"
definition "Tac_simp_all = Tact_all tac_gen_simp"
definition "Tac_simp_all_add l = Tact_all (tac_gen_simp_add2 [] l)"
definition "Tac_simp_all_only l = Tact_all (tac_gen_simp_only l)"
definition "Tac_simp_all_only' l = Tact_all (tac_gen_simp_only' l)"
definition "Tac_auto_simp_add2 l1 l2 = Tact_auto_simp_add_split (List_flatten [ List_map Thms_mult l1
                                                                , List_map (Thms_single o Thm_str) l2]) []"
definition "Tac_auto_simp_add_split l = Tact_auto_simp_add_split (List_map Thms_single l)"
definition "Tac_rename_tac = Tact_rename_tac"
definition "Tac_case_tac = Tact_case_tac"
definition "Tac_blast = Tact_blast"
definition "Tac_clarify = Tact_clarify"
definition "Tac_metis = Tact_metis0 []"
definition "Tac_metis0 = Tact_metis0"

definition "Tac_subst_asm b = Tac_subst_l0 b [\<open>0\<close>]"
definition "Tac_subst = Tac_subst_l [\<open>0\<close>]"
definition "Tac_auto_simp_add = Tac_auto_simp_add2 []"
definition "Tac_auto = Tac_auto_simp_add []"
definition "ty_arrow l = (case rev l of x # xs \<Rightarrow> List.fold Ty_arrow xs x)"

definition "App_using = App_using0 o List_map Thms_single"
definition "App_unfolding = App_unfolding0 o List_map Thms_single"
definition "App_fix l = App_fix_let l [] None []"
definition "App_have n = App_have0 n False"

fun cross_abs_aux where
   "cross_abs_aux f l x = (\<lambda> (Suc n, PureAbs s _ t) \<Rightarrow> f s (cross_abs_aux f (s # l) (n, t))
                         | (_, e) \<Rightarrow> Expr_inner0 l e)
                         x"

definition "cross_abs f n l = cross_abs_aux f [] (n, l)"

subsection{* ... *}

definition "hol_map_lemma f = (\<lambda> Theory_lemma_by x \<Rightarrow> Theory_lemma_by (f x)
                               | x \<Rightarrow> x)"

end
