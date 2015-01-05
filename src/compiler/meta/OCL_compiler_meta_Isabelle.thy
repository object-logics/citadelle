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

datatype hol_simplety = Opt string | Raw string

datatype hol_dataty = Datatype string (* name *)
                           "(string (* name *) \<times> hol_simplety list (* arguments *)) list" (* constructors *)

datatype hol_raw_ty =
   Ty_apply hol_raw_ty "hol_raw_ty list"
 | Ty_apply_bin string (* binop *) hol_raw_ty hol_raw_ty
 | Ty_base string

datatype hol_ty_synonym = Type_synonym string (* name *)
                                       hol_raw_ty (* content *)

datatype hol_expr = Expr_rewrite hol_expr (* left *) string (* symb rewriting *) hol_expr (* right *)
                  | Expr_basic "string list"
                  | Expr_oid string (* prefix *) internal_oid
                  | Expr_annot0 hol_expr hol_raw_ty
                  | Expr_bind0 string (* symbol *) hol_expr (* arg *) hol_expr
                  | Expr_function0 "hol_expr (* value *) option" (* none: function *) "(hol_expr (* pattern *) \<times> hol_expr (* to return *)) list"
                  | Expr_applys00 hol_expr "hol_expr list"
                  | Expr_paren string (* left *) string (* right *) hol_expr
                  | Expr_if_then_else hol_expr hol_expr hol_expr
                  | Expr_inner0 "string list" (* de bruijn variables under "lam", pre-initialized context *)
                                pure_term (* inner syntax term *)

datatype hol_instantiation_class = Instantiation string (* name *)
                                                 string (* name in definition *)
                                                 hol_expr

datatype hol_defs_overloaded = Defs_overloaded string (* name *) hol_expr (* content *)

datatype hol_consts_class = Consts_raw string (* name *)
                                       hol_raw_ty
                                       string (* ocl 'post' mixfix *)

datatype hol_definition_hol = Definition hol_expr
                            | Definition_abbrev string (* name *) "hol_expr (* syntax extension *) \<times> nat (* priority *)" hol_expr
                            | Definition_abbrev0 string (* name *) hol_expr (* syntax extension *) hol_expr

datatype hol_ntheorem = Thm_str string
                      | Thm_THEN hol_ntheorem hol_ntheorem
                      | Thm_simplified hol_ntheorem hol_ntheorem
                      | Thm_symmetric hol_ntheorem
                      | Thm_where hol_ntheorem "(string \<times> hol_expr) list"
                      | Thm_of hol_ntheorem "hol_expr list"
                      | Thm_OF hol_ntheorem hol_ntheorem

datatype hol_ntheorems = Thms_single hol_ntheorem
                       | Thms_mult string

type_synonym hol_ntheorems_l = "hol_ntheorems list"

datatype hol_lemmas_simp = Lemmas_simp_opt
                                       bool (* True : simp *)
                                       string (* name *)
                                       "hol_ntheorem list"
                         | Lemmas_simps string (* name *)
                                        "string (* thms *) list"

datatype hol_tactic_simp = Simp_only hol_ntheorems_l
                         | Simp_add_del_split hol_ntheorems_l (* add *) hol_ntheorems_l (* del *) hol_ntheorems_l (* split *)

datatype hol_tactic = Tact_rule0 "hol_ntheorem option"
                    | Tact_drule hol_ntheorem
                    | Tact_erule hol_ntheorem
                    | Tact_intro "hol_ntheorem list"
                    | Tact_elim hol_ntheorem
                    | Tact_subst_l0 bool (* asm *)
                                    "string (* nat *) list" (* pos *)
                                    hol_ntheorem
                    | Tact_insert hol_ntheorems_l
                    | Tact_plus "hol_tactic list"
                    | Tact_option "hol_tactic list"
                    | Tact_one hol_tactic_simp
                    | Tact_auto_simp_add_split hol_ntheorems_l "string list"
                    | Tact_rename_tac "string list"
                    | Tact_case_tac hol_expr
                    | Tact_blast "nat option"
                    | Tact_clarify

datatype hol_tactic_last = Tacl_done
                         | Tacl_by "hol_tactic list"
                         | Tacl_sorry

datatype hol_tac_apply_end = AppE "hol_tactic list" (* apply_end (... ',' ...) *)

datatype hol_tac_apply = App "hol_tactic list" (* apply (... ',' ...) *)
                       | App_using0 hol_ntheorems_l (* using ... *)
                       | App_unfolding0 hol_ntheorems_l (* unfolding ... *)
                       | App_let hol_expr (* name *) hol_expr
                       | App_have string (* name *) hol_expr hol_tactic_last
                       | App_fix_let "string list"
                                     "(hol_expr (* name *) \<times> hol_expr) list" (* let statements *) (* TODO merge recursively *)
                                     "hol_expr list option" (* None => ?thesis
                                                               Some l => "... ==> ..." *)
                                     "hol_tac_apply_end list" (* qed apply_end ... *)

datatype hol_lemma_by = Lemma_by string (* name *) "hol_expr list" (* specification to prove *)
                          "hol_tactic list list" (* tactics : apply (... ',' ...) '\n' apply ... *)
                          hol_tactic_last
                      | Lemma_by_assum string (* name *)
                          "(string (* name *) \<times> bool (* true: add [simp] *) \<times> hol_expr) list" (* specification to prove (assms) *)
                          hol_expr (* specification to prove (conclusion) *)
                          "hol_tac_apply list"
                          hol_tactic_last

datatype hol_axiom = Axiom string (* name *)
                           hol_expr

datatype hol_section_title = Section_title nat (* nesting level *)
                                           string (* content *)

datatype hol_text = Text string

datatype hol_ml = Ml sml_expr

datatype hol_thm = Thm "hol_ntheorem list"

datatype hol_thy = Theory_dataty hol_dataty
                 | Theory_ty_synonym hol_ty_synonym
                 | Theory_instantiation_class hol_instantiation_class
                 | Theory_defs_overloaded hol_defs_overloaded
                 | Theory_consts_class hol_consts_class
                 | Theory_definition_hol hol_definition_hol
                 | Theory_lemmas_simp hol_lemmas_simp
                 | Theory_lemma_by hol_lemma_by
                 | Theory_axiom hol_axiom
                 | Theory_section_title hol_section_title
                 | Theory_text hol_text
                 | Theory_ml hol_ml
                 | Theory_thm hol_thm

section{* ... *}

definition "thm_OF s l = List.fold (\<lambda>x acc. Thm_OF acc x) l s"
definition "thm_simplified s l = List.fold (\<lambda>x acc. Thm_simplified acc x) l s"
definition "Expr_annot e s = Expr_annot0 e (Ty_base s)"
definition "Expr_bind symb s e = Expr_bind0 symb (Expr_basic s) e"
definition "Expr_lambdas = Expr_bind unicode_lambda"
definition "Expr_lambda x = Expr_lambdas [x]"
definition "Expr_lambdas0 = Expr_bind0 unicode_lambda"
definition "Expr_lam x f = Expr_lambdas0 (Expr_basic [x]) (f x)"
definition "Expr_some = Expr_paren unicode_lfloor unicode_rfloor"
definition "Expr_parenthesis (* mandatory parenthesis *) = Expr_paren ''('' '')''"
definition "Expr_warning_parenthesis (* optional parenthesis that can be removed but a warning will be raised *) = Expr_parenthesis"
definition "Expr_pat b = Expr_basic [Char Nibble3 NibbleF # b]"
definition "Expr_And x f = Expr_bind0 unicode_And (Expr_basic [x]) (f x)"
definition "Expr_exists x f = Expr_bind0 unicode_exists (Expr_basic [x]) (f x)"
definition "Expr_binop = Expr_rewrite"
definition "expr_binop s l = (case rev l of x # xs \<Rightarrow> List.fold (\<lambda>x. Expr_binop x s) xs x)"
definition "expr_binop' s l = (case rev l of x # xs \<Rightarrow> List.fold (\<lambda>x. Expr_parenthesis o Expr_binop x s) xs x)"
definition "Expr_set l = (case l of [] \<Rightarrow> Expr_basic [''{}''] | _ \<Rightarrow> Expr_paren ''{'' ''}'' (expr_binop '','' l))"
definition "Expr_oclset l = (case l of [] \<Rightarrow> Expr_basic [''Set{}''] | _ \<Rightarrow> Expr_paren ''Set{'' ''}'' (expr_binop '','' l))"
definition "Expr_list l = (case l of [] \<Rightarrow> Expr_basic [''[]''] | _ \<Rightarrow> Expr_paren ''['' '']'' (expr_binop '','' l))"
definition "Expr_list' f l = Expr_list (List_map f l)"
definition "Expr_pair e1 e2 = Expr_parenthesis (Expr_binop e1 '','' e2)"
definition "Expr_string s = Expr_basic [flatten [[Char Nibble2 Nibble2], s, [Char Nibble2 Nibble2]]]"
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
definition "Consts_value = ''(_)''"
definition "Consts_raw0 s l e o_arg = Consts_raw s l (e @@ (case o_arg of
         None \<Rightarrow> ''''
       | Some arg \<Rightarrow>
           let ap = \<lambda>s. '''('' @@ s @@ ''')'' in
           ap (if arg = 0 then
                ''''
              else
                Consts_value @@ (flatten (List_map (\<lambda>_. '','' @@ Consts_value) (List_upto 2 arg))))))"
definition "Ty_arrow = Ty_apply_bin unicode_Rightarrow"
definition "Ty_times = Ty_apply_bin unicode_times"
definition "Consts s l e = Consts_raw0 s (Ty_arrow (Ty_base (Char Nibble2 Nibble7 # unicode_alpha)) l) e None"
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
definition "Tac_simp = Tact_one (Simp_add_del [] [])"
definition "Tac_simp_add2 l1 l2 = Tact_one (Simp_add_del (flatten [ List_map Thms_mult l1
                                                                  , List_map (Thms_single o Thm_str) l2])
                                                         [])"
definition "Tac_simp_add_del l1 l2 = Tact_one (Simp_add_del (List_map (Thms_single o Thm_str) l1)
                                                            (List_map (Thms_single o Thm_str) l2))"
definition "Tac_simp_add_del_split l1 l2 l3 = Tact_one (Simp_add_del_split (List_map Thms_single l1)
                                                                           (List_map Thms_single l2)
                                                                           (List_map Thms_single l3))"
definition "Tac_simp_add_split l1 l2 = Tact_one (Simp_add_del_split (List_map Thms_single l1)
                                                                    []
                                                                    (List_map Thms_single l2))"
definition "Tac_simp_only l = Tact_one (Simp_only (List_map Thms_single l))"
definition "Tac_simp_add0 l = Tact_one (Simp_add_del (List_map Thms_single l) [])"
definition "Tac_simp_add = Tac_simp_add2 []"
definition "Tac_simp_all = Tac_plus [Tac_simp]"
definition "Tac_simp_all_add l = Tac_plus [Tac_simp_add l]"
definition "Tac_simp_all_only l = Tac_plus [Tac_simp_only l]"
definition "Tac_auto_simp_add2 l1 l2 = Tact_auto_simp_add_split (flatten [ List_map Thms_mult l1
                                                                , List_map (Thms_single o Thm_str) l2]) []"
definition "Tac_auto_simp_add_split l = Tact_auto_simp_add_split (List_map Thms_single l)"
definition "Tac_rename_tac = Tact_rename_tac"
definition "Tac_case_tac = Tact_case_tac"
definition "Tac_blast = Tact_blast"
definition "Tac_clarify = Tact_clarify"

definition "Tac_subst_asm b = Tac_subst_l0 b [''0'']"
definition "Tac_subst = Tac_subst_l [''0'']"
definition "Tac_auto_simp_add = Tac_auto_simp_add2 []"
definition "Tac_auto = Tac_auto_simp_add []"
definition "ty_arrow l = (case rev l of x # xs \<Rightarrow> List.fold Ty_arrow xs x)"

definition "App_using = App_using0 o List_map Thms_single"
definition "App_unfolding = App_unfolding0 o List_map Thms_single"
definition "App_fix l = App_fix_let l [] None []"

end
