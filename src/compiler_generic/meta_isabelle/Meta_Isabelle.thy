(*****************************************************************************
 * A Meta-Model for the Isabelle API
 *
 * Copyright (c) 2013-2015 Université Paris-Saclay, Univ Paris Sud, France
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

section{* Isabelle Meta-Model aka. AST definition of Isabelle *}

theory  Meta_Isabelle
imports Meta_Pure
        Meta_SML
begin

subsection{* Type Definition *}

text{* The following datatypes beginning with \verb|hol__| represent semi-concrete syntax,
       deliberately not minimal abstract syntax like Pure Term, in order to facilitate
       the pretty-printing process.
       When using the FOCL compiler in shallow mode, variants such as @{term Ty_apply_paren}
       are irrelevant. *}

datatype hol__type = Ty_apply hol__type "hol__type list"
                   | Ty_apply_bin string (* binop *) hol__type hol__type
                   | Ty_apply_paren string (* left *) string (* right *) hol__type
                   | Ty_base string

datatype hol_datatype = Datatype string (* name *)
                                 "(string (* name *) \<times> hol__type list (* arguments *)) list" (* constructors *)

datatype hol_type_synonym = Type_synonym string (* name *)
                                         "string list" (* parametric variables *)
                                         hol__type (* content *)

datatype hol__expr = Expr_rewrite hol__expr (* left *) string (* symb rewriting *) hol__expr (* right *)
                   | Expr_basic "string list"
                   | Expr_annot hol__expr hol__type
                   | Expr_bind string (* symbol *) hol__expr (* arg *) hol__expr
                   | Expr_fun_case "hol__expr (* value *) option" (* none: function *) "(hol__expr (* pattern *) \<times> hol__expr (* to return *)) list"
                   | Expr_apply hol__expr "hol__expr list"
                   | Expr_paren string (* left *) string (* right *) hol__expr
                   | Expr_if_then_else hol__expr hol__expr hol__expr
                   | Expr_pure "string list" (* simulate a pre-initialized context (de bruijn variables under "lam") *)
                               pure_term (* usual continuation of inner syntax term *)

datatype hol_type_notation = Type_notation string (* name *)
                                           string (* content *)

datatype hol_instantiation = Instantiation string (* name *)
                                           string (* name in definition *)
                                           hol__expr

datatype hol_defs = Defs_overloaded string (* name *) hol__expr (* content *)

datatype hol_consts = Consts string (* name *)
                             hol__type
                             string (* ocl 'post' mixfix *)

datatype hol_definition = Definition hol__expr
                        | Definition_where1 string (* name *) "hol__expr (* syntax extension *) \<times> nat (* priority *)" hol__expr
                        | Definition_where2 string (* name *) hol__expr (* syntax extension *) hol__expr

datatype hol__thm_attribute = Thm_thm string (* represents a single thm *)
                            | Thm_thms string (* represents several thms *)
                            | Thm_THEN hol__thm_attribute hol__thm_attribute
                            | Thm_simplified hol__thm_attribute hol__thm_attribute
                            | Thm_symmetric hol__thm_attribute
                            | Thm_where hol__thm_attribute "(string \<times> hol__expr) list"
                            | Thm_of hol__thm_attribute "hol__expr list"
                            | Thm_OF hol__thm_attribute hol__thm_attribute

datatype hol__thm = Thms_single hol__thm_attribute
                  | Thms_mult hol__thm_attribute

type_synonym hol__thm_l = "hol__thm list"

datatype hol_lemmas = Lemmas_simp_thm bool (* True : simp *)
                                      string (* name *)
                                      "hol__thm_attribute list"
                    | Lemmas_simp_thms string (* name *)
                                       "string (* thms *) list"

datatype hol__method_simp = Method_simp_only hol__thm_l
                          | Method_simp_add_del_split hol__thm_l (* add *) hol__thm_l (* del *) hol__thm_l (* split *)

datatype hol__method = Method_rule "hol__thm_attribute option"
                     | Method_drule hol__thm_attribute
                     | Method_erule hol__thm_attribute
                     | Method_intro "hol__thm_attribute list"
                     | Method_elim hol__thm_attribute
                     | Method_subst bool (* asm *)
                                  "string (* nat *) list" (* pos *)
                                  hol__thm_attribute
                     | Method_insert hol__thm_l
                     | Method_plus "hol__method list"
                     | Method_option "hol__method list"
                     | Method_or "hol__method list"
                     | Method_one hol__method_simp
                     | Method_all hol__method_simp
                     | Method_auto_simp_add_split hol__thm_l "string list"
                     | Method_rename_tac "string list"
                     | Method_case_tac hol__expr
                     | Method_blast "nat option"
                     | Method_clarify
                     | Method_metis "string list" (* e.g. "no_types" (override_type_encs) *)
                                  "hol__thm_attribute list"

datatype hol__command_final = Command_done
                            | Command_by "hol__method list"
                            | Command_sorry

datatype hol__command_state = Command_apply_end "hol__method list" (* apply_end (... ',' ...) *)

datatype hol__command_proof = Command_apply "hol__method list" (* apply (... ',' ...) *)
                            | Command_using hol__thm_l (* using ... *)
                            | Command_unfolding hol__thm_l (* unfolding ... *)
                            | Command_let hol__expr (* name *) hol__expr
                            | Command_have string (* name *)
                                        bool (* true: add [simp] *)
                                        hol__expr
                                        hol__command_final
                            | Command_fix_let "string list"
                                           "(hol__expr (* name *) \<times> hol__expr) list" (* let statements *) (* TODO merge recursively *)
                                           "hol__expr list option" (* None => ?thesis
                                                                      Some l => "... ==> ..." *)
                                           "hol__command_state list" (* qed apply_end ... *)

datatype hol_lemma = Lemma string (* name *) "hol__expr list" (* specification to prove *)
                           "hol__method list list" (* tactics : apply (... ',' ...) '\n' apply ... *)
                           hol__command_final
                   | Lemma_assumes string (* name *)
                                   "(string (* name *) \<times> bool (* true: add [simp] *) \<times> hol__expr) list" (* specification to prove (assms) *)
                                   hol__expr (* specification to prove (conclusion) *)
                                   "hol__command_proof list"
                                   hol__command_final

datatype hol_axiomatization = Axiomatization string (* name *)
                                             hol__expr

datatype hol_section = Section nat (* nesting level *)
                               string (* content *)

datatype hol_text = Text string

datatype hol_ML = SML sml_expr

datatype hol_thm = Thm "hol__thm_attribute list"

datatype hol_interpretation = Interpretation string (* name *)
                                             string (* locale name *)
                                             "hol__expr list" (* locale param *)
                                             hol__command_final

datatype hol__t = Theory_datatype hol_datatype
                | Theory_type_synonym hol_type_synonym
                | Theory_type_notation hol_type_notation
                | Theory_instantiation hol_instantiation
                | Theory_defs hol_defs
                | Theory_consts hol_consts
                | Theory_definition hol_definition
                | Theory_lemmas hol_lemmas
                | Theory_lemma hol_lemma
                | Theory_axiomatization hol_axiomatization
                | Theory_section hol_section
                | Theory_text hol_text
                | Theory_ML hol_ML
                | Theory_thm hol_thm
                | Theory_interpretation hol_interpretation

record hol__thy_locale = 
  HolThyLocale_name :: string
  HolThyLocale_header :: "( (hol__expr (* name *) \<times> hol__type (* 'fix' statement *)) list
                          \<times> (string (* name *) \<times> hol__expr (* 'assumes' statement *)) option (* None: no 'assumes' to generate *)) list"

datatype hol__thy = H_thy_simple hol__t
                  | H_thy_locale hol__thy_locale "hol__t list (* positioning comments can occur before and after this group of commands *) list"

subsection{* Extending Type Definitions with Conservative Definitions *}

locale T
begin
definition "thm = Thm_thm"
definition "thms = Thm_thms"
definition "THEN = Thm_THEN"
definition "simplified = Thm_simplified"
definition "symmetric = Thm_symmetric"
definition "where = Thm_where"
definition "of' = Thm_of"
definition "OF = Thm_OF"
definition "OF_l s l = List.fold (\<lambda>x acc. Thm_OF acc x) l s"
definition "simplified_l s l = List.fold (\<lambda>x acc. Thm_simplified acc x) l s"
end

lemmas [code] =
  (* def *)
  T.thm_def
  T.thms_def
  T.THEN_def
  T.simplified_def
  T.symmetric_def
  T.where_def
  T.of'_def
  T.OF_def
  T.OF_l_def
  T.simplified_l_def

definition "Opt s = Ty_apply (Ty_base \<open>option\<close>) [Ty_base s]"
definition "Raw = Ty_base"
definition "Type_synonym' n = Type_synonym n []"
definition "Type_synonym'' n l f = Type_synonym n l (f l)"
definition "Expr_annot' e s = Expr_annot e (Ty_base s)"
definition "wrap_oclty x = \<open>\<cdot>\<close> @@ x"
definition "Expr_annot_ocl e s = Expr_annot' e (wrap_oclty s)"
definition "Expr_lambdas s = Expr_bind \<open>\<lambda>\<close> (Expr_basic s)"
definition "Expr_lambda x = Expr_lambdas [x]"
definition "Expr_lambdas0 = Expr_bind \<open>\<lambda>\<close>"
definition "Expr_lam x f = Expr_lambdas0 (Expr_basic [x]) (f x)"
definition "Expr_some = Expr_paren \<open>\<lfloor>\<close> \<open>\<rfloor>\<close>"
definition "Expr_parenthesis (* mandatory parenthesis *) = Expr_paren \<open>(\<close> \<open>)\<close>"
definition "Expr_warning_parenthesis (* optional parenthesis that can be removed but a warning will be raised *) = Expr_parenthesis"
definition "Expr_pat b = Expr_basic [\<open>?\<close> @@ b]"
definition "Expr_And x f = Expr_bind \<open>\<And>\<close> (Expr_basic [x]) (f x)"
definition "Expr_exists x f = Expr_bind \<open>\<exists>\<close> (Expr_basic [x]) (f x)"
definition "Expr_binop = Expr_rewrite"
definition "expr_binop s l = (case rev l of x # xs \<Rightarrow> List.fold (\<lambda>x. Expr_binop x s) xs x)"
definition "expr_binop' s l = (case rev l of x # xs \<Rightarrow> List.fold (\<lambda>x. Expr_parenthesis o Expr_binop x s) xs x)"
definition "Expr_set l = (case l of [] \<Rightarrow> Expr_basic [\<open>{}\<close>] | _ \<Rightarrow> Expr_paren \<open>{\<close> \<open>}\<close> (expr_binop \<open>,\<close> l))"
definition "Expr_oclset l = (case l of [] \<Rightarrow> Expr_basic [\<open>Set{}\<close>] | _ \<Rightarrow> Expr_paren \<open>Set{\<close> \<open>}\<close> (expr_binop \<open>,\<close> l))"
definition "Expr_list l = (case l of [] \<Rightarrow> Expr_basic [\<open>[]\<close>] | _ \<Rightarrow> Expr_paren \<open>[\<close> \<open>]\<close> (expr_binop \<open>,\<close> l))"
definition "Expr_list' f l = Expr_list (L.map f l)"
definition "Expr_pair e1 e2 = Expr_parenthesis (Expr_binop e1 \<open>,\<close> e2)"
definition "Expr_pair' l = (case l of [] \<Rightarrow> Expr_basic [\<open>()\<close>] | _ \<Rightarrow> Expr_paren \<open>(\<close> \<open>)\<close> (expr_binop \<open>,\<close> l))"
definition' \<open>Expr_string s = Expr_basic [S.flatten [\<open>"\<close>, s, \<open>"\<close>]]\<close>
definition "Expr_applys0 e l = Expr_parenthesis (Expr_apply e (L.map Expr_parenthesis l))"
definition "Expr_applys e l = Expr_applys0 (Expr_parenthesis e) l"
definition "Expr_app e = Expr_applys0 (Expr_basic [e])"
definition "Expr_preunary e1 e2 = Expr_apply e1 [e2]" (* no parenthesis and separated with one space *)
definition "Expr_postunary e1 e2 = Expr_apply e1 [e2]" (* no parenthesis and separated with one space *)
definition "Expr_case = Expr_fun_case o Some"
definition "Expr_function = Expr_fun_case None"
definition "Expr_pure' = Expr_pure []"
definition "Lemmas_simp = Lemmas_simp_thm True"
definition "Lemmas_nosimp = Lemmas_simp_thm False"
definition "Consts_value = \<open>(_)\<close>"
definition "Consts_raw0 s l e o_arg = Consts s l (String.replace_chars (\<lambda>c. if c = Char Nibble5 NibbleF then \<open>'_\<close> else \<degree>c\<degree>) e @@ (case o_arg of
         None \<Rightarrow> \<open>\<close>
       | Some arg \<Rightarrow>
           let ap = \<lambda>s. \<open>'(\<close> @@ s @@ \<open>')\<close> in
           ap (if arg = 0 then
                \<open>\<close>
              else
                Consts_value @@ (S.flatten (L.map (\<lambda>_. \<open>,\<close> @@ Consts_value) (L.upto 2 arg))))))"
definition "Ty_arrow = Ty_apply_bin \<open>\<Rightarrow>\<close>"
definition "Ty_times = Ty_apply_bin \<open>\<times>\<close>"
definition "Consts' s l e = Consts_raw0 s (Ty_arrow (Ty_base \<open>'\<alpha>\<close>) l) e None"

locale M
begin
definition "Method_simp_add_del l_a l_d = Method_simp_add_del_split l_a l_d []"
definition "Method_subst_l = Method_subst False"

definition "rule' = Method_rule None"
definition "rule = Method_rule o Some"
definition "drule = Method_drule"
definition "erule = Method_erule"
definition "intro = Method_intro"
definition "elim = Method_elim"
definition "subst_l0 = Method_subst"
definition "subst_l = Method_subst_l"
definition insert where "insert = Method_insert o L.map Thms_single"
definition plus where "plus = Method_plus"
definition "option = Method_option"
definition "or = Method_or"
definition "meth_gen_simp = Method_simp_add_del [] []"
definition "meth_gen_simp_add2 l1 l2 = Method_simp_add_del (L.flatten [ L.map Thms_mult l1
                                                    , L.map (Thms_single o Thm_thm) l2])
                                           []"
definition "meth_gen_simp_add_del l1 l2 = Method_simp_add_del (L.map (Thms_single o Thm_thm) l1)
                                              (L.map (Thms_single o Thm_thm) l2)"
definition "meth_gen_simp_add_del_split l1 l2 l3 = Method_simp_add_del_split (L.map Thms_single l1)
                                                             (L.map Thms_single l2)
                                                             (L.map Thms_single l3)"
definition "meth_gen_simp_add_split l1 l2 = Method_simp_add_del_split (L.map Thms_single l1)
                                                      []
                                                      (L.map Thms_single l2)"
definition "meth_gen_simp_only l = Method_simp_only (L.map Thms_single l)"
definition "meth_gen_simp_only' l = Method_simp_only (L.map Thms_mult l)"
definition "meth_gen_simp_add0 l = Method_simp_add_del (L.map Thms_single l) []"
definition "simp = Method_one meth_gen_simp"
definition "simp_add2 l1 l2 = Method_one (meth_gen_simp_add2 l1 l2)"
definition "simp_add_del l1 l2 = Method_one (meth_gen_simp_add_del l1 l2)"
definition "simp_add_del_split l1 l2 l3 = Method_one (meth_gen_simp_add_del_split l1 l2 l3)"
definition "simp_add_split l1 l2 = Method_one (meth_gen_simp_add_split l1 l2)"
definition "simp_only l = Method_one (meth_gen_simp_only l)"
definition "simp_only' l = Method_one (meth_gen_simp_only' l)"
definition "simp_add0 l = Method_one (meth_gen_simp_add0 l)"
definition "simp_add = simp_add2 []"
definition "simp_all = Method_all meth_gen_simp"
definition "simp_all_add l = Method_all (meth_gen_simp_add2 [] l)"
definition "simp_all_only l = Method_all (meth_gen_simp_only l)"
definition "simp_all_only' l = Method_all (meth_gen_simp_only' l)"
definition "auto_simp_add2 l1 l2 = Method_auto_simp_add_split (L.flatten [ L.map Thms_mult l1
                                                                , L.map (Thms_single o Thm_thm) l2]) []"
definition "auto_simp_add_split l = Method_auto_simp_add_split (L.map Thms_single l)"
definition "rename_tac = Method_rename_tac"
definition "case_tac = Method_case_tac"
definition "blast = Method_blast"
definition "clarify = Method_clarify"
definition "metis = Method_metis []"
definition "metis0 = Method_metis"

definition "subst_asm b = subst_l0 b [\<open>0\<close>]"
definition "subst = subst_l [\<open>0\<close>]"
definition "auto_simp_add = auto_simp_add2 []"
definition "auto = auto_simp_add []"
end

lemmas [code] =
  (* def *)
  M.Method_simp_add_del_def
  M.Method_subst_l_def
  M.rule'_def
  M.rule_def
  M.drule_def
  M.erule_def
  M.intro_def
  M.elim_def
  M.subst_l0_def
  M.subst_l_def
  M.insert_def
  M.plus_def
  M.option_def
  M.or_def
  M.meth_gen_simp_def
  M.meth_gen_simp_add2_def
  M.meth_gen_simp_add_del_def
  M.meth_gen_simp_add_del_split_def
  M.meth_gen_simp_add_split_def
  M.meth_gen_simp_only_def
  M.meth_gen_simp_only'_def
  M.meth_gen_simp_add0_def
  M.simp_def
  M.simp_add2_def
  M.simp_add_del_def
  M.simp_add_del_split_def
  M.simp_add_split_def
  M.simp_only_def
  M.simp_only'_def
  M.simp_add0_def
  M.simp_add_def
  M.simp_all_def
  M.simp_all_add_def
  M.simp_all_only_def
  M.simp_all_only'_def
  M.auto_simp_add2_def
  M.auto_simp_add_split_def
  M.rename_tac_def
  M.case_tac_def
  M.blast_def
  M.clarify_def
  M.metis_def
  M.metis0_def
  M.subst_asm_def
  M.subst_def
  M.auto_simp_add_def
  M.auto_def

definition "ty_arrow l = (case rev l of x # xs \<Rightarrow> List.fold Ty_arrow xs x)"

locale C 
begin
definition "done = Command_done"
definition "by = Command_by"
definition "sorry = Command_sorry"
definition "apply_end = Command_apply_end"
definition "apply = Command_apply"
definition "using = Command_using o L.map Thms_single"
definition "unfolding = Command_unfolding o L.map Thms_single"
definition "let' = Command_let"
definition "fix_let = Command_fix_let"
definition "fix l = Command_fix_let l [] None []"
definition "have n = Command_have n False"
definition "have0 = Command_have"
end

lemmas [code] =
  (* def *)
  C.done_def
  C.by_def
  C.sorry_def
  C.apply_end_def
  C.apply_def
  C.using_def
  C.unfolding_def
  C.let'_def
  C.fix_let_def
  C.fix_def
  C.have_def
  C.have0_def

fun cross_abs_aux where
   "cross_abs_aux f l x = (\<lambda> (Suc n, Pure_Abs s _ t) \<Rightarrow> f s (cross_abs_aux f (s # l) (n, t))
                         | (_, e) \<Rightarrow> Expr_pure l e)
                         x"

definition "cross_abs f n l = cross_abs_aux f [] (n, l)"

subsection{* Operations of Fold, Map, ..., on the Meta-Model *}

definition "hol_map_lemma f = (\<lambda> Theory_lemma x \<Rightarrow> Theory_lemma (f x)
                               | x \<Rightarrow> x)"

end
