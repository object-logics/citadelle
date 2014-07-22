(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_meta_Isabelle.thy ---
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
 | Ty_base string
 | Ty_arrow hol_raw_ty hol_raw_ty
 | Ty_times hol_raw_ty hol_raw_ty

datatype hol_ty_synonym = Type_synonym string (* name *)
                                       hol_raw_ty (* content *)

datatype hol_expr = Expr_case hol_expr (* value *)
                              "(hol_expr (* pattern *) \<times> hol_expr (* to return *)) list"
                  | Expr_rewrite hol_expr (* left *) string (* symb rewriting *) hol_expr (* right *)
                  | Expr_basic "string list"
                  | Expr_oid string (* prefix *) internal_oid
                  | Expr_binop hol_expr string hol_expr
                  | Expr_annot0 hol_expr hol_raw_ty
                  | Expr_bind string (* symbol *) "string list" (* arg *) hol_expr
                  | Expr_bind0 string (* symbol *) hol_expr (* arg *) hol_expr
                  | Expr_function "(hol_expr (* pattern *) \<times> hol_expr (* to return *)) list"
                  | Expr_apply string "hol_expr list"
                  | Expr_applys hol_expr "hol_expr list"
                  | Expr_preunary hol_expr hol_expr (* no parenthesis and separated with one space *)
                  | Expr_postunary hol_expr hol_expr (* no parenthesis and separated with one space *)
                  | Expr_paren string (* left *) string (* right *) hol_expr
                  | Expr_if_then_else hol_expr hol_expr hol_expr
                  | Expr_inner pure_term (* inner syntax term *)

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

datatype hol_lemmas_simp = Lemmas_simp string (* name *)
                                       "hol_ntheorem list"
                         | Lemmas_simps string (* name *)
                                        "string (* thms *) list"

datatype hol_tactic = Tac_rule hol_ntheorem
                    | Tac_drule hol_ntheorem
                    | Tac_erule hol_ntheorem
                    | Tac_intro "hol_ntheorem list"
                    | Tac_elim hol_ntheorem
                    | Tac_subst_l "string (* nat *) list" (* pos *) hol_ntheorem
                    | Tac_insert "hol_ntheorem list"
                    | Tac_plus "hol_tactic list"
                    | Tac_option "hol_tactic list"
                    | Tac_simp | Tac_simp_add "string list" | Tac_simp_add_del "string list" "string list" | Tac_simp_only "hol_ntheorem list" | Tac_simp_add0 "hol_ntheorem list"
                    | Tac_simp_all | Tac_simp_all_add string
                    | Tac_auto_simp_add "string list"
                    | Tac_auto_simp_add_split "hol_ntheorem list" "string list"
                    | Tac_rename_tac "string list"
                    | Tac_case_tac hol_expr
                    | Tac_blast "nat option"

datatype hol_tactic_last = Tacl_done
                         | Tacl_by "hol_tactic list"
                         | Tacl_sorry

datatype hol_tac_apply = App "hol_tactic list" (* apply (... ',' ...) *)
                       | App_using "hol_ntheorem list" (* using ... *)
                       | App_unfolding "hol_ntheorem list" (* unfolding ... *)
                       | App_let hol_expr (* name *) hol_expr
                       | App_have string (* name *) hol_expr hol_tactic_last
                       | App_fix "string list"

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

end
