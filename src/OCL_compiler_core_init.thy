(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_core_init.thy ---
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

theory  OCL_compiler_core_init
imports OCL_compiler_meta_UML
        OCL_compiler_meta_Isabelle
        "~~/src/HOL/Library/Code_Char"
begin

section{* Configuration of the Set of Meta in Input *}

datatype ocl_flush_all = OclFlushAll

(* *)

type_synonym ocl_ctxt2_pre_post = ocl_ctxt_pre_post
type_synonym ocl_ctxt2_inv = ocl_ctxt_inv

(* *)

(* le meta-model de "tout le monde" - frederic. *)
datatype ocl_deep_embed_ast = (* USE *)
                              OclAstClassRaw ocl_class_raw
                            | OclAstAssociation ocl_association
                            | OclAstAssClass ocl_ass_class
                            | OclAstCtxtPrePost ocl_ctxt_pre_post
                            | OclAstCtxtInv ocl_ctxt_inv

                              (* USE reflected 1 time *)
                            | OclAstCtxt2PrePost ocl_ctxt2_pre_post
                            | OclAstCtxt2Inv ocl_ctxt2_inv

                              (* invented *)
                            | OclAstInstance ocl_instance
                            | OclAstDefBaseL ocl_def_base_l
                            | OclAstDefState ocl_def_state
                            | OclAstDefPrePost ocl_def_pre_post
                            | OclAstFlushAll ocl_flush_all

datatype ocl_deep_mode = Gen_design | Gen_analysis


record ocl_compiler_config =  D_disable_thy_output :: bool
                              D_file_out_path_dep :: "(string (* theory *)
                                                      \<times> string list (* imports *)
                                                      \<times> string (* import optional (compiler bootstrap) *)) option"
                              D_oid_start :: internal_oids
                              D_output_position :: "nat \<times> nat"
                              D_design_analysis :: ocl_deep_mode
                              D_class_spec :: "ocl_class option"
                                              (* last class considered for the generation *)
                              D_ocl_env :: "ocl_deep_embed_ast list"
                              D_instance_rbt :: "(string (* name (as key for rbt) *)
                                                 \<times> ocl_instance_single
                                                 \<times> internal_oid) list"
                                                (* instance namespace environment *)
                              D_state_rbt :: "(string (* name (as key for rbt) *)
                                              \<times> (internal_oids
                                              \<times> (string (* name *)
                                                  \<times> ocl_instance_single (* alias *))
                                                      ocl_def_state_core) list) list"
                                             (* state namespace environment *)
                              D_import_compiler :: bool (* true : the header should import the compiler for bootstrapping *)
                              D_generation_syntax_shallow :: bool (* true : add the generation_syntax command *)
                              D_accessor_rbt :: " string (* name of the constant added *) list (* pre *)
                                                \<times> string (* name of the constant added *) list (* post *)"

subsection{* Auxilliary *}

definition "map_ctxt2_term f = (\<lambda>
    OclAstCtxt2PrePost ocl \<Rightarrow> OclAstCtxt2PrePost (Ctxt_expr_update (List_map (\<lambda>(s, x). (s, f x))) ocl)
  | OclAstCtxt2Inv ocl \<Rightarrow> OclAstCtxt2Inv (Ctxt_inv_expr_update (List_map (\<lambda>(s, x). (s, f x))) ocl)
  | x \<Rightarrow> x)"

definition "ocl_compiler_config_more_map f ocl =
            ocl_compiler_config.extend  (ocl_compiler_config.truncate ocl) (f (ocl_compiler_config.more ocl))"

definition "find_class_ass ocl =
                              List.partition (\<lambda> OclAstClassRaw _ \<Rightarrow> True
                                              | OclAstAssociation _ \<Rightarrow> True
                                              | OclAstAssClass _ \<Rightarrow> True
                                              | _ \<Rightarrow> False) (rev (D_ocl_env ocl))"

definition "filter_ass = List.map_filter (\<lambda> OclAstAssociation ass \<Rightarrow> Some ass
                                          | OclAstAssClass (OclAssClass ass _) \<Rightarrow> Some ass
                                          | _ \<Rightarrow> None)"

section{* SML Meta-Model (extended) *}
subsection{* type definition *}

datatype sml_expr_extended = Sexpr_extended sml_expr
                           | Sexpr_ocl ocl_compiler_config

section{* Isabelle/HOL Meta-Model (extended) *}
subsection{* type definition *}

datatype hol_generation_syntax = Generation_syntax_shallow ocl_deep_mode

datatype hol_ml_extended = Ml_extended sml_expr_extended

datatype hol_thy_extended = (* pure Isabelle *)
                            Isab_thy hol_thy

                            (* bootstrapping embedded languages *)
                          | Isab_thy_generation_syntax hol_generation_syntax
                          | Isab_thy_ml_extended hol_ml_extended
                          | Isab_thy_ocl_deep_embed_ast ocl_deep_embed_ast

subsection{* ... *}

definition "Thy_dataty = Isab_thy o Theory_dataty"
definition "Thy_ty_synonym = Isab_thy o Theory_ty_synonym"
definition "Thy_instantiation_class = Isab_thy o Theory_instantiation_class"
definition "Thy_defs_overloaded = Isab_thy o Theory_defs_overloaded"
definition "Thy_consts_class = Isab_thy o Theory_consts_class"
definition "Thy_definition_hol = Isab_thy o Theory_definition_hol"
definition "Thy_lemmas_simp = Isab_thy o Theory_lemmas_simp"
definition "Thy_lemma_by = Isab_thy o Theory_lemma_by"
definition "Thy_axiom = Isab_thy o Theory_axiom"
definition "Thy_section_title = Isab_thy o Theory_section_title"
definition "Thy_text = Isab_thy o Theory_text"
definition "Thy_ml = Isab_thy o Theory_ml"
definition "Thy_thm = Isab_thy o Theory_thm"

subsection{* ... *}

definition "datatype_ext_name = ''type''"
definition "datatype_name = datatype_ext_name @@ const_oid"
definition "datatype_ext_constr_name = ''mk''"
definition "datatype_constr_name = datatype_ext_constr_name @@ const_oid"
definition "datatype_in = ''in''"

section{* Translation of AST *}

definition "map_class_arg_only_var = map_class_arg_only_var_gen (\<lambda>s e. Expr_postunary s (Expr_basic e))"
definition "map_class_arg_only_var' = map_class_arg_only_var'_gen (\<lambda>s e. Expr_postunary s (Expr_basic e))"

definition "split_ty name = List_map (\<lambda>s. hol_split (s @@ isub_of_str name)) [datatype_ext_name, datatype_name]"

definition "start_map f = fold_list (\<lambda>x acc. (f x, acc))"
definition "start_map' f x accu = (f x, accu)"
definition "start_map''' f fl = (\<lambda> ocl.
  let design_analysis = D_design_analysis ocl
    ; base_attr = (if design_analysis = Gen_design then id else List_filter (\<lambda> (_, OclTy_class _) \<Rightarrow> False | _ \<Rightarrow> True))
    ; base_attr' = (\<lambda> (l_attr, l_inh). (base_attr l_attr, List_map base_attr l_inh))
    ; base_attr'' = (\<lambda> (l_attr, l_inh). (base_attr l_attr, base_attr l_inh)) in
  start_map f (fl design_analysis base_attr base_attr' base_attr'') ocl)"
definition "start_map'' f fl e = start_map''' f (\<lambda>_. fl) e"
definition "start_map'''' f fl = (\<lambda> ocl. start_map f (fl (D_design_analysis ocl)) ocl)"

definition "start_m_gen final f print = start_map'' final o (\<lambda>expr base_attr _ _.
  m_class_gen2 base_attr f print expr)"
definition "start_m final f print = start_map'' final o (\<lambda>expr base_attr _ _.
  m_class base_attr f print expr)"
definition "start_m' final print = start_map'' final o (\<lambda>expr base_attr _ _.
  m_class' base_attr print expr)"
definition "start_m'3_gen final print = start_map'' final o (\<lambda>expr base_attr _ _.
  m_class_gen3 base_attr id print expr)"

subsection{* ... *}

definition "activate_simp_optimization = True"

subsection{* AsType *}

subsection{* IsTypeOf *}

definition "print_istypeof_defined_name isub_name h_name = flatten [isub_name const_oclistypeof, ''_'', h_name, ''_defined'']"
definition "print_istypeof_defined'_name isub_name h_name = flatten [isub_name const_oclistypeof, ''_'', h_name, ''_defined'',  [Char Nibble2 Nibble7]]"
definition "print_istypeof_up_d_cast_name name_mid name_any name_pers = flatten [''down_cast_type'', isub_of_str name_mid, ''_from_'', name_any, ''_to_'', name_pers]"

subsection{* IsKindOf *}

definition "print_iskindof_up_eq_asty_name name = (flatten [''actual_eq_static'', isub_of_str name])"
definition "print_iskindof_up_larger_name name_pers name_any = flatten [''actualKind'', isub_of_str name_pers, ''_larger_staticKind'', isub_of_str name_any]"

subsection{* allInstances *}

definition "gen_pre_post f_tit spec f_lemma tac_last =
  (let b = \<lambda>s. Expr_basic [s]
     ; d = hol_definition
     ; f_allinst = \<lambda>s. ''OclAllInstances_'' @@ s
     ; f_tit = f_tit o f_allinst
     ; var_pre_post = ''pre_post''
     ; var_mk = ''mk''
     ; var_st = ''st''
     ; s_generic = ''generic''
     ; lem_gen = f_tit s_generic
     ; mk_pre_post = \<lambda>pre_post at_when f_cpl.
         let s_allinst = f_allinst at_when in
         Lemma_by_assum
           (f_tit at_when)
           []
           (spec (Expr_apply s_allinst) f_cpl pre_post)
           [App_unfolding [Thm_str (d s_allinst)]]
           (Tacl_by (Tac_rule (Thm_str lem_gen) # tac_last)) in
  [ f_lemma lem_gen (spec (\<lambda>l. Expr_apply (f_allinst s_generic) (b var_pre_post # l)) (\<lambda>e. Expr_apply var_mk [e]) var_pre_post) var_pre_post var_mk var_st
  , mk_pre_post ''snd'' ''at_post'' (Expr_pair (b var_st))
  , mk_pre_post ''fst'' ''at_pre'' (\<lambda>e. Expr_pair e (b var_st)) ])"

subsection{* accessors *}

definition "print_access_oid_uniq_name name_from_nat isub_name attr = flatten [ isub_name var_oid_uniq, ''_'', natural_of_str name_from_nat, ''_'', isup_of_str attr ]"
definition "print_access_oid_uniq_mlname name_from_nat name attr = flatten [ var_oid_uniq, name, ''_'', natural_of_str name_from_nat, ''_'', attr ]"

definition "print_access_choose_name n i j =
  flatten [var_switch, isub_of_str (natural_of_str n), ''_'', natural_of_str i, natural_of_str j]"
definition "print_access_choose_mlname n i j =
  flatten [var_switch, natural_of_str n, ''_'', natural_of_str i, natural_of_str j]"

subsection{* example *}

subsection{* context *}

subsection{* context2 *}

end
