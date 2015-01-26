(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_meta_META.thy ---
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

theory  OCL_compiler_meta_META
imports OCL_compiler_meta_UML
        OCL_compiler_meta_UML_extended
        OCL_compiler_meta_Isabelle
begin

section{* The Meta-Model of all existing Meta-Models *}
text{* Actually, the simulation occurs through one deep or shallow step (without internal recursion). *}

datatype ocl_flush_all = OclFlushAll

(* *)

datatype floor = Floor1 | Floor2 | Floor3

(* *)

(* le meta-model de "tout le monde" - frederic. *)
datatype ocl_deep_embed_ast =
  (* For the following constructors, if they are preceded by an additional
     'floor' field, then it indicates the degre of reflection
     (otherwise degre = 1 by default). *)

                              (* USE *)
                              OclAstClassRaw floor ocl_class_raw
                            | OclAstAssociation ocl_association
                            | OclAstAssClass floor ocl_ass_class
                            | OclAstCtxtPrePost floor ocl_ctxt_pre_post
                            | OclAstCtxtInv floor ocl_ctxt_inv

                              (* invented *)
                            | OclAstInstance ocl_instance
                            | OclAstDefBaseL ocl_def_base_l
                            | OclAstDefState ocl_def_state
                            | OclAstDefPrePost ocl_def_pre_post
                            | OclAstFlushAll ocl_flush_all

(* *)

datatype ocl_deep_mode = Gen_only_design | Gen_only_analysis | Gen_default


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
                              D_instance_rbt :: "(string\<^sub>b\<^sub>a\<^sub>s\<^sub>e (* name (as key for rbt) *)
                                                 \<times> ocl_instance_single
                                                 \<times> internal_oid) list"
                                                (* instance namespace environment *)
                              D_state_rbt :: "(string\<^sub>b\<^sub>a\<^sub>s\<^sub>e (* name (as key for rbt) *)
                                              \<times> (internal_oids
                                              \<times> (string (* name *)
                                                  \<times> ocl_instance_single (* alias *))
                                                      ocl_def_state_core) list) list"
                                             (* state namespace environment *)
                              D_import_compiler :: bool (* true : the header should import the compiler for bootstrapping *)
                              D_generation_syntax_shallow :: bool (* true : add the generation_syntax command *)
                              D_accessor_rbt :: " string\<^sub>b\<^sub>a\<^sub>s\<^sub>e (* name of the constant added *) list (* pre *)
                                                \<times> string\<^sub>b\<^sub>a\<^sub>s\<^sub>e (* name of the constant added *) list (* post *)"
                              D_higher_order_ty :: "(string\<^sub>b\<^sub>a\<^sub>s\<^sub>e (* raw HOL name (as key for rbt) *)) list"
                              D_sorry_mode :: bool (* true : activate sorry mode for skipping proofs *)

subsection{* Auxilliary *}

definition "map2_ctxt_term f = (\<lambda>
    OclAstCtxtPrePost Floor2 ocl \<Rightarrow> OclAstCtxtPrePost Floor2 (Ctxt_expr_update (List_map (\<lambda>(s, x). (s, f x))) ocl)
  | OclAstCtxtInv Floor2 ocl \<Rightarrow> OclAstCtxtInv Floor2 (Ctxt_inv_expr_update (List_map (\<lambda>(s, x). (s, f x))) ocl)
  | x \<Rightarrow> x)"

definition "ocl_compiler_config_more_map f ocl =
            ocl_compiler_config.extend  (ocl_compiler_config.truncate ocl) (f (ocl_compiler_config.more ocl))"

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

definition "hol_map_thy f = (\<lambda> Isab_thy x \<Rightarrow> Isab_thy (f x)
                             | x \<Rightarrow> x)"

end
