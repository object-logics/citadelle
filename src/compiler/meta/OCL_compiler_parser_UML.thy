(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_parser_UML.thy ---
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

theory  OCL_compiler_parser_UML
imports OCL_compiler_meta_UML
        OCL_compiler_parser_Pure
begin

section{* Generation to both Form (setup part) *}

definition "ocl_multiplicity_rec0 f ocl = f
  (TyMult ocl)
  (TyRole ocl)
  (TyCollect ocl)"

definition "ocl_multiplicity_rec f ocl = ocl_multiplicity_rec0 f ocl
  (ocl_multiplicity.more ocl)"

definition "ocl_ty_class_node_rec0 f ocl = f
  (TyObjN_ass_switch ocl)
  (TyObjN_role_multip ocl)
  (TyObjN_role_ty ocl)"

definition "ocl_ty_class_node_rec f ocl = ocl_ty_class_node_rec0 f ocl
  (ocl_ty_class_node.more ocl)"

definition "ocl_ty_class_rec0 f ocl = f
  (TyObj_name ocl)
  (TyObj_ass_id ocl)
  (TyObj_ass_arity ocl)
  (TyObj_from ocl)
  (TyObj_to ocl)"

definition "ocl_ty_class_rec f ocl = ocl_ty_class_rec0 f ocl
  (ocl_ty_class.more ocl)"

definition "ocl_class_raw_rec0 f ocl = f
  (ClassRaw_name ocl)
  (ClassRaw_own ocl)
  (ClassRaw_clause ocl)
  (ClassRaw_abstract ocl)"

definition "ocl_class_raw_rec f ocl = ocl_class_raw_rec0 f ocl
  (ocl_class_raw.more ocl)"

definition "ocl_association_rec0 f ocl = f
  (OclAss_type ocl)
  (OclAss_relation ocl)"

definition "ocl_association_rec f ocl = ocl_association_rec0 f ocl
  (ocl_association.more ocl)"

definition "ocl_ctxt_pre_post_rec0 f ocl = f
  (Ctxt_fun_name ocl)
  (Ctxt_fun_ty ocl)
  (Ctxt_expr ocl)"

definition "ocl_ctxt_pre_post_rec f ocl = ocl_ctxt_pre_post_rec0 f ocl
  (ocl_ctxt_pre_post.more ocl)"

definition "ocl_ctxt_rec0 f ocl = f
  (Ctxt_param ocl)
  (Ctxt_ty ocl)
  (Ctxt_clause ocl)"

definition "ocl_ctxt_rec f ocl = ocl_ctxt_rec0 f ocl
  (ocl_ctxt.more ocl)"

(* *)

lemma [code]: "ocl_class_raw.extend = (\<lambda>ocl v. ocl_class_raw_rec0 (co4 (\<lambda>f. f v) ocl_class_raw_ext) ocl)"
by(intro ext, simp add: ocl_class_raw_rec0_def
                        ocl_class_raw.extend_def
                        co4_def K_def)
lemma [code]: "ocl_class_raw.make = co4 (\<lambda>f. f ()) ocl_class_raw_ext"
by(intro ext, simp add: ocl_class_raw.make_def
                        co4_def)
lemma [code]: "ocl_class_raw.truncate = ocl_class_raw_rec (co4 K ocl_class_raw.make)"
by(intro ext, simp add: ocl_class_raw_rec0_def
                        ocl_class_raw_rec_def
                        ocl_class_raw.truncate_def
                        ocl_class_raw.make_def
                        co4_def K_def)

lemma [code]: "ocl_association.extend = (\<lambda>ocl v. ocl_association_rec0 (co2 (\<lambda>f. f v) ocl_association_ext) ocl)"
by(intro ext, simp add: ocl_association_rec0_def
                        ocl_association.extend_def
                        co2_def K_def)
lemma [code]: "ocl_association.make = co2 (\<lambda>f. f ()) ocl_association_ext"
by(intro ext, simp add: ocl_association.make_def
                        co2_def)
lemma [code]: "ocl_association.truncate = ocl_association_rec (co2 K ocl_association.make)"
by(intro ext, simp add: ocl_association_rec0_def
                        ocl_association_rec_def
                        ocl_association.truncate_def
                        ocl_association.make_def
                        co2_def K_def)

subsection{* i of ... *} (* i_of *)

subsubsection{* general *}

context i_of
begin

definition "i_of_ocl_collection b = rec_ocl_collection
  (b \<open>Set\<close>)
  (b \<open>Sequence\<close>)"

definition "i_of_ocl_multiplicity_single a b = rec_ocl_multiplicity_single
  (ap1 a (b \<open>Mult_nat\<close>) (i_of_nat a b))
  (b \<open>Mult_star\<close>)
  (b \<open>Mult_infinity\<close>)"

definition "i_of_ocl_multiplicity a b f = ocl_multiplicity_rec
  (ap4 a (b (ext \<open>ocl_multiplicity_ext\<close>))
    (i_of_list a b (i_of_pair a b (i_of_ocl_multiplicity_single a b) (i_of_option a b (i_of_ocl_multiplicity_single a b))))
    (i_of_option a b (i_of_string a b))
    (i_of_ocl_collection b)
    (f a b))"

definition "i_of_ocl_ty_class_node a b f = ocl_ty_class_node_rec
  (ap4 a (b (ext \<open>ocl_ty_class_node_ext\<close>))
    (i_of_nat a b)
    (i_of_ocl_multiplicity a b (K i_of_unit))
    (i_of_string a b)
    (f a b))"

definition "i_of_ocl_ty_class a b f = ocl_ty_class_rec
  (ap6 a (b (ext \<open>ocl_ty_class_ext\<close>))
    (i_of_string a b)
    (i_of_nat a b)
    (i_of_nat a b)
    (i_of_ocl_ty_class_node a b (K i_of_unit))
    (i_of_ocl_ty_class_node a b (K i_of_unit))
    (f a b))"

definition "i_of_ocl_ty_obj_core a b = rec_ocl_ty_obj_core
  (ap1 a (b \<open>OclTyCore_pre\<close>) (i_of_string a b))
  (ap1 a (b \<open>OclTyCore\<close>) (i_of_ocl_ty_class a b (K i_of_unit)))"

definition "i_of_ocl_ty_obj a b = rec_ocl_ty_obj
  (ap2 a (b \<open>OclTyObj\<close>) (i_of_ocl_ty_obj_core a b) (i_of_list a b (i_of_list a b (i_of_ocl_ty_obj_core a b))))"

definition "i_of_ocl_ty a b = (\<lambda>f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13.
                                    rec_ocl_ty_1 f1 f2 f3 f4 f5 f6
                                                 f7 (K o f8) (\<lambda>_ _. f9) (\<lambda>_. f10) (\<lambda>_ _. f11) f12
                                                 (K o f13))
  (b \<open>OclTy_base_void\<close>)
  (b \<open>OclTy_base_boolean\<close>)
  (b \<open>OclTy_base_integer\<close>)
  (b \<open>OclTy_base_unlimitednatural\<close>)
  (b \<open>OclTy_base_real\<close>)
  (b \<open>OclTy_base_string\<close>)
  (ap1 a (b \<open>OclTy_object\<close>) (i_of_ocl_ty_obj a b))
  (ar2 a (b \<open>OclTy_collection\<close>) (i_of_ocl_multiplicity a b (K i_of_unit)))
  (ar2 a (b \<open>OclTy_pair\<close>) id)
  (ar1 a (b \<open>OclTy_binding\<close>))
  (ar2 a (b \<open>OclTy_arrow\<close>) id)
  (ap1 a (b \<open>OclTy_raw\<close>) (i_of_string a b))
  (* *)
  (curry (i_of_pair a b (i_of_option a b (i_of_string a b)) id))"

definition "i_of_ocl_association_type a b = rec_ocl_association_type
  (b \<open>OclAssTy_native_attribute\<close>)
  (b \<open>OclAssTy_association\<close>)
  (b \<open>OclAssTy_composition\<close>)
  (b \<open>OclAssTy_aggregation\<close>)"

definition "i_of_ocl_association_relation a b = rec_ocl_association_relation
  (ap1 a (b \<open>OclAssRel\<close>)
    (i_of_list a b (i_of_pair a b (i_of_ocl_ty_obj a b) (i_of_ocl_multiplicity a b (K i_of_unit)))))"

definition "i_of_ocl_association a b f = ocl_association_rec
  (ap3 a (b (ext \<open>ocl_association_ext\<close>))
    (i_of_ocl_association_type a b)
    (i_of_ocl_association_relation a b)
    (f a b))"

definition "i_of_ocl_ctxt_prefix a b = rec_ocl_ctxt_prefix
  (b \<open>OclCtxtPre\<close>)
  (b \<open>OclCtxtPost\<close>)"

definition "i_of_ocl_ctxt_term a b = (\<lambda>f0 f1 f2. rec_ocl_ctxt_term f0 f1 (co1 K f2))
  (ap1 a (b \<open>T_pure\<close>) (i_of_pure_term a b))
  (ap2 a (b \<open>T_to_be_parsed\<close>) (i_of_string a b) (i_of_string a b))
  (ar2 a (b \<open>T_lambda\<close>) (i_of_string a b))"

definition "i_of_ocl_prop a b = rec_ocl_prop
  (ap2 a (b \<open>OclProp_ctxt\<close>) (i_of_option a b (i_of_string a b)) (i_of_ocl_ctxt_term a b))"

definition "i_of_ocl_ctxt_term_inv a b = rec_ocl_ctxt_term_inv
  (ap2 a (b \<open>T_inv\<close>) (i_of_bool b) (i_of_ocl_prop a b))"

definition "i_of_ocl_ctxt_term_pp a b = rec_ocl_ctxt_term_pp
  (ap2 a (b \<open>T_pp\<close>) (i_of_ocl_ctxt_prefix a b) (i_of_ocl_prop a b))
  (ap1 a (b \<open>T_invariant\<close>) (i_of_ocl_ctxt_term_inv a b))"

definition "i_of_ocl_ctxt_pre_post a b f = ocl_ctxt_pre_post_rec
  (ap4 a (b (ext \<open>ocl_ctxt_pre_post_ext\<close>))
    (i_of_string a b)
    (i_of_ocl_ty a b)
    (i_of_list a b (i_of_ocl_ctxt_term_pp a b))
    (f a b))"

definition "i_of_ocl_ctxt_clause a b = rec_ocl_ctxt_clause
  (ap1 a (b \<open>Ctxt_pp\<close>) (i_of_ocl_ctxt_pre_post a b (K i_of_unit)))
  (ap1 a (b \<open>Ctxt_inv\<close>) (i_of_ocl_ctxt_term_inv a b))"

definition "i_of_ocl_ctxt a b f = ocl_ctxt_rec
  (ap4 a (b (ext \<open>ocl_ctxt_ext\<close>))
    (i_of_list a b (i_of_string a b))
    (i_of_ocl_ty_obj a b)
    (i_of_list a b (i_of_ocl_ctxt_clause a b))
    (f a b))"

definition "i_of_ocl_class a b = (\<lambda>f0 f1 f2 f3 f4. rec_ocl_class_1 (co2 K (ar3 a f0 f1 f2)) f3 (\<lambda>_ _. f4))
  (b \<open>OclClass\<close>)
    (i_of_string a b)
    (i_of_list a b (i_of_pair a b (i_of_string a b) (i_of_ocl_ty a b)))
    (* *)
    (b i_Nil)
    (ar2 a (b i_Cons) id)"

definition "i_of_ocl_class_raw a b f = ocl_class_raw_rec
  (ap5 a (b (ext \<open>ocl_class_raw_ext\<close>))
    (i_of_ocl_ty_obj a b)
    (i_of_list a b (i_of_pair a b (i_of_string a b) (i_of_ocl_ty a b)))
    (i_of_list a b (i_of_ocl_ctxt_clause a b))
    (i_of_bool b)
    (f a b))"

definition "i_of_ocl_ass_class a b = rec_ocl_ass_class
  (ap2 a (b \<open>OclAssClass\<close>)
    (i_of_ocl_association a b (K i_of_unit))
    (i_of_ocl_class_raw a b (K i_of_unit)))"

end

lemmas [code] =
  i_of.i_of_ocl_collection_def
  i_of.i_of_ocl_multiplicity_single_def
  i_of.i_of_ocl_multiplicity_def
  i_of.i_of_ocl_ty_class_node_def
  i_of.i_of_ocl_ty_class_def
  i_of.i_of_ocl_ty_obj_core_def
  i_of.i_of_ocl_ty_obj_def
  i_of.i_of_ocl_ty_def
  i_of.i_of_ocl_association_type_def
  i_of.i_of_ocl_association_relation_def
  i_of.i_of_ocl_association_def
  i_of.i_of_ocl_ctxt_prefix_def
  i_of.i_of_ocl_ctxt_term_def
  i_of.i_of_ocl_prop_def
  i_of.i_of_ocl_ctxt_term_inv_def
  i_of.i_of_ocl_ctxt_term_pp_def
  i_of.i_of_ocl_ctxt_pre_post_def
  i_of.i_of_ocl_ctxt_clause_def
  i_of.i_of_ocl_ctxt_def
  i_of.i_of_ocl_class_def
  i_of.i_of_ocl_class_raw_def
  i_of.i_of_ocl_ass_class_def

end
