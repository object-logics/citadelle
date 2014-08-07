(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_printer_UML.thy ---
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

theory  OCL_compiler_printer_UML
imports OCL_compiler_meta_UML
begin

section{* Generation to both Form (setup part) *}

definition "ocl_ty_class_node_rec0 f ocl = f
  (TyObjN_ass_switch ocl)
  (TyObjN_role_multip ocl)
  (TyObjN_role_name ocl)
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
  (ClassRaw_inh ocl)"

definition "ocl_class_raw_rec f ocl = ocl_class_raw_rec0 f ocl
  (ocl_class_raw.more ocl)"

definition "ocl_association_rec0 f ocl = f
  (OclAss_type ocl)
  (OclAss_relation ocl)"

definition "ocl_association_rec f ocl = ocl_association_rec0 f ocl
  (ocl_association.more ocl)"

definition "ocl_instance_single_rec0 f ocl = f
  (Inst_name ocl)
  (Inst_ty ocl)
  (Inst_attr ocl)"

definition "ocl_instance_single_rec f ocl = ocl_instance_single_rec0 f ocl
  (ocl_instance_single.more ocl)"

definition "ocl_ctxt_pre_post_rec0 f ocl = f
  (Ctxt_ty ocl)
  (Ctxt_fun_name ocl)
  (Ctxt_fun_ty_arg ocl)
  (Ctxt_fun_ty_out ocl)
  (Ctxt_expr ocl)"

definition "ocl_ctxt_pre_post_rec f ocl = ocl_ctxt_pre_post_rec0 f ocl
  (ocl_ctxt_pre_post.more ocl)"

definition "ocl_ctxt_inv_rec0 f ocl = f
  (Ctxt_inv_ty ocl)
  (Ctxt_inv_expr ocl)"

definition "ocl_ctxt_inv_rec f ocl = ocl_ctxt_inv_rec0 f ocl
  (ocl_ctxt_inv.more ocl)"

(* *)

definition "K x _ = x"

definition "co1 = op o"
definition "co2 f g x1 x2 = f (g x1 x2)"
definition "co3 f g x1 x2 x3 = f (g x1 x2 x3)"
definition "co4 f g x1 x2 x3 x4 = f (g x1 x2 x3 x4)"
definition "co5 f g x1 x2 x3 x4 x5 = f (g x1 x2 x3 x4 x5)"
definition "co6 f g x1 x2 x3 x4 x5 x6 = f (g x1 x2 x3 x4 x5 x6)"
definition "co7 f g x1 x2 x3 x4 x5 x6 x7 = f (g x1 x2 x3 x4 x5 x6 x7)"
definition "co8 f g x1 x2 x3 x4 x5 x6 x7 x8 = f (g x1 x2 x3 x4 x5 x6 x7 x8)"
definition "co9 f g x1 x2 x3 x4 x5 x6 x7 x8 x9 = f (g x1 x2 x3 x4 x5 x6 x7 x8 x9)"
definition "co10 f g x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 = f (g x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)"
definition "co11 f g x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 = f (g x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)"
definition "co12 f g x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 = f (g x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)"
definition "co13 f g x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 = f (g x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)"

definition "ap1 a v0 f1 v1 = a v0 [f1 v1]"
definition "ap2 a v0 f1 f2 v1 v2 = a v0 [f1 v1, f2 v2]"
definition "ap3 a v0 f1 f2 f3 v1 v2 v3 = a v0 [f1 v1, f2 v2, f3 v3]"
definition "ap4 a v0 f1 f2 f3 f4 v1 v2 v3 v4 = a v0 [f1 v1, f2 v2, f3 v3, f4 v4]"
definition "ap5 a v0 f1 f2 f3 f4 f5 v1 v2 v3 v4 v5 = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5]"
definition "ap6 a v0 f1 f2 f3 f4 f5 f6 v1 v2 v3 v4 v5 v6 = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6]"
definition "ap7 a v0 f1 f2 f3 f4 f5 f6 f7 v1 v2 v3 v4 v5 v6 v7 = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7]"
definition "ap8 a v0 f1 f2 f3 f4 f5 f6 f7 f8 v1 v2 v3 v4 v5 v6 v7 v8 = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7, f8 v8]"
definition "ap9 a v0 f1 f2 f3 f4 f5 f6 f7 f8 f9 v1 v2 v3 v4 v5 v6 v7 v8 v9 = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7, f8 v8, f9 v9]"
definition "ap10 a v0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7, f8 v8, f9 v9, f10 v10]"
definition "ap11 a v0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7, f8 v8, f9 v9, f10 v10, f11 v11]"
definition "ap12 a v0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7, f8 v8, f9 v9, f10 v10, f11 v11, f12 v12]"
definition "ap13 a v0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7, f8 v8, f9 v9, f10 v10, f11 v11, f12 v12, f13 v13]"

definition "ar1 a v0 z = a v0 [z]"
definition "ar2 a v0 f1 v1 z = a v0 [f1 v1, z]"
definition "ar3 a v0 f1 f2 v1 v2 z = a v0 [f1 v1, f2 v2, z]"
definition "ar4 a v0 f1 f2 f3 v1 v2 v3 z = a v0 [f1 v1, f2 v2, f3 v3, z]"
definition "ar5 a v0 f1 f2 f3 f4 v1 v2 v3 v4 z = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, z]"
definition "ar6 a v0 f1 f2 f3 f4 f5 v1 v2 v3 v4 v5 z = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, z]"
definition "ar7 a v0 f1 f2 f3 f4 f5 f6 v1 v2 v3 v4 v5 v6 z = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, z]"
definition "ar8 a v0 f1 f2 f3 f4 f5 f6 f7 v1 v2 v3 v4 v5 v6 v7 z = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7, z]"
definition "ar9 a v0 f1 f2 f3 f4 f5 f6 f7 f8 v1 v2 v3 v4 v5 v6 v7 v8 z = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7, f8 v8, z]"
definition "ar10 a v0 f1 f2 f3 f4 f5 f6 f7 f8 f9 v1 v2 v3 v4 v5 v6 v7 v8 v9 z = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7, f8 v8, f9 v9, z]"
definition "ar11 a v0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 z = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7, f8 v8, f9 v9, f10 v10, z]"
definition "ar12 a v0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 z = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7, f8 v8, f9 v9, f10 v10, f11 v11, z]"
definition "ar13 a v0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 z = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7, f8 v8, f9 v9, f10 v10, f11 v11, f12 v12, z]"

(* *)

lemma [code]: "ocl_class_raw.extend = (\<lambda>ocl v. ocl_class_raw_rec0 (co3 (\<lambda>f. f v) ocl_class_raw_ext) ocl)"
by(intro ext, simp add: ocl_class_raw_rec0_def
                        ocl_class_raw.extend_def
                        co3_def K_def)
lemma [code]: "ocl_class_raw.make = co3 (\<lambda>f. f ()) ocl_class_raw_ext"
by(intro ext, simp add: ocl_class_raw.make_def
                        co3_def)
lemma [code]: "ocl_class_raw.truncate = ocl_class_raw_rec (co3 K ocl_class_raw.make)"
by(intro ext, simp add: ocl_class_raw_rec0_def
                        ocl_class_raw_rec_def
                        ocl_class_raw.truncate_def
                        ocl_class_raw.make_def
                        co3_def K_def)

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

lemma [code]: "ocl_instance_single.extend = (\<lambda>ocl v. ocl_instance_single_rec0 (co3 (\<lambda>f. f v) ocl_instance_single_ext) ocl)"
by(intro ext, simp add: ocl_instance_single_rec0_def
                        ocl_instance_single.extend_def
                        co3_def K_def)
lemma [code]: "ocl_instance_single.make = co3 (\<lambda>f. f ()) ocl_instance_single_ext"
by(intro ext, simp add: ocl_instance_single.make_def
                        co3_def)
lemma [code]: "ocl_instance_single.truncate = ocl_instance_single_rec (co3 K ocl_instance_single.make)"
by(intro ext, simp add: ocl_instance_single_rec0_def
                        ocl_instance_single_rec_def
                        ocl_instance_single.truncate_def
                        ocl_instance_single.make_def
                        co3_def K_def)

subsection{* i of ... *} (* i_of *)

subsubsection{* general *}

locale i_of =
  fixes ext :: "char list \<Rightarrow> char list"

  (* (effective) first order *)
  fixes i_of_string :: "('a \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> (char list \<Rightarrow> 'a) \<Rightarrow> char list \<Rightarrow> 'a"
  fixes i_of_nat :: "('a \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> (char list \<Rightarrow> 'a) \<Rightarrow> natural \<Rightarrow> 'a"
  fixes i_of_unit :: "(char list \<Rightarrow> 'a) \<Rightarrow> unit \<Rightarrow> 'a"
  fixes i_of_bool :: "(char list \<Rightarrow> 'a) \<Rightarrow> bool \<Rightarrow> 'a"

  (* (simulation) higher order *)
  fixes i_Pair i_Nil i_Cons i_None i_Some :: "char list"
begin

definition "i_of_pair a b f1 f2 = (\<lambda>f. \<lambda>(c, d) \<Rightarrow> f c d)
  (ap2 a (b i_Pair) f1 f2)"

definition "i_of_list a b f = (\<lambda>f0. list_rec f0 o co1 K)
  (b i_Nil)
  (ar2 a (b i_Cons) f)"

definition "i_of_option a b f = option_rec
  (b i_None)
  (ap1 a (b i_Some) f)"

(* *)

definition "i_of_pure_indexname a b = pure_indexname_rec
  (ap2 a (b ''PureIndexname'') (i_of_string a b) (i_of_nat a b))"

definition "i_of_pure_class a b = pure_class_rec
  (ap1 a (b ''PureClass'') (i_of_string a b))"

definition "i_of_pure_sort a b = pure_sort_rec
  (ap1 a (b ''PureSort'') (i_of_list a b (i_of_pure_class a b)))"

definition "i_of_pure_typ a b = (\<lambda>f1 f2 f3 f4 f5. pure_typ_rec_1 (co1 K f1) f2 f3 f4 (\<lambda>_ _. f5))
  (ar2 a (b ''PureType'') (i_of_string a b))
  (ap2 a (b ''PureTFree'') (i_of_string a b) (i_of_pure_sort a b))
  (ap2 a (b ''PureTVar'') (i_of_pure_indexname a b) (i_of_pure_sort a b))
  (* *)
  (b i_Nil)
  (ar2 a (b i_Cons) id)"

definition "i_of_pure_term a b = (\<lambda>f0 f1 f2 f3 f4 f5. pure_term_rec f0 f1 f2 f3 (co2 K f4) (\<lambda>_ _. f5))
  (ap2 a (b ''PureConst'') (i_of_string a b) (i_of_pure_typ a b))
  (ap2 a (b ''PureFree'') (i_of_string a b) (i_of_pure_typ a b))
  (ap2 a (b ''PureVar'') (i_of_pure_indexname a b) (i_of_pure_typ a b))
  (ap1 a (b ''PureBound'') (i_of_nat a b))
  (ar3 a (b ''PureAbs'') (i_of_string a b) (i_of_pure_typ a b))
  (ar2 a (b ''PureApp'') id)"

definition "i_of_internal_oid a b = internal_oid_rec
  (ap1 a (b ''Oid'') (i_of_nat a b))"

definition "i_of_internal_oids a b = internal_oids_rec
  (ap3 a (b ''Oids'')
    (i_of_nat a b)
    (i_of_nat a b)
    (i_of_nat a b))"

definition "i_of_ocl_collection b = ocl_collection_rec
  (b ''Set'')
  (b ''Sequence'')"

definition "i_of_ocl_multiplicity_single a b = ocl_multiplicity_single_rec
  (ap1 a (b ''Mult_nat'') (i_of_nat a b))
  (b ''Mult_star'')"

definition "i_of_ocl_multiplicity a b = ocl_multiplicity_rec
  (ap1 a (b ''OclMult'') (i_of_list a b (i_of_pair a b (i_of_ocl_multiplicity_single a b) (i_of_option a b (i_of_ocl_multiplicity_single a b)))))"

definition "i_of_ocl_ty_class_node a b f = ocl_ty_class_node_rec
  (ap5 a (b (ext ''ocl_ty_class_node_ext''))
    (i_of_nat a b)
    (i_of_ocl_multiplicity a b)
    (i_of_option a b (i_of_string a b))
    (i_of_string a b)
    (f a b))"

definition "i_of_ocl_ty_class a b f = ocl_ty_class_rec
  (ap6 a (b (ext ''ocl_ty_class_ext''))
    (i_of_string a b)
    (i_of_nat a b)
    (i_of_nat a b)
    (i_of_ocl_ty_class_node a b (K i_of_unit))
    (i_of_ocl_ty_class_node a b (K i_of_unit))
    (f a b))"

definition "i_of_ocl_ty a b = (\<lambda>f1 f2 f3. ocl_ty_rec f1 f2 f3 o co1 K)
  (b ''OclTy_boolean'')
  (b ''OclTy_integer'')
  (ap1 a (b ''OclTy_class'') (i_of_ocl_ty_class a b (K i_of_unit)))
  (ar2 a (b ''OclTy_collection'') (i_of_ocl_collection b))
  (ap1 a (b ''OclTy_raw'') (i_of_string a b))"

definition "i_of_ocl_class a b = (\<lambda>f0 f1 f2 f3 f4. ocl_class_rec_1 (co2 K (ar3 a f0 f1 f2)) f3 (\<lambda>_ _. f4))
  (b ''OclClass'')
    (i_of_string a b)
    (i_of_list a b (i_of_pair a b (i_of_string a b) (i_of_ocl_ty a b)))
    (* *)
    (b i_Nil)
    (ar2 a (b i_Cons) id)"

definition "i_of_ocl_class_raw a b f = ocl_class_raw_rec
  (ap4 a (b (ext ''ocl_class_raw_ext''))
    (i_of_string a b)
    (i_of_list a b (i_of_pair a b (i_of_string a b) (i_of_ocl_ty a b)))
    (i_of_option a b (i_of_string a b))
    (f a b))"

definition "i_of_ocl_association_type a b = ocl_association_type_rec
  (b ''OclAssTy_association'')
  (b ''OclAssTy_composition'')
  (b ''OclAssTy_aggregation'')"

definition "i_of_ocl_association a b f = ocl_association_rec
  (ap3 a (b (ext ''ocl_association_ext''))
    (i_of_ocl_association_type a b)
    (i_of_list a b (i_of_pair a b (i_of_string a b) (i_of_pair a b (i_of_ocl_multiplicity a b) (i_of_option a b (i_of_string a b)))))
    (f a b))"

definition "i_of_ocl_ass_class a b = ocl_ass_class_rec
  (ap2 a (b ''OclAssClass'')
    (i_of_ocl_association a b (K i_of_unit))
    (i_of_ocl_class_raw a b (K i_of_unit)))"

definition "i_of_ocl_data_shallow_base a b = ocl_data_shallow_base_rec
  (ap1 a (b ''ShallB_str'') (i_of_string a b))
  (ap1 a (b ''ShallB_self'') (i_of_internal_oid a b))"

definition "i_of_ocl_data_shallow a b = ocl_data_shallow_rec
  (ap1 a (b ''Shall_base'') (i_of_ocl_data_shallow_base a b))
  (ap1 a (b ''Shall_list'') (i_of_list a b (i_of_ocl_data_shallow_base a b)))"

definition "i_of_ocl_list_attr a b f = (\<lambda>f0. co4 (\<lambda>f1. ocl_list_attr_rec f0 (\<lambda>s _ a rec. f1 s rec a)) (ap3 a))
  (ap1 a (b ''OclAttrNoCast'') f)
  (b ''OclAttrCast'')
    (i_of_string a b)
    id
    f"

definition "i_of_ocl_instance_single a b f = ocl_instance_single_rec
  (ap4 a (b (ext ''ocl_instance_single_ext''))
    (i_of_string a b)
    (i_of_string a b)
    (i_of_ocl_list_attr a b (i_of_list a b (i_of_pair a b (i_of_string a b) (i_of_ocl_data_shallow a b))))
    (f a b))"

definition "i_of_ocl_instance a b = ocl_instance_rec
  (ap1 a (b ''OclInstance'')
    (i_of_list a b (i_of_ocl_instance_single a b (K i_of_unit))))"

definition "i_of_ocl_def_int a b = ocl_def_int_rec
  (ap1 a (b ''OclDefI'') (i_of_list a b (i_of_string a b)))"

definition "i_of_ocl_def_state_core a b f = ocl_def_state_core_rec
  (ap1 a (b ''OclDefCoreAdd'') (i_of_ocl_instance_single a b (K i_of_unit)))
  (b ''OclDefCoreSkip'')
  (ap1 a (b ''OclDefCoreBinding'') f)"

definition "i_of_ocl_def_state a b = ocl_def_state_rec
  (ap2 a (b ''OclDefSt'') (i_of_string a b) (i_of_list a b (i_of_ocl_def_state_core a b (i_of_string a b))))"

definition "i_of_ocl_def_pre_post a b = ocl_def_pre_post_rec
  (ap2 a (b ''OclDefPP'') (i_of_string a b) (i_of_string a b))"

definition "i_of_ocl_ctxt_prefix a b = ocl_ctxt_prefix_rec
  (b ''OclCtxtPre'')
  (b ''OclCtxtPost'')"

definition "i_of_ocl_ctxt_term a b = ocl_ctxt_term_rec
  (ap1 a (b ''T_pure'') (i_of_pure_term a b))
  (ap1 a (b ''T_to_be_parsed'') (i_of_string a b))"

definition "i_of_ocl_ctxt_pre_post a b f = ocl_ctxt_pre_post_rec
  (ap6 a (b (ext ''ocl_ctxt_pre_post_ext''))
    (i_of_string a b)
    (i_of_string a b)
    (i_of_list a b (i_of_pair a b (i_of_string a b) (i_of_ocl_ty a b)))
    (i_of_option a b (i_of_ocl_ty a b))
    (i_of_list a b (i_of_pair a b (i_of_ocl_ctxt_prefix a b) (i_of_ocl_ctxt_term a b)))
    (f a b))"

definition "i_of_ocl_ctxt2_pre_post = i_of_ocl_ctxt_pre_post"

definition "i_of_ocl_ctxt_inv a b f = ocl_ctxt_inv_rec
  (ap3 a (b (ext ''ocl_ctxt_inv_ext''))
    (i_of_string a b)
    (i_of_list a b (i_of_pair a b (i_of_string a b) (i_of_ocl_ctxt_term a b)))
    (f a b))"

definition "i_of_ocl_ctxt2_inv = i_of_ocl_ctxt_inv"

end

lemmas [code] =
  i_of.i_of_pair_def
  i_of.i_of_list_def
  i_of.i_of_option_def
  (* *)
  i_of.i_of_pure_indexname_def
  i_of.i_of_pure_class_def
  i_of.i_of_pure_sort_def
  i_of.i_of_pure_typ_def
  i_of.i_of_pure_term_def
  i_of.i_of_internal_oid_def
  i_of.i_of_internal_oids_def
  i_of.i_of_ocl_collection_def
  i_of.i_of_ocl_multiplicity_single_def
  i_of.i_of_ocl_multiplicity_def
  i_of.i_of_ocl_ty_class_node_def
  i_of.i_of_ocl_ty_class_def
  i_of.i_of_ocl_ty_def
  i_of.i_of_ocl_class_def
  i_of.i_of_ocl_class_raw_def
  i_of.i_of_ocl_association_type_def
  i_of.i_of_ocl_association_def
  i_of.i_of_ocl_ass_class_def
  i_of.i_of_ocl_data_shallow_base_def
  i_of.i_of_ocl_data_shallow_def
  i_of.i_of_ocl_list_attr_def
  i_of.i_of_ocl_instance_single_def
  i_of.i_of_ocl_instance_def
  i_of.i_of_ocl_def_int_def
  i_of.i_of_ocl_def_state_core_def
  i_of.i_of_ocl_def_state_def
  i_of.i_of_ocl_def_pre_post_def
  i_of.i_of_ocl_ctxt_prefix_def
  i_of.i_of_ocl_ctxt_term_def
  i_of.i_of_ocl_ctxt_pre_post_def
  i_of.i_of_ocl_ctxt2_pre_post_def
  i_of.i_of_ocl_ctxt_inv_def
  i_of.i_of_ocl_ctxt2_inv_def

end
