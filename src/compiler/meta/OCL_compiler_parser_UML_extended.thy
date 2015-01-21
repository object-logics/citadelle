(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_parser_UML_extended.thy ---
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

theory  OCL_compiler_parser_UML_extended
imports OCL_compiler_meta_UML_extended
        OCL_compiler_parser_oid
begin

section{* Generation to both Form (setup part) *}

definition "ocl_instance_single_rec0 f ocl = f
  (Inst_name ocl)
  (Inst_ty ocl)
  (Inst_attr ocl)"

definition "ocl_instance_single_rec f ocl = ocl_instance_single_rec0 f ocl
  (ocl_instance_single.more ocl)"

(* *)

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

context i_of
begin

definition "i_of_ocl_def_base a b = ocl_def_base_rec
  (ap1 a (b \<langle>''OclDefInteger''\<rangle>) (i_of_string a b))
  (ap1 a (b \<langle>''OclDefReal''\<rangle>) (i_of_pair a b (i_of_string a b) (i_of_string a b)))
  (ap1 a (b \<langle>''OclDefString''\<rangle>) (i_of_string a b))"

definition "i_of_ocl_data_shallow a b = (\<lambda>f1 f2 f3 f4 f5 f6. ocl_data_shallow_rec_1 f1 f2 f3 (K f4) f5 (\<lambda>_ _. f6))
  (ap1 a (b \<langle>''ShallB_term''\<rangle>) (i_of_ocl_def_base a b))
  (ap1 a (b \<langle>''ShallB_str''\<rangle>) (i_of_string a b))
  (ap1 a (b \<langle>''ShallB_self''\<rangle>) (i_of_internal_oid a b))
  (ar1 a (b \<langle>''ShallB_list''\<rangle>))
  (* *)
  (b i_Nil)
  (ar2 a (b i_Cons) id)"

definition "i_of_ocl_list_attr a b f = (\<lambda>f0. co4 (\<lambda>f1. ocl_list_attr_rec f0 (\<lambda>s _ a rec. f1 s rec a)) (ap3 a))
  (ap1 a (b \<langle>''OclAttrNoCast''\<rangle>) f)
  (b \<langle>''OclAttrCast''\<rangle>)
    (i_of_string a b)
    id
    f"

definition "i_of_ocl_instance_single a b f = ocl_instance_single_rec
  (ap4 a (b (ext \<langle>''ocl_instance_single_ext''\<rangle>))
    (i_of_string a b)
    (i_of_string a b)
    (i_of_ocl_list_attr a b (i_of_list a b (i_of_pair a b (i_of_string a b) (i_of_ocl_data_shallow a b))))
    (f a b))"

definition "i_of_ocl_instance a b = ocl_instance_rec
  (ap1 a (b \<langle>''OclInstance''\<rangle>)
    (i_of_list a b (i_of_ocl_instance_single a b (K i_of_unit))))"

definition "i_of_ocl_def_base_l a b = ocl_def_base_l_rec
  (ap1 a (b \<langle>''OclDefBase''\<rangle>) (i_of_list a b (i_of_ocl_def_base a b)))"

definition "i_of_ocl_def_state_core a b f = ocl_def_state_core_rec
  (ap1 a (b \<langle>''OclDefCoreAdd''\<rangle>) (i_of_ocl_instance_single a b (K i_of_unit)))
  (b \<langle>''OclDefCoreSkip''\<rangle>)
  (ap1 a (b \<langle>''OclDefCoreBinding''\<rangle>) f)"

definition "i_of_ocl_def_state a b = ocl_def_state_rec
  (ap2 a (b \<langle>''OclDefSt''\<rangle>) (i_of_string a b) (i_of_list a b (i_of_ocl_def_state_core a b (i_of_string a b))))"

definition "i_of_ocl_def_pre_post a b = ocl_def_pre_post_rec
  (ap2 a (b \<langle>''OclDefPP''\<rangle>) (i_of_string a b) (i_of_string a b))"

end

lemmas [code] =
  i_of.i_of_ocl_def_base_def
  i_of.i_of_ocl_data_shallow_def
  i_of.i_of_ocl_list_attr_def
  i_of.i_of_ocl_instance_single_def
  i_of.i_of_ocl_instance_def
  i_of.i_of_ocl_def_base_l_def
  i_of.i_of_ocl_def_state_core_def
  i_of.i_of_ocl_def_state_def
  i_of.i_of_ocl_def_pre_post_def

end
