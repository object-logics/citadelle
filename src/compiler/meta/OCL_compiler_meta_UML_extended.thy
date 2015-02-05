(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_meta_UML_extended.thy ---
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

theory  OCL_compiler_meta_UML_extended
imports OCL_compiler_meta_oid
begin

section{* OCL Meta-Model aka. AST definition of OCL *}

subsection{* type definition *}

datatype ocl_def_base = OclDefInteger "string" (* integer digit *)
                      | OclDefReal "string (* integer digit (left) *) \<times> string (* integer digit (right) *)"
                      | OclDefString "string"

datatype ocl_data_shallow = ShallB_term ocl_def_base
                          | ShallB_str string (* binding *)
                          | ShallB_self internal_oid
                          | ShallB_list "ocl_data_shallow list"

datatype 'a ocl_list_attr = OclAttrNoCast 'a (* inh, own *)
                          | OclAttrCast
                              string (* cast from *)
                              "'a ocl_list_attr" (* cast entity *)
                              'a (* inh, own *)

record ocl_instance_single = Inst_name :: "string option" (* None: fresh name to be generated *)
                             Inst_ty :: string (* type *)
                             Inst_attr :: "((string (*name*) \<times> ocl_data_shallow) list) (* inh and own *)
                                           ocl_list_attr"

datatype ocl_instance = OclInstance "ocl_instance_single list" (* mutual recursive *)

datatype ocl_def_base_l = OclDefBase "ocl_def_base list"

datatype 'a ocl_def_state_core = OclDefCoreAdd ocl_instance_single
                               | OclDefCoreBinding 'a

datatype ocl_def_state = OclDefSt  string (* name *)
                                  "string (* name *) ocl_def_state_core list"

datatype ocl_def_pp_core = OclDefPPCoreAdd "string (* name *) ocl_def_state_core list"
                         | OclDefPPCoreBinding string (* name *)

datatype ocl_def_pre_post = OclDefPP
                              "string option" (* None: fresh name to be generated *)
                              ocl_def_pp_core (* pre *)
                              "ocl_def_pp_core option" (* post *) (* None: same as pre *)

subsection{* ... *}

definition "ocl_instance_single_empty = \<lparr> Inst_name = None, Inst_ty = \<open>\<close>, Inst_attr = OclAttrNoCast [] \<rparr>"

fun map_data_shallow_self where
   "map_data_shallow_self f e = (\<lambda> ShallB_self s \<Rightarrow> f s
                                 | ShallB_list l \<Rightarrow> ShallB_list (List.map (map_data_shallow_self f) l)
                                 | x \<Rightarrow> x) e"

fun map_list_attr where
   "map_list_attr f e = 
     (\<lambda> OclAttrNoCast x \<Rightarrow> OclAttrNoCast (f x)
      | OclAttrCast c_from l_attr x \<Rightarrow> OclAttrCast c_from (map_list_attr f l_attr) (f x)) e"

definition "map_instance_single f ocli = ocli \<lparr> Inst_attr := map_list_attr (List_map f) (Inst_attr ocli) \<rparr>"

fun fold_list_attr where
   "fold_list_attr cast_from f l_attr accu = (case l_attr of
        OclAttrNoCast x \<Rightarrow> f cast_from x accu
      | OclAttrCast c_from l_attr x \<Rightarrow> fold_list_attr c_from f l_attr (f cast_from x accu))"

definition "fold_instance_single f ocli = fold_list_attr (Inst_ty ocli) f (Inst_attr ocli)"

end
