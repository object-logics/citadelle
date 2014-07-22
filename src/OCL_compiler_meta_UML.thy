(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_meta_UML.thy ---
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

theory  OCL_compiler_meta_UML
imports OCL_compiler_meta_Pure
begin

section{* OCL Meta-Model aka. AST definition of OCL *}

subsection{* type definition *}

datatype ocl_collection =   Set | Sequence

datatype ocl_multiplicity_single = Mult_nat nat
                                 | Mult_star

datatype ocl_multiplicity = OclMult "(ocl_multiplicity_single \<times> ocl_multiplicity_single option) list"

record ocl_ty_class_node =  TyObjN_ass_switch :: nat
                            TyObjN_role_multip :: ocl_multiplicity
                            TyObjN_role_name :: "string option"
                            TyObjN_role_ty :: string
record ocl_ty_class =       TyObj_name :: string
                            TyObj_ass_id :: nat
                            TyObj_ass_arity :: nat
                            TyObj_from :: ocl_ty_class_node
                            TyObj_to :: ocl_ty_class_node
datatype ocl_ty =           OclTy_boolean
                          | OclTy_integer
                          | OclTy_class ocl_ty_class
                          | OclTy_collection ocl_collection ocl_ty
                          | OclTy_raw string (* denoting raw HOL-type.*)


record ocl_operation = Op_args :: "(string \<times> ocl_ty) list"
                       Op_result :: ocl_ty
                       Op_pre :: "(string \<times> string) list"
                       Op_post :: "(string \<times> string) list"

datatype ocl_class =   OclClass
                         string (* name of the class *)
                         "(string (* name *) \<times> ocl_ty) list" (* attribute *)
                         (*"(string (* name *) \<times> ocl_operation) list" (* contract *)
                         "(string (* name *) \<times> string) list" (* invariant *) *)
                         "ocl_class list" (* link to subclasses *)

record ocl_class_raw = ClassRaw_name :: string
                       ClassRaw_own :: "(string (* name *) \<times> ocl_ty) list" (* attribute *)
                      (*ClassRaw_contract :: "(string (* name *) \<times> ocl_operation) list" (* contract *)
                       ClassRaw_inv :: "(string (* name *) \<times> string) list" (* invariant *) *)
                       ClassRaw_inh :: "string option" (* superclass *)



datatype ocl_association_type = OclAssTy_association
                              | OclAssTy_composition
                              | OclAssTy_aggregation
record ocl_association =        OclAss_type     :: ocl_association_type
                                OclAss_relation :: "( string (* name class *)
                                                    \<times> ocl_multiplicity (* multiplicity *)
                                                    \<times> string option (* role *)) list"
datatype ocl_ass_class =        OclAssClass ocl_association ocl_class_raw

datatype ocl_data_shallow_base = ShallB_str string
                               | ShallB_self internal_oid
datatype ocl_data_shallow =      Shall_base ocl_data_shallow_base
                               | Shall_list "ocl_data_shallow_base list"

datatype 'a ocl_list_attr = OclAttrNoCast 'a (* inh, own *)
                          | OclAttrCast
                              string (* cast from *)
                              "'a ocl_list_attr" (* cast entity *)
                              'a (* inh, own *)

record ocl_instance_single = Inst_name :: string
                             Inst_ty :: string (* type *)
                             Inst_attr :: "((string (*name*) \<times> ocl_data_shallow) list) (* inh and own *)
                                           ocl_list_attr"

datatype ocl_instance = OclInstance "ocl_instance_single list" (* mutual recursive *)

datatype ocl_def_int = OclDefI "string list"

datatype 'a ocl_def_state_core = OclDefCoreAdd ocl_instance_single
                               | OclDefCoreSkip
                               | OclDefCoreBinding 'a

datatype ocl_def_state = OclDefSt  string (* name *)
                                  "string (* name *) ocl_def_state_core list"

datatype ocl_def_pre_post = OclDefPP
                              string (* pre *)
                              string (* post *)

datatype ocl_ctxt_prefix = OclCtxtPre | OclCtxtPost

datatype ocl_ctxt_term = T_pure pure_term
                       | T_to_be_parsed string

record ocl_ctxt_pre_post = Ctxt_ty :: string (* class ty *)
                           Ctxt_fun_name :: string (* function name *)
                           Ctxt_fun_ty_arg :: "(string (* arg name *) \<times> ocl_ty) list"
                           Ctxt_fun_ty_out :: "ocl_ty option" (* None : Void *)
                           Ctxt_expr :: "(ocl_ctxt_prefix \<times> ocl_ctxt_term (* expr *)) list"

type_synonym ocl_ctxt2_pre_post = ocl_ctxt_pre_post

record ocl_ctxt_inv =      Ctxt_inv_ty :: string
                           Ctxt_inv_expr :: "(string (* name *) \<times> ocl_ctxt_term (* expr *)) list"

type_synonym ocl_ctxt2_inv = ocl_ctxt_inv



subsection{* Class Translation Preliminaries *}

definition "const_oid = ''oid''"
definition "const_oid_list = ''list''"
definition "const_oclany = ''OclAny''"

definition "single_multip = (\<lambda> OclMult l \<Rightarrow>
  List.list_all (\<lambda> (_, Some (Mult_nat n)) \<Rightarrow> n \<le> 1
                 | (Mult_nat n, None) \<Rightarrow> n \<le> 1
                 | _ \<Rightarrow> False) l)"

fun_quick fold_max_aux where
   "fold_max_aux f l l_acc accu = (case l of
      [] \<Rightarrow> accu
    | x # xs \<Rightarrow> fold_max_aux f xs (x # l_acc) (f x (flatten [rev l_acc, xs]) accu))"

definition "fold_max f l = fold_max_aux f (List_mapi Pair l) []"

function (sequential) class_unflat_aux where
(* (* FIXME replace with this simplified form *)
   "class_unflat_aux rbt rbt_inv rbt_cycle r =
   (case lookup rbt_cycle r of (None (* cycle detection *)) \<Rightarrow>
      OclClass
        r
        (bug_ocaml_extraction (case lookup rbt r of Some l \<Rightarrow> l))
        (List_map
          (class_unflat_aux rbt rbt_inv (insert r () rbt_cycle))
          (case lookup rbt_inv r of None \<Rightarrow> [] | Some l \<Rightarrow> l)))"
*)
   "class_unflat_aux rbt rbt_inv rbt_cycle r =
   (case lookup rbt_inv r of
  None \<Rightarrow>
(case lookup rbt_cycle r of (None (* cycle detection *)) \<Rightarrow>
      OclClass
        r
        (bug_ocaml_extraction (case lookup rbt r of Some l \<Rightarrow> l))
        ( ( [])))
| Some l \<Rightarrow>
(case lookup rbt_cycle r of (None (* cycle detection *)) \<Rightarrow>
      OclClass
        r
        (bug_ocaml_extraction (case lookup rbt r of Some l \<Rightarrow> l))
        (List_map
          (class_unflat_aux rbt rbt_inv (insert r () rbt_cycle))
          ( l))))"
by pat_completeness auto

termination
proof -
 have arith_diff: "\<And>a1 a2 (b :: Nat.nat). a1 = a2 \<Longrightarrow> a1 > b \<Longrightarrow> a1 - (b + 1) < a2 - b"
 by arith

 have arith_less: "\<And>(a:: Nat.nat) b c. b \<ge> max (a + 1) c \<Longrightarrow> a < b"
 by arith

 have rbt_length: "\<And>rbt_cycle r v. lookup rbt_cycle r = None \<Longrightarrow>
     length (keys (insert r v rbt_cycle)) = length (keys rbt_cycle) + 1"
  apply(subst (1 2) distinct_card[symmetric], (rule distinct_keys)+)
  apply(simp only: lookup_keys[symmetric], simp)
 by (metis card_insert_if domIff finite_dom_lookup)

 have rbt_fold_union'': "\<And>ab a x k. dom (\<lambda>b. if b = ab then Some a else k b) = {ab} \<union> dom k"
 by(auto)

 have rbt_fold_union': "\<And>l rbt_inv a.
       dom (lookup (List.fold (\<lambda>(k, _). RBT.insert k a) l rbt_inv)) =
       dom (map_of l) \<union> dom (lookup rbt_inv)"
  apply(rule_tac P = "\<lambda>rbt_inv . dom (lookup (List.fold (\<lambda>(k, _). RBT.insert k a) l rbt_inv)) =
       dom (map_of l) \<union> dom (lookup rbt_inv)" in allE, simp_all)
  apply(induct_tac l, simp, rule allI)
  apply(case_tac aa, simp)
  apply(simp add: rbt_fold_union'')
 done

 have rbt_fold_union: "\<And>rbt_cycle rbt_inv a.
   dom (lookup (RBT.fold (\<lambda>k _. RBT.insert k a) rbt_cycle rbt_inv)) =
   dom (lookup rbt_cycle) \<union> dom (lookup rbt_inv)"
  apply(simp add: fold_fold)
  apply(subst (2) map_of_entries[symmetric])
  apply(rule rbt_fold_union')
 done

 have rbt_fold_eq: "\<And>rbt_cycle rbt_inv a b.
   dom (lookup (RBT.fold (\<lambda>k _. RBT.insert k a) rbt_cycle rbt_inv)) =
   dom (lookup (RBT.fold (\<lambda>k _. RBT.insert k b) rbt_inv rbt_cycle))"
 by(simp add: rbt_fold_union Un_commute)

 let ?len = "\<lambda>x. length (keys x)"
 let ?len_merge = "\<lambda>rbt_cycle rbt_inv. ?len (fold (\<lambda>k _. insert k []) rbt_cycle rbt_inv)"

 have rbt_fold_large: "\<And>rbt_cycle rbt_inv. ?len_merge rbt_cycle rbt_inv \<ge> max (?len rbt_cycle) (?len rbt_inv)"
  apply(subst (1 2 3) distinct_card[symmetric], (rule distinct_keys)+)
  apply(simp only: lookup_keys[symmetric], simp)
  apply(subst (1 2) card_mono, simp_all)
  apply(simp add: rbt_fold_union)+
 done

 have rbt_fold_eq: "\<And>rbt_cycle rbt_inv r a.
     lookup rbt_inv r = Some a \<Longrightarrow>
     ?len_merge (insert r () rbt_cycle) rbt_inv = ?len_merge rbt_cycle rbt_inv"
  apply(subst (1 2) distinct_card[symmetric], (rule distinct_keys)+)
  apply(simp only: lookup_keys[symmetric])
  apply(simp add: rbt_fold_union)
 by (metis Un_insert_right insert_dom)

 show ?thesis
  apply(relation "measure (\<lambda>(_, rbt_inv, rbt_cycle, r).
    ?len_merge rbt_cycle rbt_inv - length (keys rbt_cycle)
    )", simp+)
  apply(subst rbt_length, simp)
  apply(rule arith_diff)
  apply(rule rbt_fold_eq, simp)
  apply(rule arith_less)
  apply(subst rbt_length[symmetric], simp)
  apply(rule rbt_fold_large)
 done
qed

end
