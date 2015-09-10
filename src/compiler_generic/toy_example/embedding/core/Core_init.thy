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

chapter{* Part ... *}

theory  Core_init
imports "../../Toy_Library_Static"
        "../meta_toy/Meta_META"
begin

section{* Preliminaries Compiler *}

subsection{* RBT Miscellaneous *}

subsection{* ... *} (* optimized data-structure version *)

datatype opt_attr_type = OptInh | OptOwn
datatype opt_ident = OptIdent nat

instantiation internal_oid :: linorder
begin
 definition "n_of_internal_oid = (\<lambda> Oid n \<Rightarrow> n)"
 definition "n \<le> m \<longleftrightarrow> n_of_internal_oid n \<le> n_of_internal_oid m"
 definition "n < m \<longleftrightarrow> n_of_internal_oid n < n_of_internal_oid m"
 instance
   apply(default)
   apply (metis less_eq_internal_oid_def less_imp_le less_internal_oid_def not_less)
   apply (metis less_eq_internal_oid_def order_refl)
   apply (metis less_eq_internal_oid_def order.trans)
   apply(simp add: less_eq_internal_oid_def n_of_internal_oid_def, case_tac x, case_tac y, simp)
 by (metis le_cases less_eq_internal_oid_def)
end

subsection{* ... *}

definition "var_oid_uniq = \<open>oid\<close>"
definition "var_deref_assocs_list = \<open>deref_assocs_list\<close>"
definition "var_inst_assoc = \<open>inst_assoc\<close>"
definition "var_choose = \<open>choose\<close>"
definition "var_switch = \<open>switch\<close>"
definition "var_assocs = \<open>assocs\<close>"
definition "var_map_of_list = \<open>map_of_list\<close>"
definition "var_self = \<open>self\<close>"
definition "var_result = \<open>result\<close>"

subsection{* ... *}

definition "find_class_ass ocl =
 (let (l_class, l_ocl) =
    partition (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l f = \<lambda>class. ClassRaw_clause class = [] in
               \<lambda> META_class_raw Floor1 class \<Rightarrow> f class
               | META_association _ \<Rightarrow> True
               | META_ass_class Floor1 (OclAssClass _ class) \<Rightarrow> f class
               | META_class_synonym _ \<Rightarrow> True
               | _ \<Rightarrow> False) (rev (D_input_meta ocl)) in
  ( L.flatten [l_class, List.map_filter (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l f = \<lambda>class. class \<lparr> ClassRaw_clause := [] \<rparr> in
                                       \<lambda> META_class_raw Floor1 c \<Rightarrow> Some (META_class_raw Floor1 (f c))
                                       | META_ass_class Floor1 (OclAssClass ass class) \<Rightarrow> Some (META_ass_class Floor1 (OclAssClass ass (f class)))
                                       | _ \<Rightarrow> None) l_ocl]
  , L.flatten (L.map
      (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l f = \<lambda>class. [ META_ctxt Floor1 (ocl_ctxt_ext [] (ClassRaw_name class) (ClassRaw_clause class) ()) ] in
       \<lambda> META_class_raw Floor1 class \<Rightarrow> f class
       | META_ass_class Floor1 (OclAssClass _ class) \<Rightarrow> f class
       | x \<Rightarrow> [x]) l_ocl)))"

definition "map_enum_syn l_enum l_syn =
 (\<lambda> OclTy_object (OclTyObj (OclTyCore_pre s) []) \<Rightarrow> 
      if list_ex (\<lambda>syn. s \<triangleq> (case syn of OclClassSynonym n _ \<Rightarrow> n)) l_syn then
        OclTy_class_syn s
      else if list_ex (\<lambda>enum. s \<triangleq> (case enum of OclEnum n _ \<Rightarrow> n)) l_enum then
        OclTy_enum s
      else
        OclTy_object (OclTyObj (OclTyCore_pre s) [])
  | x \<Rightarrow> x)"

definition "arrange_ass with_aggreg with_optim_ass l_c l_enum =
   (let l_syn = List.map_filter (\<lambda> META_class_synonym e \<Rightarrow> Some e
                                 | _ \<Rightarrow> None) l_c
      ; l_class = List.map_filter (\<lambda> META_class_raw Floor1 cflat \<Rightarrow> Some cflat
                                   | META_ass_class Floor1 (OclAssClass _ cflat) \<Rightarrow> Some cflat
                                   | _ \<Rightarrow> None) l_c
      ; l_class = (* map classes: change the (enumeration) type of every attributes to 'raw'
                                instead of the default 'object' type *)
        L.map
          (\<lambda> cflat \<Rightarrow>
            cflat \<lparr> ClassRaw_own :=
                      L.map (map_prod id (map_enum_syn l_enum l_syn))
                               (ClassRaw_own cflat) \<rparr>) l_class
    ; l_ass = List.map_filter (\<lambda> META_association ass \<Rightarrow> Some ass
                                 | META_ass_class Floor1 (OclAssClass ass _) \<Rightarrow> Some ass
                                 | _ \<Rightarrow> None) l_c
      ; OclMult = \<lambda>l set. ocl_multiplicity_ext l None set ()
      ; (l_class, l_ass0) = 
          if with_optim_ass then
            (* move from classes to associations:
                 attributes of object types
                 + those constructed with at most 1 recursive call to OclTy_collection *)
            map_prod rev rev (List.fold
                  (\<lambda>c (l_class, l_ass).
                    let default = [Set]
                      ; f = \<lambda>role t mult_out. \<lparr> OclAss_type = OclAssTy_native_attribute
                                              , OclAss_relation = OclAssRel [(ClassRaw_name c, OclMult [(Mult_star, None)] default)
                                                                            ,(t, mult_out \<lparr> TyRole := Some role \<rparr>)] \<rparr>
                      ; (l_own, l_ass) =
                        List.fold (\<lambda> (role, OclTy_object t) \<Rightarrow>
                                          \<lambda> (l_own, l). (l_own, f role t (OclMult [(Mult_nat 0, Some (Mult_nat 1))] default) # l)
                                   | (role, OclTy_collection mult (OclTy_object t)) \<Rightarrow>
                                          \<lambda> (l_own, l). (l_own, f role t mult # l)
                                   | x \<Rightarrow> \<lambda> (l_own, l). (x # l_own, l))
                                  (ClassRaw_own c)
                                  ([], l_ass) in
                    (c \<lparr> ClassRaw_own := rev l_own \<rparr> # l_class, l_ass))
                  l_class
                  ([], []))
          else
            (l_class, [])
      ; (l_class, l_ass) =
          if with_aggreg then
            (* move from associations to classes:
                 attributes of aggregation form *)
            map_prod rev rev (List.fold
            (\<lambda>ass (l_class, l_ass).
              if OclAss_type ass = OclAssTy_aggregation then
                ( fold_max
                    (\<lambda> (cpt_to, (name_to, category_to)).
                      case TyRole category_to of
                        Some role_to \<Rightarrow>
                        List.fold (\<lambda> (cpt_from, (name_from, multip_from)).
                          L.map_find (\<lambda>cflat.
                            if cl_name_to_string cflat \<triangleq> ty_obj_to_string name_from then
                              Some (cflat \<lparr> ClassRaw_own :=
                                              L.flatten [ ClassRaw_own cflat
                                                           , [(role_to, let ty = OclTy_object name_to in
                                                                        if single_multip category_to then 
                                                                          ty
                                                                        else
                                                                          OclTy_collection category_to ty)]] \<rparr>)
                            else None))
                     | _ \<Rightarrow> \<lambda>_. id)
                    (OclAss_relation' ass)
                    l_class
                , l_ass)
              else
                (l_class, ass # l_ass)) l_ass (l_class, []))
          else
            (l_class, l_ass) in
    ( l_class
    , L.flatten [l_ass, l_ass0]))"

subsection{* ... *}

definition "datatype_name = \<open>ty\<close>"
definition "datatype_ext_name = datatype_name @@ \<open>\<E>\<X>\<T>\<close>"
definition "datatype_constr_name = \<open>mk\<close>"
definition "datatype_ext_constr_name = datatype_constr_name @@ \<open>\<E>\<X>\<T>\<close>"
definition "datatype_in = \<open>in\<close>"

section{* Translation of AST *}

definition "start_map f = L.mapM (\<lambda>x acc. (f x, acc))"
definition "start_map''' f fl = (\<lambda> ocl.
  let design_analysis = D_ocl_semantics ocl
    ; base_attr = (if design_analysis = Gen_only_design then id else L.filter (\<lambda> (_, OclTy_object (OclTyObj (OclTyCore _) _)) \<Rightarrow> False | _ \<Rightarrow> True))
    ; base_attr' = (\<lambda> (l_attr, l_inh). (base_attr l_attr, L.map base_attr l_inh))
    ; base_attr'' = (\<lambda> (l_attr, l_inh). (base_attr l_attr, base_attr l_inh)) in
  start_map f (fl design_analysis base_attr base_attr' base_attr'') ocl)"
definition "start_map'' f fl e = start_map''' f (\<lambda>_. fl) e"
definition "start_map'''' f fl = (\<lambda> ocl. start_map f (fl (D_ocl_semantics ocl)) ocl)"

subsection{* ... *}

definition "bootstrap_floor f_x l ocl =
 (let (l, ocl) = f_x l ocl
    ; l_setup = Isab_thy_ml_extended (Ml_extended (SML_ocl (ocl \<lparr> D_output_disable_thy := True
                                                              , D_output_header_thy := None
                                                              , D_output_position := (0, 0) \<rparr>) ))
            # l
    ; l = if case D_input_meta ocl of [] \<Rightarrow> True | x # _ \<Rightarrow> ignore_meta_header x then
            l
          else
            l_setup in
  ( if D_output_auto_bootstrap ocl then
      l
    else
      Isab_thy_generation_syntax (Gen_semantics (D_ocl_semantics ocl))
      # l_setup
  , ocl \<lparr> D_output_auto_bootstrap := True \<rparr> ))"

definition "wrap_oclty x = \<open>\<cdot>\<close> @@ x"
definition "Term_annot_ocl e s = Term_annot' e (wrap_oclty s)"
definition "Term_oclset l = (case l of [] \<Rightarrow> Term_basic [\<open>Set{}\<close>] | _ \<Rightarrow> Term_paren \<open>Set{\<close> \<open>}\<close> (term_binop \<open>,\<close> l))"
definition "Term_oid s = (\<lambda>Oid n \<Rightarrow> Term_basic [s @@ String.of_natural n])"

subsection{* Infra *}

subsection{* accessors *}

definition "print_access_oid_uniq_name' name_from_nat isub_name attr = S.flatten [ isub_name var_oid_uniq, \<open>_\<close>, String.of_natural name_from_nat, \<open>_\<close>, attr ]"
definition "print_access_oid_uniq_name name_from_nat isub_name attr = print_access_oid_uniq_name' name_from_nat isub_name (String.isup attr)"

definition "print_access_choose_name n i j =
  S.flatten [var_switch, String.isub (String.of_natural n), \<open>_\<close>, String.of_natural i, String.of_natural j]"

subsection{* example *}

datatype reporting = Warning
                   | Error
                   | Writeln

subsection{* context *}

definition "make_ctxt_free_var pref ctxt =
 (var_self # L.flatten [ L.map fst (Ctxt_fun_ty_arg ctxt)
                          , if pref = OclCtxtPre then [] else [var_result] ])"

end
