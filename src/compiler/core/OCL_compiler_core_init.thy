(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_core_init.thy ---
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

theory  OCL_compiler_core_init
imports "../meta/OCL_compiler_meta_META"
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

instantiation opt_ident :: linorder
begin
 definition "n_of_opt_ident = (\<lambda> OptIdent n \<Rightarrow> n)"
 definition "n \<le> m \<longleftrightarrow> n_of_opt_ident n \<le> n_of_opt_ident m"
 definition "n < m \<longleftrightarrow> n_of_opt_ident n < n_of_opt_ident m"
 instance
 apply(default)
 apply (metis less_eq_opt_ident_def less_imp_le less_opt_ident_def not_less)
 apply (metis less_eq_opt_ident_def order_refl)
   apply (metis less_eq_opt_ident_def order.trans)
   apply(simp add: less_eq_opt_ident_def n_of_opt_ident_def, case_tac x, case_tac y, simp)
 by (metis le_cases less_eq_opt_ident_def)
end

subsection{* ... *}

definition "const_oclastype = \<open>OclAsType\<close>"
definition "const_oclistypeof = \<open>OclIsTypeOf\<close>"
definition "const_ocliskindof = \<open>OclIsKindOf\<close>"
definition "const_mixfix dot_ocl name = flatten [dot_ocl, \<open>'(\<close>, name, \<open>')\<close>]"
definition "const_oid_of s = \<open>oid_of_\<close> @@ s"
definition "dot_oclastype = \<open>.oclAsType\<close>"
definition "dot_oclistypeof = \<open>.oclIsTypeOf\<close>"
definition "dot_ocliskindof = \<open>.oclIsKindOf\<close>"
definition "dot_astype = mk_dot_par dot_oclastype"
definition "dot_istypeof = mk_dot_par dot_oclistypeof"
definition "dot_iskindof = mk_dot_par dot_ocliskindof"

definition "var_reconst_basetype = \<open>reconst_basetype\<close>"
definition "var_reconst_basetype_void = \<open>reconst_basetype\<^sub>V\<^sub>o\<^sub>i\<^sub>d\<close>"
definition "var_Abs_Void = \<open>Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<close>"
definition "var_oid_uniq = \<open>oid\<close>"
definition "var_eval_extract = \<open>eval_extract\<close>"
definition "var_deref = \<open>deref\<close>"
definition "var_deref_oid = \<open>deref_oid\<close>"
definition "var_deref_assocs = \<open>deref_assocs\<close>"
definition "var_deref_assocs_list = \<open>deref_assocs_list\<close>"
definition "var_inst_assoc = \<open>inst_assoc\<close>"
definition "var_select = \<open>select\<close>"
definition "var_select_object = \<open>select_object\<close>"
definition "var_select_object_set = \<open>select_object\<^sub>S\<^sub>e\<^sub>t\<close>"
definition "var_select_object_set_any = \<open>select_object_any\<^sub>S\<^sub>e\<^sub>t\<close>"
definition "var_select_object_set_any_exec = \<open>select_object_any_exec\<^sub>S\<^sub>e\<^sub>t\<close>"
definition "var_select_object_sequence = \<open>select_object\<^sub>S\<^sub>e\<^sub>q\<close>"
definition "var_select_object_sequence_any = \<open>select_object_any\<^sub>S\<^sub>e\<^sub>q\<close>"
definition "var_select_object_sequence_any_exec = \<open>select_object_any_exec\<^sub>S\<^sub>e\<^sub>q\<close>"
definition "var_select_object_pair = \<open>select_object\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<close>"
definition "var_select_object_pair_any = \<open>select_object_any\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<close>"
definition "var_select_object_pair_any_exec = \<open>select_object_any_exec\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<close>"
definition "var_choose = \<open>choose\<close>"
definition "var_switch = \<open>switch\<close>"
definition "var_assocs = \<open>assocs\<close>"
definition "var_map_of_list = \<open>map_of_list\<close>"
definition "var_OclInteger = \<open>OclInt\<close>"
definition "var_OclReal = \<open>OclReal\<close>"
definition "var_OclString = \<open>OclString\<close>"
definition "var_Abs_Set = \<open>Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<close>"
definition "var_Abs_Set_inverse = var_Abs_Set @@ \<open>_inverse\<close>"
definition "var_Set_base = \<open>Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<close>"
definition "var_Sequence_base = \<open>Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<close>"
definition "var_Pair_base = \<open>Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<close>"
definition "var_mt_set = \<open>mtSet\<close>"
definition "var_ANY_set = \<open>UML_Set.OclANY\<close>"
definition "var_OclIncluding_set = \<open>UML_Set.OclIncluding\<close>"
definition "var_OclForall_set = \<open>UML_Set.OclForall\<close>"
definition "var_mt_sequence = \<open>mtSequence\<close>"
definition "var_ANY_sequence = \<open>UML_Sequence.OclANY\<close>"
definition "var_OclIncluding_sequence = \<open>UML_Sequence.OclIncluding\<close>"
definition "var_OclForall_sequence = \<open>UML_Sequence.OclForall\<close>"
definition "var_self = \<open>self\<close>"
definition "var_result = \<open>result\<close>"

definition "update_D_accessor_rbt_pre f = (\<lambda>(l_pre, l_post). (f l_pre, l_post))"
definition "update_D_accessor_rbt_post f = (\<lambda>(l_pre, l_post). (l_pre, f l_post))"

definition "Expr_basety = (let var_x = \<open>x\<close> in
                           Expr_lambdas [var_x, wildcard] (Expr_some (Expr_some (Expr_basic [var_x]))))"

subsection{* ... *}

definition "find_class_ass ocl =
 (let (l_class, l_ocl) =
    partition (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l f = \<lambda>class. ClassRaw_contract class = [] & ClassRaw_invariant class = [] in
               \<lambda> OclAstClassRaw Floor1 class \<Rightarrow> f class
               | OclAstAssociation _ \<Rightarrow> True
               | OclAstAssClass Floor1 (OclAssClass _ class) \<Rightarrow> f class
               | _ \<Rightarrow> False) (rev (D_ocl_env ocl)) in
  ( List_flatten [l_class, List.map_filter (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l f = \<lambda>class. class \<lparr> ClassRaw_contract := [], ClassRaw_invariant := [] \<rparr> in
                                       \<lambda> OclAstClassRaw Floor1 c \<Rightarrow> Some (OclAstClassRaw Floor1 (f c))
                                       | OclAstAssClass Floor1 (OclAssClass ass class) \<Rightarrow> Some (OclAstAssClass Floor1 (OclAssClass ass (f class)))
                                       | _ \<Rightarrow> None) l_ocl]
  , List_flatten (List_map
      (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l f = \<lambda>class.
          List_flatten [ List_map (OclAstCtxtPrePost Floor1) (ClassRaw_contract class)
                  , List_map (OclAstCtxtInv Floor1) (ClassRaw_invariant class) ] in
       \<lambda> OclAstClassRaw Floor1 class \<Rightarrow> f class
       | OclAstAssClass Floor1 (OclAssClass _ class) \<Rightarrow> f class
       | x \<Rightarrow> [x]) l_ocl)))"

definition "arrange_ass with_aggreg with_optim_ass l_c =
   (let l_class = List.map_filter (\<lambda> OclAstClassRaw Floor1 cflat \<Rightarrow> Some cflat
                                    | OclAstAssClass Floor1 (OclAssClass _ cflat) \<Rightarrow> Some cflat
                                    | _ \<Rightarrow> None) l_c
      ; l_ass = List.map_filter (\<lambda> OclAstAssociation ass \<Rightarrow> Some ass
                                 | OclAstAssClass Floor1 (OclAssClass ass _) \<Rightarrow> Some ass
                                 | _ \<Rightarrow> None) l_c
      ; OclMult = \<lambda>l set. ocl_multiplicity_ext l None set ()
      ; (l_class, l_ass0) = 
          if with_optim_ass then
            (* move from classes to associations:
                 attributes of object types
                 + those constructed with at most 1 recursive call to OclTy_collection *)
            map_prod rev rev (List.fold
                  (\<lambda>c (l_class, l_ass).
                    let default = Set
                      ; f = \<lambda>role t mult_out. \<lparr> OclAss_type = OclAssTy_native_attribute
                                              , OclAss_relation = [(ClassRaw_name c, OclMult [(Mult_star, None)] default)
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
                          List_map_find (\<lambda>cflat.
                            if String_equal (cl_name_to_string cflat) (ty_obj_to_string name_from) then
                              Some (cflat \<lparr> ClassRaw_own :=
                                              List_flatten [ ClassRaw_own cflat
                                                           , [(role_to, let ty = OclTy_object name_to in
                                                                        if single_multip category_to then 
                                                                          ty
                                                                        else
                                                                          OclTy_collection category_to ty)]] \<rparr>)
                            else None))
                     | _ \<Rightarrow> \<lambda>_. id)
                    (OclAss_relation ass)
                    l_class
                , l_ass)
              else
                (l_class, ass # l_ass)) l_ass (l_class, []))
          else
            (l_class, l_ass) in
    (l_class, List_flatten [l_ass, l_ass0]))"

subsection{* ... *}

definition "datatype_ext_name = \<open>type\<close>"
definition "datatype_name = datatype_ext_name @@ const_oid"
definition "datatype_ext_constr_name = \<open>mk\<close>"
definition "datatype_constr_name = datatype_ext_constr_name @@ const_oid"
definition "datatype_in = \<open>in\<close>"

section{* Translation of AST *}

definition "map_class_arg_only_var = map_class_arg_only_var_gen (\<lambda>s e. Expr_postunary s (Expr_basic e))"
definition "map_class_arg_only_var' = map_class_arg_only_var'_gen (\<lambda>s e. Expr_postunary s (Expr_basic e))"

definition "split_ty name = List_map (\<lambda>s. hol_split (s @@ isub_of_str name)) [datatype_ext_name, datatype_name]"

definition "start_map f = fold_list (\<lambda>x acc. (f x, acc))"
definition "start_map' f x accu = (f x, accu)"
definition "start_map''' f fl = (\<lambda> ocl.
  let design_analysis = D_design_analysis ocl
    ; base_attr = (if design_analysis = Gen_only_design then id else List_filter (\<lambda> (_, OclTy_object (OclTyObj (OclTyCore _) _)) \<Rightarrow> False | _ \<Rightarrow> True))
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

definition "bootstrap_floor f_x l ocl =
 (let (l, ocl) = f_x l ocl in
  ( if D_generation_syntax_shallow ocl then
      l
    else
      Isab_thy_generation_syntax (Generation_syntax_shallow (D_design_analysis ocl))
      # Isab_thy_ml_extended (Ml_extended (Sexpr_ocl (ocl \<lparr> D_disable_thy_output := True
                                                          , D_file_out_path_dep := None
                                                          , D_output_position := (0, 0) \<rparr>) ))
      # l
  , ocl \<lparr> D_generation_syntax_shallow := True \<rparr> ))"

subsection{* Infra *}

fun print_infra_type_synonym_class_rec_aux0 where
   "print_infra_type_synonym_class_rec_aux0 e =
   (let option = \<lambda>x. Ty_apply (Ty_base \<open>option\<close>) [x] in
     (\<lambda> OclTy_collection c t \<Rightarrow>
          let s = TyCollect c
            ; (name, ty) = print_infra_type_synonym_class_rec_aux0 t in
          ( (if s = Set then \<open>Set\<close> else \<open>Sequence\<close>) @@ \<open>_\<close> @@ name
          , Ty_apply (Ty_base (if s = Set then var_Set_base else var_Sequence_base)) [ty])
      | OclTy_pair (_, t1) (_, t2) \<Rightarrow>
          let (name1, ty1) = print_infra_type_synonym_class_rec_aux0 t1
            ; (name2, ty2) = print_infra_type_synonym_class_rec_aux0 t2 in
          ( \<open>Pair\<close> @@ \<open>_\<close> @@ name1 @@ \<open>_\<close> @@ name2
          , Ty_apply (Ty_base var_Pair_base) [ty1, ty2])
      | OclTy_object (OclTyObj (OclTyCore_pre s) _) \<Rightarrow> (s, option (option (Ty_base (datatype_name @@ isub_of_str s))))
      | t \<Rightarrow> (str_of_ty t, Ty_base (str_of_ty t @@ isub_of_str \<open>base\<close>))) e)"

definition "print_infra_type_synonym_class_rec_aux t =
 (let (tit, body) = print_infra_type_synonym_class_rec_aux0 t in
  (tit, Ty_apply (Ty_base \<open>val\<close>) [Ty_base \<open>\<AA>\<close>, body]))"

subsection{* AsType *}

definition "print_astype_from_universe_name name = flatten [const_oclastype, isub_of_str name, \<open>_\<AA>\<close>]"

subsection{* IsTypeOf *}

definition "print_istypeof_defined_name isub_name h_name = flatten [isub_name const_oclistypeof, \<open>_\<close>, h_name, \<open>_defined\<close>]"
definition "print_istypeof_defined'_name isub_name h_name = flatten [isub_name const_oclistypeof, \<open>_\<close>, h_name, \<open>_defined'\<close>]"
definition "print_istypeof_up_d_cast_name name_mid name_any name_pers = flatten [\<open>down_cast_type\<close>, isub_of_str name_mid, \<open>_from_\<close>, name_any, \<open>_to_\<close>, name_pers]"

subsection{* IsKindOf *}

definition "print_iskindof_up_eq_asty_name name = (flatten [\<open>actual_eq_static\<close>, isub_of_str name])"
definition "print_iskindof_up_larger_name name_pers name_any = flatten [\<open>actualKind\<close>, isub_of_str name_pers, \<open>_larger_staticKind\<close>, isub_of_str name_any]"

subsection{* allInstances *}

definition "gen_pre_post f_tit spec f_lemma tac_last =
  (let b = \<lambda>s. Expr_basic [s]
     ; d = hol_definition
     ; f_allinst = \<lambda>s. \<open>OclAllInstances_\<close> @@ s
     ; f_tit = f_tit o f_allinst
     ; var_pre_post = \<open>pre_post\<close>
     ; var_mk = \<open>mk\<close>
     ; var_st = \<open>st\<close>
     ; s_generic = \<open>generic\<close>
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
  , mk_pre_post \<open>snd\<close> \<open>at_post\<close> (Expr_pair (b var_st))
  , mk_pre_post \<open>fst\<close> \<open>at_pre\<close> (\<lambda>e. Expr_pair e (b var_st)) ])"

subsection{* accessors *}

definition "print_access_oid_uniq_name name_from_nat isub_name attr = flatten [ isub_name var_oid_uniq, \<open>_\<close>, natural_of_str name_from_nat, \<open>_\<close>, isup_of_str attr ]"
definition "print_access_oid_uniq_mlname name_from_nat name attr = flatten [ var_oid_uniq, name, \<open>_\<close>, natural_of_str name_from_nat, \<open>_\<close>, attr ]"

definition "print_access_choose_name n i j =
  flatten [var_switch, isub_of_str (natural_of_str n), \<open>_\<close>, natural_of_str i, natural_of_str j]"
definition "print_access_choose_mlname n i j =
  flatten [var_switch, natural_of_str n, \<open>_\<close>, natural_of_str i, natural_of_str j]"

subsection{* example *}

datatype reporting = Warning
                   | Error
                   | Writeln

definition "raise_ml l_out s = Ml (Sexpr_apply \<open>Ty'.check\<close>
    [ Sexpr_list'
        (\<lambda>(rep, s).
          Sexpr_pair (Sexpr_basic [flatten [ \<open>OCL.\<close>
                                           , case rep of Warning \<Rightarrow> \<open>Warning\<close>
                                                       | Error \<Rightarrow> \<open>Error\<close>
                                                       | Writeln \<Rightarrow> \<open>Writeln\<close> ]])
                     (Sexpr_string s))
        l_out
    , Sexpr_string s ])"

definition "print_examp_def_st_inst_var_name ocli name = flatten [case Inst_name ocli of Some n \<Rightarrow> n, name]"

subsection{* context *}

definition "print_ctxt_const_name attr_n var_at_when_hol = flatten [ \<open>dot\<close>, isup_of_str attr_n, var_at_when_hol]"
definition "print_ctxt_pre_post_name attr_n var_at_when_hol = hol_definition (print_ctxt_const_name attr_n var_at_when_hol)"
definition "print_ctxt_inv_name n tit var_at_when = hol_definition (flatten [n, \<open>_\<close>, tit, var_at_when])"

definition "make_ctxt_free_var pref ctxt =
 (let l = var_self # List_map fst (Ctxt_fun_ty_arg ctxt) in
  if pref = OclCtxtPre then l else var_result # l)"

subsection{* context2 *}

end
