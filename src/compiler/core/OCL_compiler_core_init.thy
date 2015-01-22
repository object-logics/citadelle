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

definition "const_oclastype = \<langle>''OclAsType''\<rangle>"
definition "const_oclistypeof = \<langle>''OclIsTypeOf''\<rangle>"
definition "const_ocliskindof = \<langle>''OclIsKindOf''\<rangle>"
definition "const_mixfix dot_ocl name = (let t = \<lambda>s. \<degree>Char Nibble2 Nibble7\<degree> @@ s in
                                         flatten [dot_ocl, t \<langle>''(''\<rangle>, name, t \<langle>'')''\<rangle>])"
definition "const_oid_of s = \<langle>''oid_of_''\<rangle> @@ s"
definition "dot_oclastype = \<langle>''.oclAsType''\<rangle>"
definition "dot_oclistypeof = \<langle>''.oclIsTypeOf''\<rangle>"
definition "dot_ocliskindof = \<langle>''.oclIsKindOf''\<rangle>"
definition "dot_astype = mk_dot_par dot_oclastype"
definition "dot_istypeof = mk_dot_par dot_oclistypeof"
definition "dot_iskindof = mk_dot_par dot_ocliskindof"

definition "var_reconst_basetype = \<langle>''reconst_basetype''\<rangle>"
definition "var_reconst_basetype_void = \<langle>''reconst_basetype''\<rangle> @@ isub_of_str \<langle>''Void''\<rangle>"
definition "var_Abs_Void = \<langle>''Abs_Void''\<rangle> @@ isub_of_str \<langle>''base''\<rangle>"
definition "var_oid_uniq = \<langle>''oid''\<rangle>"
definition "var_eval_extract = \<langle>''eval_extract''\<rangle>"
definition "var_deref = \<langle>''deref''\<rangle>"
definition "var_deref_oid = \<langle>''deref_oid''\<rangle>"
definition "var_deref_assocs = \<langle>''deref_assocs''\<rangle>"
definition "var_deref_assocs_list = \<langle>''deref_assocs_list''\<rangle>"
definition "var_inst_assoc = \<langle>''inst_assoc''\<rangle>"
definition "var_select = \<langle>''select''\<rangle>"
definition "var_select_object = \<langle>''select_object''\<rangle>"
definition "var_select_object_set = \<langle>''select_object''\<rangle> @@ isub_of_str \<langle>''Set''\<rangle>"
definition "var_select_object_set_any = \<langle>''select_object_any''\<rangle> @@ isub_of_str \<langle>''Set''\<rangle>"
definition "var_select_object_set_any_exec = \<langle>''select_object_any_exec''\<rangle> @@ isub_of_str \<langle>''Set''\<rangle>"
definition "var_select_object_sequence = \<langle>''select_object''\<rangle> @@ isub_of_str \<langle>''Seq''\<rangle>"
definition "var_select_object_sequence_any = \<langle>''select_object_any''\<rangle> @@ isub_of_str \<langle>''Seq''\<rangle>"
definition "var_select_object_sequence_any_exec = \<langle>''select_object_any_exec''\<rangle> @@ isub_of_str \<langle>''Seq''\<rangle>"
definition "var_select_object_pair = \<langle>''select_object''\<rangle> @@ isub_of_str \<langle>''Pair''\<rangle>"
definition "var_select_object_pair_any = \<langle>''select_object_any''\<rangle> @@ isub_of_str \<langle>''Pair''\<rangle>"
definition "var_select_object_pair_any_exec = \<langle>''select_object_any_exec''\<rangle> @@ isub_of_str \<langle>''Pair''\<rangle>"
definition "var_choose = \<langle>''choose''\<rangle>"
definition "var_switch = \<langle>''switch''\<rangle>"
definition "var_assocs = \<langle>''assocs''\<rangle>"
definition "var_map_of_list = \<langle>''map_of_list''\<rangle>"
definition "var_OclInteger = \<langle>''OclInt''\<rangle>"
definition "var_OclReal = \<langle>''OclReal''\<rangle>"
definition "var_OclString = \<langle>''OclString''\<rangle>"
definition "var_Abs_Set = \<langle>''Abs_Set''\<rangle> @@ isub_of_str \<langle>''base''\<rangle>"
definition "var_Abs_Set_inverse = var_Abs_Set @@ \<langle>''_inverse''\<rangle>"
definition "var_Set_base = \<langle>''Set''\<rangle> @@ isub_of_str \<langle>''base''\<rangle>"
definition "var_Sequence_base = \<langle>''Sequence''\<rangle> @@ isub_of_str \<langle>''base''\<rangle>"
definition "var_Pair_base = \<langle>''Pair''\<rangle> @@ isub_of_str \<langle>''base''\<rangle>"
definition "var_mt_set = \<langle>''mtSet''\<rangle>"
definition "var_ANY_set = \<langle>''UML_Set.OclANY''\<rangle>"
definition "var_OclIncluding_set = \<langle>''UML_Set.OclIncluding''\<rangle>"
definition "var_OclForall_set = \<langle>''UML_Set.OclForall''\<rangle>"
definition "var_mt_sequence = \<langle>''mtSequence''\<rangle>"
definition "var_ANY_sequence = \<langle>''UML_Sequence.OclANY''\<rangle>"
definition "var_OclIncluding_sequence = \<langle>''UML_Sequence.OclIncluding''\<rangle>"
definition "var_OclForall_sequence = \<langle>''UML_Sequence.OclForall''\<rangle>"
definition "var_self = \<langle>''self''\<rangle>"
definition "var_result = \<langle>''result''\<rangle>"

definition "update_D_accessor_rbt_pre f = (\<lambda>(l_pre, l_post). (f l_pre, l_post))"
definition "update_D_accessor_rbt_post f = (\<lambda>(l_pre, l_post). (l_pre, f l_post))"

definition "Expr_basety = (let var_x = \<langle>''x''\<rangle> in
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

definition "arrange_ass l_c =
   (let l_class = List.map_filter (\<lambda> OclAstClassRaw Floor1 cflat \<Rightarrow> Some cflat
                                    | OclAstAssClass Floor1 (OclAssClass _ cflat) \<Rightarrow> Some cflat
                                    | _ \<Rightarrow> None) l_c
      ; l_ass = List.map_filter (\<lambda> OclAstAssociation ass \<Rightarrow> Some ass
                                 | OclAstAssClass Floor1 (OclAssClass ass _) \<Rightarrow> Some ass
                                 | _ \<Rightarrow> None) l_c in
    (* move from classes to associations:
         attributes of object types
         + those constructed with at most 1 recursive call to OclTy_collection *)
    map_pair rev rev (List.fold
          (\<lambda>c (l_class, l_ass).
            let f = \<lambda>role t mult_out ty. \<lparr> OclAss_type = OclAssTy_native_attribute
                                         , OclAss_relation = [(ClassRaw_name c, OclMult [(Mult_star, None)] ty, None)
                                                             ,(t, OclMult [mult_out] ty, Some role)] \<rparr>
              ; (l_own, l_ass) =
                List.fold (\<lambda> (role, OclTy_class_pre t) \<Rightarrow>
                                  \<lambda> (l_own, l). (l_own, f role t (Mult_nat 0, Some (Mult_nat 1)) Set # l)
                           | (role, OclTy_collection ty (OclTy_class_pre t)) \<Rightarrow>
                                  \<lambda> (l_own, l). (l_own, f role t (Mult_star, None) ty # l)
                           | x \<Rightarrow> \<lambda> (l_own, l). (x # l_own, l))
                          (ClassRaw_own c)
                          ([], l_ass) in
            (c \<lparr> ClassRaw_own := rev l_own \<rparr> # l_class, l_ass))
          l_class
          ([], rev l_ass)))"

subsection{* ... *}

definition "datatype_ext_name = \<langle>''type''\<rangle>"
definition "datatype_name = datatype_ext_name @@ const_oid"
definition "datatype_ext_constr_name = \<langle>''mk''\<rangle>"
definition "datatype_constr_name = datatype_ext_constr_name @@ const_oid"
definition "datatype_in = \<langle>''in''\<rangle>"

section{* Translation of AST *}

definition "map_class_arg_only_var = map_class_arg_only_var_gen (\<lambda>s e. Expr_postunary s (Expr_basic e))"
definition "map_class_arg_only_var' = map_class_arg_only_var'_gen (\<lambda>s e. Expr_postunary s (Expr_basic e))"

definition "split_ty name = List_map (\<lambda>s. hol_split (s @@ isub_of_str name)) [datatype_ext_name, datatype_name]"

definition "start_map f = fold_list (\<lambda>x acc. (f x, acc))"
definition "start_map' f x accu = (f x, accu)"
definition "start_map''' f fl = (\<lambda> ocl.
  let design_analysis = D_design_analysis ocl
    ; base_attr = (if design_analysis = Gen_only_design then id else List_filter (\<lambda> (_, OclTy_class _) \<Rightarrow> False | _ \<Rightarrow> True))
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

subsection{* Infra *}

fun_quick print_infra_type_synonym_class_rec_aux where
   "print_infra_type_synonym_class_rec_aux e =
   (let option = \<lambda>x. Ty_apply (Ty_base \<langle>''option''\<rangle>) [x] in
     (\<lambda> OclTy_collection s t \<Rightarrow>
          let (name, ty) = print_infra_type_synonym_class_rec_aux t in
          ( (if s = Set then \<langle>''Set''\<rangle> else \<langle>''Sequence''\<rangle>) @@ \<langle>''_''\<rangle> @@ name
          , Ty_apply (Ty_base (if s = Set then var_Set_base else var_Sequence_base)) [ty])
      | OclTy_pair t1 t2 \<Rightarrow>
          let (name1, ty1) = print_infra_type_synonym_class_rec_aux t1
            ; (name2, ty2) = print_infra_type_synonym_class_rec_aux t2 in
          ( \<langle>''Pair''\<rangle> @@ \<langle>''_''\<rangle> @@ name1 @@ \<langle>''_''\<rangle> @@ name2
          , Ty_apply (Ty_base var_Pair_base) [ty1, ty2])
      | OclTy_class_pre s \<Rightarrow> (s, option (option (Ty_base (datatype_name @@ isub_of_str s))))
      | t \<Rightarrow> (str_of_ty t, Ty_base (str_of_ty t @@ isub_of_str \<langle>''base''\<rangle>))) e)"

subsection{* AsType *}

definition "print_astype_from_universe_name name = flatten [const_oclastype, isub_of_str name, \<langle>''_''\<rangle>, unicode_AA]"

subsection{* IsTypeOf *}

definition "print_istypeof_defined_name isub_name h_name = flatten [isub_name const_oclistypeof, \<langle>''_''\<rangle>, h_name, \<langle>''_defined''\<rangle>]"
definition "print_istypeof_defined'_name isub_name h_name = flatten [isub_name const_oclistypeof, \<langle>''_''\<rangle>, h_name, \<langle>''_defined''\<rangle>, \<degree>Char Nibble2 Nibble7\<degree>]"
definition "print_istypeof_up_d_cast_name name_mid name_any name_pers = flatten [\<langle>''down_cast_type''\<rangle>, isub_of_str name_mid, \<langle>''_from_''\<rangle>, name_any, \<langle>''_to_''\<rangle>, name_pers]"

subsection{* IsKindOf *}

definition "print_iskindof_up_eq_asty_name name = (flatten [\<langle>''actual_eq_static''\<rangle>, isub_of_str name])"
definition "print_iskindof_up_larger_name name_pers name_any = flatten [\<langle>''actualKind''\<rangle>, isub_of_str name_pers, \<langle>''_larger_staticKind''\<rangle>, isub_of_str name_any]"

subsection{* allInstances *}

definition "gen_pre_post f_tit spec f_lemma tac_last =
  (let b = \<lambda>s. Expr_basic [s]
     ; d = hol_definition
     ; f_allinst = \<lambda>s. \<langle>''OclAllInstances_''\<rangle> @@ s
     ; f_tit = f_tit o f_allinst
     ; var_pre_post = \<langle>''pre_post''\<rangle>
     ; var_mk = \<langle>''mk''\<rangle>
     ; var_st = \<langle>''st''\<rangle>
     ; s_generic = \<langle>''generic''\<rangle>
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
  , mk_pre_post \<langle>''snd''\<rangle> \<langle>''at_post''\<rangle> (Expr_pair (b var_st))
  , mk_pre_post \<langle>''fst''\<rangle> \<langle>''at_pre''\<rangle> (\<lambda>e. Expr_pair e (b var_st)) ])"

subsection{* accessors *}

definition "print_access_oid_uniq_name name_from_nat isub_name attr = flatten [ isub_name var_oid_uniq, \<langle>''_''\<rangle>, natural_of_str name_from_nat, \<langle>''_''\<rangle>, isup_of_str attr ]"
definition "print_access_oid_uniq_mlname name_from_nat name attr = flatten [ var_oid_uniq, name, \<langle>''_''\<rangle>, natural_of_str name_from_nat, \<langle>''_''\<rangle>, attr ]"

definition "print_access_choose_name n i j =
  flatten [var_switch, isub_of_str (natural_of_str n), \<langle>''_''\<rangle>, natural_of_str i, natural_of_str j]"
definition "print_access_choose_mlname n i j =
  flatten [var_switch, natural_of_str n, \<langle>''_''\<rangle>, natural_of_str i, natural_of_str j]"

subsection{* example *}

datatype reporting = Warning
                   | Error
                   | Writeln

definition "raise_ml l_out s = Ml (Sexpr_apply \<langle>''Ty'.check''\<rangle>
    [ Sexpr_list'
        (\<lambda>(rep, s).
          Sexpr_pair (Sexpr_basic [flatten [ \<langle>''OCL.''\<rangle>
                                           , case rep of Warning \<Rightarrow> \<langle>''Warning''\<rangle>
                                                       | Error \<Rightarrow> \<langle>''Error''\<rangle>
                                                       | Writeln \<Rightarrow> \<langle>''Writeln''\<rangle> ]])
                     (Sexpr_string s))
        l_out
    , Sexpr_string s ])"

subsection{* context *}

definition "print_ctxt_const_name attr_n var_at_when_hol = flatten [ \<langle>''dot''\<rangle>, isup_of_str attr_n, var_at_when_hol]"
definition "print_ctxt_pre_post_name attr_n var_at_when_hol = hol_definition (print_ctxt_const_name attr_n var_at_when_hol)"
definition "print_ctxt_inv_name n tit var_at_when = hol_definition (flatten [n, \<langle>''_''\<rangle>, tit, var_at_when])"

definition "make_ctxt_free_var pref ctxt =
 (let l = var_self # List_map fst (Ctxt_fun_ty_arg ctxt) in
  if pref = OclCtxtPre then l else var_result # l)"

subsection{* context2 *}

end
