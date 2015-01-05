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

definition "const_oclastype = ''OclAsType''"
definition "const_oclistypeof = ''OclIsTypeOf''"
definition "const_ocliskindof = ''OclIsKindOf''"
definition "const_mixfix dot_ocl name = (let t = \<lambda>s. Char Nibble2 Nibble7 # s in
                                         flatten [dot_ocl, t ''('', name, t '')''])"
definition "const_oid_of s = flatten [''oid_of_'', s]"
definition "dot_oclastype = ''.oclAsType''"
definition "dot_oclistypeof = ''.oclIsTypeOf''"
definition "dot_ocliskindof = ''.oclIsKindOf''"
definition "dot_astype = mk_dot_par dot_oclastype"
definition "dot_istypeof = mk_dot_par dot_oclistypeof"
definition "dot_iskindof = mk_dot_par dot_ocliskindof"

definition "var_reconst_basetype = ''reconst_basetype''"
definition "var_oid_uniq = ''oid''"
definition "var_eval_extract = ''eval_extract''"
definition "var_deref = ''deref''"
definition "var_deref_oid = ''deref_oid''"
definition "var_deref_assocs = ''deref_assocs''"
definition "var_deref_assocs_list = ''deref_assocs_list''"
definition "var_inst_assoc = ''inst_assoc''"
definition "var_select = ''select''"
definition "var_select_object = ''select_object''"
definition "var_select_object_set = ''select_object'' @@ isub_of_str ''Set''"
definition "var_select_object_set_any = ''select_object_any'' @@ isub_of_str ''Set''"
definition "var_select_object_set_any_exec = ''select_object_any_exec'' @@ isub_of_str ''Set''"
definition "var_select_object_sequence = ''select_object'' @@ isub_of_str ''Seq''"
definition "var_select_object_sequence_any = ''select_object_any'' @@ isub_of_str ''Seq''"
definition "var_select_object_sequence_any_exec = ''select_object_any_exec'' @@ isub_of_str ''Seq''"
definition "var_choose = ''choose''"
definition "var_switch = ''switch''"
definition "var_assocs = ''assocs''"
definition "var_map_of_list = ''map_of_list''"
definition "var_OclInteger = ''OclInt''"
definition "var_OclReal = ''OclReal''"
definition "var_OclString = ''OclString''"
definition "var_Abs_Set = flatten [''Abs_Set'',isub_of_str ''base'']"
definition "var_Abs_Set_inverse = flatten [var_Abs_Set, ''_inverse'']"
definition "var_mt_set = ''mtSet''"
definition "var_ANY_set = ''UML_Set.OclANY''"
definition "var_OclIncluding_set = ''UML_Set.OclIncluding''"
definition "var_OclForall_set = ''UML_Set.OclForall''"
definition "var_mt_sequence = ''mtSequence''"
definition "var_ANY_sequence = ''UML_Sequence.OclANY''"
definition "var_OclIncluding_sequence = ''UML_Sequence.OclIncluding''"
definition "var_OclForall_sequence = ''UML_Sequence.OclForall''"
definition "var_self = ''self''"
definition "var_result = ''result''"

definition "update_D_accessor_rbt_pre f = (\<lambda>(l_pre, l_post). (f l_pre, l_post))"
definition "update_D_accessor_rbt_post f = (\<lambda>(l_pre, l_post). (l_pre, f l_post))"

definition "Expr_basety = (let var_x = ''x'' in
                           Expr_lambdas [var_x, wildcard] (Expr_some (Expr_some (Expr_basic [var_x]))))"

subsection{* ... *}

definition "find_class_ass ocl =
 (let (l_class, l_ocl) =
    partition (bug_ocaml_extraction
              (let f = \<lambda>class. ClassRaw_contract class = [] & ClassRaw_invariant class = [] in
               \<lambda> OclAstClassRaw Floor1 class \<Rightarrow> f class
               | OclAstAssociation _ \<Rightarrow> True
               | OclAstAssClass Floor1 (OclAssClass _ class) \<Rightarrow> f class
               | _ \<Rightarrow> False)) (rev (D_ocl_env ocl)) in
  ( flatten [l_class, List.map_filter (bug_ocaml_extraction
                                      (let f = \<lambda>class. class \<lparr> ClassRaw_contract := [], ClassRaw_invariant := [] \<rparr> in
                                       \<lambda> OclAstClassRaw Floor1 c \<Rightarrow> Some (OclAstClassRaw Floor1 (f c))
                                       | OclAstAssClass Floor1 (OclAssClass ass class) \<Rightarrow> Some (OclAstAssClass Floor1 (OclAssClass ass (f class)))
                                       | _ \<Rightarrow> None)) l_ocl]
  , flatten (List_map
      (bug_ocaml_extraction
      (let f = \<lambda>class. 
          flatten [ List_map (OclAstCtxtPrePost Floor1) (ClassRaw_contract class)
                  , List_map (OclAstCtxtInv Floor1) (ClassRaw_invariant class) ] in
       \<lambda> OclAstClassRaw Floor1 class \<Rightarrow> f class
       | OclAstAssClass Floor1 (OclAssClass _ class) \<Rightarrow> f class
       | x \<Rightarrow> [x])) l_ocl)))"

definition "filter_ass = List.map_filter (\<lambda> OclAstAssociation ass \<Rightarrow> Some ass
                                          | OclAstAssClass Floor1 (OclAssClass ass _) \<Rightarrow> Some ass
                                          | _ \<Rightarrow> None)"

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

definition "print_astype_from_universe_name name = flatten [const_oclastype, isub_of_str name, ''_'', unicode_AA]"

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

datatype reporting = Warning
                   | Error
                   | Writeln

definition "raise_ml l_out s = Ml (Sexpr_apply ''Ty'.check''
    [ Sexpr_list'
        (\<lambda>(rep, s).
          Sexpr_pair (Sexpr_basic [flatten [ ''OCL.''
                                           , case rep of Warning \<Rightarrow> ''Warning''
                                                       | Error \<Rightarrow> ''Error''
                                                       | Writeln \<Rightarrow> ''Writeln'' ]])
                     (Sexpr_string s))
        l_out
    , Sexpr_string s ])"

subsection{* context *}

definition "print_ctxt_const_name attr_n var_at_when_hol = flatten [ ''dot'', isup_of_str attr_n, var_at_when_hol]"
definition "print_ctxt_pre_post_name attr_n var_at_when_hol = hol_definition (print_ctxt_const_name attr_n var_at_when_hol)"
definition "print_ctxt_inv_name n tit var_at_when = hol_definition (flatten [n, ''_'', tit, var_at_when])"

definition "make_ctxt_free_var pref ctxt =
 (let l = var_self # List_map fst (Ctxt_fun_ty_arg ctxt) in
  if pref = OclCtxtPre then l else var_result # l)"

subsection{* context2 *}

end
