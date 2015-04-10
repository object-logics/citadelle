(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_floor1_astype.thy ---
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

theory  OCL_compiler_floor1_astype
imports OCL_compiler_core_init
begin

section{* Translation of AST *}

subsection{* AsType *}

definition "print_astype_consts = start_map Thy_consts_class o
  map_class (\<lambda>isub_name name _ _ _ _.
    Consts (isub_name const_oclastype) (Ty_base (wrap_oclty name)) (const_mixfix dot_oclastype name))"

definition "print_astype_class = start_m' Thy_defs_overloaded
  (\<lambda> compare (isub_name, name, nl_attr). \<lambda> OclClass h_name hl_attr _ \<Rightarrow>
    Defs_overloaded
          (flatten [isub_name const_oclastype, \<open>_\<close>, h_name])
          (let var_x = \<open>x\<close> in
           Expr_rewrite
             (Expr_postunary (Expr_annot_ocl (Expr_basic [var_x]) h_name) (Expr_basic [dot_astype name]))
             \<open>\<equiv>\<close>
             (case compare
              of EQ \<Rightarrow>
                Expr_basic [var_x]
              | x \<Rightarrow>
                Expr_lam \<open>\<tau>\<close>
                  (\<lambda>var_tau. let val_invalid = Expr_apply \<open>invalid\<close> [Expr_basic [var_tau]] in
                  Expr_case
                    (Expr_apply var_x [Expr_basic [var_tau]])
                    ( (Expr_basic [\<open>\<bottom>\<close>], val_invalid)
                    # (Expr_some (Expr_basic [\<open>\<bottom>\<close>]), Expr_apply \<open>null\<close> [Expr_basic [var_tau]])
                    # (let pattern_complex = (\<lambda>h_name name l_extra.
                            let isub_h = (\<lambda> s. s @@ isub_of_str h_name)
                              ; isub_name = (\<lambda>s. s @@ isub_of_str name)
                              ; isub_n = (\<lambda>s. isub_name (s @@ \<open>_\<close>))
                              ; var_name = name in
                             Expr_apply (isub_h datatype_constr_name)
                                        ( Expr_apply (isub_n (isub_h datatype_ext_constr_name)) [Expr_basic [var_name]]
                                        # l_extra) )
                         ; pattern_simple = (\<lambda> name.
                            let isub_name = (\<lambda>s. s @@ isub_of_str name)
                              ; var_name = name in
                             Expr_basic [var_name])
                         ; some_some = (\<lambda>x. Expr_some (Expr_some x)) in
                       if x = LT then
                         [ (some_some (pattern_simple h_name), some_some (pattern_complex name h_name (List_map (\<lambda>_. Expr_basic [\<open>None\<close>]) nl_attr))) ]
                       else
                         let l = [(Expr_basic [wildcard], val_invalid)] in
                         if x = GT then
                           (some_some (pattern_complex h_name name (List_map (\<lambda>_. Expr_basic [wildcard]) hl_attr)), some_some (pattern_simple name))
                           # l
                         else l) ) ))))"

definition "print_astype_from_universe =
 (let f_finish = (\<lambda> [] \<Rightarrow> ((id, Expr_binop (Expr_basic [\<open>Some\<close>]) \<open>o\<close>), [])
                  | _ \<Rightarrow> ((Expr_some, id), [(Expr_basic [wildcard], Expr_basic [\<open>None\<close>])])) in
  start_m_gen Thy_definition_hol
  (\<lambda> name l_inh _ l.
    let const_astype = print_astype_from_universe_name name in
    [ Definition (Expr_rewrite (Expr_basic [const_astype]) \<open>=\<close>
        (case f_finish l_inh of ((_, finish_with_some2), last_case_none) \<Rightarrow>
          finish_with_some2 (Expr_function (List_flatten [l, last_case_none]))))])
  (\<lambda> l_inh _ _ compare (_, name, nl_attr). \<lambda> OclClass h_name hl_attr _ \<Rightarrow>
     if compare = UN' then [] else
     let ((finish_with_some1, _), _) = f_finish l_inh
       ; isub_h = (\<lambda> s. s @@ isub_of_str h_name)
       ; pattern_complex = (\<lambda>h_name name l_extra.
                            let isub_h = (\<lambda> s. s @@ isub_of_str h_name)
                              ; isub_name = (\<lambda>s. s @@ isub_of_str name)
                              ; isub_n = (\<lambda>s. isub_name (s @@ \<open>_\<close>))
                              ; var_name = name in
                             Expr_apply (isub_h datatype_constr_name)
                                        ( Expr_apply (isub_n (isub_h datatype_ext_constr_name)) [Expr_basic [var_name]]
                                        # l_extra ))
       ; pattern_simple = (\<lambda> name.
                            let isub_name = (\<lambda>s. s @@ isub_of_str name)
                              ; var_name = name in
                             Expr_basic [var_name])
       ; case_branch = (\<lambda>pat res. [(Expr_apply (isub_h datatype_in) [pat], finish_with_some1 res)]) in
             case compare
             of GT \<Rightarrow> case_branch (pattern_complex h_name name (List_map (\<lambda>_. Expr_basic [wildcard]) hl_attr)) (pattern_simple name)
              | EQ \<Rightarrow> let n = Expr_basic [name] in case_branch n n
              | LT \<Rightarrow> case_branch (pattern_simple h_name) (pattern_complex name h_name (List_map (\<lambda>_. Expr_basic [\<open>None\<close>]) nl_attr))))"

definition "print_astype_lemma_cp_set =
  (if activate_simp_optimization then
    map_class (\<lambda>isub_name name _ _ _ _. ((isub_name, name), name))
   else (\<lambda>_. []))"

definition "print_astype_lemmas_id = start_map' (\<lambda>expr.
  (let name_set = print_astype_lemma_cp_set expr in
   case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
  [ Lemmas_simp \<open>\<close> (List_map (\<lambda>((isub_name, _), name).
    Thm_str (flatten [isub_name const_oclastype, \<open>_\<close>, name])) name_set) ]))"

definition "print_astype_lemma_cp_set2 =
  (if activate_simp_optimization then
     \<lambda>expr base_attr.
       List_flatten (m_class' base_attr (\<lambda> compare (isub_name, name, _). \<lambda> OclClass name2 _ _ \<Rightarrow>
         if compare = EQ then
           []
         else
           [((isub_name, name), ((\<lambda>s. s @@ isub_of_str name2), name2))]) expr)
   else (\<lambda>_ _. []))"

definition "print_astype_lemmas_id2 = start_map'' id o (\<lambda>expr base_attr _ _.
  (let name_set = print_astype_lemma_cp_set2 expr base_attr in
   case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
  [ Lemmas_simp \<open>\<close> (List_map (\<lambda>((isub_name_h, _), (_, name)).
    Thm_str (flatten [isub_name_h const_oclastype, \<open>_\<close>, name])) name_set) ]))"

definition "print_astype_lemma_cp expr = (start_map Thy_lemma_by o get_hierarchy_map (
  let check_opt =
    let set = print_astype_lemma_cp_set expr in
    (\<lambda>n1 n2. list_ex (\<lambda>((_, name1), name2). name1 = n1 & name2 = n2) set) in
  (\<lambda>name1 name2 name3.
    Lemma_by
      (flatten [\<open>cp_\<close>, const_oclastype, isub_of_str name1, \<open>_\<close>, name3, \<open>_\<close>, name2])
      (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l var_p = \<open>p\<close> in
       List_map
         (\<lambda>x. Expr_apply \<open>cp\<close> [x])
         [ Expr_basic [var_p]
         , Expr_lam \<open>x\<close>
             (\<lambda>var_x. Expr_warning_parenthesis (Expr_postunary
               (Expr_annot_ocl (Expr_apply var_p [Expr_annot_ocl (Expr_basic [var_x]) name3]) name2)
               (Expr_basic [dot_astype name1])))])
      []
      (Tacl_by [Tac_rule (Thm_str \<open>cpI1\<close>), if check_opt name1 name2 then Tac_simp
                                             else Tac_simp_add [flatten [const_oclastype, isub_of_str name1, \<open>_\<close>, name2]]])
  )) (\<lambda>x. (x, x, x))) expr"

definition "print_astype_lemmas_cp = start_map'
 (if activate_simp_optimization then List_map Thy_lemmas_simp o
  (\<lambda>expr. [Lemmas_simp \<open>\<close> (get_hierarchy_map
  (\<lambda>name1 name2 name3.
      Thm_str (flatten [\<open>cp_\<close>, const_oclastype, isub_of_str name1, \<open>_\<close>, name3, \<open>_\<close>, name2]))
  (\<lambda>x. (x, x, x)) expr)])
  else (\<lambda>_. []))"

definition "print_astype_lemma_strict expr = (start_map Thy_lemma_by o
 get_hierarchy_map (
  let check_opt =
    let set = print_astype_lemma_cp_set expr in
    (\<lambda>n1 n2. list_ex (\<lambda>((_, name1), name2). name1 = n1 & name2 = n2) set) in
  (\<lambda>name1 name2 name3.
    Lemma_by
      (flatten [const_oclastype, isub_of_str name1, \<open>_\<close>, name3, \<open>_\<close>, name2])
      [ Expr_rewrite
             (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot_ocl (Expr_basic [name2]) name3)
               (Expr_basic [dot_astype name1])))
             \<open>=\<close>
             (Expr_basic [name2])]
      []
      (Tacl_by (if check_opt name1 name3 then [Tac_simp]
                else [Tac_rule (Thm_str \<open>ext\<close>)
                                      , Tac_simp_add (flatten [const_oclastype, isub_of_str name1, \<open>_\<close>, name3]
                                                      # hol_definition \<open>bot_option\<close>
                                                      # List_map hol_definition (if name2 = \<open>invalid\<close> then [\<open>invalid\<close>]
                                                         else [\<open>null_fun\<close>,\<open>null_option\<close>]))]))
  )) (\<lambda>x. (x, [\<open>invalid\<close>,\<open>null\<close>], x))) expr"

definition "print_astype_lemmas_strict = start_map'
 (if activate_simp_optimization then List_map Thy_lemmas_simp o
  (\<lambda>expr. [ Lemmas_simp \<open>\<close> (get_hierarchy_map (\<lambda>name1 name2 name3.
        Thm_str (flatten [const_oclastype, isub_of_str name1, \<open>_\<close>, name3, \<open>_\<close>, name2])
      ) (\<lambda>x. (x, [\<open>invalid\<close>,\<open>null\<close>], x)) expr)])
  else (\<lambda>_. []))"

definition "print_astype_defined = start_m Thy_lemma_by m_class_default
  (\<lambda> compare (isub_name, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
     let var_X = \<open>X\<close>
       ; var_isdef = \<open>isdef\<close>
       ; f = \<lambda>e. Expr_binop (Expr_basic [\<open>\<tau>\<close>]) \<open>\<Turnstile>\<close> (Expr_apply \<open>\<delta>\<close> [e]) in
     case compare of LT \<Rightarrow>
        [ Lemma_by_assum
          (flatten [isub_name const_oclastype, \<open>_\<close>, h_name, \<open>_defined\<close>])
          [(var_isdef, False, f (Expr_basic [var_X]))]
          (f (Expr_postunary (Expr_annot_ocl (Expr_basic [var_X]) h_name) (Expr_basic [dot_astype name])))
          [App_using [Thm_str var_isdef]]
          (Tacl_by [Tac_auto_simp_add (flatten [isub_name const_oclastype, \<open>_\<close>, h_name]
                                        # \<open>foundation16\<close>
                                        # List_map hol_definition [\<open>null_option\<close>, \<open>bot_option\<close> ])]) ]
      | _ \<Rightarrow> [])"

definition "print_astype_up_d_cast0_name name_any name_pers = flatten [\<open>up\<close>, isub_of_str name_any, \<open>_down\<close>, isub_of_str name_pers, \<open>_cast0\<close>]"
definition "print_astype_up_d_cast0 = start_map Thy_lemma_by o
  map_class_nupl2'_inh (\<lambda>name_pers name_any.
    let var_X = \<open>X\<close>
      ; var_isdef = \<open>isdef\<close>
      ; f = Expr_binop (Expr_basic [\<open>\<tau>\<close>]) \<open>\<Turnstile>\<close> in
    Lemma_by_assum
        (print_astype_up_d_cast0_name name_any name_pers)
        [(var_isdef, False, f (Expr_apply \<open>\<delta>\<close> [Expr_basic [var_X]]))]
        (f (Expr_binop
             (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l asty = \<lambda>x ty. Expr_warning_parenthesis (Expr_postunary x (Expr_basic [dot_astype ty])) in
              asty (asty (Expr_annot_ocl (Expr_basic [var_X]) name_pers) name_any) name_pers)
             \<open>\<triangleq>\<close> (Expr_basic [var_X])))
        [App_using [Thm_str var_isdef]]
        (Tacl_by [Tac_auto_simp_add_split
                                    (List_map Thm_str
                                    ( flatten [const_oclastype, isub_of_str name_any, \<open>_\<close>, name_pers]
                                    # flatten [const_oclastype, isub_of_str name_pers, \<open>_\<close>, name_any]
                                    # \<open>foundation22\<close>
                                    # \<open>foundation16\<close>
                                    # List_map hol_definition [\<open>null_option\<close>, \<open>bot_option\<close> ]))
                                    (split_ty name_pers) ]))"

definition "print_astype_up_d_cast_name name_any name_pers = flatten [\<open>up\<close>, isub_of_str name_any, \<open>_down\<close>, isub_of_str name_pers, \<open>_cast\<close>]"
definition "print_astype_up_d_cast = start_map Thy_lemma_by o
  map_class_nupl2'_inh (\<lambda>name_pers name_any.
    let var_X = \<open>X\<close>
      ; var_tau = \<open>\<tau>\<close> in
    Lemma_by_assum
        (flatten [\<open>up\<close>, isub_of_str name_any, \<open>_down\<close>, isub_of_str name_pers, \<open>_cast\<close>])
        []
        (Expr_binop
             (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l asty = \<lambda>x ty. Expr_warning_parenthesis (Expr_postunary x (Expr_basic [dot_astype ty])) in
              asty (asty (Expr_annot_ocl (Expr_basic [var_X]) name_pers) name_any) name_pers)
             \<open>=\<close> (Expr_basic [var_X]))
        (List_map App
          [[Tac_rule (Thm_str \<open>ext\<close>), Tac_rename_tac [var_tau]]
          ,[Tac_rule (Thm_THEN (Thm_str \<open>foundation22\<close>) (Thm_str \<open>iffD1\<close>))]
          ,[Tac_case_tac (Expr_binop (Expr_basic [var_tau]) \<open>\<Turnstile>\<close>
              (Expr_apply \<open>\<delta>\<close> [Expr_basic [var_X]])), Tac_simp_add [print_astype_up_d_cast0_name name_any name_pers]]
          ,[Tac_simp_add [\<open>defined_split\<close>], Tac_elim (Thm_str \<open>disjE\<close>)]
          ,[Tac_plus [Tac_erule (Thm_str \<open>StrongEq_L_subst2_rev\<close>), Tac_simp, Tac_simp]]])
        Tacl_done)"

definition "print_astype_d_up_cast = start_map Thy_lemma_by o
  map_class_nupl2'_inh (\<lambda>name_pers name_any.
    let var_X = \<open>X\<close>
      ; var_Y = \<open>Y\<close>
      ; a = \<lambda>f x. Expr_apply f [x]
      ; b = \<lambda>s. Expr_basic [s]
      ; var_tau = \<open>\<tau>\<close>
      ; f_tau = \<lambda>s. Expr_warning_parenthesis (Expr_binop (b var_tau) \<open>\<Turnstile>\<close> (Expr_warning_parenthesis s))
      ; var_def_X = \<open>def_X\<close>
      ; asty = \<lambda>x ty. Expr_warning_parenthesis (Expr_postunary x (Expr_basic [dot_astype ty]))
      ; not_val = a \<open>not\<close> (a \<open>\<upsilon>\<close> (b var_X)) in
    Lemma_by_assum
      (flatten [\<open>down\<close>, isub_of_str name_pers, \<open>_up\<close>, isub_of_str name_any, \<open>_cast\<close>])
      [(var_def_X, False, Expr_binop
             (Expr_basic [var_X])
             \<open>=\<close>
             (asty (Expr_annot_ocl (Expr_basic [var_Y]) name_pers) name_any))]
      (f_tau (Expr_binop not_val \<open>or\<close>
               (Expr_binop
                 (asty (asty (Expr_basic [var_X]) name_pers) name_any)
                 \<open>\<doteq>\<close>
                 (b var_X))))
      (List_map App
        [[Tac_case_tac (f_tau not_val), Tac_rule (Thm_str \<open>foundation25\<close>), Tac_simp]])
      (Tacl_by [ Tac_rule (Thm_str \<open>foundation25'\<close>)
               , Tac_simp_add [ var_def_X
                              , print_astype_up_d_cast_name name_any name_pers
                              , \<open>StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym\<close>]]) )"

end
