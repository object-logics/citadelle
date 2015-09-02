(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_floor1_istypeof.thy ---
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

theory  OCL_compiler_floor1_istypeof
imports OCL_compiler_core_init
begin

section{* Translation of AST *}

subsection{* IsTypeOf *}
definition "print_istypeof_consts = start_map Thy_consts_class o
  map_class (\<lambda>isub_name name _ _ _ _.
    Consts' (isub_name const_oclistypeof) (Ty_base ty_boolean) (const_mixfix dot_oclistypeof name))"

definition "print_istypeof_class = start_m_gen Thy_defs_overloaded m_class_default
  (\<lambda> l_inh _ _ compare (isub_name, name, _). \<lambda> OclClass h_name hl_attr h_last \<Rightarrow>
   [Defs_overloaded
          (flatten [isub_name const_oclistypeof, \<open>_\<close>, h_name])
          (let var_x = \<open>x\<close> in
           Expr_rewrite
             (Expr_postunary (Expr_annot_ocl (Expr_basic [var_x]) h_name) (Expr_basic [dot_istypeof name]))
             \<open>\<equiv>\<close>
             (Expr_lam \<open>\<tau>\<close>
                  (\<lambda>var_tau. let ocl_tau = (\<lambda>v. Expr_app v [Expr_basic [var_tau]]) in
                  Expr_case
                    (ocl_tau var_x)
                    ( (Expr_basic [\<open>\<bottom>\<close>], ocl_tau \<open>invalid\<close>)
                    # (Expr_some (Expr_basic [\<open>\<bottom>\<close>]), ocl_tau \<open>true\<close>)
                    # (let l_false = [(Expr_basic [wildcard], ocl_tau \<open>false\<close>)]
                         ; pattern_complex_gen = (\<lambda>f1 f2.
                            let isub_h = (\<lambda> s. s @@ isub_of_str h_name) in
                             (Expr_some (Expr_some
                               (Expr_app (isub_h datatype_constr_name)
                                           ( Expr_app (f2 (\<lambda>s. isub_name (s @@ \<open>_\<close>)) (isub_h datatype_ext_constr_name))
                                                        (Expr_basic [wildcard] # f1)
                                           # List_map (\<lambda>_. Expr_basic [wildcard]) hl_attr))), ocl_tau \<open>true\<close>)
                             # (if h_last = [] then [] else l_false)) in
                       case compare
                       of EQ \<Rightarrow> pattern_complex_gen (List_flatten (List_map (List_map (\<lambda>_. Expr_basic [wildcard]) o (\<lambda> OclClass _ l _ \<Rightarrow> l)) (of_linh l_inh))) (\<lambda>_. id)
                        | GT \<Rightarrow> pattern_complex_gen [] id
                        | _ \<Rightarrow> l_false) ) )))] )"

definition "print_istypeof_from_universe = start_m Thy_definition_hol
  (\<lambda> name _ _ l.
    let const_istypeof = flatten [const_oclistypeof, isub_of_str name, \<open>_\<AA>\<close>] in
    [ Definition (Expr_rewrite (Expr_basic [const_istypeof]) \<open>=\<close> (Expr_function l))])
  (\<lambda>_ (_, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
     let isub_h = (\<lambda> s. s @@ isub_of_str h_name) in
     [( Expr_app (isub_h datatype_in) [Expr_basic [h_name]]
      , Expr_warning_parenthesis
        (Expr_postunary (Expr_annot_ocl (Expr_applys Expr_basety [Expr_basic [h_name]])
                                    h_name)
                        (Expr_basic [dot_istypeof name])))])"

definition "print_istypeof_lemma_cp_set =
  (if activate_simp_optimization then
    map_class (\<lambda>isub_name name _ _ _ _. ((isub_name, name), name))
   else (\<lambda>_. []))"

definition "print_istypeof_lemmas_id = start_map' (\<lambda>expr.
  (let name_set = print_istypeof_lemma_cp_set expr in
   case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
  [ Lemmas_simp \<open>\<close> (List_map (\<lambda>((isub_name, _), name).
    Thm_thm (flatten [isub_name const_oclistypeof, \<open>_\<close>, name] )) name_set) ]))"

definition "print_istypeof_lemma_cp expr = (start_map Thy_lemma_by o
  (get_hierarchy_map (
  let check_opt =
    let set = print_istypeof_lemma_cp_set expr in
    (\<lambda>n1 n2. list_ex (\<lambda>((_, name1), name2). name1 = n1 & name2 = n2) set) in
  (\<lambda>name1 name2 name3.
    Lemma
      (flatten [\<open>cp_\<close>, const_oclistypeof, isub_of_str name1, \<open>_\<close>, name3, \<open>_\<close>, name2])
      (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l var_p = \<open>p\<close> in
       List_map
         (\<lambda>x. Expr_app \<open>cp\<close> [x])
         [ Expr_basic [var_p]
         , Expr_lam \<open>x\<close>
             (\<lambda>var_x. Expr_warning_parenthesis (Expr_postunary
               (Expr_annot_ocl (Expr_app var_p [Expr_annot_ocl (Expr_basic [var_x]) name3]) name2)
               (Expr_basic [dot_istypeof name1])))])
      []
      (C.by [M.rule (Thm_thm \<open>cpI1\<close>), if check_opt name1 name2 then M.simp
                                             else M.simp_add [flatten [const_oclistypeof, isub_of_str name1, \<open>_\<close>, name2]]])
  )) (\<lambda>x. (x, x, x))) ) expr"

definition "print_istypeof_lemmas_cp = start_map'
 (if activate_simp_optimization then List_map Thy_lemmas_simp o
    (\<lambda>expr. [Lemmas_simp \<open>\<close>
  (get_hierarchy_map (\<lambda>name1 name2 name3.
      Thm_thm (flatten [\<open>cp_\<close>, const_oclistypeof, isub_of_str name1, \<open>_\<close>, name3, \<open>_\<close>, name2]))
   (\<lambda>x. (x, x, x)) expr)])
  else (\<lambda>_. []))"

definition "print_istypeof_lemma_strict expr = (start_map Thy_lemma_by o
  get_hierarchy_map (
  let check_opt =
    let set = print_istypeof_lemma_cp_set expr in
    (\<lambda>n1 n2. list_ex (\<lambda>((_, name1), name2). name1 = n1 & name2 = n2) set) in
  (\<lambda>name1 (name2,name2') name3.
    Lemma
      (flatten [const_oclistypeof, isub_of_str name1, \<open>_\<close>, name3, \<open>_\<close>, name2])
      [ Expr_rewrite
             (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot_ocl (Expr_basic [name2]) name3)
               (Expr_basic [dot_istypeof name1])))
             \<open>=\<close>
             (Expr_basic [name2'])]
      []
      (C.by (let l = List_map hol_definition (\<open>bot_option\<close> # (if name2 = \<open>invalid\<close> then [\<open>invalid\<close>]
                                                              else [\<open>null_fun\<close>,\<open>null_option\<close>])) in
                [M.rule (Thm_thm \<open>ext\<close>), M.simp_add (if check_opt name1 name3 then l
                                                           else flatten [const_oclistypeof, isub_of_str name1, \<open>_\<close>, name3] # l)]))
  )) (\<lambda>x. (x, [(\<open>invalid\<close>,\<open>invalid\<close>),(\<open>null\<close>,\<open>true\<close>)], x))) expr"

definition "print_istypeof_lemmas_strict_set =
  (if activate_simp_optimization then
    get_hierarchy_map (\<lambda>name1 name2 name3. (name1, name3, name2)) (\<lambda>x. (x, [\<open>invalid\<close>,\<open>null\<close>], x))
   else (\<lambda>_. []))"

definition "print_istypeof_lemmas_strict expr = start_map Thy_lemmas_simp
  (case print_istypeof_lemmas_strict_set expr
   of [] \<Rightarrow> []
    | l \<Rightarrow> [ Lemmas_simp \<open>\<close> (List_map
      (\<lambda>(name1, name3, name2).
        Thm_thm (flatten [const_oclistypeof, isub_of_str name1, \<open>_\<close>, name3, \<open>_\<close>, name2]))
      l) ])"

definition "print_istypeof_defined = start_m Thy_lemma_by m_class_default
  (\<lambda> _ (isub_name, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
      let var_X = \<open>X\<close>
        ; var_isdef = \<open>isdef\<close>
        ; f = \<lambda>symb e. Expr_binop (Expr_basic [\<open>\<tau>\<close>]) \<open>\<Turnstile>\<close> (Expr_app symb [e]) in
      [ Lemma_assumes
          (print_istypeof_defined_name isub_name h_name)
          [(var_isdef, False, f \<open>\<upsilon>\<close> (Expr_basic [var_X]))]
          (f \<open>\<delta>\<close> (Expr_postunary (Expr_annot_ocl (Expr_basic [var_X]) h_name) (Expr_basic [dot_istypeof name])))
          [C.apply [M.insert' [Thm_simplified (Thm_thm var_isdef) (Thm_thm \<open>foundation18'\<close>) ]
               ,M.simp_only [Thm_thm (hol_definition \<open>OclValid\<close>)]
               ,M.subst (Thm_thm \<open>cp_defined\<close>)]]
          (C.by [M.auto_simp_add_split ( Thm_symmetric (Thm_thm \<open>cp_defined\<close>)
                                            # List_map Thm_thm ( hol_definition \<open>bot_option\<close>
                                                          # [ flatten [isub_name const_oclistypeof, \<open>_\<close>, h_name] ]))
                                            (\<open>option.split\<close> # split_ty h_name) ]) ])"

definition "print_istypeof_defined' = start_m Thy_lemma_by m_class_default
  (\<lambda> _ (isub_name, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
      let var_X = \<open>X\<close>
        ; var_isdef = \<open>isdef\<close>
        ; f = \<lambda>e. Expr_binop (Expr_basic [\<open>\<tau>\<close>]) \<open>\<Turnstile>\<close> (Expr_app \<open>\<delta>\<close> [e]) in
      [ Lemma_assumes
          (print_istypeof_defined'_name isub_name h_name)
          [(var_isdef, False, f (Expr_basic [var_X]))]
          (f (Expr_postunary (Expr_annot_ocl (Expr_basic [var_X]) h_name) (Expr_basic [dot_istypeof name])))
          []
          (C.by [M.rule (Thm_OF (Thm_thm (print_istypeof_defined_name isub_name h_name))
                                     (Thm_THEN (Thm_thm var_isdef) (Thm_thm \<open>foundation20\<close>)))]) ])"

definition "print_istypeof_up_larger_name name_pers name_any = flatten [\<open>actualType\<close>, isub_of_str name_pers, \<open>_larger_staticType\<close>, isub_of_str name_any]"
definition "print_istypeof_up_larger = start_map Thy_lemma_by o
  map_class_nupl2'_inh_large (\<lambda>name_pers name_any.
    let var_X = \<open>X\<close>
      ; var_isdef = \<open>isdef\<close>
      ; f = Expr_binop (Expr_basic [\<open>\<tau>\<close>]) \<open>\<Turnstile>\<close> in
    Lemma_assumes
        (print_istypeof_up_larger_name name_pers name_any)
        [(var_isdef, False, f (Expr_app \<open>\<delta>\<close> [Expr_basic [var_X]]))]
        (f (Expr_binop (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot_ocl (Expr_basic [var_X]) name_pers)
               (Expr_basic [dot_istypeof name_any]))
             ) \<open>\<triangleq>\<close> (Expr_basic [\<open>false\<close>])))
        [C.using [Thm_thm var_isdef]]
        (C.by [M.auto_simp_add ( flatten [const_oclistypeof, isub_of_str name_any, \<open>_\<close>, name_pers]
                                    # \<open>foundation22\<close>
                                    # \<open>foundation16\<close>
                                    # List_map hol_definition [\<open>null_option\<close>, \<open>bot_option\<close> ])]))"

definition "print_istypeof_up_d_cast expr = (start_map Thy_lemma_by o
  map_class_nupl3'_GE_inh (\<lambda>name_pers name_mid name_any.
    let var_X = \<open>X\<close>
      ; var_istyp = \<open>istyp\<close>
      ; var_isdef = \<open>isdef\<close>
      ; f = Expr_binop (Expr_basic [\<open>\<tau>\<close>]) \<open>\<Turnstile>\<close> in
    Lemma_assumes
        (print_istypeof_up_d_cast_name name_mid name_any name_pers)
        [(var_istyp, False, f (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot_ocl (Expr_basic [var_X]) name_any)
               (Expr_basic [dot_istypeof name_mid]))))
        ,(var_isdef, False, f (Expr_app \<open>\<delta>\<close> [Expr_basic [var_X]]))]
        (f (Expr_binop (Expr_warning_parenthesis (Expr_postunary
               (Expr_basic [var_X])
               (Expr_basic [dot_astype name_pers]))
             ) \<open>\<triangleq>\<close> (Expr_basic [\<open>invalid\<close>])))
        [C.using (List_map Thm_thm [var_istyp, var_isdef])
        ,C.apply [M.auto_simp_add_split (List_map Thm_thm
                                      ( flatten [const_oclastype, isub_of_str name_pers, \<open>_\<close>, name_any]
                                      # \<open>foundation22\<close>
                                      # \<open>foundation16\<close>
                                      # List_map hol_definition [\<open>null_option\<close>, \<open>bot_option\<close> ]))
                                      (split_ty name_any) ]]
        (C.by [M.simp_add (let l = List_map hol_definition [\<open>OclValid\<close>, \<open>false\<close>, \<open>true\<close>] in
                                if name_mid = name_any & ~(print_istypeof_lemma_cp_set expr = []) then
                                  l
                                else
                                  flatten [const_oclistypeof, isub_of_str name_mid, \<open>_\<close>, name_any] # l)]))) expr"

end
