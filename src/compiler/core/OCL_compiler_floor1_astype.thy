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
    Consts (isub_name const_oclastype) (Ty_base name) (const_mixfix dot_oclastype name))"

definition "print_astype_class = start_m' Thy_defs_overloaded
  (\<lambda> compare (isub_name, name, nl_attr). \<lambda> OclClass h_name hl_attr _ \<Rightarrow>
    Defs_overloaded
          (flatten [isub_name const_oclastype, \<langle>''_''\<rangle>, h_name])
          (let var_x = \<langle>''x''\<rangle> in
           Expr_rewrite
             (Expr_postunary (Expr_annot (Expr_basic [var_x]) h_name) (Expr_basic [dot_astype name]))
             unicode_equiv
             (case compare
              of EQ \<Rightarrow>
                Expr_basic [var_x]
              | x \<Rightarrow>
                Expr_lam unicode_tau
                  (\<lambda>var_tau. let val_invalid = Expr_apply \<langle>''invalid''\<rangle> [Expr_basic [var_tau]] in
                  Expr_case
                    (Expr_apply var_x [Expr_basic [var_tau]])
                    ( (Expr_basic [unicode_bottom], val_invalid)
                    # (Expr_some (Expr_basic [unicode_bottom]), Expr_apply \<langle>''null''\<rangle> [Expr_basic [var_tau]])
                    # (let pattern_complex = (\<lambda>h_name name l_extra.
                            let isub_h = (\<lambda> s. s @@ isub_of_str h_name)
                              ; isub_name = (\<lambda>s. s @@ isub_of_str name)
                              ; isub_n = (\<lambda>s. isub_name (s @@ \<langle>''_''\<rangle>))
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
                         [ (some_some (pattern_simple h_name), some_some (pattern_complex name h_name (List_map (\<lambda>_. Expr_basic [\<langle>''None''\<rangle>]) nl_attr))) ]
                       else
                         let l = [(Expr_basic [wildcard], val_invalid)] in
                         if x = GT then
                           (some_some (pattern_complex h_name name (List_map (\<lambda>_. Expr_basic [wildcard]) hl_attr)), some_some (pattern_simple name))
                           # l
                         else l) ) ))))"

definition "print_astype_from_universe =
 (let f_finish = (\<lambda> [] \<Rightarrow> ((id, Expr_binop (Expr_basic [\<langle>''Some''\<rangle>]) \<langle>''o''\<rangle>), [])
                  | _ \<Rightarrow> ((Expr_some, id), [(Expr_basic [wildcard], Expr_basic [\<langle>''None''\<rangle>])])) in
  start_m_gen Thy_definition_hol
  (\<lambda> name l_inh _ l.
    let const_astype = print_astype_from_universe_name name in
    [ Definition (Expr_rewrite (Expr_basic [const_astype]) \<langle>''=''\<rangle>
        (case f_finish l_inh of ((_, finish_with_some2), last_case_none) \<Rightarrow>
          finish_with_some2 (Expr_function (flatten [l, last_case_none]))))])
  (\<lambda> l_inh _ _ compare (_, name, nl_attr). \<lambda> OclClass h_name hl_attr _ \<Rightarrow>
     if compare = UN' then [] else
     let ((finish_with_some1, _), _) = f_finish l_inh
       ; isub_h = (\<lambda> s. s @@ isub_of_str h_name)
       ; pattern_complex = (\<lambda>h_name name l_extra.
                            let isub_h = (\<lambda> s. s @@ isub_of_str h_name)
                              ; isub_name = (\<lambda>s. s @@ isub_of_str name)
                              ; isub_n = (\<lambda>s. isub_name (s @@ \<langle>''_''\<rangle>))
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
              | LT \<Rightarrow> case_branch (pattern_simple h_name) (pattern_complex name h_name (List_map (\<lambda>_. Expr_basic [\<langle>''None''\<rangle>]) nl_attr))))"

definition "print_astype_lemma_cp_set =
  (if activate_simp_optimization then
    map_class (\<lambda>isub_name name _ _ _ _. ((isub_name, name), name))
   else (\<lambda>_. []))"

definition "print_astype_lemmas_id = start_map' (\<lambda>expr.
  (let name_set = print_astype_lemma_cp_set expr in
   case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
  [ Lemmas_simp \<langle>''''\<rangle> (List_map (\<lambda>((isub_name, _), name).
    Thm_str (flatten [isub_name const_oclastype, \<langle>''_''\<rangle>, name])) name_set) ]))"

definition "print_astype_lemma_cp_set2 =
  (if activate_simp_optimization then
     \<lambda>expr base_attr.
       flatten (m_class' base_attr (\<lambda> compare (isub_name, name, _). \<lambda> OclClass name2 _ _ \<Rightarrow>
         if compare = EQ then
           []
         else
           [((isub_name, name), ((\<lambda>s. s @@ isub_of_str name2), name2))]) expr)
   else (\<lambda>_ _. []))"

definition "print_astype_lemmas_id2 = start_map'' id o (\<lambda>expr base_attr _ _.
  (let name_set = print_astype_lemma_cp_set2 expr base_attr in
   case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
  [ Lemmas_simp \<langle>''''\<rangle> (List_map (\<lambda>((isub_name_h, _), (_, name)).
    Thm_str (flatten [isub_name_h const_oclastype, \<langle>''_''\<rangle>, name])) name_set) ]))"

definition "print_astype_lemma_cp expr = (start_map Thy_lemma_by o get_hierarchy_map (
  let check_opt =
    let set = print_astype_lemma_cp_set expr in
    (\<lambda>n1 n2. list_ex (\<lambda>((_, name1), name2). name1 = n1 & name2 = n2) set) in
  (\<lambda>name1 name2 name3.
    Lemma_by
      (flatten [\<langle>''cp_''\<rangle>, const_oclastype, isub_of_str name1, \<langle>''_''\<rangle>, name3, \<langle>''_''\<rangle>, name2])
      (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l var_p = \<langle>''p''\<rangle> in
       List_map
         (\<lambda>x. Expr_apply \<langle>''cp''\<rangle> [x])
         [ Expr_basic [var_p]
         , Expr_lam \<langle>''x''\<rangle>
             (\<lambda>var_x. Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_apply var_p [Expr_annot (Expr_basic [var_x]) name3]) name2)
               (Expr_basic [dot_astype name1])))])
      []
      (Tacl_by [Tac_rule (Thm_str \<langle>''cpI1''\<rangle>), if check_opt name1 name2 then Tac_simp
                                             else Tac_simp_add [flatten [const_oclastype, isub_of_str name1, \<langle>''_''\<rangle>, name2]]])
  )) (\<lambda>x. (x, x, x))) expr"

definition "print_astype_lemmas_cp = start_map'
 (if activate_simp_optimization then List_map Thy_lemmas_simp o
  (\<lambda>expr. [Lemmas_simp \<langle>''''\<rangle> (get_hierarchy_map
  (\<lambda>name1 name2 name3.
      Thm_str (flatten [\<langle>''cp_''\<rangle>, const_oclastype, isub_of_str name1, \<langle>''_''\<rangle>, name3, \<langle>''_''\<rangle>, name2]))
  (\<lambda>x. (x, x, x)) expr)])
  else (\<lambda>_. []))"

definition "print_astype_lemma_strict expr = (start_map Thy_lemma_by o
 get_hierarchy_map (
  let check_opt =
    let set = print_astype_lemma_cp_set expr in
    (\<lambda>n1 n2. list_ex (\<lambda>((_, name1), name2). name1 = n1 & name2 = n2) set) in
  (\<lambda>name1 name2 name3.
    Lemma_by
      (flatten [const_oclastype, isub_of_str name1, \<langle>''_''\<rangle>, name3, \<langle>''_''\<rangle>, name2])
      [ Expr_rewrite
             (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [name2]) name3)
               (Expr_basic [dot_astype name1])))
             \<langle>''=''\<rangle>
             (Expr_basic [name2])]
      []
      (Tacl_by (if check_opt name1 name3 then [Tac_simp]
                else [Tac_rule (Thm_str \<langle>''ext''\<rangle>)
                                      , Tac_simp_add (flatten [const_oclastype, isub_of_str name1, \<langle>''_''\<rangle>, name3]
                                                      # hol_definition \<langle>''bot_option''\<rangle>
                                                      # List_map hol_definition (if name2 = \<langle>''invalid''\<rangle> then [\<langle>''invalid''\<rangle>]
                                                         else [\<langle>''null_fun''\<rangle>,\<langle>''null_option''\<rangle>]))]))
  )) (\<lambda>x. (x, [\<langle>''invalid''\<rangle>,\<langle>''null''\<rangle>], x))) expr"

definition "print_astype_lemmas_strict = start_map'
 (if activate_simp_optimization then List_map Thy_lemmas_simp o
  (\<lambda>expr. [ Lemmas_simp \<langle>''''\<rangle> (get_hierarchy_map (\<lambda>name1 name2 name3.
        Thm_str (flatten [const_oclastype, isub_of_str name1, \<langle>''_''\<rangle>, name3, \<langle>''_''\<rangle>, name2])
      ) (\<lambda>x. (x, [\<langle>''invalid''\<rangle>,\<langle>''null''\<rangle>], x)) expr)])
  else (\<lambda>_. []))"

definition "print_astype_defined = start_m Thy_lemma_by m_class_default
  (\<lambda> compare (isub_name, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
     let var_X = \<langle>''X''\<rangle>
       ; var_isdef = \<langle>''isdef''\<rangle>
       ; f = \<lambda>e. Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile (Expr_apply unicode_delta [e]) in
     case compare of LT \<Rightarrow>
        [ Lemma_by_assum
          (flatten [isub_name const_oclastype, \<langle>''_''\<rangle>, h_name, \<langle>''_defined''\<rangle>])
          [(var_isdef, False, f (Expr_basic [var_X]))]
          (f (Expr_postunary (Expr_annot (Expr_basic [var_X]) h_name) (Expr_basic [dot_astype name])))
          [App_using [Thm_str var_isdef]]
          (Tacl_by [Tac_auto_simp_add (flatten [isub_name const_oclastype, \<langle>''_''\<rangle>, h_name]
                                        # \<langle>''foundation16''\<rangle>
                                        # List_map hol_definition [\<langle>''null_option''\<rangle>, \<langle>''bot_option''\<rangle> ])]) ]
      | _ \<Rightarrow> [])"

definition "print_astype_up_d_cast0_name name_any name_pers = flatten [\<langle>''up''\<rangle>, isub_of_str name_any, \<langle>''_down''\<rangle>, isub_of_str name_pers, \<langle>''_cast0''\<rangle>]"
definition "print_astype_up_d_cast0 = start_map Thy_lemma_by o
  map_class_nupl2'_inh (\<lambda>name_pers name_any.
    let var_X = \<langle>''X''\<rangle>
      ; var_isdef = \<langle>''isdef''\<rangle>
      ; f = Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile in
    Lemma_by_assum
        (print_astype_up_d_cast0_name name_any name_pers)
        [(var_isdef, False, f (Expr_apply unicode_delta [Expr_basic [var_X]]))]
        (f (Expr_binop
             (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l asty = \<lambda>x ty. Expr_warning_parenthesis (Expr_postunary x (Expr_basic [dot_astype ty])) in
              asty (asty (Expr_annot (Expr_basic [var_X]) name_pers) name_any) name_pers)
             unicode_triangleq (Expr_basic [var_X])))
        [App_using [Thm_str var_isdef]]
        (Tacl_by [Tac_auto_simp_add_split
                                    (List_map Thm_str
                                    ( flatten [const_oclastype, isub_of_str name_any, \<langle>''_''\<rangle>, name_pers]
                                    # flatten [const_oclastype, isub_of_str name_pers, \<langle>''_''\<rangle>, name_any]
                                    # \<langle>''foundation22''\<rangle>
                                    # \<langle>''foundation16''\<rangle>
                                    # List_map hol_definition [\<langle>''null_option''\<rangle>, \<langle>''bot_option''\<rangle> ]))
                                    (split_ty name_pers) ]))"

definition "print_astype_up_d_cast_name name_any name_pers = flatten [\<langle>''up''\<rangle>, isub_of_str name_any, \<langle>''_down''\<rangle>, isub_of_str name_pers, \<langle>''_cast''\<rangle>]"
definition "print_astype_up_d_cast = start_map Thy_lemma_by o
  map_class_nupl2'_inh (\<lambda>name_pers name_any.
    let var_X = \<langle>''X''\<rangle>
      ; var_tau = unicode_tau in
    Lemma_by_assum
        (flatten [\<langle>''up''\<rangle>, isub_of_str name_any, \<langle>''_down''\<rangle>, isub_of_str name_pers, \<langle>''_cast''\<rangle>])
        []
        (Expr_binop
             (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l asty = \<lambda>x ty. Expr_warning_parenthesis (Expr_postunary x (Expr_basic [dot_astype ty])) in
              asty (asty (Expr_annot (Expr_basic [var_X]) name_pers) name_any) name_pers)
             \<langle>''=''\<rangle> (Expr_basic [var_X]))
        (List_map App
          [[Tac_rule (Thm_str \<langle>''ext''\<rangle>), Tac_rename_tac [var_tau]]
          ,[Tac_rule (Thm_THEN (Thm_str \<langle>''foundation22''\<rangle>) (Thm_str \<langle>''iffD1''\<rangle>))]
          ,[Tac_case_tac (Expr_binop (Expr_basic [var_tau]) unicode_Turnstile
              (Expr_apply unicode_delta [Expr_basic [var_X]])), Tac_simp_add [print_astype_up_d_cast0_name name_any name_pers]]
          ,[Tac_simp_add [\<langle>''defined_split''\<rangle>], Tac_elim (Thm_str \<langle>''disjE''\<rangle>)]
          ,[Tac_plus [Tac_erule (Thm_str \<langle>''StrongEq_L_subst2_rev''\<rangle>), Tac_simp, Tac_simp]]])
        Tacl_done)"

definition "print_astype_d_up_cast = start_map Thy_lemma_by o
  map_class_nupl2'_inh (\<lambda>name_pers name_any.
    let var_X = \<langle>''X''\<rangle>
      ; var_Y = \<langle>''Y''\<rangle>
      ; a = \<lambda>f x. Expr_apply f [x]
      ; b = \<lambda>s. Expr_basic [s]
      ; var_tau = unicode_tau
      ; f_tau = \<lambda>s. Expr_warning_parenthesis (Expr_binop (b var_tau) unicode_Turnstile (Expr_warning_parenthesis s))
      ; var_def_X = \<langle>''def_X''\<rangle>
      ; asty = \<lambda>x ty. Expr_warning_parenthesis (Expr_postunary x (Expr_basic [dot_astype ty]))
      ; not_val = a \<langle>''not''\<rangle> (a unicode_upsilon (b var_X)) in
    Lemma_by_assum
      (flatten [\<langle>''down''\<rangle>, isub_of_str name_pers, \<langle>''_up''\<rangle>, isub_of_str name_any, \<langle>''_cast''\<rangle>])
      [(var_def_X, False, Expr_binop
             (Expr_basic [var_X])
             \<langle>''=''\<rangle>
             (asty (Expr_annot (Expr_basic [var_Y]) name_pers) name_any))]
      (f_tau (Expr_binop not_val \<langle>''or''\<rangle>
               (Expr_binop
                 (asty (asty (Expr_basic [var_X]) name_pers) name_any)
                 unicode_doteq
                 (b var_X))))
      (List_map App
        [[Tac_case_tac (f_tau not_val), Tac_rule (Thm_str \<langle>''foundation25''\<rangle>), Tac_simp]])
      (Tacl_by [ Tac_rule (Thm_str (flatten [\<langle>''foundation25''\<rangle>, [Char Nibble2 Nibble7]]))
               , Tac_simp_add [ var_def_X
                              , print_astype_up_d_cast_name name_any name_pers
                              , flatten [\<langle>''StrictRefEq''\<rangle>, isub_of_str \<langle>''Object''\<rangle>, \<langle>''_sym''\<rangle>]]]) )"

end
