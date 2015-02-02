(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_floor1_iskindof.thy ---
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

theory  OCL_compiler_floor1_iskindof
imports OCL_compiler_core_init
begin

section{* Translation of AST *}

subsection{* IsKindOf *}

definition "print_iskindof_consts = start_map Thy_consts_class o
  map_class (\<lambda>isub_name name _ _ _ _.
    Consts (isub_name const_ocliskindof) (Ty_base ty_boolean) (const_mixfix dot_ocliskindof name))"

definition "print_iskindof_class_name isub_name h_name = flatten [isub_name const_ocliskindof, \<open>_\<close>, h_name]"
definition "print_iskindof_class = start_m_gen Thy_defs_overloaded m_class_default
  (\<lambda> _ _ next_dataty _ (isub_name, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
    [ Defs_overloaded
          (print_iskindof_class_name isub_name h_name)
          (let var_x = \<open>x\<close> in
           Expr_rewrite
             (Expr_postunary (Expr_annot (Expr_basic [var_x]) h_name) (Expr_basic [dot_iskindof name]))
             unicode_equiv
             (let isof = (\<lambda>f name. Expr_warning_parenthesis (Expr_postunary (Expr_basic [var_x]) (Expr_basic [f name]))) in
              expr_binop \<open>or\<close> (isof dot_istypeof name # List_map (\<lambda> OclClass name_past _ _ \<Rightarrow> isof dot_iskindof name_past) next_dataty)))])"

definition "print_iskindof_from_universe = start_m Thy_definition_hol
  (\<lambda>name _ _ l.
    let const_iskindof = flatten [const_ocliskindof, isub_of_str name, \<open>_\<close>, unicode_AA] in
    [ Definition (Expr_rewrite (Expr_basic [const_iskindof]) \<open>=\<close> (Expr_function l)) ])
  (\<lambda> _ (_, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
    let isub_h = (\<lambda> s. s @@ isub_of_str h_name) in
    [ ( Expr_apply (isub_h datatype_in) [Expr_basic [h_name]]
      , Expr_warning_parenthesis
        (Expr_postunary (Expr_annot (Expr_applys Expr_basety [Expr_basic [h_name]])
                                    h_name)
                        (Expr_basic [dot_iskindof name])))])"

definition "print_iskindof_lemma_cp_set =
  (if activate_simp_optimization then
    map_class (\<lambda>isub_name name _ _ _ _. ((isub_name, name), name))
   else (\<lambda>_. []))"

definition "print_iskindof_lemmas_id = start_map' (\<lambda>expr.
  (let name_set = print_iskindof_lemma_cp_set expr in
   case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
  [ Lemmas_simp \<open>\<close> (List_map (\<lambda>((isub_name, _), name).
    Thm_str (flatten [isub_name const_ocliskindof, \<open>_\<close>, name] )) name_set) ]))"

definition "print_iskindof_lemma_cp = start_m'3_gen Thy_lemma_by
 (\<lambda> _ _ next_dataty name1 name2 name3.
    let lemma_name = flatten [\<open>cp_\<close>, const_ocliskindof, isub_of_str name1, \<open>_\<close>, name3, \<open>_\<close>, name2]
      ; lemma_spec = let var_p = \<open>p\<close> in
       List_map
         (\<lambda>x. Expr_apply \<open>cp\<close> [x])
         [ Expr_basic [var_p]
         , Expr_lam \<open>x\<close>
             (\<lambda>var_x. Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_apply var_p [Expr_annot (Expr_basic [var_x]) name3]) name2)
               (Expr_basic [dot_iskindof name1])))]
      ; lem_simp1 = Tac_simp_only [Thm_str (flatten [const_ocliskindof, isub_of_str name1, \<open>_\<close>, name2])]
      ; lem_simp2 = Tac_simp_only [Thm_str (flatten [\<open>cp_\<close>, const_oclistypeof, isub_of_str name1, \<open>_\<close>, name3, \<open>_\<close>, name2])] in
    let (tac1, tac2) =
      if next_dataty = [] then ([], Tacl_by [ lem_simp1 , lem_simp2 ])
      else
      ( [ [ lem_simp1 ]
        , [ Tac_plus
            [ Tac_rule (Thm_where (Thm_str \<open>cpI2\<close>) [(\<open>f\<close>, Expr_preunary (Expr_basic [\<open>op\<close>]) (Expr_basic [\<open>or\<close>]))])
            , Tac_plus [Tac_rule (Thm_str \<open>allI\<close>)]
            , Tac_rule (Thm_str \<open>cp_OclOr\<close>) ]]
        , [ lem_simp2 ] ]
      , Tacl_by (List_map
            (\<lambda> OclClass n _ _ \<Rightarrow> Tac_simp_only [Thm_str (flatten [\<open>cp_\<close>, const_ocliskindof, isub_of_str n, \<open>_\<close>, name3, \<open>_\<close>, name2])] )
            next_dataty))
    in Lemma_by lemma_name lemma_spec tac1 tac2)"

definition "print_iskindof_lemmas_cp = start_map'
 (if activate_simp_optimization then List_map Thy_lemmas_simp o
    (\<lambda>expr. [Lemmas_simp \<open>\<close>
  (get_hierarchy_map (\<lambda>name1 name2 name3.
      Thm_str (flatten [\<open>cp_\<close>, const_ocliskindof, isub_of_str name1, \<open>_\<close>, name3, \<open>_\<close>, name2])
  ) (\<lambda>x. (x, x, x)) expr)])
  else (\<lambda>_. []))"

definition "print_iskindof_lemma_strict = start_m_gen Thy_lemma_by m_class_default
 (\<lambda> _ _ next_dataty _ (_, name1, _). \<lambda> OclClass name3 _ _ \<Rightarrow>
  List_map (\<lambda>(name2, name2').
    Lemma_by
      (flatten [const_ocliskindof, isub_of_str name1, \<open>_\<close>, name3, \<open>_\<close>, name2])
      [ Expr_rewrite
             (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [name2]) name3)
               (Expr_basic [dot_iskindof name1])))
             \<open>=\<close>
             (Expr_basic [name2'])]
      []
      (Tacl_by
        (Tac_simp_only
           (List_map Thm_str (List_flatten
              [ [flatten [const_ocliskindof, isub_of_str name1, \<open>_\<close>, name3]]
              , [flatten [const_oclistypeof, isub_of_str name1, \<open>_\<close>, name3, \<open>_\<close>, name2]]
              , List_map
                  (\<lambda> OclClass n _ _ \<Rightarrow>
                    flatten [const_ocliskindof, isub_of_str n, \<open>_\<close>, name3, \<open>_\<close>, name2])
                  next_dataty ]))
        # (if next_dataty = [] then [] else [Tac_simp])) ))
    [(\<open>invalid\<close>,\<open>invalid\<close>),(\<open>null\<close>,\<open>true\<close>)])"

definition "print_iskindof_lemmas_strict = start_map'
 (if activate_simp_optimization then List_map Thy_lemmas_simp o
  (\<lambda>expr. [ Lemmas_simp \<open>\<close> (get_hierarchy_map (\<lambda>name1 name2 name3.
      Thm_str (flatten [const_ocliskindof, isub_of_str name1, \<open>_\<close>, name3, \<open>_\<close>, name2])
  ) (\<lambda>x. (x, [\<open>invalid\<close>,\<open>null\<close>], x)) expr)])
  else (\<lambda>_. []))"

definition "print_iskindof_defined_name isub_name h_name = flatten [isub_name const_ocliskindof, \<open>_\<close>, h_name, \<open>_defined\<close>]"
definition "print_iskindof_defined = start_m_gen Thy_lemma_by m_class_default
  (\<lambda> _ _ next_dataty _ (isub_name, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
      let var_X = \<open>X\<close>
        ; var_isdef = \<open>isdef\<close>
        ; f = \<lambda>symb e. Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile (Expr_apply symb [e]) in
      [ Lemma_by_assum
          (print_iskindof_defined_name isub_name h_name)
          [(var_isdef, False, f unicode_upsilon (Expr_basic [var_X]))]
          (f unicode_delta (Expr_postunary (Expr_annot (Expr_basic [var_X]) h_name) (Expr_basic [dot_iskindof name])))
          []
          (Tacl_by [ Tac_simp_only [Thm_str (flatten [isub_name const_ocliskindof, \<open>_\<close>, h_name])]
                   , Tac_rule
                      (let mk_OF = \<lambda>f. Thm_OF (Thm_str (f h_name)) (Thm_str var_isdef) in
                       List.fold
                         (\<lambda> OclClass n _ _ \<Rightarrow> \<lambda> prf.
                           thm_OF
                             (Thm_str \<open>defined_or_I\<close>)
                             [ prf
                             , mk_OF (print_iskindof_defined_name (\<lambda>name. name @@ isub_of_str n))])
                         next_dataty
                         (mk_OF (print_istypeof_defined_name isub_name))) ])])"

definition "print_iskindof_defined'_name isub_name h_name = flatten [isub_name const_ocliskindof, \<open>_\<close>, h_name, \<open>_defined\<close>, \<langle>[Char Nibble2 Nibble7]\<rangle>]"
definition "print_iskindof_defined' = start_m Thy_lemma_by m_class_default
  (\<lambda> _ (isub_name, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
      let var_X = \<open>X\<close>
        ; var_isdef = \<open>isdef\<close>
        ; f = \<lambda>e. Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile (Expr_apply unicode_delta [e]) in
      [ Lemma_by_assum
          (print_iskindof_defined'_name isub_name h_name)
          [(var_isdef, False, f (Expr_basic [var_X]))]
          (f (Expr_postunary (Expr_annot (Expr_basic [var_X]) h_name) (Expr_basic [dot_iskindof name])))
          []
          (Tacl_by [Tac_rule (Thm_OF (Thm_str (print_iskindof_defined_name isub_name h_name))
                                     (Thm_THEN (Thm_str var_isdef) (Thm_str \<open>foundation20\<close>)))]) ])"

definition "print_iskindof_up_eq_asty = start_map Thy_lemma_by o map_class_gen_h'''''
  (\<lambda> _ name l_attr _ l_subtree next_dataty.
    let var_X = \<open>X\<close>
      ; var_isdef = \<open>isdef\<close>
      ; f = Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile in
    [Lemma_by_assum
        (print_iskindof_up_eq_asty_name name)
        [(var_isdef, False, f (Expr_apply unicode_delta [Expr_basic [var_X]]))]
        (f (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [var_X]) name)
               (Expr_basic [dot_iskindof name]))))
        (List_map App
        [ [ Tac_simp_only [Thm_str (hol_definition \<open>OclValid\<close>)]
          , Tac_insert [Thm_str var_isdef]]
        , List_flatten (fst (fold_list
                      (\<lambda> OclClass n _ next \<Rightarrow> \<lambda>accu.
                        let (l_subst, accu) = fold_list (\<lambda> _ (cpt, l_sub).
                          let l_sub = natural_of_str cpt # l_sub in
                          ( Tac_subst_l
                              l_sub (* subst could fail without the list of integers *)
                              (Thm_str \<open>cp_OclOr\<close>)
                          , Succ cpt
                          , l_sub)) next accu in
                        ( Tac_simp_only [Thm_str (flatten [const_ocliskindof, isub_of_str n, \<open>_\<close>, name])]
                        # l_subst
                        , accu))
                      (OclClass name l_attr next_dataty # rev l_subtree) (1, [])))
        , [ Tac_auto_simp_add_split
              (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l l = List_map Thm_str (List_flatten ( [\<open>foundation16\<close>, hol_definition \<open>bot_option\<close>]
                                                     # List_map
                                                         (\<lambda> OclClass n _ _ \<Rightarrow> [flatten [const_oclistypeof, isub_of_str n, \<open>_\<close>, name]])
                                                         l_subtree)) in
               if l_subtree = [] then l else Thm_symmetric (Thm_str \<open>cp_OclOr\<close>) # l)
              (\<open>option.split\<close> # List_flatten (split_ty name # List_map (\<lambda> OclClass n _ _ \<Rightarrow> split_ty n) l_subtree))]])
        (Tacl_by [Tac_option [Tac_simp_all_add (List_map hol_definition [\<open>false\<close>, \<open>true\<close>, \<open>OclOr\<close>, \<open>OclAnd\<close>, \<open>OclNot\<close>])]])])"

definition "print_iskindof_up_larger = start_map Thy_lemma_by o
  map_class_nupl2''_inh (\<lambda>name_pers name_any name_pred.
    let var_X = \<open>X\<close>
      ; var_isdef = \<open>isdef\<close>
      ; f = Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile
      ; disjI1 = \<open>foundation25\<close>
      ; disjI2 = \<open>foundation25\<close> @@ \<langle>[Char Nibble2 Nibble7]\<rangle> in
    Lemma_by_assum
      (print_iskindof_up_larger_name name_pers name_any)
      [(var_isdef, False, f (Expr_apply unicode_delta [Expr_basic [var_X]]))]
      (f (Expr_warning_parenthesis (Expr_postunary
             (Expr_annot (Expr_basic [var_X]) name_pers)
             (Expr_basic [dot_iskindof name_any]))))
      [App [Tac_simp_only [Thm_str (flatten [const_ocliskindof, isub_of_str name_any, \<open>_\<close>, name_pers])]] ]
      (Tacl_by
        (case
            fst (List.fold (\<lambda> cl. \<lambda> (l, True) \<Rightarrow> (l, True)
                                  | (l, False) \<Rightarrow>
                                     let v =
                                       case cl of (OclClass n _ _, inh) \<Rightarrow>
                                         if n = name_pers then
                                           Some (print_iskindof_up_eq_asty_name name_pers)
                                         else if inh then
                                           Some (print_iskindof_up_larger_name name_pers n)
                                         else None in
                                     (v # l, v \<noteq> None))
              (rev (* priority of '_ or _' is right to left so we reverse *) name_pred)
              ([], False))
         of Some tac_last # l \<Rightarrow>
           List_map Tac_rule
             (List_flatten [ List_map (\<lambda>_. Thm_str disjI1) l
                      , [ Thm_str disjI2]
                      , [ Thm_OF (Thm_str tac_last) (Thm_str var_isdef)] ]))))"

datatype ('a, 'b, 'c, 'd, 'e) print_iskindof_up_istypeof_output
  = I_simp_only 'a
  | I_erule 'b
  | I_simp_add_iskin 'c
  | I_simp 'd
  | I_blast 'e

fun_quick print_iskindof_up_istypeof_child
      and print_iskindof_up_istypeof_child_l where
 (* *)
 "print_iskindof_up_istypeof_child l = (case l of
   [] \<Rightarrow> []
 | (cl, next_dataty) # xs \<Rightarrow>
    case Inh cl of OclClass name_pred _ _ \<Rightarrow>
      I_simp_only name_pred # print_iskindof_up_istypeof_child_l name_pred xs [] (rev next_dataty))"
 (* *) |
 "print_iskindof_up_istypeof_child_l name_pred l l_tac lc = (case lc of
   [] \<Rightarrow> l_tac
 | (x, path_inh) # next_dataty \<Rightarrow>
    let get_n = \<lambda> OclClass n _ _ \<Rightarrow> n
      ; n = get_n x in
    List_flatten [ [I_erule (name_pred, (x, path_inh) # next_dataty)]
            , if next_dataty = [] then [I_blast n] else []
            , print_iskindof_up_istypeof_child_l name_pred l
                (List_flatten [ if path_inh then
                             if l = [] then
                               [I_simp_add_iskin n]
                             else print_iskindof_up_istypeof_child l
                           else [I_simp n]
                         , l_tac ])
                next_dataty ])"

definition "print_iskindof_up_istypeof_erule var_isdef next_dataty name_pers name_any =
 (let mk_OF = \<lambda>f. Thm_OF (Thm_str (f name_any)) (Thm_str var_isdef)
    ; next_dataty = case next_dataty of x # xs \<Rightarrow>
                      rev ((\<open>foundation26\<close>, x) # List_map (Pair \<open>defined_or_I\<close>) xs) in
  Tac_erule (List.fold
              (\<lambda> (rule_name, OclClass n _ _) \<Rightarrow> \<lambda> prf.
                thm_OF
                  (Thm_str rule_name)
                  [ prf
                  , mk_OF (print_iskindof_defined'_name (\<lambda>name. name @@ isub_of_str n))])
              next_dataty
              (mk_OF (print_istypeof_defined'_name (\<lambda>name. name @@ isub_of_str name_pers)))))"

definition "print_iskindof_up_istypeof_unfold_name name_pers name_any = flatten [\<open>not_\<close>, const_ocliskindof, isub_of_str name_pers, \<open>_then_\<close>, name_any, \<open>_\<close>, const_oclistypeof, \<open>_others_unfold\<close>]"
definition "print_iskindof_up_istypeof_unfold = start_m_gen Thy_lemma_by m_class_default
  (\<lambda> _ name_pred0 next_dataty compare (isub_name, name_pers, _). \<lambda> OclClass name_any _ _ \<Rightarrow>
  if compare = GT then
    let var_X = \<open>X\<close>
      ; var_iskin = \<open>iskin\<close>
      ; var_isdef = \<open>isdef\<close>
      ; f = \<lambda>f. f o Expr_parenthesis o Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile in
    [ Lemma_by_assum
        (print_iskindof_up_istypeof_unfold_name name_pers name_any)
        [(var_isdef, False, f id (Expr_apply unicode_delta [Expr_basic [var_X]]))
        ,(var_iskin, False, f id (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [var_X]) name_any)
                 (Expr_basic [dot_iskindof name_pers]))))]
        (expr_binop' unicode_or
          (List_flatten
            (List_map (\<lambda>(f_dot, l). List_map
                 (\<lambda>name_pred. f id (Expr_warning_parenthesis (Expr_postunary
                   (Expr_annot (Expr_basic [var_X]) name_any)
                   (Expr_basic [f_dot name_pred])))) l)
               [ (dot_istypeof, name_pers # List_map (\<lambda> OclClass n _ _ \<Rightarrow> n) name_pred0) ])))
        (App_using [Thm_str var_iskin]
         # App [Tac_simp_only [Thm_str (flatten [isub_name const_ocliskindof, \<open>_\<close>, name_any])]]
         # (if next_dataty = [] then [] else List_flatten
              [ fst (fold_list
                  (\<lambda>_ next_dataty.
                      ( App [print_iskindof_up_istypeof_erule var_isdef next_dataty name_pers name_any]
                      , tl next_dataty))
                  next_dataty
                  (rev next_dataty))
              , [ App [Tac_simp] ]
              , List_map (\<lambda> OclClass n _ _ \<Rightarrow>
                  App [Tac_drule (Thm_OF (Thm_str (print_iskindof_up_istypeof_unfold_name n name_any)) (Thm_str var_isdef)), Tac_blast None]) next_dataty ]))
        Tacl_done ]
  else [])"

definition "print_iskindof_up_istypeof_name name_pers name_any = flatten [\<open>not_\<close>, const_ocliskindof, isub_of_str name_pers, \<open>_then_\<close>, name_any, \<open>_\<close>, const_oclistypeof, \<open>_others\<close>]"
definition "print_iskindof_up_istypeof = start_map Thy_lemma_by o
  map_class_nupl2l'_inh (\<lambda>name_pers name_pred0.
    case name_pred0 of (name_any, _) # name_pred \<Rightarrow>
    let name_any = case Inh name_any of OclClass name_any _ _ \<Rightarrow> name_any
      ; var_X = \<open>X\<close>
      ; var_iskin = \<open>iskin\<close>
      ; var_isdef = \<open>isdef\<close>
      ; f = \<lambda>f. f o Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile in
    Lemma_by_assum
      (print_iskindof_up_istypeof_name name_pers name_any)
      [(var_iskin, False, f (Expr_preunary (Expr_basic [unicode_not])) (Expr_warning_parenthesis (Expr_postunary
             (Expr_annot (Expr_basic [var_X]) name_any)
               (Expr_basic [dot_iskindof name_pers]))))
      ,(var_isdef, False, f id (Expr_apply unicode_delta [Expr_basic [var_X]]))]
      (expr_binop' unicode_or
        (List_flatten
          (List_map (\<lambda>(f_dot, l). List_map
               (\<lambda>name_pred. f id (Expr_warning_parenthesis (Expr_postunary
                 (Expr_annot (Expr_basic [var_X]) name_any)
                 (Expr_basic [f_dot name_pred])))) l)
             [ (dot_istypeof, List_map (\<lambda> (name_pred, _). case Inh name_pred of OclClass n _ _ \<Rightarrow> n) name_pred0)
             , (dot_iskindof, List_flatten (List_map (\<lambda> (name_pred, _). case Inh_sib_unflat name_pred of l \<Rightarrow> List_map (\<lambda> OclClass n _ _ \<Rightarrow> n) l) name_pred0)) ])))
      (App_using [Thm_OF (Thm_str (print_iskindof_up_eq_asty_name name_any)) (Thm_str var_isdef)]
       # List_map (\<lambda>x. App [x])
         (List_map
           (\<lambda> I_simp_only name_pred \<Rightarrow> Tac_simp_only [Thm_str (print_iskindof_class_name (\<lambda>s. s @@ isub_of_str name_pred) name_any)]
            | I_erule (name_pred, next_dataty) \<Rightarrow>
                print_iskindof_up_istypeof_erule var_isdef (List_map fst next_dataty) name_pred name_any
            | I_simp_add_iskin _ \<Rightarrow> Tac_simp_add [var_iskin]
            | _ \<Rightarrow> Tac_simp)
           (print_iskindof_up_istypeof_child name_pred0)))
        Tacl_done)"

definition "print_iskindof_up_d_cast = start_map Thy_lemma_by o
  map_class_nupl3'_LE'_inh (\<lambda>name_pers name_mid name_pred0.
    case name_pred0 of (name_any, _) # name_pred \<Rightarrow>
    let name_any = case Inh name_any of OclClass name_any _ _ \<Rightarrow> name_any
      ; var_X = \<open>X\<close>
      ; var_iskin = \<open>iskin\<close>
      ; var_isdef = \<open>isdef\<close>
      ; f = \<lambda>f. f o Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile in
    Lemma_by_assum
        (flatten [\<open>down_cast_kind\<close>, isub_of_str name_mid, \<open>_from_\<close>, name_any, \<open>_to_\<close>, name_pers])
        [(var_iskin, False, f (Expr_preunary (Expr_basic [unicode_not])) (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [var_X]) name_any)
               (Expr_basic [dot_iskindof name_mid]))))
        ,(var_isdef, False, f id (Expr_apply unicode_delta [Expr_basic [var_X]]))]
        (f id (Expr_binop (Expr_warning_parenthesis (Expr_postunary
               (Expr_basic [var_X])
               (Expr_basic [dot_astype name_pers]))
             ) unicode_triangleq (Expr_basic [\<open>invalid\<close>])))
        (List_flatten
          (let name_pred_inh = List_map (\<lambda> (name_pred, _). Inh name_pred) name_pred0
             ; name_pred_inh_sib_gen = List_flatten (List_map (\<lambda> (name_pred, _). case Inh_sib name_pred of l \<Rightarrow> l) name_pred0)
             ; name_pred_inh_sib = List_map fst name_pred_inh_sib_gen
             ; f0 = \<lambda>name_pred. let name_pred = case name_pred of OclClass n _ _ \<Rightarrow> n in
                                [ Tac_rule (Thm_str (print_istypeof_up_d_cast_name name_pred name_any name_pers))
                                , Tac_simp_only [] (* FIXME use wildcard *)
                                , Tac_simp_only [Thm_str var_isdef]] in
           [ App (  Tac_insert [thm_OF (Thm_str (print_iskindof_up_istypeof_name name_mid name_any)) (List_map Thm_str [var_iskin, var_isdef])]
                  # (case List_flatten [ name_pred_inh, name_pred_inh_sib ]
                     of [] \<Rightarrow> [] | [_] \<Rightarrow> [] | _ \<Rightarrow> [ Tac_elim (Thm_str \<open>disjE\<close>) ]))]
           # List_map (App o f0) name_pred_inh
           # List_map (\<lambda> (OclClass name_pred l_attr next_d, l_subtree) \<Rightarrow>
                         List_map App
                           [ [ Tac_drule (Thm_OF (Thm_str (print_iskindof_up_istypeof_unfold_name name_pred name_any)) (Thm_str var_isdef))]
                           , if next_d = [] then
                               f0 (OclClass name_pred l_attr next_d)
                             else
                               [ Tac_auto_simp_add
                                 (var_isdef # List_map
                                                (\<lambda> OclClass name_pred _ _ \<Rightarrow>
                                                  print_istypeof_up_d_cast_name name_pred name_any name_pers)
                                                l_subtree)] ])
                      name_pred_inh_sib_gen))
        Tacl_done)"

end
