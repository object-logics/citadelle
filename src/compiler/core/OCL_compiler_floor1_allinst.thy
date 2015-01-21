(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_floor1_allinst.thy ---
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

theory  OCL_compiler_floor1_allinst
imports OCL_compiler_core_init
begin

section{* Translation of AST *}

subsection{* allInstances *}

definition "print_allinst_def_id = start_map Thy_definition_hol o
  map_class (\<lambda>isub_name name _ _ _ _.
    let const_astype = flatten [const_oclastype, isub_of_str name, \<langle>''_''\<rangle>, unicode_AA] in
    Definition (Expr_rewrite (Expr_basic [name]) \<langle>''=''\<rangle> (Expr_basic [const_astype])))"

definition "print_allinst_lemmas_id = start_map'
  (if activate_simp_optimization then
     \<lambda>expr.
       let name_set = map_class (\<lambda>_ name _ _ _ _. name) expr in
       case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
         [ Lemmas_simp \<langle>''''\<rangle> (List_map (Thm_str o hol_definition) name_set) ]
  else (\<lambda>_. []))"

definition "print_allinst_astype_name isub_name = flatten [isub_name const_oclastype, \<langle>''_''\<rangle>, unicode_AA, \<langle>''_some''\<rangle>]"
definition "print_allinst_astype = start_map Thy_lemma_by o map_class_top (\<lambda>isub_name name _ _ _ _.
  let b = \<lambda>s. Expr_basic [s]
    ; var_x = \<langle>''x''\<rangle>
    ; d = hol_definition in
  [Lemma_by
    (print_allinst_astype_name isub_name)
    [ Expr_rewrite
        (Expr_apply (flatten [isub_name const_oclastype, \<langle>''_''\<rangle>, unicode_AA]) [b var_x])
        unicode_noteq
        (b \<langle>''None''\<rangle>)]
    []
    (Tacl_by [Tac_simp_add [d (flatten [isub_name const_oclastype, \<langle>''_''\<rangle>, unicode_AA])]])])"

definition "print_allinst_exec = start_map Thy_lemma_by o map_class_top (\<lambda>isub_name name _ _ _ _.
  let b = \<lambda>s. Expr_basic [s]
    ; a = \<lambda>f x. Expr_apply f [x]
    ; d = hol_definition
    ; f = Expr_paren unicode_lfloor unicode_rfloor
    ; f_img = \<lambda>e1. Expr_binop (b e1) \<langle>''`''\<rangle>
    ; ran_heap = \<lambda>var_pre_post var_tau. f_img name (a \<langle>''ran''\<rangle> (a \<langle>''heap''\<rangle> (Expr_apply var_pre_post [b var_tau])))
    ; f_incl = \<lambda>v1 v2.
        let var_tau = unicode_tau in
        Expr_bind0 unicode_And (b var_tau) (Expr_binop (Expr_applys (Expr_pat v1) [b var_tau]) unicode_subseteq (Expr_applys (Expr_pat v2) [b var_tau]))
    ; var_B = \<langle>''B''\<rangle>
    ; var_C = \<langle>''C''\<rangle> in
  gen_pre_post
    (\<lambda>s. flatten [isub_name s, \<langle>''_exec''\<rangle>])
    (\<lambda>f_expr _ var_pre_post.
      Expr_rewrite
       (f_expr [b name])
       \<langle>''=''\<rangle>
       (Expr_lam unicode_tau (\<lambda>var_tau. Expr_apply var_Abs_Set [f (f (f_img \<langle>''Some''\<rangle> (ran_heap var_pre_post var_tau))) ])))
    (\<lambda>lem_tit lem_spec var_pre_post _ _.
      Lemma_by_assum
        lem_tit
        []
        lem_spec
        (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l var_S1 = \<langle>''S1''\<rangle>
           ; var_S2 = \<langle>''S2''\<rangle> in
         [ App_let (Expr_pat var_S1) (Expr_lam unicode_tau (ran_heap var_pre_post))
         , App_let (Expr_pat var_S2) (Expr_lam unicode_tau (\<lambda>var_tau. Expr_binop (Expr_applys (Expr_pat var_S1) [b var_tau]) \<langle>''-''\<rangle> (Expr_paren \<langle>''{''\<rangle> \<langle>''}''\<rangle> (b \<langle>''None''\<rangle>))))
         , App_have var_B (f_incl var_S2 var_S1) (Tacl_by [Tac_auto])
         , App_have var_C (f_incl var_S1 var_S2) (Tacl_by [Tac_auto_simp_add [print_allinst_astype_name isub_name]])
         , App [Tac_simp_add_del [d \<langle>''OclValid''\<rangle>] [d \<langle>''OclAllInstances_generic''\<rangle>, flatten [isub_name const_ocliskindof, \<langle>''_''\<rangle>, name]]] ])
        (Tacl_by [Tac_insert [thm_OF (Thm_str \<langle>''equalityI''\<rangle>) (List_map Thm_str [var_B, var_C])], Tac_simp]))
    [])"

definition "print_allinst_istypeof_pre_name1 = \<langle>''ex_ssubst''\<rangle>"
definition "print_allinst_istypeof_pre_name2 = \<langle>''ex_def''\<rangle>"
definition "print_allinst_istypeof_pre = start_map Thy_lemma_by o (\<lambda>_.
  [ Lemma_by
      print_allinst_istypeof_pre_name1
      (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l var_x = \<langle>''x''\<rangle>
         ; var_B = \<langle>''B''\<rangle>
         ; var_s = \<langle>''s''\<rangle>
         ; var_t = \<langle>''t''\<rangle>
         ; var_P = \<langle>''P''\<rangle>
         ; b = \<lambda>s. Expr_basic [s]
         ; a = \<lambda>f x. Expr_apply f [x]
         ; bind = \<lambda>symb. Expr_bind0 symb (Expr_binop (b var_x) unicode_in (b var_B))
         ; f = \<lambda>v. bind unicode_exists (a var_P (a v (b var_x))) in
       [ Expr_bind0 unicode_forall (Expr_binop (b var_x) unicode_in (b var_B)) (Expr_rewrite (a var_s (b var_x)) \<langle>''=''\<rangle> (a var_t (b var_x)))
       , Expr_rewrite (f var_s) \<langle>''=''\<rangle> (f var_t) ])
      []
      (Tacl_by [Tac_simp])
  , Lemma_by
      print_allinst_istypeof_pre_name2
      (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l var_x = \<langle>''x''\<rangle>
         ; var_X = \<langle>''X''\<rangle>
         ; var_y = \<langle>''y''\<rangle>
         ; b = \<lambda>s. Expr_basic [s]
         ; c = Expr_paren unicode_lceil unicode_rceil
         ; f = Expr_paren unicode_lfloor unicode_rfloor
         ; p = Expr_paren \<langle>''{''\<rangle> \<langle>''}''\<rangle> in
       [ Expr_binop (b var_x) unicode_in (c (c (f (f (Expr_binop (b \<langle>''Some''\<rangle>) \<langle>''`''\<rangle> (Expr_parenthesis (Expr_binop (b var_X) \<langle>''-''\<rangle> (p (b \<langle>''None''\<rangle>)))))))))
       , Expr_bind0 unicode_exists (b var_y) (Expr_rewrite (b var_x) \<langle>''=''\<rangle> (f (f (b var_y)))) ])
      []
      (Tacl_by [Tac_auto_simp_add []]) ])"

definition "print_allinst_istypeof_single isub_name name isub_name2 name2 const_oclisof dot_isof f_simp1 f_simp2 =
  (let b = \<lambda>s. Expr_basic [s]
    ; d = hol_definition
    ; s = Tac_subst_l [\<langle>''1''\<rangle>,\<langle>''2''\<rangle>,\<langle>''3''\<rangle>]
    ; var_tau = unicode_tau in
  gen_pre_post
    (\<lambda>s. flatten [name, \<langle>''_''\<rangle>, s, \<langle>''_''\<rangle>, isub_name2 const_oclisof])
    (\<lambda>f_expr _ _. Expr_binop (b var_tau) unicode_Turnstile (Expr_apply var_OclForall_set [f_expr [b name], b (isub_name2 const_oclisof) ]))
    (\<lambda>lem_tit lem_spec _ _ _. Lemma_by
      lem_tit
      [lem_spec]
      [ [Tac_simp_add_del [d \<langle>''OclValid''\<rangle>] (d \<langle>''OclAllInstances_generic''\<rangle> # f_simp1 [flatten [isub_name2 const_oclisof, \<langle>''_''\<rangle>, name]])]
      , [Tac_simp_only (List_flatten [List_map Thm_str [ d var_OclForall_set, \<langle>''refl''\<rangle>, \<langle>''if_True''\<rangle> ], [Thm_simplified (Thm_str \<langle>''OclAllInstances_generic_defined''\<rangle>) (Thm_str (d \<langle>''OclValid''\<rangle>))]])]
      , [Tac_simp_only [Thm_str (d \<langle>''OclAllInstances_generic''\<rangle>)]]
      , [s (Thm_str var_Abs_Set_inverse), Tac_simp_add [d \<langle>''bot_option''\<rangle>]]
      , [s (Thm_where
             (Thm_str print_allinst_istypeof_pre_name1)
             [ (\<langle>''s''\<rangle>, Expr_lam \<langle>''x''\<rangle> (\<lambda>var_x. Expr_applys (Expr_postunary (Expr_lambda wildcard (b var_x)) (b (dot_isof name2))) [b var_tau]))
             , (\<langle>''t''\<rangle>, Expr_lambda wildcard (Expr_apply \<langle>''true''\<rangle> [b var_tau]))])]
      , [Tac_intro [ Thm_str \<langle>''ballI''\<rangle>
                   , thm_simplified
                       (Thm_str (if name = name2 then
                                   print_iskindof_up_eq_asty_name name
                                 else
                                   print_iskindof_up_larger_name name name2))
                       (List_map Thm_str (d \<langle>''OclValid''\<rangle> # f_simp2 [flatten [isub_name const_ocliskindof, \<langle>''_''\<rangle>, name]]))]]
      , [Tac_drule (Thm_str print_allinst_istypeof_pre_name2), Tac_erule (Thm_str (\<langle>''exE''\<rangle>)), Tac_simp]]
      (Tacl_by [Tac_simp]))
      [])"

definition "print_allinst_istypeof = start_map'' Thy_lemma_by o (\<lambda>expr base_attr _ _. map_class_gen (\<lambda>isub_name name l_attr _ _ next_dataty.
  let l_attr = base_attr l_attr in
  let b = \<lambda>s. Expr_basic [s]
    ; d = hol_definition
    ; s = Tac_subst_l [\<langle>''1''\<rangle>,\<langle>''2''\<rangle>,\<langle>''3''\<rangle>]
    ; var_tau = unicode_tau in
  case next_dataty of [] \<Rightarrow>
    print_allinst_istypeof_single isub_name name isub_name name const_oclistypeof dot_istypeof (\<lambda>_. []) id
  | OclClass name_next _ _ # _ \<Rightarrow>
    List_flatten
    [ gen_pre_post
        (\<lambda>s. flatten [name, \<langle>''_''\<rangle>, s, \<langle>''_''\<rangle>, isub_name const_oclistypeof, \<langle>''1''\<rangle>])
        (\<lambda>f_expr _ _.
           Expr_exists
             unicode_tau
             (\<lambda>var_tau. Expr_binop (b var_tau) unicode_Turnstile (Expr_apply var_OclForall_set [f_expr [b name], b (isub_name const_oclistypeof) ])))
        (\<lambda>lem_tit lem_spec var_pre_post _ _. Lemma_by_assum
           lem_tit
           [(\<langle>''''\<rangle>, True, Expr_And \<langle>''x''\<rangle> (\<lambda>var_x. Expr_rewrite (Expr_apply var_pre_post [Expr_parenthesis (Expr_binop (b var_x) \<langle>'',''\<rangle> (b var_x))]) \<langle>''=''\<rangle> (b var_x)) )]
           lem_spec
           (List_map App
              [ let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l var_tau0 = var_tau @@ isub_of_str \<langle>''0''\<rangle> in
                [Tac_rule (Thm_where (Thm_str \<langle>''exI''\<rangle>) [(\<langle>''x''\<rangle>, b var_tau0)]), Tac_simp_add_del (List_map d [var_tau0, \<langle>''OclValid''\<rangle>]) [d \<langle>''OclAllInstances_generic''\<rangle>]]
              , [Tac_simp_only (List_flatten [List_map Thm_str [ d var_OclForall_set, \<langle>''refl''\<rangle>, \<langle>''if_True''\<rangle> ], [Thm_simplified (Thm_str \<langle>''OclAllInstances_generic_defined''\<rangle>) (Thm_str (d \<langle>''OclValid''\<rangle>))]])]
              , [Tac_simp_only [Thm_str (d \<langle>''OclAllInstances_generic''\<rangle>)]]
              , [s (Thm_str var_Abs_Set_inverse), Tac_simp_add [d \<langle>''bot_option''\<rangle>]] ] )
           (Tacl_by [Tac_simp (*Tac_simp_add [flatten [isub_name const_oclistypeof, \<langle>''_''\<rangle>, name]]*)]))
        [Tac_simp]
    , gen_pre_post
        (\<lambda>s. flatten [name, \<langle>''_''\<rangle>, s, \<langle>''_''\<rangle>, isub_name const_oclistypeof, \<langle>''2''\<rangle>])
        (\<lambda>f_expr _ _.
           Expr_exists
             unicode_tau
             (\<lambda>var_tau. Expr_binop (b var_tau) unicode_Turnstile (Expr_apply \<langle>''not''\<rangle> [Expr_apply var_OclForall_set [f_expr [b name], b (isub_name const_oclistypeof) ]])))
        (\<lambda>lem_tit lem_spec var_pre_post _ _. Lemma_by_assum
           lem_tit
           [(\<langle>''''\<rangle>, True, Expr_And \<langle>''x''\<rangle> (\<lambda>var_x. Expr_rewrite (Expr_apply var_pre_post [Expr_parenthesis (Expr_binop (b var_x) \<langle>'',''\<rangle> (b var_x))]) \<langle>''=''\<rangle> (b var_x)) )]
           lem_spec
           (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l var_oid = \<langle>''oid''\<rangle>
              ; var_a = \<langle>''a''\<rangle>
              ; var_t0 = \<langle>''t0''\<rangle>
              ; s_empty = \<langle>''Map.empty''\<rangle> in
            [ App_fix [var_oid, var_a]
            , App_let (Expr_pat var_t0) (Expr_apply \<langle>''state.make''\<rangle>
                [ Expr_apply s_empty [Expr_binop (b var_oid) unicode_mapsto (Expr_apply (isub_name datatype_in) [Expr_apply (isub_name datatype_constr_name) (Expr_apply (datatype_ext_constr_name @@ mk_constr_name name name_next) [b var_a] # List_map (\<lambda>_. b \<langle>''None''\<rangle>) l_attr)])]
                , b s_empty])
            , App [Tac_rule (Thm_where (Thm_str \<langle>''exI''\<rangle>) [(\<langle>''x''\<rangle>, Expr_parenthesis (Expr_binop (Expr_pat var_t0) \<langle>'',''\<rangle> (Expr_pat var_t0)))]), Tac_simp_add_del [d \<langle>''OclValid''\<rangle>] [d \<langle>''OclAllInstances_generic''\<rangle>]]
            , App [Tac_simp_only (List_flatten [List_map Thm_str [ d var_OclForall_set, \<langle>''refl''\<rangle>, \<langle>''if_True''\<rangle> ], [Thm_simplified (Thm_str \<langle>''OclAllInstances_generic_defined''\<rangle>) (Thm_str (d \<langle>''OclValid''\<rangle>))]])]
            , App [Tac_simp_only (List_map (\<lambda>x. Thm_str (d x)) [\<langle>''OclAllInstances_generic''\<rangle>, flatten [isub_name const_oclastype, \<langle>''_''\<rangle>, unicode_AA]])]
            , App [s (Thm_str var_Abs_Set_inverse), Tac_simp_add [d \<langle>''bot_option''\<rangle>]] ] )
           (Tacl_by [Tac_simp_add [d \<langle>''state.make''\<rangle>, d \<langle>''OclNot''\<rangle>]]))
        [Tac_simp]]) expr)"

definition "print_allinst_iskindof_eq = start_map Thy_lemma_by o map_class_gen (\<lambda>isub_name name _ _ _ _.
  print_allinst_istypeof_single isub_name name isub_name name const_ocliskindof dot_iskindof id (\<lambda>_. []))"

definition "print_allinst_iskindof_larger = start_map Thy_lemma_by o List_flatten o map_class_nupl2'_inh (\<lambda>name name2.
  print_allinst_istypeof_single (\<lambda>s. s @@ isub_of_str name) name (\<lambda>s. s @@ isub_of_str name2) name2 const_ocliskindof dot_iskindof id (\<lambda>_. []))"

end
