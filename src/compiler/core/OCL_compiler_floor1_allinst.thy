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
    let const_astype = flatten [const_oclastype, isub_of_str name, \<open>_\<close>, unicode_AA] in
    Definition (Expr_rewrite (Expr_basic [name]) \<open>=\<close> (Expr_basic [const_astype])))"

definition "print_allinst_lemmas_id = start_map'
  (if activate_simp_optimization then
     \<lambda>expr.
       let name_set = map_class (\<lambda>_ name _ _ _ _. name) expr in
       case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
         [ Lemmas_simp \<open>\<close> (List_map (Thm_str o hol_definition) name_set) ]
  else (\<lambda>_. []))"

definition "print_allinst_astype_name isub_name = flatten [isub_name const_oclastype, \<open>_\<close>, unicode_AA, \<open>_some\<close>]"
definition "print_allinst_astype = start_map Thy_lemma_by o map_class_top (\<lambda>isub_name name _ _ _ _.
  let b = \<lambda>s. Expr_basic [s]
    ; var_x = \<open>x\<close>
    ; d = hol_definition in
  [Lemma_by
    (print_allinst_astype_name isub_name)
    [ Expr_rewrite
        (Expr_apply (flatten [isub_name const_oclastype, \<open>_\<close>, unicode_AA]) [b var_x])
        unicode_noteq
        (b \<open>None\<close>)]
    []
    (Tacl_by [Tac_simp_add [d (flatten [isub_name const_oclastype, \<open>_\<close>, unicode_AA])]])])"

definition "print_allinst_exec = start_map Thy_lemma_by o map_class_top (\<lambda>isub_name name _ _ _ _.
  let b = \<lambda>s. Expr_basic [s]
    ; a = \<lambda>f x. Expr_apply f [x]
    ; d = hol_definition
    ; f = Expr_paren unicode_lfloor unicode_rfloor
    ; f_img = \<lambda>e1. Expr_binop (b e1) \<open>`\<close>
    ; ran_heap = \<lambda>var_pre_post var_tau. f_img name (a \<open>ran\<close> (a \<open>heap\<close> (Expr_apply var_pre_post [b var_tau])))
    ; f_incl = \<lambda>v1 v2.
        let var_tau = unicode_tau in
        Expr_bind0 unicode_And (b var_tau) (Expr_binop (Expr_applys (Expr_pat v1) [b var_tau]) unicode_subseteq (Expr_applys (Expr_pat v2) [b var_tau]))
    ; var_B = \<open>B\<close>
    ; var_C = \<open>C\<close> in
  gen_pre_post
    (\<lambda>s. flatten [isub_name s, \<open>_exec\<close>])
    (\<lambda>f_expr _ var_pre_post.
      Expr_rewrite
       (f_expr [b name])
       \<open>=\<close>
       (Expr_lam unicode_tau (\<lambda>var_tau. Expr_apply var_Abs_Set [f (f (f_img \<open>Some\<close> (ran_heap var_pre_post var_tau))) ])))
    (\<lambda>lem_tit lem_spec var_pre_post _ _.
      Lemma_by_assum
        lem_tit
        []
        lem_spec
        (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l var_S1 = \<open>S1\<close>
           ; var_S2 = \<open>S2\<close> in
         [ App_let (Expr_pat var_S1) (Expr_lam unicode_tau (ran_heap var_pre_post))
         , App_let (Expr_pat var_S2) (Expr_lam unicode_tau (\<lambda>var_tau. Expr_binop (Expr_applys (Expr_pat var_S1) [b var_tau]) \<open>-\<close> (Expr_paren \<open>{\<close> \<open>}\<close> (b \<open>None\<close>))))
         , App_have var_B (f_incl var_S2 var_S1) (Tacl_by [Tac_auto])
         , App_have var_C (f_incl var_S1 var_S2) (Tacl_by [Tac_auto_simp_add [print_allinst_astype_name isub_name]])
         , App [Tac_simp_add_del [d \<open>OclValid\<close>] [d \<open>OclAllInstances_generic\<close>, flatten [isub_name const_ocliskindof, \<open>_\<close>, name]]] ])
        (Tacl_by [Tac_insert [thm_OF (Thm_str \<open>equalityI\<close>) (List_map Thm_str [var_B, var_C])], Tac_simp]))
    [])"

definition "print_allinst_istypeof_pre_name1 = \<open>ex_ssubst\<close>"
definition "print_allinst_istypeof_pre_name2 = \<open>ex_def\<close>"
definition "print_allinst_istypeof_pre = start_map Thy_lemma_by o (\<lambda>_.
  [ Lemma_by
      print_allinst_istypeof_pre_name1
      (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l var_x = \<open>x\<close>
         ; var_B = \<open>B\<close>
         ; var_s = \<open>s\<close>
         ; var_t = \<open>t\<close>
         ; var_P = \<open>P\<close>
         ; b = \<lambda>s. Expr_basic [s]
         ; a = \<lambda>f x. Expr_apply f [x]
         ; bind = \<lambda>symb. Expr_bind0 symb (Expr_binop (b var_x) unicode_in (b var_B))
         ; f = \<lambda>v. bind unicode_exists (a var_P (a v (b var_x))) in
       [ Expr_bind0 unicode_forall (Expr_binop (b var_x) unicode_in (b var_B)) (Expr_rewrite (a var_s (b var_x)) \<open>=\<close> (a var_t (b var_x)))
       , Expr_rewrite (f var_s) \<open>=\<close> (f var_t) ])
      []
      (Tacl_by [Tac_simp])
  , Lemma_by
      print_allinst_istypeof_pre_name2
      (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l var_x = \<open>x\<close>
         ; var_X = \<open>X\<close>
         ; var_y = \<open>y\<close>
         ; b = \<lambda>s. Expr_basic [s]
         ; c = Expr_paren unicode_lceil unicode_rceil
         ; f = Expr_paren unicode_lfloor unicode_rfloor
         ; p = Expr_paren \<open>{\<close> \<open>}\<close> in
       [ Expr_binop (b var_x) unicode_in (c (c (f (f (Expr_binop (b \<open>Some\<close>) \<open>`\<close> (Expr_parenthesis (Expr_binop (b var_X) \<open>-\<close> (p (b \<open>None\<close>)))))))))
       , Expr_bind0 unicode_exists (b var_y) (Expr_rewrite (b var_x) \<open>=\<close> (f (f (b var_y)))) ])
      []
      (Tacl_by [Tac_auto_simp_add []]) ])"

definition "print_allinst_istypeof_single isub_name name isub_name2 name2 const_oclisof dot_isof f_simp1 f_simp2 =
  (let b = \<lambda>s. Expr_basic [s]
    ; d = hol_definition
    ; s = Tac_subst_l [\<open>1\<close>,\<open>2\<close>,\<open>3\<close>]
    ; var_tau = unicode_tau in
  gen_pre_post
    (\<lambda>s. flatten [name, \<open>_\<close>, s, \<open>_\<close>, isub_name2 const_oclisof])
    (\<lambda>f_expr _ _. Expr_binop (b var_tau) unicode_Turnstile (Expr_apply var_OclForall_set [f_expr [b name], b (isub_name2 const_oclisof) ]))
    (\<lambda>lem_tit lem_spec _ _ _. Lemma_by
      lem_tit
      [lem_spec]
      [ [Tac_simp_add_del [d \<open>OclValid\<close>] (d \<open>OclAllInstances_generic\<close> # f_simp1 [flatten [isub_name2 const_oclisof, \<open>_\<close>, name]])]
      , [Tac_simp_only (List_flatten [List_map Thm_str [ d var_OclForall_set, \<open>refl\<close>, \<open>if_True\<close> ], [Thm_simplified (Thm_str \<open>OclAllInstances_generic_defined\<close>) (Thm_str (d \<open>OclValid\<close>))]])]
      , [Tac_simp_only [Thm_str (d \<open>OclAllInstances_generic\<close>)]]
      , [s (Thm_str var_Abs_Set_inverse), Tac_simp_add [d \<open>bot_option\<close>]]
      , [s (Thm_where
             (Thm_str print_allinst_istypeof_pre_name1)
             [ (\<open>s\<close>, Expr_lam \<open>x\<close> (\<lambda>var_x. Expr_applys (Expr_postunary (Expr_lambda wildcard (b var_x)) (b (dot_isof name2))) [b var_tau]))
             , (\<open>t\<close>, Expr_lambda wildcard (Expr_apply \<open>true\<close> [b var_tau]))])]
      , [Tac_intro [ Thm_str \<open>ballI\<close>
                   , thm_simplified
                       (Thm_str (if name = name2 then
                                   print_iskindof_up_eq_asty_name name
                                 else
                                   print_iskindof_up_larger_name name name2))
                       (List_map Thm_str (d \<open>OclValid\<close> # f_simp2 [flatten [isub_name const_ocliskindof, \<open>_\<close>, name]]))]]
      , [Tac_drule (Thm_str print_allinst_istypeof_pre_name2), Tac_erule (Thm_str (\<open>exE\<close>)), Tac_simp]]
      (Tacl_by [Tac_simp]))
      [])"

definition "print_allinst_istypeof = start_map'' Thy_lemma_by o (\<lambda>expr base_attr _ _. map_class_gen (\<lambda>isub_name name l_attr _ _ next_dataty.
  let l_attr = base_attr l_attr in
  let b = \<lambda>s. Expr_basic [s]
    ; d = hol_definition
    ; s = Tac_subst_l [\<open>1\<close>,\<open>2\<close>,\<open>3\<close>]
    ; var_tau = unicode_tau in
  case next_dataty of [] \<Rightarrow>
    print_allinst_istypeof_single isub_name name isub_name name const_oclistypeof dot_istypeof (\<lambda>_. []) id
  | OclClass name_next _ _ # _ \<Rightarrow>
    List_flatten
    [ gen_pre_post
        (\<lambda>s. flatten [name, \<open>_\<close>, s, \<open>_\<close>, isub_name const_oclistypeof, \<open>1\<close>])
        (\<lambda>f_expr _ _.
           Expr_exists
             unicode_tau
             (\<lambda>var_tau. Expr_binop (b var_tau) unicode_Turnstile (Expr_apply var_OclForall_set [f_expr [b name], b (isub_name const_oclistypeof) ])))
        (\<lambda>lem_tit lem_spec var_pre_post _ _. Lemma_by_assum
           lem_tit
           [(\<open>\<close>, True, Expr_And \<open>x\<close> (\<lambda>var_x. Expr_rewrite (Expr_apply var_pre_post [Expr_parenthesis (Expr_binop (b var_x) \<open>,\<close> (b var_x))]) \<open>=\<close> (b var_x)) )]
           lem_spec
           (List_map App
              [ let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l var_tau0 = var_tau @@ isub_of_str \<open>0\<close> in
                [Tac_rule (Thm_where (Thm_str \<open>exI\<close>) [(\<open>x\<close>, b var_tau0)]), Tac_simp_add_del (List_map d [var_tau0, \<open>OclValid\<close>]) [d \<open>OclAllInstances_generic\<close>]]
              , [Tac_simp_only (List_flatten [List_map Thm_str [ d var_OclForall_set, \<open>refl\<close>, \<open>if_True\<close> ], [Thm_simplified (Thm_str \<open>OclAllInstances_generic_defined\<close>) (Thm_str (d \<open>OclValid\<close>))]])]
              , [Tac_simp_only [Thm_str (d \<open>OclAllInstances_generic\<close>)]]
              , [s (Thm_str var_Abs_Set_inverse), Tac_simp_add [d \<open>bot_option\<close>]] ] )
           (Tacl_by [Tac_simp (*Tac_simp_add [flatten [isub_name const_oclistypeof, \<open>_\<close>, name]]*)]))
        [Tac_simp]
    , gen_pre_post
        (\<lambda>s. flatten [name, \<open>_\<close>, s, \<open>_\<close>, isub_name const_oclistypeof, \<open>2\<close>])
        (\<lambda>f_expr _ _.
           Expr_exists
             unicode_tau
             (\<lambda>var_tau. Expr_binop (b var_tau) unicode_Turnstile (Expr_apply \<open>not\<close> [Expr_apply var_OclForall_set [f_expr [b name], b (isub_name const_oclistypeof) ]])))
        (\<lambda>lem_tit lem_spec var_pre_post _ _. Lemma_by_assum
           lem_tit
           [(\<open>\<close>, True, Expr_And \<open>x\<close> (\<lambda>var_x. Expr_rewrite (Expr_apply var_pre_post [Expr_parenthesis (Expr_binop (b var_x) \<open>,\<close> (b var_x))]) \<open>=\<close> (b var_x)) )]
           lem_spec
           (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l var_oid = \<open>oid\<close>
              ; var_a = \<open>a\<close>
              ; var_t0 = \<open>t0\<close>
              ; s_empty = \<open>Map.empty\<close> in
            [ App_fix [var_oid, var_a]
            , App_let (Expr_pat var_t0) (Expr_apply \<open>state.make\<close>
                [ Expr_apply s_empty [Expr_binop (b var_oid) unicode_mapsto (Expr_apply (isub_name datatype_in) [Expr_apply (isub_name datatype_constr_name) (Expr_apply (datatype_ext_constr_name @@ mk_constr_name name name_next) [b var_a] # List_map (\<lambda>_. b \<open>None\<close>) l_attr)])]
                , b s_empty])
            , App [Tac_rule (Thm_where (Thm_str \<open>exI\<close>) [(\<open>x\<close>, Expr_parenthesis (Expr_binop (Expr_pat var_t0) \<open>,\<close> (Expr_pat var_t0)))]), Tac_simp_add_del [d \<open>OclValid\<close>] [d \<open>OclAllInstances_generic\<close>]]
            , App [Tac_simp_only (List_flatten [List_map Thm_str [ d var_OclForall_set, \<open>refl\<close>, \<open>if_True\<close> ], [Thm_simplified (Thm_str \<open>OclAllInstances_generic_defined\<close>) (Thm_str (d \<open>OclValid\<close>))]])]
            , App [Tac_simp_only (List_map (\<lambda>x. Thm_str (d x)) [\<open>OclAllInstances_generic\<close>, flatten [isub_name const_oclastype, \<open>_\<close>, unicode_AA]])]
            , App [s (Thm_str var_Abs_Set_inverse), Tac_simp_add [d \<open>bot_option\<close>]] ] )
           (Tacl_by [Tac_simp_add [d \<open>state.make\<close>, d \<open>OclNot\<close>]]))
        [Tac_simp]]) expr)"

definition "print_allinst_iskindof_eq = start_map Thy_lemma_by o map_class_gen (\<lambda>isub_name name _ _ _ _.
  print_allinst_istypeof_single isub_name name isub_name name const_ocliskindof dot_iskindof id (\<lambda>_. []))"

definition "print_allinst_iskindof_larger = start_map Thy_lemma_by o List_flatten o map_class_nupl2'_inh (\<lambda>name name2.
  print_allinst_istypeof_single (\<lambda>s. s @@ isub_of_str name) name (\<lambda>s. s @@ isub_of_str name2) name2 const_ocliskindof dot_iskindof id (\<lambda>_. []))"

end
