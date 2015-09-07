(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Floor2_examp.thy ---
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

theory  Floor2_examp
imports Floor1_examp
begin

section{* Translation of AST *}

subsection{* example *}

definition "print_examp_def_st_locale_distinct = \<open>distinct_oid\<close>"
definition "print_examp_def_st_locale_metis = M.metis (L.map T.thm [print_examp_def_st_locale_distinct, \<open>distinct_length_2_or_more\<close>])"
definition "print_examp_def_st_locale_aux f_ocli l = 
 (let b = \<lambda>s. Expr_basic [s] in
  map_prod
    id
    L.flatten
    (L.split
      (L.map
        (\<lambda> name.
           let (ocli, cpt) = f_ocli name 
             ; n = inst_name ocli
             ; ty = inst_ty ocli
             ; f = \<lambda>s. s @@ String.isub ty
             ; name_pers = print_examp_instance_name f n in
           ( Expr_oid var_oid_uniq (oidGetInh cpt)
           , [ ( [(b name_pers, Ty_base (f datatype_name))], None)
             , ( [(b n, Ty_base (wrap_oclty ty))]
               , Some (hol_definition n, Expr_rewrite (b n) \<open>=\<close> (Expr_lambda wildcard (Expr_some (Expr_some (b name_pers)))))) ]))
        l)))"
definition "print_examp_def_st_locale_make f_name f_ocli f_spec l =
 (let (oid, l_fix_assum) = print_examp_def_st_locale_aux f_ocli l
    ; ty_n = \<open>nat\<close> in
  \<lparr> HolThyLocale_name = f_name
  , HolThyLocale_header = L.flatten
                            [ [ ( L.map (\<lambda>x. (x, Ty_base ty_n)) oid
                                , Some ( print_examp_def_st_locale_distinct
                                       , Expr_app \<open>distinct\<close> [let e = Expr_list oid in
                                                                if oid = [] then Expr_annot' e (ty_n @@ \<open> list\<close>) else e])) ]
                            , l_fix_assum
                            , f_spec ] \<rparr>)"

definition "print_examp_def_st_locale_name n = \<open>state_\<close> @@ n"
definition "print_examp_def_st_locale = (\<lambda> OclDefSt n l \<Rightarrow> \<lambda>ocl.
 (\<lambda>d. (d, ocl))
  (print_examp_def_st_locale_make
    (\<open>state_\<close> @@ n)
    (\<lambda> OclDefCoreBinding name \<Rightarrow> case String.assoc name (D_input_instance ocl) of Some n \<Rightarrow> n)
    []
    l))"

definition "print_examp_def_st_defassoc_typecheck_gen l ocl =
 ([ raise_ml
      (case
         List.fold
           (\<lambda> OclDefCoreBinding name \<Rightarrow>
            \<lambda>(l, rbt).
             ( ( (if String.assoc name (D_input_instance ocl) = None then
                    Cons (Error, name)
                  else
                    id)
               o (if lookup rbt name = None then
                    id
                  else
                    Cons (Warning, name))) l
             , insert name () rbt))
           l
           ([], RBT.empty)
       of
         ([], _) \<Rightarrow> []
       | (l, _) \<Rightarrow> L.rev_map (\<lambda> (Error, n) \<Rightarrow> (Error, \<open>Extra variables on rhs: \<close> @@ n)
                            | (Warning, n) \<Rightarrow> (Warning, \<open>Duplicate variables on rhs: \<close> @@ n)) l)
      \<open> error(s)\<close> ])"

definition "print_examp_def_st_defassoc_typecheck = (\<lambda> OclDefSt _ l \<Rightarrow> \<lambda> ocl.
  (\<lambda>l_res. (L.map O'.ML l_res, ocl \<lparr> D_output_header_force := True \<rparr>))
  (print_examp_def_st_defassoc_typecheck_gen
    l
    ocl))"

definition "print_examp_def_st_mapsto_gen f ocl =
  L.map
    (\<lambda>(cpt, ocore).
        let b = \<lambda>s. Expr_basic [s]
          ; (ocli, exp) = case ocore of
               OclDefCoreBinding (name, ocli) \<Rightarrow>
                 (ocli, Some (b (print_examp_instance_name (\<lambda>s. s @@ String.isub (inst_ty ocli)) name))) in
        f (cpt, ocore) ocli exp)"

definition "print_examp_def_st_mapsto ocl l = list_bind id id
 (print_examp_def_st_mapsto_gen
    (\<lambda>(cpt, _) ocli. map_option (\<lambda>exp.
      Expr_binop (Expr_oid var_oid_uniq (oidGetInh cpt)) \<open>\<mapsto>\<close> (Expr_app (datatype_in @@ String.isub (inst_ty ocli)) [exp])))
    ocl
    l)"

definition "print_examp_def_st2 = (\<lambda> OclDefSt name l \<Rightarrow> \<lambda>ocl.
 (\<lambda>(l, l_st). (L.map O'.definition l, ocl \<lparr> D_input_state := (String.to_String\<^sub>b\<^sub>a\<^sub>s\<^sub>e name, l_st) # D_input_state ocl \<rparr>))
  (let b = \<lambda>s. Expr_basic [s]
     ; l = L.map (\<lambda> OclDefCoreBinding name \<Rightarrow> map_option (Pair name) (String.assoc name (D_input_instance ocl))) l
     ; (rbt, (map_self, map_username)) =
         (init_map_class 
           (ocl \<lparr> D_ocl_oid_start := oidReinitInh (D_ocl_oid_start ocl) \<rparr>)
           (L.map (\<lambda> Some (_, ocli, _) \<Rightarrow> ocli | None \<Rightarrow> ocl_instance_single_empty) l)
          :: (_ \<Rightarrow> _ \<times> _ \<times> (_ \<Rightarrow> ((_ \<Rightarrow> nat \<Rightarrow> _ \<Rightarrow> _) \<Rightarrow> _
                        \<Rightarrow> (ocl_ty_class option \<times> (ocl_ty \<times> ocl_data_shallow) option) list) option)) \<times> _ \<times> _)
     ; (l_st, l_assoc) = L.mapM (\<lambda> o_n l_assoc.
           case o_n of
              Some (name, ocli, cpt) \<Rightarrow> ([(cpt, OclDefCoreBinding (name, ocli))], (ocli, cpt) # l_assoc)
            | None \<Rightarrow> ([], l_assoc)) l []
     ; l_st = L.unique oidGetInh (L.flatten l_st) in

   ( [ Definition (Expr_rewrite (b name) \<open>=\<close> (Expr_app \<open>state.make\<close>
        ( Expr_app \<open>Map.empty\<close> (case print_examp_def_st_mapsto ocl l_st of None \<Rightarrow> [] | Some l \<Rightarrow> l)
        # [ print_examp_def_st_assoc (snd o rbt) map_self map_username l_assoc ]))) ]
   , l_st)))"

definition "print_examp_def_st_dom_name name = S.flatten [\<open>dom_\<close>, name]"
definition "print_examp_def_st_dom = (\<lambda> _ ocl.
 (\<lambda> l. (L.map O'.lemma l, ocl))
  (let (name, l_st) = map_prod String\<^sub>b\<^sub>a\<^sub>s\<^sub>e.to_String id (hd (D_input_state ocl))
     ; a = \<lambda>f x. Expr_app f [x]
     ; b = \<lambda>s. Expr_basic [s]
     ; d = hol_definition in
   [ Lemma
       (print_examp_def_st_dom_name name)
       [Expr_rewrite (a \<open>dom\<close> (a \<open>heap\<close> (b name))) \<open>=\<close> (Expr_set (L.map (\<lambda>(cpt, _). Expr_oid var_oid_uniq (oidGetInh cpt)) l_st))]
       []
       (C.by [M.auto_simp_add [d name]])]))"

definition "print_examp_def_st_dom_lemmas = (\<lambda> _ ocl.
 (\<lambda> l. (L.map O'.lemmas l, ocl))
  (let (name, _) = hd (D_input_state ocl) in
   [ Lemmas_simp \<open>\<close>
       [T.thm (print_examp_def_st_dom_name (String\<^sub>b\<^sub>a\<^sub>s\<^sub>e.to_String name))] ]))"

definition "print_examp_def_st_perm_name name = S.flatten [\<open>perm_\<close>, name]"
definition "print_examp_def_st_perm = (\<lambda> _ ocl.
 (\<lambda> l. (L.map O'.lemma l, ocl))
  (let (name, l_st) = map_prod String\<^sub>b\<^sub>a\<^sub>s\<^sub>e.to_String id (hd (D_input_state ocl))
     ; expr_app = let ocl = ocl \<lparr> D_ocl_oid_start := oidReinitInh (D_ocl_oid_start ocl) \<rparr> in
                  print_examp_def_st_mapsto
                    ocl
                    (rev l_st)
     ; b = \<lambda>s. Expr_basic [s]
     ; d = hol_definition
     ; (l_app, l_last) =
         case l_st of [] \<Rightarrow> ([], C.by [M.simp_add [d name]])
         | [_] \<Rightarrow> ([], C.by [M.simp_add [d name]])
         | _ \<Rightarrow>
           ( [ M.simp_add [d name]]
             # L.flatten (L.map (\<lambda>i_max. L.map (\<lambda>i. [M.subst_l (L.map String.of_nat [i_max - i]) (T.thm \<open>fun_upd_twist\<close>), print_examp_def_st_locale_metis]) (List.upt 0 i_max)) (List.upt 1 (List.length l_st)))
           , C.by [M.simp]) in
   case expr_app of None \<Rightarrow> [] | Some expr_app \<Rightarrow>
   [ Lemma
       (print_examp_def_st_perm_name name)
       [Expr_rewrite (b name) \<open>=\<close> (Expr_app \<open>state.make\<close>
          (Expr_app \<open>Map.empty\<close> expr_app # [Expr_app var_assocs [b name]]))]
       l_app
       l_last ]))"

definition "print_examp_def_st_allinst = (\<lambda> _ ocl.
 (\<lambda> l. (L.map O'.lemma l, ocl))
  (let a = \<lambda>f x. Expr_app f [x]
     ; b = \<lambda>s. Expr_basic [s]
     ; d = hol_definition
     ; (name_st, expr_app) =
         map_prod
           String\<^sub>b\<^sub>a\<^sub>s\<^sub>e.to_String
           (print_examp_def_st_mapsto_gen
             (\<lambda>(_, ocore) ocli _.
               ( ocore
               , ocli
               , case ocore of OclDefCoreBinding (name, _) \<Rightarrow> b name))
             (ocl \<lparr> D_ocl_oid_start := oidReinitInh (D_ocl_oid_start ocl) \<rparr>))
           (hd (D_input_state ocl)) in
   map_class_gen_h'_inh (\<lambda> isub_name name compare.
     let in_name = \<lambda>ocli. b (print_examp_instance_name (\<lambda>s. s @@ String.isub (inst_ty ocli)) (inst_name ocli))
       ; in_pers = \<lambda>ocli. a name (a (datatype_in @@ String.isub (inst_ty ocli)) (in_name ocli))
       ; expr_app = L.map (\<lambda>(ocore, ocli, exp).
              ( (ocore, ocli)
              , let asty = \<lambda>e. Expr_postunary e (b (dot_astype name))
                  ; exp_annot = [( [S.flatten [const_oclastype, String.isub name, \<open>_\<close>, inst_ty ocli]]
                                 , ( asty (case ocore of OclDefCoreBinding _ \<Rightarrow> exp)
                                   , Some (let und = \<lambda>e. Expr_lam \<open>_\<close> (\<lambda>_. Expr_some e) in
                                           Expr_rewrite (und (in_pers ocli))
                                                        \<open>=\<close>
                                                        (Expr_warning_parenthesis (asty (Expr_parenthesis
                                                                                          (Expr_annot' (und (Expr_some (in_name ocli))) (wrap_oclty (inst_ty ocli))))))))
                                 , True
                                 , ocore)] in
                case compare (inst_ty ocli) of
                  EQ \<Rightarrow> [([], (exp, None), False, ocore)]
                | LT \<Rightarrow> exp_annot
                | GT \<Rightarrow> (case fold_list_attr None (\<lambda>ty _. Cons ty) (Inst_attr ocli) [] of Some name2 # _ \<Rightarrow>
                           if name \<triangleq> name2 then exp_annot
                           else [] | _ \<Rightarrow> [])
                | UN' \<Rightarrow> [])) expr_app
       ; (l_asty, ((l_spec, l_spec'), l_body)) = map_prod (M.simp_add_del [] o L.flatten)
                                                          (map_prod L.split id o L.split)
                                                          (L.split (L.flatten (L.map snd expr_app)))
       ; only_assms = Cons (M.simp_all_only' [ T.thms \<open>assms\<close> ])
       ; l_assum = L.flatten [ L.map (\<lambda> ((_, ocli), l).
                                              (\<open>\<close>, True, Expr_rewrite (in_pers ocli) (if l = [] then \<open>=\<close> else \<open>\<noteq>\<close>) (b \<open>None\<close>)))
                                           expr_app
                                , List.map_filter (map_option (\<lambda> e \<Rightarrow> (\<open>\<close>, True, e))) l_spec'] in
     gen_pre_post0
       (\<lambda>s. S.flatten [ name_st, \<open>_\<close>, s, \<open>_exec_\<close>, name ])
       l_assum
       (\<lambda>f_expr f_mk _. Expr_binop
            (f_mk (b name_st))
            \<open>\<Turnstile>\<close>
            (Expr_binop (f_expr [b name]) \<open>\<doteq>\<close> (Expr_oclset l_spec)))
       (\<lambda>lem_tit lem_assum lem_spec var_pre_post var_mk _. Lemma_assumes
         lem_tit
         (L.flatten [ lem_assum
                       , [(\<open>\<close>, True, Expr_And \<open>a\<close> (\<lambda>var_a. Expr_rewrite (a var_pre_post (a var_mk (b var_a))) \<open>=\<close> (b var_a)))]])
         lem_spec
         (L.map C.apply
           (L.flatten
            [ [[M.subst (T.thm (print_examp_def_st_perm_name name_st))]]
            , [[M.simp_only (L.map (T.thm o d)
                                        (\<open>state.make\<close> # L.map (\<lambda>(_, OclDefCoreBinding (n, _)) \<Rightarrow> n) l_body))]]
            , fst (L.mapM (\<lambda> expr l_spec.
                let mk_StrictRefEq_including = \<lambda>l.  M.rule (T.thm \<open>const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including\<close>)
                                                  # l_asty
                                                  # l_asty
                                                  # M.simp
                                                  # l
                  ; (state_update_vs_allInstances_generic, l_spec, l_OclIncluding_cong) =
                      let f = Cons M.simp in
                      case expr of ((ocore, _), []) \<Rightarrow>
                        ( \<open>state_update_vs_allInstances_generic_ntc\<close>
                        , l_spec
                        , f (if l_spec = [] then
                               [M.rule (T.thm \<open>const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_empty\<close>), M.simp]
                             else
                               mk_StrictRefEq_including []))
                      | _ \<Rightarrow>
                        ( \<open>state_update_vs_allInstances_generic_tc\<close>
                        , tl l_spec
                        , ( M.blast None
                          # f (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l f = \<lambda>l.  M.option [M.simp_only [T.symmetric (T.thms \<open>assms\<close>)]]
                                              # M.simp_add (L.map d [\<open>valid\<close>, \<open>OclValid\<close>, \<open>bot_fun\<close>, \<open>bot_option\<close>])
                                              # l in
                               mk_StrictRefEq_including (M.rule (T.thm \<open>OclIncluding_cong\<close>) # f (f []))))) in
                ( M.subst (T.thm state_update_vs_allInstances_generic)
                  # M.simp
                  # M.simp
                  # M.option [print_examp_def_st_locale_metis]
                  # M.simp_only' [ T.thms \<open>assms\<close> ]
                  # l_OclIncluding_cong
                , l_spec) ) expr_app l_spec)
            , [[M.rule (T.thm \<open>state_update_vs_allInstances_generic_empty\<close>)]] ]))
         (C.by (if l_spec = [] then [ M.simp ]
                   else only_assms [ M.option [M.simp_all_add [d (S.flatten [isub_name const_oclastype, \<open>_\<AA>\<close>])]]])) )
       (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l l = [ M.simp_all ] in if l_assum = [] then l else only_assms l))
     (case D_input_class ocl of Some class_spec \<Rightarrow> class_spec)))"

definition "merge_unique_gen f l = List.fold (List.fold (\<lambda>x. case f x of Some (x, v) \<Rightarrow> RBT.insert x v | None \<Rightarrow> id)) l RBT.empty"
definition "merge_unique f l = RBT.entries (merge_unique_gen f l)"
definition "merge_unique' = L.map snd o merge_unique (\<lambda> (a, b). ((\<lambda>x. Some (x, (a, b))) o oidGetInh) a)"

definition "get_state f = (\<lambda> OclDefPP _ s_pre s_post \<Rightarrow> \<lambda> ocl. 
  let get_state = let l_st = D_input_state ocl in \<lambda>OclDefPPCoreBinding s \<Rightarrow> (s, case String.assoc s l_st of None \<Rightarrow> [] | Some l \<Rightarrow> l)
    ; (s_pre, l_pre) = get_state s_pre
    ; (s_post, l_post) = case s_post of None \<Rightarrow> (s_pre, l_pre) | Some s_post \<Rightarrow> get_state s_post in
  f (s_pre, l_pre)
    (s_post, l_post)
    ((s_pre, l_pre) # (if s_pre \<triangleq> s_post then
                         []
                       else
                         [ (s_post, l_post) ]))
    ocl)"

definition "print_pre_post_locale_aux f_ocli l =
 (let (oid, l_fix_assum) = print_examp_def_st_locale_aux f_ocli l in
  L.flatten [oid, L.flatten (L.map (L.map fst o fst) l_fix_assum) ])"

definition "print_pre_post_locale = get_state (\<lambda> (s_pre, l_pre) (s_post, l_post) l_pre_post. Pair
 (let f_ocli = \<lambda>(cpt, OclDefCoreBinding (_, ocli)) \<Rightarrow> (ocli, cpt) in
  print_examp_def_st_locale_make
    (\<open>pre_post_\<close> @@ s_pre @@ \<open>_\<close> @@ s_post)
    f_ocli
    (L.map (\<lambda>(s, l). ([], Some (s, Expr_app
                                        (print_examp_def_st_locale_name s)
                                        (print_pre_post_locale_aux f_ocli l))))
              l_pre_post)
    (merge_unique' [l_pre, l_post])))"

definition "print_pre_post_interp = get_state (\<lambda> _ _.
 Pair o L.map O'.interpretation o L.map
  (\<lambda>(s, l).
    let n = print_examp_def_st_locale_name s in
    Interpretation n n (print_pre_post_locale_aux (\<lambda>(cpt, OclDefCoreBinding (_, ocli)) \<Rightarrow> (ocli, cpt)) l) (C.by [M.rule (T.thm s)])))"

definition "print_pre_post_wff = get_state (\<lambda> (s_pre, l_pre) (s_post, l_post) l_pre_post ocl.
 (\<lambda> l. (L.map O'.lemma l, ocl))
  (let a = \<lambda>f x. Expr_app f [x]
     ; b = \<lambda>s. Expr_basic [s]
     ; d = hol_definition
     ; mk_n = \<lambda>s. print_examp_def_st_locale_name s @@ \<open>.\<close> @@ s in
   [ Lemma_assumes
       (S.flatten [\<open>basic_\<close>, s_pre, \<open>_\<close>, s_post, \<open>_wff\<close>])
       (L.map (\<lambda> (cpt, OclDefCoreBinding (_, ocli)) \<Rightarrow>
                    let ty = \<lambda>s. s @@ String.isub (inst_ty ocli)
                      ; n = inst_name ocli in
                    (\<open>\<close>, True, Expr_rewrite 
                                 (a \<open>oid_of\<close> (a (ty datatype_in) (b (print_examp_instance_name ty n))))
                                 \<open>=\<close>
                                 (Expr_oid var_oid_uniq (oidGetInh cpt))))
                 (merge_unique' [l_pre, l_post]))
       (a \<open>WFF\<close> (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l mk_n = b o mk_n in Expr_pair (mk_n s_pre) (mk_n s_post)))
       (L.map snd
         (merge_unique (\<lambda> [oid_b, oid_a] \<Rightarrow>
                          if oid_a = oid_b then
                            None
                          else
                            Some ( [oid_a, oid_b]
                                 , C.have0 \<open>\<close>
                                           True
                                           (Expr_rewrite (Expr_oid var_oid_uniq oid_a) \<open>\<noteq>\<close> (Expr_oid var_oid_uniq oid_b))
                                           (C.by [print_examp_def_st_locale_metis])))
                       [List.n_lists 2 (L.map (oidGetInh o fst)
                                                 (L.flatten (L.map snd l_pre_post)))]))
       (C.by [M.auto_simp_add (L.map d (\<open>WFF\<close> # L.map (mk_n o fst) l_pre_post))])] ))"

definition "print_pre_post_where = get_state (\<lambda> (s_pre, l_pre) (s_post, l_post) l_pre_post ocl.
 (\<lambda> l. ((L.map O'.lemma o L.flatten) l, ocl))
  (let a = \<lambda>f x. Expr_app f [x]
     ; b = \<lambda>s. Expr_basic [s]
     ; d = hol_definition
     ; mk_n = \<lambda>s. print_examp_def_st_locale_name s @@ \<open>.\<close> @@ s
     ; f_name = \<lambda>(cpt, ocore). Some (oidGetInh cpt, ocore)
     ; rbt_pre = merge_unique_gen f_name [l_pre]
     ; rbt_post = merge_unique_gen f_name [l_post] in
   L.map
     (\<lambda>x_pers_oid.
       let (x_where, l_ocore) =
           case (RBT.lookup rbt_pre x_pers_oid, RBT.lookup rbt_post x_pers_oid) of
             (Some ocore1, Some ocore2) \<Rightarrow> (\<open>OclIsMaintained\<close>, let l = [(ocore1, s_pre), (ocore2, s_post)] in
                                                               if String.to_list s_pre = String.to_list s_post then [hd l] else l)
           | (Some ocore, None) \<Rightarrow> (\<open>OclIsDeleted\<close>, [(ocore, s_pre)])
           | (None, Some ocore) \<Rightarrow> (\<open>OclIsNew\<close>, [(ocore, s_post)]) in
       L.map
         (\<lambda> (OclDefCoreBinding (name, ocli), name_st) \<Rightarrow>
           Lemma_assumes
             (S.flatten [var_oid_uniq, String.of_natural (case x_pers_oid of Oid i \<Rightarrow> i), s_pre, s_post, \<open>_\<close>, name_st, \<open>_\<close>, x_where])
             [(\<open>\<close>, True, Expr_rewrite (a \<open>oid_of\<close> (b (print_examp_instance_name (\<lambda>s. s @@ String.isub (inst_ty ocli)) (inst_name ocli))))
                                      \<open>=\<close>
                                      (Expr_oid var_oid_uniq x_pers_oid))]
             (Expr_binop (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l mk_n = b o mk_n in Expr_pair (mk_n s_pre) (mk_n s_post))
                         \<open>\<Turnstile>\<close>
                         (a x_where (b name)))
             [C.apply [M.simp_add (L.map d (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l l = [ mk_n s_post, name, x_where, \<open>OclValid\<close>, const_oid_of \<open>option\<close> ] in
                                             case l_pre_post of [_] \<Rightarrow> l | _ \<Rightarrow> mk_n s_pre # l))]]
             (C.by [M.option [print_examp_def_st_locale_metis]]))
         l_ocore)
     (RBT.keys (RBT.union rbt_pre rbt_post)) ))"

end
