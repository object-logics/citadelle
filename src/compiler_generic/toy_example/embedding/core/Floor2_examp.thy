(*****************************************************************************
 * A Meta-Model for the Isabelle API
 *
 * Copyright (c) 2013-2015 Université Paris-Saclay, Univ Paris Sud, France
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

chapter{* Part ... *}

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

end
