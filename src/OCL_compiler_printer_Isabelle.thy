(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_printer_Isabelle.thy ---
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013-2014 Universite Paris-Sud, France
 *               2013-2014 IRT SystemX, France
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

theory  OCL_compiler_printer_Isabelle
imports OCL_compiler_meta_Isabelle
        OCL_compiler_printer_Pure
        OCL_compiler_printer_SML
begin


subsection{* s of ... *} (* s_of *)

context s_of
begin
definition "s_of_dataty _ = (\<lambda> Datatype n l \<Rightarrow>
  sprintf2 (STR ''datatype %s = %s'')
    (To_string n)
    (String_concat (STR ''
                        | '')
      (List_map
        (\<lambda>(n,l).
         sprintf2 (STR ''%s %s'')
           (To_string n)
           (String_concat (STR '' '')
            (List_map
              (\<lambda> Opt o_ \<Rightarrow> sprintf1 (STR ''\"%s option\"'') (To_string o_)
               | Raw o_ \<Rightarrow> sprintf1 (STR ''%s'') (To_string o_))
              l))) l) ))"

fun_quick s_of_rawty where "s_of_rawty e = (\<lambda>
    Ty_base s \<Rightarrow> To_string s
  | Ty_apply name l \<Rightarrow> sprintf2 (STR ''%s %s'') (let s = String_concat (STR '', '') (List.map s_of_rawty l) in
                                                 case l of [_] \<Rightarrow> s | _ \<Rightarrow> sprintf1 (STR ''(%s)'') s)
                                                (s_of_rawty name)
  | Ty_arrow ty1 ty2 \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_rawty ty1) (To_string unicode_Rightarrow) (s_of_rawty ty2)
  | Ty_times ty1 ty2 \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_rawty ty1) (To_string unicode_times) (s_of_rawty ty2)) e"

definition "s_of_ty_synonym _ = (\<lambda> Type_synonym n l \<Rightarrow>
    sprintf2 (STR ''type_synonym %s = \"%s\"'') (To_string n) (s_of_rawty l))"

fun_quick s_of_expr where "s_of_expr e = (\<lambda>
    Expr_case e l \<Rightarrow> sprintf2 (STR ''(case %s of %s)'') (s_of_expr e) (String_concat (STR ''
    | '') (List.map (\<lambda> (s1, s2) \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr s1) (To_string unicode_Rightarrow) (s_of_expr s2)) l))
  | Expr_rewrite e1 symb e2 \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr e1) (To_string symb) (s_of_expr e2)
  | Expr_basic l \<Rightarrow> sprintf1 (STR ''%s'') (String_concat (STR '' '') (List_map To_string l))
  | Expr_oid tit s \<Rightarrow> sprintf2 (STR ''%s%d'') (To_string tit) (To_oid s)
  | Expr_binop e1 s e2 \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr e1) (s_of_expr (Expr_basic [s])) (s_of_expr e2)
  | Expr_annot0 e s \<Rightarrow> sprintf2 (STR ''(%s::%s)'') (s_of_expr e) (s_of_rawty s)
  | Expr_bind symb l e \<Rightarrow> sprintf3 (STR ''(%s%s. %s)'') (To_string symb) (String_concat (STR '' '') (List_map To_string l)) (s_of_expr e)
  | Expr_bind0 symb e1 e2 \<Rightarrow> sprintf3 (STR ''(%s%s. %s)'') (To_string symb) (s_of_expr e1) (s_of_expr e2)
  | Expr_function l \<Rightarrow> sprintf2 (STR ''(%s %s)'') (To_string unicode_lambda) (String_concat (STR ''
    | '') (List.map (\<lambda> (s1, s2) \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr s1) (To_string unicode_Rightarrow) (s_of_expr s2)) l))
  (*| Expr_apply s [e] \<Rightarrow> sprintf2 (STR ''(%s %s)'') (To_string s) (s_of_expr e)*)
  | Expr_apply s l \<Rightarrow> sprintf2 (STR ''(%s %s)'') (To_string s) (String_concat (STR '' '') (List.map (\<lambda> e \<Rightarrow> sprintf1 (STR ''(%s)'') (s_of_expr e)) l))
  | Expr_applys e l \<Rightarrow> sprintf2 (STR ''((%s) %s)'') (s_of_expr e) (String_concat (STR '' '') (List.map (\<lambda> e \<Rightarrow> sprintf1 (STR ''(%s)'') (s_of_expr e)) l))
  | Expr_postunary e1 e2 \<Rightarrow> sprintf2 (STR ''%s %s'') (s_of_expr e1) (s_of_expr e2)
  | Expr_preunary e1 e2 \<Rightarrow> sprintf2 (STR ''%s %s'') (s_of_expr e1) (s_of_expr e2)
  | Expr_paren p_left p_right e \<Rightarrow> sprintf3 (STR ''%s%s%s'') (To_string p_left) (s_of_expr e) (To_string p_right)
  | Expr_if_then_else e_if e_then e_else \<Rightarrow> sprintf3 (STR ''if %s then %s else %s'') (s_of_expr e_if) (s_of_expr e_then) (s_of_expr e_else)
  | Expr_inner pure \<Rightarrow> s_of_pure_term pure) e"

definition "s_of_instantiation_class _ = (\<lambda> Instantiation n n_def expr \<Rightarrow>
    let name = To_string n in
    sprintf4 (STR ''instantiation %s :: object
begin
  definition %s_%s_def : \"%s\"
  instance ..
end'')
      name
      (To_string n_def)
      name
      (s_of_expr expr))"

definition "s_of_defs_overloaded _ = (\<lambda> Defs_overloaded n e \<Rightarrow>
    sprintf2 (STR ''defs(overloaded) %s : \"%s\"'') (To_string n) (s_of_expr e))"

definition "s_of_consts_class _ = (\<lambda> Consts_raw n ty symb \<Rightarrow>
    sprintf4 (STR ''consts %s :: \"%s\" (\"%s %s\")'') (To_string n) (s_of_rawty ty) (To_string Consts_value) (To_string symb))"

definition "s_of_definition_hol _ = (\<lambda>
    Definition e \<Rightarrow> sprintf1 (STR ''definition \"%s\"'') (s_of_expr e)
  | Definition_abbrev name (abbrev, prio) e \<Rightarrow> sprintf4 (STR ''definition %s (\"(1%s)\" %d)
  where \"%s\"'') (To_string name) (s_of_expr abbrev) (To_nat prio) (s_of_expr e)
  | Definition_abbrev0 name abbrev e \<Rightarrow> sprintf3 (STR ''definition %s (\"%s\")
  where \"%s\"'') (To_string name) (s_of_expr abbrev) (s_of_expr e))"

fun_quick s_of_ntheorem_aux where "s_of_ntheorem_aux lacc e =
  ((* FIXME regroup all the 'let' declarations at the beginning *)
   (*let f_where = (\<lambda>l. (STR ''where'', String_concat (STR '' and '')
                                        (List_map (\<lambda>(var, expr). sprintf2 (STR ''%s = \"%s\"'')
                                                        (To_string var)
                                                        (s_of_expr expr)) l)))
     ; f_of = (\<lambda>l. (STR ''of'', String_concat (STR '' '')
                                  (List_map (\<lambda>expr. sprintf1 (STR ''\"%s\"'')
                                                        (s_of_expr expr)) l)))
     ; f_symmetric = (STR ''symmetric'', STR '''')
     ; s_base = (\<lambda>s lacc. sprintf2 (STR ''%s[%s]'') (To_string s) (String_concat (STR '', '') (List_map (\<lambda>(s, x). sprintf2 (STR ''%s %s'') s x) lacc))) in
   *)\<lambda> Thm_str s \<Rightarrow> To_string s
   | Thm_THEN (Thm_str s) e2 \<Rightarrow>
let s_base = (\<lambda>s lacc. sprintf2 (STR ''%s[%s]'') (To_string s) (String_concat (STR '', '') (List_map (\<lambda>(s, x). sprintf2 (STR ''%s %s'') s x) lacc))) in
       s_base s ((STR ''THEN'', s_of_ntheorem_aux [] e2) # lacc)
   | Thm_THEN e1 e2 \<Rightarrow> s_of_ntheorem_aux ((STR ''THEN'', s_of_ntheorem_aux [] e2) # lacc) e1
   | Thm_simplified (Thm_str s) e2 \<Rightarrow>
let s_base = (\<lambda>s lacc. sprintf2 (STR ''%s[%s]'') (To_string s) (String_concat (STR '', '') (List_map (\<lambda>(s, x). sprintf2 (STR ''%s %s'') s x) lacc))) in
       s_base s ((STR ''simplified'', s_of_ntheorem_aux [] e2) # lacc)
   | Thm_simplified e1 e2 \<Rightarrow> s_of_ntheorem_aux ((STR ''simplified'', s_of_ntheorem_aux [] e2) # lacc) e1
   | Thm_symmetric (Thm_str s) \<Rightarrow>
let s_base = (\<lambda>s lacc. sprintf2 (STR ''%s[%s]'') (To_string s) (String_concat (STR '', '') (List_map (\<lambda>(s, x). sprintf2 (STR ''%s %s'') s x) lacc))) in
let f_symmetric = (STR ''symmetric'', STR '''') in
       s_base s (f_symmetric # lacc)
   | Thm_symmetric e1 \<Rightarrow>
let f_symmetric = (STR ''symmetric'', STR '''') in
       s_of_ntheorem_aux (f_symmetric # lacc) e1
   | Thm_where (Thm_str s) l \<Rightarrow>
let s_base = (\<lambda>s lacc. sprintf2 (STR ''%s[%s]'') (To_string s) (String_concat (STR '', '') (List_map (\<lambda>(s, x). sprintf2 (STR ''%s %s'') s x) lacc))) in
let f_where = (\<lambda>l. (STR ''where'', String_concat (STR '' and '')
                                        (List_map (\<lambda>(var, expr). sprintf2 (STR ''%s = \"%s\"'')
                                                        (To_string var)
                                                        (s_of_expr expr)) l))) in
       s_base s (f_where l # lacc)
   | Thm_where e1 l \<Rightarrow>
let f_where = (\<lambda>l. (STR ''where'', String_concat (STR '' and '')
                                        (List_map (\<lambda>(var, expr). sprintf2 (STR ''%s = \"%s\"'')
                                                        (To_string var)
                                                        (s_of_expr expr)) l))) in
       s_of_ntheorem_aux (f_where l # lacc) e1
   | Thm_of (Thm_str s) l \<Rightarrow>
let s_base = (\<lambda>s lacc. sprintf2 (STR ''%s[%s]'') (To_string s) (String_concat (STR '', '') (List_map (\<lambda>(s, x). sprintf2 (STR ''%s %s'') s x) lacc))) in
let f_of = (\<lambda>l. (STR ''of'', String_concat (STR '' '')
                                  (List_map (\<lambda>expr. sprintf1 (STR ''\"%s\"'')
                                                        (s_of_expr expr)) l))) in
       s_base s (f_of l # lacc)
   | Thm_of e1 l \<Rightarrow>
let f_of = (\<lambda>l. (STR ''of'', String_concat (STR '' '')
                                  (List_map (\<lambda>expr. sprintf1 (STR ''\"%s\"'')
                                                        (s_of_expr expr)) l))) in
       s_of_ntheorem_aux (f_of l # lacc) e1
   | Thm_OF (Thm_str s) e2 \<Rightarrow>
let s_base = (\<lambda>s lacc. sprintf2 (STR ''%s[%s]'') (To_string s) (String_concat (STR '', '') (List_map (\<lambda>(s, x). sprintf2 (STR ''%s %s'') s x) lacc))) in
       s_base s ((STR ''OF'', s_of_ntheorem_aux [] e2) # lacc)
   | Thm_OF e1 e2 \<Rightarrow> s_of_ntheorem_aux ((STR ''OF'', s_of_ntheorem_aux [] e2) # lacc) e1) e"

definition "s_of_ntheorem = s_of_ntheorem_aux []"

definition "s_of_ntheorem_list l = String_concat (STR ''
                            '') (List_map s_of_ntheorem l)"

definition "s_of_lemmas_simp _ = (\<lambda> Lemmas_simp s l \<Rightarrow>
    sprintf2 (STR ''lemmas%s [simp,code_unfold] = %s'')
      (if s = [] then STR '''' else To_string ('' '' @@ s))
      (s_of_ntheorem_list l)
                                  | Lemmas_simps s l \<Rightarrow>
    sprintf2 (STR ''lemmas%s [simp,code_unfold] = %s'')
      (if s = [] then STR '''' else To_string ('' '' @@ s))
      (String_concat (STR ''
                            '') (List_map To_string l)))"

fun_quick s_of_tactic where "s_of_tactic expr = (\<lambda>
    Tac_rule s \<Rightarrow> sprintf1 (STR ''rule %s'') (s_of_ntheorem s)
  | Tac_drule s \<Rightarrow> sprintf1 (STR ''drule %s'') (s_of_ntheorem s)
  | Tac_erule s \<Rightarrow> sprintf1 (STR ''erule %s'') (s_of_ntheorem s)
  | Tac_intro l \<Rightarrow> sprintf1 (STR ''intro %s'') (String_concat (STR '' '') (List_map s_of_ntheorem l))
  | Tac_elim s \<Rightarrow> sprintf1 (STR ''elim %s'') (s_of_ntheorem s)
  | Tac_subst_l l s =>
      if l = [''0''] then
        sprintf1 (STR ''subst %s'') (s_of_ntheorem s)
      else
        sprintf2 (STR ''subst (%s) %s'') (String_concat (STR '' '') (List_map To_string l)) (s_of_ntheorem s)
  | Tac_insert l => sprintf1 (STR ''insert %s'') (String_concat (STR '' '') (List_map s_of_ntheorem l))
  | Tac_plus t \<Rightarrow> sprintf1 (STR ''(%s)+'') (String_concat (STR '', '') (List.map s_of_tactic t))
  | Tac_option t \<Rightarrow> sprintf1 (STR ''(%s)?'') (String_concat (STR '', '') (List.map s_of_tactic t))
  | Tac_blast None \<Rightarrow> sprintf0 (STR ''blast'')
  | Tac_blast (Some n) \<Rightarrow> sprintf1 (STR ''blast %d'') (To_nat n)
  | Tac_simp \<Rightarrow> sprintf0 (STR ''simp'')
  | Tac_simp_add l \<Rightarrow> sprintf1 (STR ''simp add: %s'') (String_concat (STR '' '') (List_map To_string l))
  | Tac_simp_add0 l \<Rightarrow> sprintf1 (STR ''simp add: %s'') (String_concat (STR '' '') (List_map s_of_ntheorem l))
  | Tac_simp_add_del l_add l_del \<Rightarrow> sprintf2 (STR ''simp add: %s del: %s'') (String_concat (STR '' '') (List_map To_string l_add)) (String_concat (STR '' '') (List_map To_string l_del))
  | Tac_simp_only l \<Rightarrow> sprintf1 (STR ''simp only: %s'') (String_concat (STR '' '') (List_map s_of_ntheorem l))
  | Tac_simp_all \<Rightarrow> sprintf0 (STR ''simp_all'')
  | Tac_simp_all_add s \<Rightarrow> sprintf1 (STR ''simp_all add: %s'') (To_string s)
  | Tac_auto_simp_add l \<Rightarrow> sprintf1 (STR ''auto simp: %s'') (String_concat (STR '' '') (List_map To_string l))
  | Tac_auto_simp_add_split l_simp l_split \<Rightarrow>
      let f = String_concat (STR '' '') in
      sprintf2 (STR ''auto simp: %s split: %s'') (f (List_map s_of_ntheorem l_simp)) (f (List_map To_string l_split))
  | Tac_rename_tac l \<Rightarrow> sprintf1 (STR ''rename_tac %s'') (String_concat (STR '' '') (List_map To_string l))
  | Tac_case_tac e \<Rightarrow> sprintf1 (STR ''case_tac \"%s\"'') (s_of_expr e)) expr"

definition "s_of_tactic_last = (\<lambda> Tacl_done \<Rightarrow> STR ''done''
                                | Tacl_by l_apply \<Rightarrow> sprintf1 (STR ''by(%s)'') (String_concat (STR '', '') (List_map s_of_tactic l_apply))
                                | Tacl_sorry \<Rightarrow> STR ''sorry'')"

definition "s_of_tac_apply = (
  let scope_thesis = sprintf1 (STR ''  proof - %s show ?thesis
'') in
  \<lambda> App [] \<Rightarrow> STR ''''
  | App l_apply \<Rightarrow> sprintf1 (STR ''  apply(%s)
'') (String_concat (STR '', '') (List_map s_of_tactic l_apply))
  | App_using l \<Rightarrow> sprintf1 (STR ''  using %s
'') (String_concat (STR '' '') (List_map s_of_ntheorem l))
  | App_unfolding l \<Rightarrow> sprintf1 (STR ''  unfolding %s
'') (String_concat (STR '' '') (List_map s_of_ntheorem l))
  | App_let e_name e_body \<Rightarrow> scope_thesis (sprintf2 (STR ''let %s = \"%s\"'') (s_of_expr e_name) (s_of_expr e_body))
  | App_have n e e_last \<Rightarrow> scope_thesis (sprintf3 (STR ''have %s: \"%s\" %s'') (To_string n) (s_of_expr e) (s_of_tactic_last e_last))
  | App_fix l \<Rightarrow> scope_thesis (sprintf1 (STR ''fix %s'') (String_concat (STR '' '') (List_map To_string l))))"

definition "s_of_lemma_by _ =
 (\<lambda> Lemma_by n l_spec l_apply tactic_last \<Rightarrow>
    sprintf4 (STR ''lemma %s : \"%s\"
%s%s'')
      (To_string n)
      (String_concat (sprintf1 (STR '' %s '') (To_string unicode_Longrightarrow)) (List_map s_of_expr l_spec))
      (String_concat (STR '''') (List_map (\<lambda> [] \<Rightarrow> STR '''' | l_apply \<Rightarrow> sprintf1 (STR ''  apply(%s)
'') (String_concat (STR '', '') (List_map s_of_tactic l_apply))) l_apply))
      (s_of_tactic_last tactic_last)
  | Lemma_by_assum n l_spec concl l_apply tactic_last \<Rightarrow>
    sprintf5 (STR ''lemma %s : %s
%s%s %s'')
      (To_string n)
      (String_concat (STR '''') (List_map (\<lambda>(n, b, e).
          sprintf2 (STR ''
assumes %s\"%s\"'')
            (let n = if b then flatten [n, ''[simp]''] else n in
             if n = '''' then STR '''' else sprintf1 (STR ''%s: '') (To_string n))
            (s_of_expr e)) l_spec
       @@
       [sprintf1 (STR ''
shows \"%s\"'') (s_of_expr concl)]))
      (String_concat (STR '''') (List_map s_of_tac_apply l_apply))
      (s_of_tactic_last tactic_last)
      (String_concat (STR '' '')
        (List_map
          (\<lambda>_. STR ''qed'')
          (filter (\<lambda> App_let _ _ \<Rightarrow> True | App_have _ _ _ \<Rightarrow> True | App_fix _ \<Rightarrow> True | _ \<Rightarrow> False) l_apply))))"

definition "s_of_axiom _ = (\<lambda> Axiom n e \<Rightarrow> sprintf2 (STR ''axiomatization where %s:
\"%s\"'') (To_string n) (s_of_expr e))"


definition "s_of_text _ = (\<lambda> Text s \<Rightarrow> sprintf1 (STR ''text{* %s *}'') (To_string s))"

definition "s_of_ml _ = (\<lambda> Ml e \<Rightarrow> sprintf1 (STR ''ML{* %s *}'') (s_of_sexpr e))"

definition "s_of_thm _ = (\<lambda> Thm thm \<Rightarrow> sprintf1 (STR ''thm %s'') (s_of_ntheorem_list thm))"

end

end
