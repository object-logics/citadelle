(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_printer_Isabelle.thy ---
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

theory  OCL_compiler_printer_Isabelle
imports OCL_compiler_meta_Isabelle
        OCL_compiler_printer_Pure
        OCL_compiler_printer_SML
begin


subsection{* s of ... *} (* s_of *)

context s_of
begin
fun_quick s_of_rawty where "s_of_rawty e = (\<lambda>
    Ty_base s \<Rightarrow> To_string s
  | Ty_apply name l \<Rightarrow> sprintf2 (STR ''%s %s'') (let s = String_concat (STR '', '') (List.map s_of_rawty l) in
                                                 case l of [_] \<Rightarrow> s | _ \<Rightarrow> sprintf1 (STR ''(%s)'') s)
                                                (s_of_rawty name)
  | Ty_apply_bin s ty1 ty2 \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_rawty ty1) (To_string s) (s_of_rawty ty2)) e"

definition "s_of_dataty _ = (\<lambda> Datatype n l \<Rightarrow>
  sprintf2 (STR ''datatype %s = %s'')
    (To_string n)
    (String_concat (STR ''
                        | '')
      (List_map
        (\<lambda>(n,l).
         sprintf2 (STR ''%s %s'')
           (To_string n)
           (String_concat (STR '' '') (List_map (\<lambda>x. sprintf1 (STR ''\"%s\"'') (s_of_rawty x)) l))) l) ))"

definition "s_of_ty_synonym _ = (\<lambda> Type_synonym n l \<Rightarrow>
    sprintf2 (STR ''type_synonym %s = \"%s\"'') (To_string n) (s_of_rawty l))"

fun_quick s_of_expr where "s_of_expr e = (\<lambda>
    Expr_rewrite e1 symb e2 \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr e1) (To_string symb) (s_of_expr e2)
  | Expr_basic l \<Rightarrow> sprintf1 (STR ''%s'') (String_concat (STR '' '') (List_map To_string l))
  | Expr_oid tit s \<Rightarrow> sprintf2 (STR ''%s%d'') (To_string tit) (To_oid s)
  | Expr_annot0 e s \<Rightarrow> sprintf2 (STR ''(%s::%s)'') (s_of_expr e) (s_of_rawty s)
  | Expr_bind0 symb e1 e2 \<Rightarrow> sprintf3 (STR ''(%s%s. %s)'') (To_string symb) (s_of_expr e1) (s_of_expr e2)
  | Expr_function0 e_case l \<Rightarrow> sprintf2 (STR ''(%s %s)'')
      (case e_case of None \<Rightarrow> To_string unicode_lambda
                    | Some e \<Rightarrow> sprintf1 (STR ''case %s of'') (s_of_expr e))
      (String_concat (STR ''
    | '') (List.map (\<lambda> (s1, s2) \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr s1) (To_string unicode_Rightarrow) (s_of_expr s2)) l))
  | Expr_applys00 e l \<Rightarrow> sprintf2 (STR ''%s %s'') (s_of_expr e) (String_concat (STR '' '') (List.map (\<lambda> e \<Rightarrow> sprintf1 (STR ''%s'') (s_of_expr e)) l))
  | Expr_paren p_left p_right e \<Rightarrow> sprintf3 (STR ''%s%s%s'') (To_string p_left) (s_of_expr e) (To_string p_right)
  | Expr_if_then_else e_if e_then e_else \<Rightarrow> sprintf3 (STR ''if %s then %s else %s'') (s_of_expr e_if) (s_of_expr e_then) (s_of_expr e_else)
  | Expr_inner0 l pure \<Rightarrow> s_of_pure_term (List_map To_string l) pure) e"

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

definition "s_of_ntheorems = (\<lambda> Thms_single thy \<Rightarrow> s_of_ntheorem thy
                              | Thms_mult thy \<Rightarrow> To_string thy)"

definition "s_of_ntheorem_l l = String_concat (STR ''
                            '') (List_map s_of_ntheorem l)"
definition "s_of_ntheorem_l1 l = String_concat (STR '' '') (List_map s_of_ntheorem l)"

definition "s_of_ntheorems_l l = String_concat (STR '' '') (List_map s_of_ntheorems l)"

definition "s_of_lemmas_simp _ = (\<lambda> Lemmas_simp_opt simp s l \<Rightarrow>
    sprintf3 (STR ''lemmas%s%s = %s'')
      (if s = [] then STR '''' else To_string ('' '' @@ s))
      (if simp then STR ''[simp,code_unfold]'' else STR '''')
      (s_of_ntheorem_l l)
                                  | Lemmas_simps s l \<Rightarrow>
    sprintf2 (STR ''lemmas%s [simp,code_unfold] = %s'')
      (if s = [] then STR '''' else To_string ('' '' @@ s))
      (String_concat (STR ''
                            '') (List_map To_string l)))"

definition "s_of_attrib (attr::String.literal) l = (* error reflection: to be merged *)
 (if l = [] then
    STR ''''
  else
    sprintf2 (STR '' %s: %s'') attr (s_of_ntheorems_l l))"

definition "s_of_attrib1 (attr::String.literal) l = (* error reflection: to be merged *)
 (if l = [] then
    STR ''''
  else
    sprintf2 (STR '' %s: %s'') attr (String_concat (STR '' '') (List_map To_string l)))"

fun_quick s_of_tactic where "s_of_tactic expr = (\<lambda>
    Tact_rule0 o_s \<Rightarrow> sprintf1 (STR ''rule%s'') (case o_s of None \<Rightarrow> STR ''''
                                                           | Some s \<Rightarrow> sprintf1 (STR '' %s'') (s_of_ntheorem s))
  | Tact_drule s \<Rightarrow> sprintf1 (STR ''drule %s'') (s_of_ntheorem s)
  | Tact_erule s \<Rightarrow> sprintf1 (STR ''erule %s'') (s_of_ntheorem s)
  | Tact_intro l \<Rightarrow> sprintf1 (STR ''intro %s'') (s_of_ntheorem_l1 l)
  | Tact_elim s \<Rightarrow> sprintf1 (STR ''elim %s'') (s_of_ntheorem s)
  | Tact_subst_l0 asm l s =>
      let s_asm = if asm then STR ''(asm) '' else STR '''' in
      if l = [''0''] then
        sprintf2 (STR ''subst %s%s'') s_asm (s_of_ntheorem s)
      else
        sprintf3 (STR ''subst %s(%s) %s'') s_asm (String_concat (STR '' '') (List_map To_string l)) (s_of_ntheorem s)
  | Tact_insert l => sprintf1 (STR ''insert %s'') (s_of_ntheorems_l l)
  | Tact_plus t \<Rightarrow> sprintf1 (STR ''(%s)+'') (String_concat (STR '', '') (List.map s_of_tactic t))
  | Tact_option t \<Rightarrow> sprintf1 (STR ''(%s)?'') (String_concat (STR '', '') (List.map s_of_tactic t))
  | Tact_one (Simp_only l) \<Rightarrow> sprintf1 (STR ''simp only: %s'') (s_of_ntheorems_l l)
  | Tact_one (Simp_add_del_split l1 l2 []) \<Rightarrow> sprintf2 (STR ''simp%s%s'')
      (s_of_attrib (STR ''add'') l1)
      (s_of_attrib (STR ''del'') l2)
  | Tact_one (Simp_add_del_split l1 l2 l3) \<Rightarrow> sprintf3 (STR ''simp%s%s%s'')
      (s_of_attrib (STR ''add'') l1)
      (s_of_attrib (STR ''del'') l2)
      (s_of_attrib (STR ''split'') l3)
  | Tact_all (Simp_only l) \<Rightarrow> sprintf1 (STR ''simp_all only: %s'') (s_of_ntheorems_l l)
  | Tact_all (Simp_add_del_split l1 l2 []) \<Rightarrow> sprintf2 (STR ''simp_all%s%s'')
      (s_of_attrib (STR ''add'') l1)
      (s_of_attrib (STR ''del'') l2)
  | Tact_all (Simp_add_del_split l1 l2 l3) \<Rightarrow> sprintf3 (STR ''simp_all%s%s%s'')
      (s_of_attrib (STR ''add'') l1)
      (s_of_attrib (STR ''del'') l2)
      (s_of_attrib (STR ''split'') l3)
  | Tact_auto_simp_add_split l_simp l_split \<Rightarrow> sprintf2 (STR ''auto%s%s'')
      (s_of_attrib (STR ''simp'') l_simp)
      (s_of_attrib1 (STR ''split'') l_split)
  | Tact_rename_tac l \<Rightarrow> sprintf1 (STR ''rename_tac %s'') (String_concat (STR '' '') (List_map To_string l))
  | Tact_case_tac e \<Rightarrow> sprintf1 (STR ''case_tac \"%s\"'') (s_of_expr e)
  | Tact_blast None \<Rightarrow> sprintf0 (STR ''blast'')
  | Tact_blast (Some n) \<Rightarrow> sprintf1 (STR ''blast %d'') (To_nat n)
  | Tact_clarify \<Rightarrow> sprintf0 (STR ''clarify'')) expr"

definition "s_of_tactic_last = (\<lambda> Tacl_done \<Rightarrow> STR ''done''
                                | Tacl_by l_apply \<Rightarrow> sprintf1 (STR ''by(%s)'') (String_concat (STR '', '') (List_map s_of_tactic l_apply))
                                | Tacl_sorry \<Rightarrow> STR ''sorry'')"

definition "s_of_tac_apply_end = (
  \<lambda> AppE [] \<Rightarrow> STR ''''
  | AppE l_apply \<Rightarrow> sprintf1 (STR ''  apply_end(%s)
'') (String_concat (STR '', '') (List_map s_of_tactic l_apply)))"

definition "s_of_tac_apply = (
  let thesis = STR ''?thesis''
    ; scope_thesis_gen = sprintf2 (STR ''  proof - %s show %s
'')
    ; scope_thesis = \<lambda>s. scope_thesis_gen s thesis in
  \<lambda> App [] \<Rightarrow> STR ''''
  | App l_apply \<Rightarrow> sprintf1 (STR ''  apply(%s)
'') (String_concat (STR '', '') (List_map s_of_tactic l_apply))
  | App_using0 l \<Rightarrow> sprintf1 (STR ''  using %s
'') (s_of_ntheorems_l l)
  | App_unfolding0 l \<Rightarrow> sprintf1 (STR ''  unfolding %s
'') (s_of_ntheorems_l l)
  | App_let e_name e_body \<Rightarrow> scope_thesis (sprintf2 (STR ''let %s = \"%s\"'') (s_of_expr e_name) (s_of_expr e_body))
  | App_have n e e_last \<Rightarrow> scope_thesis (sprintf3 (STR ''have %s: \"%s\" %s'') (To_string n) (s_of_expr e) (s_of_tactic_last e_last))
  | App_fix_let l l_let o_show _ \<Rightarrow>
      scope_thesis_gen
        (sprintf2 (STR ''fix %s%s'') (String_concat (STR '' '') (List_map To_string l))
                                     (String_concat
                                       (STR ''
''                                            )
                                       (List_map
                                         (\<lambda>(e_name, e_body).
                                           sprintf2 (STR ''          let %s = \"%s\"'') (s_of_expr e_name) (s_of_expr e_body))
                                         l_let)))
        (case o_show of None \<Rightarrow> thesis
                      | Some l_show \<Rightarrow> 
                          let g = STR [Char Nibble2 Nibble2] in
                          sprintf3 (STR ''%s%s%s'')
                            g
                            (String_concat (sprintf1 (STR '' %s '') (To_string unicode_Longrightarrow)) (List_map s_of_expr l_show))
                            g))"

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
       @@@
       [sprintf1 (STR ''
shows \"%s\"'') (s_of_expr concl)]))
      (String_concat (STR '''') (List_map s_of_tac_apply l_apply))
      (s_of_tactic_last tactic_last)
      (String_concat (STR '' '')
        (List_map
          (\<lambda>l_apply_e.
            sprintf1 (STR ''%sqed'')
              (if l_apply_e = [] then
                 STR ''''
               else
                 sprintf1 (STR ''
%s '') (String_concat (STR '''') (List_map s_of_tac_apply_end l_apply_e))))
          (List.map_filter
            (\<lambda> App_let _ _ \<Rightarrow> Some [] | App_have _ _ _ \<Rightarrow> Some [] | App_fix_let _ _ _ l \<Rightarrow> Some l | _ \<Rightarrow> None)
            (rev l_apply)))))"


definition "s_of_axiom _ = (\<lambda> Axiom n e \<Rightarrow> sprintf2 (STR ''axiomatization where %s:
\"%s\"'') (To_string n) (s_of_expr e))"


definition "s_of_text _ = (\<lambda> Text s \<Rightarrow> sprintf1 (STR ''text{* %s *}'') (To_string s))"

definition "s_of_ml _ = (\<lambda> Ml e \<Rightarrow> sprintf1 (STR ''ML{* %s *}'') (s_of_sexpr e))"

definition "s_of_thm _ = (\<lambda> Thm thm \<Rightarrow> sprintf1 (STR ''thm %s'') (s_of_ntheorem_l1 thm))"

end

lemmas [code] =
  (* def *)
  s_of.s_of_dataty_def
  s_of.s_of_ty_synonym_def
  s_of.s_of_instantiation_class_def
  s_of.s_of_defs_overloaded_def
  s_of.s_of_consts_class_def
  s_of.s_of_definition_hol_def
  s_of.s_of_ntheorem_def
  s_of.s_of_ntheorems_def
  s_of.s_of_ntheorem_l_def
  s_of.s_of_ntheorem_l1_def
  s_of.s_of_ntheorems_l_def
  s_of.s_of_lemmas_simp_def
  s_of.s_of_attrib_def
  s_of.s_of_attrib1_def
  s_of.s_of_tactic_last_def
  s_of.s_of_tac_apply_end_def
  s_of.s_of_tac_apply_def
  s_of.s_of_lemma_by_def
  s_of.s_of_axiom_def
  s_of.s_of_text_def
  s_of.s_of_ml_def
  s_of.s_of_thm_def

  (* fun *)
  s_of.s_of_rawty.simps
  s_of.s_of_expr.simps
  s_of.s_of_ntheorem_aux.simps
  s_of.s_of_tactic.simps

end
