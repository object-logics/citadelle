(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_printer_META.thy ---
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

theory  OCL_compiler_printer_META
imports OCL_compiler_parser_META
        OCL_compiler_printer_Isabelle
begin

subsection{* s of ... *} (* s_of *)

context s_of
begin

definition "s_of_sexpr_extended = (\<lambda>
    Sexpr_extended s \<Rightarrow> s_of_sexpr s
  | Sexpr_ocl ocl \<Rightarrow> s_of_sexpr
     (Sexpr_apply \<langle>''Generation_mode.update_compiler_config''\<rangle>
       [Sexpr_apply \<langle>''K''\<rangle> [Sexpr_let_open \<langle>''OCL''\<rangle> (Sexpr_basic [sml_of_ocl_unit sml_apply id ocl])]]))"

definition "s_of_section_title ocl = (\<lambda> Section_title n section_title \<Rightarrow>
  if D_disable_thy_output ocl then
    \<prec>''''\<succ>
  else
    sprint2 ''%s{* %s *}''\<acute>
      (To_string ((if n = 0 then \<langle>''''\<rangle>
                   else if n = 1 then \<langle>''sub''\<rangle>
                   else \<langle>''subsub''\<rangle>) @@ \<langle>''section''\<rangle>))
      (To_string section_title))"

fun_quick s_of_ctxt2_term_aux where "s_of_ctxt2_term_aux l e =
 (\<lambda> T_pure pure \<Rightarrow> (if l = [] then id else sprint2 ''(%s. (%s))''\<acute> (To_string (String_concatWith \<langle>'' ''\<rangle> (unicode_lambda # rev l))))
                     (s_of_pure_term [] pure)
  | T_to_be_parsed _ s \<Rightarrow> (if l = [] then id else sprint2 ''(%s. (%s))''\<acute> (To_string (String_concatWith \<langle>'' ''\<rangle> (unicode_lambda # rev l))))
                            (To_string s)
  | T_lambda s c \<Rightarrow> s_of_ctxt2_term_aux (s # l) c) e"
definition "s_of_ctxt2_term = s_of_ctxt2_term_aux []"

definition "s_of_ocl_deep_embed_ast _ =
 (let g = \<ordmasculine>Char Nibble2 Nibble2\<ordmasculine> in
  \<lambda> OclAstCtxtPrePost Floor2 ctxt \<Rightarrow>
      sprint5 ''Context[shallow] %s :: %s (%s) %s
%s''\<acute>
        (To_string (Ctxt_ty ctxt))
        (To_string (Ctxt_fun_name ctxt))
        (String_concat \<prec>'', ''\<succ>
          (List_map
            (\<lambda> (s, ty). sprint2 ''%s : %s''\<acute> (To_string s) (To_string (str_of_ty ty)))
            (Ctxt_fun_ty_arg ctxt)))
        (case Ctxt_fun_ty_out ctxt of None \<Rightarrow> \<prec>''''\<succ>
                                    | Some ty \<Rightarrow> sprint1 '': %s''\<acute> (To_string (str_of_ty ty)))
        (String_concat \<prec>''
''\<succ>
          (List_map
            (\<lambda> (pref, s). sprint4 ''  %s : %s%s%s''\<acute>
              (case pref of OclCtxtPre \<Rightarrow> \<prec>''Pre''\<succ>
                          | OclCtxtPost \<Rightarrow> \<prec>''Post''\<succ>)
              g
              (s_of_ctxt2_term s)
              g)
            (Ctxt_expr ctxt)))
  | OclAstCtxtInv Floor2 ctxt \<Rightarrow>
      sprint3 ''Context[shallow] %s%s
%s''\<acute>
        (case Ctxt_inv_param ctxt of
           [] \<Rightarrow> \<prec>''''\<succ>
         | l \<Rightarrow> sprint1 ''%s:''\<acute> (String_concat \<prec>'',''\<succ> (List_map To_string l)))
        (To_string (Ctxt_inv_ty ctxt))
        (String_concat \<prec>''
''\<succ>
          (List_map
            (\<lambda> (n, s). sprint4 ''  Inv %s : %s%s%s''\<acute>
              (To_string n)
              g
              (s_of_ctxt2_term s)
              g)
            (Ctxt_inv_expr ctxt))))"

definition "s_of_thy ocl =
            (\<lambda> Theory_dataty dataty \<Rightarrow> s_of_dataty ocl dataty
             | Theory_ty_synonym ty_synonym \<Rightarrow> s_of_ty_synonym ocl ty_synonym
             | Theory_instantiation_class instantiation_class \<Rightarrow> s_of_instantiation_class ocl instantiation_class
             | Theory_defs_overloaded defs_overloaded \<Rightarrow> s_of_defs_overloaded ocl defs_overloaded
             | Theory_consts_class consts_class \<Rightarrow> s_of_consts_class ocl consts_class
             | Theory_definition_hol definition_hol \<Rightarrow> s_of_definition_hol ocl definition_hol
             | Theory_lemmas_simp lemmas_simp \<Rightarrow> s_of_lemmas_simp ocl lemmas_simp
             | Theory_lemma_by lemma_by \<Rightarrow> s_of_lemma_by ocl lemma_by
             | Theory_axiom axiom \<Rightarrow> s_of_axiom ocl axiom
             | Theory_section_title section_title \<Rightarrow> s_of_section_title ocl section_title
             | Theory_text text \<Rightarrow> s_of_text ocl text
             | Theory_ml ml \<Rightarrow> s_of_ml ocl ml
             | Theory_thm thm \<Rightarrow> s_of_thm ocl thm)"

definition "s_of_generation_syntax _ = (\<lambda> Generation_syntax_shallow mode \<Rightarrow>
  sprint1 ''generation_syntax [ shallow%s ]''\<acute>
    (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l f = sprint1 '' (generation_semantics [ %s ])''\<acute> in
     case mode of Gen_only_design \<Rightarrow> f \<prec>''design''\<succ>
                | Gen_only_analysis \<Rightarrow> f \<prec>''analysis''\<succ>
                | Gen_default \<Rightarrow> \<prec>''''\<succ>))"

definition "s_of_ml_extended _ = (\<lambda> Ml_extended e \<Rightarrow> sprint1 ''setup{* %s *}''\<acute> (s_of_sexpr_extended e))"

definition "s_of_thy_extended ocl = (\<lambda>
    Isab_thy thy \<Rightarrow> s_of_thy ocl thy
  | Isab_thy_generation_syntax generation_syntax \<Rightarrow> s_of_generation_syntax ocl generation_syntax
  | Isab_thy_ml_extended ml_extended \<Rightarrow> s_of_ml_extended ocl ml_extended
  | Isab_thy_ocl_deep_embed_ast ocl_deep_embed_ast \<Rightarrow> s_of_ocl_deep_embed_ast ocl ocl_deep_embed_ast)"

definition "s_of_thy_list ocl l_thy =
  (let (th_beg, th_end) = case D_file_out_path_dep ocl of None \<Rightarrow> ([], [])
   | Some (name, fic_import, fic_import_boot) \<Rightarrow>
       ( [ sprint2 ''theory %s imports %s begin''\<acute> (To_string name) (s_of_expr (expr_binop \<langle>'' ''\<rangle> (List_map Expr_string (fic_import @@@@ (if D_import_compiler ocl | D_generation_syntax_shallow ocl then [fic_import_boot] else []))))) ]
       , [ \<prec>''''\<succ>, \<prec>''end''\<succ> ]) in
  List_flatten
        [ th_beg
        , List_flatten (fst (fold_list (\<lambda>l (i, cpt).
            let (l_thy, lg) = fold_list (\<lambda>l n. (s_of_thy_extended ocl l, Succ n)) l 0 in
            (( \<prec>''''\<succ>
             # sprint4 ''%s(* %d ************************************ %d + %d *)''\<acute>
                 (To_string (if ocl_compiler_config.more ocl then \<langle>''''\<rangle> else \<degree>char_escape\<degree>)) (To_nat (Succ i)) (To_nat cpt) (To_nat lg)
             # l_thy), Succ i, cpt + lg)) l_thy (D_output_position ocl)))
        , th_end ])"
end

lemmas [code] =
  (* def *)
  s_of.s_of_sexpr_extended_def
  s_of.s_of_section_title_def
  s_of.s_of_ctxt2_term_def
  s_of.s_of_ocl_deep_embed_ast_def
  s_of.s_of_thy_def
  s_of.s_of_generation_syntax_def
  s_of.s_of_ml_extended_def
  s_of.s_of_thy_extended_def
  s_of.s_of_thy_list_def

  (* fun *)
  s_of.s_of_ctxt2_term_aux.simps

end
