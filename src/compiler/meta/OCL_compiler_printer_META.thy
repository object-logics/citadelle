(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_printer_META.thy ---
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
     (Sexpr_apply ''Generation_mode.update_compiler_config''
       [Sexpr_apply ''K'' [Sexpr_let_open ''OCL'' (Sexpr_basic [sml_of_ocl_unit sml_apply id ocl])]]))"

definition "s_of_section_title ocl = (\<lambda> Section_title n section_title \<Rightarrow>
  if D_disable_thy_output ocl then
    STR ''''
  else
    sprintf2 (STR ''%s{* %s *}'')
      (To_string ((if n = 0 then ''''
                   else if n = 1 then ''sub''
                   else ''subsub'') @@ ''section''))
      (To_string section_title))"

definition "s_of_ctxt2_term = (\<lambda> T_pure pure \<Rightarrow> s_of_pure_term pure
                               | T_to_be_parsed s \<Rightarrow> To_string s)"

definition "s_of_ocl_deep_embed_ast _ =
 (\<lambda> OclAstCtxtPrePost Floor2 ctxt \<Rightarrow>
      sprintf5 (STR ''Context[shallow] %s :: %s (%s) %s
%s'')
        (To_string (Ctxt_ty ctxt))
        (To_string (Ctxt_fun_name ctxt))
        (String_concat (STR '', '')
          (List_map
            (\<lambda> (s, ty). sprintf2 (STR ''%s : %s'') (To_string s) (To_string (str_of_ty ty)))
            (Ctxt_fun_ty_arg ctxt)))
        (case Ctxt_fun_ty_out ctxt of None \<Rightarrow> STR ''''
                                    | Some ty \<Rightarrow> sprintf1 (STR '': %s'') (To_string (str_of_ty ty)))
        (String_concat (STR ''
'')
          (List_map
            (\<lambda> (pref, s). sprintf2 (STR ''  %s : `%s`'')
              (case pref of OclCtxtPre \<Rightarrow> STR ''Pre''
                          | OclCtxtPost \<Rightarrow> STR ''Post'')
              (s_of_ctxt2_term s))
            (Ctxt_expr ctxt)))
  | OclAstCtxtInv Floor2 ctxt \<Rightarrow>
      sprintf2 (STR ''Context[shallow] %s
%s'')
        (To_string (Ctxt_inv_ty ctxt))
        (String_concat (STR ''
'')
          (List_map
            (\<lambda> (n, s). sprintf2 (STR ''  Inv %s : `%s`'')
              (To_string n)
              (s_of_ctxt2_term s))
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
  sprintf1 (STR ''generation_syntax [ shallow (generation_semantics [ %s ]) ]'') (case mode of Gen_design \<Rightarrow> STR ''design'' | Gen_analysis \<Rightarrow> STR ''analysis''))"

definition "s_of_ml_extended _ = (\<lambda> Ml_extended e \<Rightarrow> sprintf1 (STR ''setup{* %s *}'') (s_of_sexpr_extended e))"

definition "s_of_thy_extended ocl = (\<lambda>
    Isab_thy thy \<Rightarrow> s_of_thy ocl thy
  | Isab_thy_generation_syntax generation_syntax \<Rightarrow> s_of_generation_syntax ocl generation_syntax
  | Isab_thy_ml_extended ml_extended \<Rightarrow> s_of_ml_extended ocl ml_extended
  | Isab_thy_ocl_deep_embed_ast ocl_deep_embed_ast \<Rightarrow> s_of_ocl_deep_embed_ast ocl ocl_deep_embed_ast)"

definition "s_of_thy_list ocl l_thy =
  (let (th_beg, th_end) = case D_file_out_path_dep ocl of None \<Rightarrow> ([], [])
   | Some (name, fic_import, fic_import_boot) \<Rightarrow>
       ( [ sprintf2 (STR ''theory %s imports %s begin'') (To_string name) (s_of_expr (expr_binop '' '' (List_map Expr_string (fic_import @@ (if D_import_compiler ocl | D_generation_syntax_shallow ocl then [fic_import_boot] else []))))) ]
       , [ STR '''', STR ''end'' ]) in
  flatten
        [ th_beg
        , flatten (fst (fold_list (\<lambda>l (i, cpt).
            let (l_thy, lg) = fold_list (\<lambda>l n. (s_of_thy_extended ocl l, Succ n)) l 0 in
            (( STR ''''
             # sprintf4 (STR ''%s(* %d ************************************ %d + %d *)'')
                 (To_string (if ocl_compiler_config.more ocl then '''' else [char_escape])) (To_nat (Succ i)) (To_nat cpt) (To_nat lg)
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

end
