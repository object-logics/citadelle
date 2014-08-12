(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_printer.thy ---
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

theory  OCL_compiler_printer
imports OCL_compiler_core
        OCL_compiler_printer_UML
        OCL_compiler_printer_Isabelle
begin

section{* Generation to both Form (setup part) *}

definition "ocl_compiler_config_rec0 f ocl = f
  (D_disable_thy_output ocl)
  (D_file_out_path_dep ocl)
  (D_oid_start ocl)
  (D_output_position ocl)
  (D_design_analysis ocl)
  (D_class_spec ocl)
  (D_ocl_env ocl)
  (D_instance_rbt ocl)
  (D_state_rbt ocl)
  (D_import_compiler ocl)
  (D_generation_syntax_shallow ocl)
  (D_accessor_rbt ocl)"

definition "ocl_compiler_config_rec f ocl = ocl_compiler_config_rec0 f ocl
  (ocl_compiler_config.more ocl)"

(* *)

lemma [code]: "ocl_compiler_config.extend = (\<lambda>ocl v. ocl_compiler_config_rec0 (co12 (\<lambda>f. f v) ocl_compiler_config_ext) ocl)"
by(intro ext, simp add: ocl_compiler_config_rec0_def
                        ocl_compiler_config.extend_def
                        co12_def K_def)
lemma [code]: "ocl_compiler_config.make = co12 (\<lambda>f. f ()) ocl_compiler_config_ext"
by(intro ext, simp add: ocl_compiler_config.make_def
                        co12_def)
lemma [code]: "ocl_compiler_config.truncate = ocl_compiler_config_rec (co12 K ocl_compiler_config.make)"
by(intro ext, simp add: ocl_compiler_config_rec0_def
                        ocl_compiler_config_rec_def
                        ocl_compiler_config.truncate_def
                        ocl_compiler_config.make_def
                        co12_def K_def)

subsection{* i of ... *} (* i_of *)

subsubsection{* general *}

context i_of 
begin

definition "i_of_ocl_flush_all a b = ocl_flush_all_rec
  (b ''OclFlushAll'')"

definition "i_of_ocl_deep_embed_ast a b = ocl_deep_embed_ast_rec
  (ap1 a (b ''OclAstClassRaw'') (i_of_ocl_class_raw a b (K i_of_unit)))
  (ap1 a (b ''OclAstAssociation'') (i_of_ocl_association a b (K i_of_unit)))
  (ap1 a (b ''OclAstAssClass'') (i_of_ocl_ass_class a b))
  (ap1 a (b ''OclAstInstance'') (i_of_ocl_instance a b))
  (ap1 a (b ''OclAstDefBaseL'') (i_of_ocl_def_base_l a b))
  (ap1 a (b ''OclAstDefState'') (i_of_ocl_def_state a b))
  (ap1 a (b ''OclAstDefPrePost'') (i_of_ocl_def_pre_post a b))
  (ap1 a (b ''OclAstCtxtPrePost'') (i_of_ocl_ctxt_pre_post a b (K i_of_unit)))
  (ap1 a (b ''OclAstCtxt2PrePost'') (i_of_ocl_ctxt2_pre_post a b (K i_of_unit)))
  (ap1 a (b ''OclAstCtxtInv'') (i_of_ocl_ctxt_inv a b (K i_of_unit)))
  (ap1 a (b ''OclAstCtxt2Inv'') (i_of_ocl_ctxt2_inv a b (K i_of_unit)))
  (ap1 a (b ''OclAstFlushAll'') (i_of_ocl_flush_all a b))"

definition "i_of_ocl_deep_mode a b = ocl_deep_mode_rec
  (b ''Gen_design'')
  (b ''Gen_analysis'')"

definition "i_of_ocl_compiler_config a b f = ocl_compiler_config_rec
  (ap13 a (b (ext ''ocl_compiler_config_ext''))
    (i_of_bool b)
    (i_of_option a b (i_of_pair a b (i_of_string a b) (i_of_pair a b (i_of_list a b (i_of_string a b)) (i_of_string a b))))
    (i_of_internal_oids a b)
    (i_of_pair a b (i_of_nat a b) (i_of_nat a b))
    (i_of_ocl_deep_mode a b)
    (i_of_option a b (i_of_ocl_class a b))
    (i_of_list a b (i_of_ocl_deep_embed_ast a b))
    (i_of_list a b (i_of_pair a b (i_of_string a b) (i_of_pair a b (i_of_ocl_instance_single a b (K i_of_unit)) (i_of_internal_oid a b))))
    (i_of_list a b (i_of_pair a b (i_of_string a b) (i_of_list a b (i_of_pair a b (i_of_internal_oids a b) (i_of_ocl_def_state_core a b (i_of_pair a b (i_of_string a b) (i_of_ocl_instance_single a b  (K i_of_unit))))))))
    (i_of_bool b)
    (i_of_bool b)
    (i_of_pair a b (i_of_list a b (i_of_string a b)) (i_of_list a b (i_of_string a b)))
    (f a b))"

end

lemmas [code] =
  i_of.i_of_ocl_flush_all_def
  i_of.i_of_ocl_deep_embed_ast_def
  i_of.i_of_ocl_deep_mode_def
  i_of.i_of_ocl_compiler_config_def

subsubsection{* Isabelle *}

locale isabelle_of
begin

definition "i_Pair = ''Pair''"
definition "i_Nil = ''Nil''"
definition "i_Cons = ''Cons''"
definition "i_None = ''None''"
definition "i_Some = ''Some''"

(* *)

definition "i_of_pair a b f1 f2 = (\<lambda>f. \<lambda>(c, d) \<Rightarrow> f c d)
  (ap2 a (b i_Pair) f1 f2)"

definition "i_of_list a b f = (\<lambda>f0. list_rec f0 o co1 K)
  (b i_Nil)
  (ar2 a (b i_Cons) f)"

definition "i_of_option a b f = option_rec
  (b i_None)
  (ap1 a (b i_Some) f)"

(* *)

definition "i_of_unit b = unit_rec
  (b ''()'')"

definition "i_of_bool b = bool_rec
  (b ''True'')
  (b ''False'')"

definition "i_of_nibble b = nibble_rec
  (b ''Nibble0'')
  (b ''Nibble1'')
  (b ''Nibble2'')
  (b ''Nibble3'')
  (b ''Nibble4'')
  (b ''Nibble5'')
  (b ''Nibble6'')
  (b ''Nibble7'')
  (b ''Nibble8'')
  (b ''Nibble9'')
  (b ''NibbleA'')
  (b ''NibbleB'')
  (b ''NibbleC'')
  (b ''NibbleD'')
  (b ''NibbleE'')
  (b ''NibbleF'')"

definition "i_of_char a b = char_rec
  (ap2 a (b ''Char'') (i_of_nibble b) (i_of_nibble b))"

definition "i_of_string a b = i_of_list a b (i_of_char a b)"

definition "i_of_nat a b = b o natural_of_str"

end

sublocale isabelle_of < i_of "id"
                             isabelle_of.i_of_string
                             isabelle_of.i_of_nat
                             isabelle_of.i_of_unit
                             isabelle_of.i_of_bool
                             isabelle_of.i_Pair
                             isabelle_of.i_Nil
                             isabelle_of.i_Cons
                             isabelle_of.i_None
                             isabelle_of.i_Some
done

context isabelle_of begin
  definition "ocl_embed a b =
    i_of_ocl_compiler_config a b (\<lambda> a b.
      i_of_pair a b
        (i_of_list a b (i_of_ocl_deep_embed_ast a b))
        (i_of_option a b (i_of_string a b)))"
end

definition "isabelle_of_ocl_embed = isabelle_of.ocl_embed"

lemmas [code] =
  isabelle_of.i_Pair_def
  isabelle_of.i_Nil_def
  isabelle_of.i_Cons_def
  isabelle_of.i_None_def
  isabelle_of.i_Some_def

  isabelle_of.i_of_pair_def
  isabelle_of.i_of_list_def
  isabelle_of.i_of_option_def
  isabelle_of.i_of_unit_def
  isabelle_of.i_of_bool_def
  isabelle_of.i_of_nibble_def
  isabelle_of.i_of_char_def
  isabelle_of.i_of_string_def
  isabelle_of.i_of_nat_def

  isabelle_of.ocl_embed_def

(* *)

definition "isabelle_apply s l = flatten [s, flatten (List_map (\<lambda> s. flatten ['' ('', s, '')'']) l)]"

subsubsection{* SML *}

locale sml_of
begin

definition "i_Pair = ''I''"
definition "i_Nil = ''nil''"
definition "i_Cons = ''uncurry cons''" (* val cons2 = uncurry cons *)
definition "i_None = ''NONE''"
definition "i_Some = ''SOME''"

(* *)

definition "i_of_pair a b f1 f2 = (\<lambda>f. \<lambda>(c, d) \<Rightarrow> f c d)
  (ap2 a (b i_Pair) f1 f2)"

definition "i_of_list a b f = (\<lambda>f0. list_rec f0 o co1 K)
  (b i_Nil)
  (ar2 a (b i_Cons) f)"

definition "i_of_option a b f = option_rec
  (b i_None)
  (ap1 a (b i_Some) f)"

(* *)

definition "i_of_unit b = unit_rec
  (b ''()'')"

definition "i_of_bool b = bool_rec
  (b ''true'')
  (b ''false'')"

definition "i_of_string a b =
 (let c = [Char Nibble2 Nibble2] in
  (\<lambda>x. b (flatten [''(String.explode '', c, List_replace x (Char Nibble0 NibbleA) (Char Nibble5 NibbleC # ''n''), c,'')''])))"

definition "i_of_nat a b = (\<lambda>x. b (flatten [''(Code_Numeral.Nat '', natural_of_str x, '')'']))"

end

sublocale sml_of < i_of "\<lambda>x # xs \<Rightarrow> flatten [uppercase_of_str [x], xs]"
                        sml_of.i_of_string
                        sml_of.i_of_nat
                        sml_of.i_of_unit
                        sml_of.i_of_bool
                        sml_of.i_Pair
                        sml_of.i_Nil
                        sml_of.i_Cons
                        sml_of.i_None
                        sml_of.i_Some
done

context sml_of begin
  definition "ocl_unit a b = i_of_ocl_compiler_config a b (\<lambda> _. i_of_unit)"
end

definition "sml_of_ocl_unit = sml_of.ocl_unit"

lemmas [code] =
  sml_of.i_Pair_def
  sml_of.i_Nil_def
  sml_of.i_Cons_def
  sml_of.i_None_def
  sml_of.i_Some_def

  sml_of.i_of_pair_def
  sml_of.i_of_list_def
  sml_of.i_of_option_def
  sml_of.i_of_unit_def
  sml_of.i_of_bool_def
  sml_of.i_of_string_def
  sml_of.i_of_nat_def

  sml_of.ocl_unit_def

(* *)

definition "sml_apply s l = flatten [s, '' ('', bug_ocaml_extraction (case l of x # xs \<Rightarrow> flatten [x, flatten (List_map (\<lambda>s. flatten ['', '', s]) xs)]), '')'' ]"

section{* Generation to Deep Form: OCaml *}

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
 (\<lambda> OclAstCtxt2PrePost ctxt \<Rightarrow>
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
  | OclAstCtxt2Inv ctxt \<Rightarrow>
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

subsection{* conclusion *}

definition "List_iterM f l =
  List.fold (\<lambda>x m. bind m (\<lambda> () \<Rightarrow> f x)) l (return ())"

context s_of
begin
definition "write_file ocl = (
  let (l_thy, Sys_argv) = ocl_compiler_config.more ocl
    ; (is_file, f_output) = case (D_file_out_path_dep ocl, Sys_argv)
     of (Some (file_out, _), Some dir) \<Rightarrow>
          let dir = To_string dir in
          (True, \<lambda>f. bind (Sys_is_directory2 dir) (\<lambda> Sys_is_directory2_dir.
                     out_file1 f (if Sys_is_directory2_dir then sprintf2 (STR ''%s/%s.thy'') dir (To_string file_out) else dir)))
      | _ \<Rightarrow> (False, out_stand1) in
  f_output
    (\<lambda>fprintf1.
      List_iterM (fprintf1 (STR ''%s
''                                 ))
        (bug_ocaml_extraction (let (ocl, l) =
           fold_thy'
             (\<lambda>f. f ())
             (\<lambda>_ _. [])
             (\<lambda>x acc1 acc2. (acc1, Cons x acc2))
             l_thy
             (ocl_compiler_config.truncate ocl, []) in
         s_of_thy_list (ocl_compiler_config_more_map (\<lambda>_. is_file) ocl) (rev l)))))"
end

definition "write_file = s_of.write_file implode (ToNat integer_of_natural)"

lemmas [code] =
  (* def *)
  s_of.To_oid_def

  s_of.s_of_dataty_def
  s_of.s_of_ty_synonym_def
  s_of.s_of_sexpr_extended_def
  s_of.s_of_instantiation_class_def
  s_of.s_of_defs_overloaded_def
  s_of.s_of_consts_class_def
  s_of.s_of_definition_hol_def
  s_of.s_of_ntheorem_def
  s_of.s_of_ntheorem_list_def
  s_of.s_of_lemmas_simp_def
  s_of.s_of_tactic_last_def
  s_of.s_of_tac_apply_def
  s_of.s_of_lemma_by_def
  s_of.s_of_axiom_def
  s_of.s_of_section_title_def
  s_of.s_of_text_def
  s_of.s_of_ml_def
  s_of.s_of_thm_def
  s_of.s_of_ctxt2_term_def
  s_of.s_of_ocl_deep_embed_ast_def
  s_of.s_of_thy_def
  s_of.s_of_generation_syntax_def
  s_of.s_of_ml_extended_def
  s_of.s_of_thy_extended_def
  s_of.s_of_thy_list_def

  s_of.write_file_def

  (* fun *)
  s_of.s_of_rawty.simps
  s_of.s_of_pure_term.simps
  s_of.s_of_expr.simps
  s_of.s_of_ntheorem_aux.simps
  s_of.s_of_tactic.simps
  s_of.s_of_sexpr.simps

end
