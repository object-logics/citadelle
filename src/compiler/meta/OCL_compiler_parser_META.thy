(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_parser_META.thy ---
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

theory  OCL_compiler_parser_META
imports OCL_compiler_meta_META
        OCL_compiler_parser_UML
        OCL_compiler_parser_UML_extended
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
  (D_accessor_rbt ocl)
  (D_higher_order_ty ocl)
  (D_sorry_mode ocl)"

definition "ocl_compiler_config_rec f ocl = ocl_compiler_config_rec0 f ocl
  (ocl_compiler_config.more ocl)"

(* *)

lemma [code]: "ocl_compiler_config.extend = (\<lambda>ocl v. ocl_compiler_config_rec0 (co14 (\<lambda>f. f v) ocl_compiler_config_ext) ocl)"
by(intro ext, simp add: ocl_compiler_config_rec0_def
                        ocl_compiler_config.extend_def
                        co14_def K_def)
lemma [code]: "ocl_compiler_config.make = co14 (\<lambda>f. f ()) ocl_compiler_config_ext"
by(intro ext, simp add: ocl_compiler_config.make_def
                        co14_def)
lemma [code]: "ocl_compiler_config.truncate = ocl_compiler_config_rec (co14 K ocl_compiler_config.make)"
by(intro ext, simp add: ocl_compiler_config_rec0_def
                        ocl_compiler_config_rec_def
                        ocl_compiler_config.truncate_def
                        ocl_compiler_config.make_def
                        co14_def K_def)

subsection{* i of ... *} (* i_of *)

subsubsection{* general *}

context i_of 
begin

definition "i_of_ocl_flush_all a b = ocl_flush_all_rec
  (b ''OclFlushAll'')"

definition "i_of_floor a b = floor_rec
  (b ''Floor1'')
  (b ''Floor2'')
  (b ''Floor3'')"

definition "i_of_ocl_deep_embed_ast a b = ocl_deep_embed_ast_rec
  (ap2 a (b ''OclAstClassRaw'') (i_of_floor a b) (i_of_ocl_class_raw a b (K i_of_unit)))
  (ap1 a (b ''OclAstAssociation'') (i_of_ocl_association a b (K i_of_unit)))
  (ap2 a (b ''OclAstAssClass'') (i_of_floor a b) (i_of_ocl_ass_class a b))
  (ap2 a (b ''OclAstCtxtPrePost'') (i_of_floor a b) (i_of_ocl_ctxt_pre_post a b (K i_of_unit)))
  (ap2 a (b ''OclAstCtxtInv'') (i_of_floor a b) (i_of_ocl_ctxt_inv a b (K i_of_unit)))

  (ap1 a (b ''OclAstInstance'') (i_of_ocl_instance a b))
  (ap1 a (b ''OclAstDefBaseL'') (i_of_ocl_def_base_l a b))
  (ap1 a (b ''OclAstDefState'') (i_of_ocl_def_state a b))
  (ap1 a (b ''OclAstDefPrePost'') (i_of_ocl_def_pre_post a b))
  (ap1 a (b ''OclAstFlushAll'') (i_of_ocl_flush_all a b))"

definition "i_of_ocl_deep_mode a b = ocl_deep_mode_rec
  (b ''Gen_only_design'')
  (b ''Gen_only_analysis'')
  (b ''Gen_default'')"

definition "i_of_ocl_compiler_config a b f = ocl_compiler_config_rec
  (ap15 a (b (ext ''ocl_compiler_config_ext''))
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
    (i_of_list a b (i_of_pair a b (i_of_string a b) (i_of_ocl_ty a b)))
    (i_of_bool b)
    (f a b))"

end

lemmas [code] =
  i_of.i_of_ocl_flush_all_def
  i_of.i_of_floor_def
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

definition "sml_apply s l = flatten [s, '' ('', case\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l l of x # xs \<Rightarrow> flatten [x, flatten (List_map (\<lambda>s. flatten ['', '', s]) xs)], '')'' ]"

end
