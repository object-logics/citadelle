(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Printer_META.thy ---
 * This file is part of HOL-TestGen.
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

header{* Part ... *}

theory  Printer_META
imports Parser_META
        "../../compiler_generic/meta_isabelle/Printer_Isabelle"
begin

subsection{* s of ... *} (* s_of *)

context Print
begin

declare[[cartouche_type' = "abr_string"]]

definition "of_sexpr_extended = (\<lambda>
    SML_extended s \<Rightarrow> of_sexpr s
  | SML_compiler_env ocl \<Rightarrow> of_sexpr
     (SML_apply \<open>Generation_mode.update_compiler_config\<close>
       [SML_apply \<open>K\<close> [SML_let_open \<open>META\<close> (SML_basic [sml_of_meta_unit sml_apply id ocl])]]))"

definition "concatWith l =
 (if l = [] then
    id
  else
    sprint2 \<prec>''(%s. (%s))''\<succ>\<acute> (To_string (String_concatWith \<open> \<close> (\<open>\<lambda>\<close> # rev l))))"

declare[[cartouche_type' = "fun\<^sub>p\<^sub>r\<^sub>i\<^sub>n\<^sub>t\<^sub>f"]]

definition "of_section_title ocl =
 (if D_output_disable_thy ocl then
    \<lambda>_. \<open>\<close>
  else
    of_section ocl)"

fun of_ctxt2_term_aux where "of_ctxt2_term_aux l e =
 (\<lambda> T_pure pure \<Rightarrow> concatWith l (of_pure_term [] pure)
  | T_to_be_parsed _ s \<Rightarrow> concatWith l (To_string s)
  | T_lambda s c \<Rightarrow> of_ctxt2_term_aux (s # l) c) e"
definition "of_ctxt2_term = of_ctxt2_term_aux []"

definition "To_oid = (\<lambda>Oid n \<Rightarrow> To_nat n)"

fun of_ocl_list_attr where
   "of_ocl_list_attr f e = (\<lambda> OclAttrNoCast x \<Rightarrow> f x
                            | OclAttrCast ty (OclAttrNoCast x) _ \<Rightarrow> \<open>(%s :: %s)\<close> (f x) (To_string ty)
                            | OclAttrCast ty l _ \<Rightarrow> \<open>%s \<rightarrow> oclAsType( %s )\<close> (of_ocl_list_attr f l) (To_string ty)) e"

definition' \<open>of_ocl_def_base = (\<lambda> OclDefInteger i \<Rightarrow> To_string i
                                | OclDefReal (i1, i2) \<Rightarrow> \<open>%s.%s\<close> (To_string i1) (To_string i2)
                                | OclDefString s \<Rightarrow> \<open>"%s"\<close> (To_string s))\<close>

fun of_ocl_data_shallow where
   "of_ocl_data_shallow e = (\<lambda> ShallB_term b \<Rightarrow> of_ocl_def_base b
                             | ShallB_str s \<Rightarrow> To_string s
                             | ShallB_self s \<Rightarrow> \<open>self %d\<close> (To_oid s)
                             | ShallB_list l \<Rightarrow> \<open>[ %s ]\<close> (String_concat \<open>, \<close> (List.map of_ocl_data_shallow l))) e"

definition' \<open>of_ocl_instance_single ocli =
  \<open>%s%s = %s\<close>
    (case Inst_name ocli of Some s \<Rightarrow> To_string s)
    (case Inst_ty ocli of None \<Rightarrow> \<open>\<close> | Some ty \<Rightarrow> \<open> :: %s\<close> (To_string ty))
    (of_ocl_list_attr
      (\<lambda>l. \<open>[ %s ]\<close>
             (String_concat \<open>, \<close>
               (L.map (\<lambda>(pre_post, attr, v).
                            \<open>%s"%s" = %s\<close> (case pre_post of None \<Rightarrow> \<open>\<close>
                                                          | Some (s1, s2) \<Rightarrow> \<open>("%s", "%s") |= \<close> (To_string s1) (To_string s2))
                                          (To_string attr)
                                          (of_ocl_data_shallow v))
                         l)))
      (Inst_attr ocli))\<close>

definition "of_def_state l =
  String_concat \<open>, \<close> (L.map (\<lambda> OclDefCoreBinding s \<Rightarrow> To_string s
                             | OclDefCoreAdd ocli \<Rightarrow> of_ocl_instance_single ocli) l)"

definition "of_def_pp_core = (\<lambda> OclDefPPCoreBinding s \<Rightarrow> To_string s
                              | OclDefPPCoreAdd l \<Rightarrow> \<open>[ %s ]\<close> (of_def_state l))"

definition' \<open>of_all_meta_embedding _ =
 (\<lambda> META_ctxt Floor2 ctxt \<Rightarrow>
    let f_inv = \<lambda> T_inv b (OclProp_ctxt n s) \<Rightarrow> \<open>  %sInv %s : "%s"\<close>
              (if b then \<open>Existential\<close> else \<open>\<close>)
              (case n of None \<Rightarrow> \<open>\<close> | Some s \<Rightarrow> To_string s)
              (of_ctxt2_term s) in
    \<open>Context[shallow] %s%s %s\<close>
        (case Ctxt_param ctxt of
           [] \<Rightarrow> \<open>\<close>
         | l \<Rightarrow> \<open>%s : \<close> (String_concat \<open>, \<close> (L.map To_string l)))
        (To_string (ty_obj_to_string (Ctxt_ty ctxt)))
        (String_concat \<open>
\<close> (L.map (\<lambda> Ctxt_pp ctxt \<Rightarrow>
                \<open>:: %s (%s) %s
%s\<close>
        (To_string (Ctxt_fun_name ctxt))
        (String_concat \<open>, \<close>
          (L.map
            (\<lambda> (s, ty). \<open>%s : %s\<close> (To_string s) (To_string (str_of_ty ty)))
            (Ctxt_fun_ty_arg ctxt)))
        (case Ctxt_fun_ty_out ctxt of None \<Rightarrow> \<open>\<close>
                                    | Some ty \<Rightarrow> \<open>: %s\<close> (To_string (str_of_ty ty)))
        (String_concat \<open>
\<close>
          (L.map
            (\<lambda> T_pp pref (OclProp_ctxt n s) \<Rightarrow> \<open>  %s %s: "%s"\<close>
                (case pref of OclCtxtPre \<Rightarrow> \<open>Pre\<close>
                            | OclCtxtPost \<Rightarrow> \<open>Post\<close>)
                (case n of None \<Rightarrow> \<open>\<close> | Some s \<Rightarrow> To_string s)
                (of_ctxt2_term s)
             | T_invariant inva \<Rightarrow> f_inv inva)
            (Ctxt_expr ctxt)))
          | Ctxt_inv inva \<Rightarrow> f_inv inva)
         (Ctxt_clause ctxt)))

  | META_instance (OclInstance l) \<Rightarrow>
      \<open>Instance %s\<close> (String_concat \<open>
     and \<close> (L.map of_ocl_instance_single l))
  | META_def_state Floor2 (OclDefSt n l) \<Rightarrow> 
      \<open>State[shallow] %s = [ %s ]\<close>
        (To_string n)
        (of_def_state l)
  | META_def_pre_post Floor2 (OclDefPP n s_pre s_post) \<Rightarrow>
      \<open>PrePost[shallow] %s%s%s\<close>
        (case n of None \<Rightarrow> \<open>\<close> | Some n \<Rightarrow> \<open>%s = \<close> (To_string n))
        (of_def_pp_core s_pre)
        (case s_post of None \<Rightarrow> \<open>\<close> | Some s_post \<Rightarrow> \<open> %s\<close> (of_def_pp_core s_post)))\<close>

definition "of_semi__t0 ocl =
            (\<lambda> Theory_section section_title \<Rightarrow> of_section_title ocl section_title
             | x \<Rightarrow> of_semi__t ocl x)"

definition' \<open>of_semi__theory0 ocl =
 (\<lambda> H_thy_simple t \<Rightarrow> of_semi__t0 ocl t
  | H_thy_locale data l \<Rightarrow> 
      \<open>locale %s =
%s
begin
%s
end\<close>   (To_string (HolThyLocale_name data))
        (String_concat_map
           \<open>
\<close>
           (\<lambda> (l_fix, o_assum).
                \<open>%s%s\<close> (String_concat_map \<open>
\<close> (\<lambda>(e, ty). \<open>fixes "%s" :: "%s"\<close> (of_semi__term e) (of_semi__typ ty)) l_fix)
                                (case o_assum of None \<Rightarrow> \<open>\<close>
                                               | Some (name, e) \<Rightarrow> \<open>
assumes %s: "%s"\<close> (To_string name) (of_semi__term e)))
           (HolThyLocale_header data))
        (String_concat_map \<open>

\<close> (String_concat_map \<open>

\<close> (of_semi__t0 ocl)) l))\<close>

definition "of_generation_syntax _ = (\<lambda> Gen_semantics mode \<Rightarrow>
  \<open>generation_syntax [ shallow%s ]\<close>
    (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l f = \<open> (generation_semantics [ %s ])\<close> in
     case mode of Gen_only_design \<Rightarrow> f \<open>design\<close>
                | Gen_only_analysis \<Rightarrow> f \<open>analysis\<close>
                | Gen_default \<Rightarrow> \<open>\<close>))"

definition "of_ml_extended _ = (\<lambda> Ml_extended e \<Rightarrow> \<open>setup{* %s *}\<close> (of_sexpr_extended e))"

definition "of_thy_extended ocl = (\<lambda>
    Isab_thy thy \<Rightarrow> of_semi__theory0 ocl thy
  | Isab_thy_generation_syntax generation_syntax \<Rightarrow> of_generation_syntax ocl generation_syntax
  | Isab_thy_ml_extended ml_extended \<Rightarrow> of_ml_extended ocl ml_extended
  | Isab_thy_all_meta_embedding all_meta_embedding \<Rightarrow> of_all_meta_embedding ocl all_meta_embedding)"

definition "of_thy_list ocl l_thy =
  (let (th_beg, th_end) = case D_output_header_thy ocl of None \<Rightarrow> ([], [])
   | Some (name, fic_import, fic_import_boot) \<Rightarrow>
       ( [ \<open>theory %s imports %s begin\<close>
             (To_string name)
             (of_semi__term (term_binop \<langle>'' ''\<rangle>
                                        (L.map Term_string
                                               (fic_import @@@@ (if D_output_header_force ocl
                                                                  | D_output_auto_bootstrap ocl then
                                                                   [fic_import_boot]
                                                                 else
                                                                   []))))) ]
       , [ \<open>\<close>, \<open>end\<close> ]) in
  L.flatten
        [ th_beg
        , L.flatten (fst (L.mapM (\<lambda>l (i, cpt).
            let (l_thy, lg) = L.mapM (\<lambda>l n. (of_thy_extended ocl l, Succ n)) l 0 in
            (( \<open>\<close>
             # \<open>%s(* %d ************************************ %d + %d *)\<close>
                 (To_string (if compiler_env_config.more ocl then \<langle>''''\<rangle> else \<degree>char_escape\<degree>)) (To_nat (Succ i)) (To_nat cpt) (To_nat lg)
             # l_thy), Succ i, cpt + lg)) l_thy (D_output_position ocl)))
        , th_end ])"
end

lemmas [code] =
  (* def *)
  Print.of_sexpr_extended_def
  Print.concatWith_def
  Print.of_section_title_def
  Print.of_ctxt2_term_def
  Print.To_oid_def
  Print.of_ocl_def_base_def
  Print.of_ocl_instance_single_def
  Print.of_def_state_def
  Print.of_def_pp_core_def
  Print.of_all_meta_embedding_def
  Print.of_semi__t0_def
  Print.of_semi__theory0_def
  Print.of_generation_syntax_def
  Print.of_ml_extended_def
  Print.of_thy_extended_def
  Print.of_thy_list_def

  (* fun *)
  Print.of_ctxt2_term_aux.simps
  Print.of_ocl_list_attr.simps
  Print.of_ocl_data_shallow.simps

end
