(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_floor1_infra.thy ---
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

theory  OCL_compiler_floor1_infra
imports OCL_compiler_core_init
begin

section{* Translation of AST *}

subsection{* infrastructure *}

definition "print_infra_datatype_class = start_map'' Thy_dataty o (\<lambda>expr _ base_attr' _. map_class_gen_h''''
  (\<lambda>isub_name name _ l_attr l_inherited l_cons.
    let (l_attr, l_inherited) = base_attr' (l_attr, of_inh l_inherited)
      ; map_ty = List_map ((\<lambda>x. Ty_apply (Ty_base \<langle>''option''\<rangle>) [str_hol_of_ty_all Ty_apply Ty_base x]) o snd) in
    [ Datatype
        (isub_name datatype_ext_name)
        (  (rev_map (\<lambda>x. ( datatype_ext_constr_name @@ mk_constr_name name x
                         , [Raw (datatype_name @@ isub_of_str x)])) (of_sub l_cons))
        @@@@ [(isub_name datatype_ext_constr_name, Raw const_oid # List_maps map_ty l_inherited)])
    , Datatype
        (isub_name datatype_name)
        [ (isub_name datatype_constr_name, Raw (isub_name datatype_ext_name) # map_ty l_attr ) ] ]) expr)"

definition "print_latex_infra_datatype_class = start_map'' Thy_dataty o (\<lambda>expr _ base_attr' _. map_class_gen_h''''
  (\<lambda>isub_name name _ l_attr l_inherited l_cons.
    let (l_attr, l_inherited) = base_attr' (l_attr, of_inh l_inherited)
      ; map_ty = List_map ((\<lambda>x. Ty_apply (Ty_base \<langle>''option''\<rangle>) [str_hol_of_ty_all Ty_apply Ty_base x]) o snd) in let c = [Char Nibble5 NibbleC]
      ; n1 = \<langle>''{ext}''\<rangle>
      ; n2 = \<langle>''{ty}''\<rangle> in
    [ Datatype
        (\<langle>''''\<rangle>@@c@@\<langle>''operatorname{''\<rangle> @@ name @@ \<langle>''}_''\<rangle> @@ n1 @@ \<langle>''''\<rangle>)
        (  (rev_map (\<lambda>x. ( \<langle>''''\<rangle>@@c@@\<langle>''operatorname{mk}_''\<rangle>@@c@@\<langle>''text{''\<rangle> @@ name @@ \<langle>''''\<rangle>@@c@@\<langle>''_''\<rangle> @@ x @@ \<langle>''}''\<rangle>
                         , [Raw (\<langle>''''\<rangle>@@c@@\<langle>''operatorname{''\<rangle> @@ x @@ \<langle>''}_''\<rangle> @@ n2 @@ \<langle>''''\<rangle>)])) (of_sub l_cons))
        @@@@ [(\<langle>''''\<rangle>@@c@@\<langle>''operatorname{mk}_''\<rangle>@@c@@\<langle>''text{''\<rangle> @@ name @@ \<langle>''}''\<rangle>, Raw const_oid # List_maps map_ty l_inherited)])
    , Datatype
        (\<langle>''''\<rangle>@@c@@\<langle>''operatorname{''\<rangle> @@ name @@ \<langle>''}_''\<rangle> @@ n2 @@ \<langle>''''\<rangle>)
        [ (\<langle>''''\<rangle>@@c@@\<langle>''operatorname{mkoid}_''\<rangle>@@c@@\<langle>''text{''\<rangle> @@ name @@ \<langle>''}''\<rangle>, Raw (\<langle>''''\<rangle>@@c@@\<langle>''operatorname{''\<rangle> @@ name @@ \<langle>''}_''\<rangle> @@ n1 @@ \<langle>''''\<rangle>) # map_ty l_attr ) ] ]) expr)"

definition "print_infra_datatype_universe expr = start_map Thy_dataty
  [ Datatype unicode_AA
      (map_class (\<lambda>isub_name _ _ _ _ _. (isub_name datatype_in, [Raw (isub_name datatype_name)])) expr) ]"

definition "print_infra_type_synonym_class expr = start_map Thy_ty_synonym
  (let option = (\<lambda>x. Ty_apply (Ty_base \<langle>''option''\<rangle>) [x])
     ; ty = \<lambda> t s. Type_synonym (print_ctxt_ty t) (Ty_apply (Ty_base s) [Ty_base unicode_AA]) in
   (* base type *)
   ty OclTy_base_void ty_void #
   ty OclTy_base_boolean ty_boolean #
   ty OclTy_base_integer ty_integer #
   (*ty OclTy_base_unlimitednatural ty_unlimitednatural #*)
   ty OclTy_base_real ty_real #
   ty OclTy_base_string ty_string #
   (* *)
   (map_class (\<lambda>isub_name name _ _ _ _.
     Type_synonym name (Ty_apply (Ty_base \<langle>''val''\<rangle>) [Ty_base unicode_AA,
     option (option (Ty_base (isub_name datatype_name))) ])) expr))"

definition "print_infra_type_synonym_class_rec = (\<lambda>expr.
  Pair (List_map (\<lambda>x. let (tit, body) = print_infra_type_synonym_class_rec_aux x in
                      Thy_ty_synonym (Type_synonym tit (Ty_apply (Ty_base \<langle>''val''\<rangle>) [Ty_base unicode_AA, body])))
                 (snd (fold_class (\<lambda>_ _ l_attr _ _ _.
                                    Pair () o List.fold
                                      (\<lambda>(_, t) l.
                                        let f = (* WARNING we may test with RBT instead of List *)
                                                \<lambda>t l. if List.member l t then l else t # l in
                                        case t of
                                          OclTy_class obj \<Rightarrow>
                                            let t = OclTy_class_pre (TyObjN_role_ty (TyObj_to obj)) in
                                            f (OclTy_collection Sequence t) (f (OclTy_collection Set t) l)
                                        | OclTy_collection _ _ \<Rightarrow> f t l
                                        | OclTy_pair _ _ \<Rightarrow> f t l
                                        | _ \<Rightarrow> l)
                                      l_attr)
                                  []
                                  expr))))"

definition "print_infra_instantiation_class = start_map'' Thy_instantiation_class o (\<lambda>expr _ base_attr' _. map_class_gen_h''''
  (\<lambda>isub_name name _ l_attr l_inherited l_cons.
    let (l_attr, l_inherited) = base_attr' (l_attr, of_inh l_inherited) in
    let oid_of = \<langle>''oid_of''\<rangle> in
    [Instantiation
      (isub_name datatype_name)
      oid_of
      (Expr_rewrite
        (Expr_basic [oid_of])
        \<langle>''=''\<rangle>
        (Expr_function
                   [ let var_oid = \<langle>''t''\<rangle> in
                     ( Expr_basic (isub_name datatype_constr_name # var_oid # List_map (\<lambda>_. wildcard) l_attr)
                     , Expr_case
                         (Expr_basic [var_oid])
                         ( ( Expr_apply
                               (isub_name datatype_ext_constr_name)
                               (Expr_basic [var_oid] # List_flatten (List_map (List_map (\<lambda>_. Expr_basic [wildcard])) l_inherited))
                           , Expr_basic [var_oid])
                         # List_map (\<lambda>x. ( Expr_apply (datatype_ext_constr_name @@ mk_constr_name name x) [Expr_basic [var_oid]]
                                         , Expr_apply oid_of [Expr_basic [var_oid]])) (of_sub l_cons)))]))
    ]) expr)"

definition "print_infra_instantiation_universe expr = start_map Thy_instantiation_class
  [ let oid_of = \<langle>''oid_of''\<rangle> in
    Instantiation unicode_AA oid_of
      (Expr_rewrite
        (Expr_basic [oid_of])
        \<langle>''=''\<rangle>
        (Expr_function (map_class (\<lambda>isub_name name _ _ _ _.
    let esc = (\<lambda>h. Expr_basic (h # [name])) in
    (esc (isub_name datatype_in), esc oid_of)) expr))) ]"


definition "print_instantia_def_strictrefeq_name mk_strict name = mk_strict [\<langle>''_''\<rangle>, isub_of_str name]"
definition "print_instantia_def_strictrefeq = start_map Thy_defs_overloaded o
  map_class (\<lambda>isub_name name _ _ _ _.
    let mk_strict = (\<lambda>l. flatten (\<langle>''StrictRefEq''\<rangle> # isub_of_str \<langle>''Object''\<rangle> # l))
      ; s_strict = mk_strict [\<langle>''_''\<rangle>, isub_of_str name]
      ; var_x = \<langle>''x''\<rangle>
      ; var_y = \<langle>''y''\<rangle> in
    Defs_overloaded
      (print_instantia_def_strictrefeq_name mk_strict name)
      (Expr_rewrite (Expr_binop (Expr_annot (Expr_basic [var_x]) name)
                                unicode_doteq
                                (Expr_basic [var_y]))
                    unicode_equiv
                    (Expr_basic [mk_strict [], var_x, var_y])) )"

definition "print_instantia_lemmas_strictrefeq = start_map'
  (if activate_simp_optimization then
     \<lambda>expr.
       let mk_strict = (\<lambda>l. flatten (\<langle>''StrictRefEq''\<rangle> # isub_of_str \<langle>''Object''\<rangle> # l))
         ; name_set = map_class (\<lambda>_ name _ _ _ _. print_instantia_def_strictrefeq_name mk_strict name) expr in
       case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
         [ Lemmas_simp \<langle>''''\<rangle> (List_map (Thm_str) name_set) ]
  else (\<lambda>_. []))"

end
