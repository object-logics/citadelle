(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_class_diagram_generator.thy --- 
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013      Universite Paris-Sud, France
 *               2013      IRT SystemX, France
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

theory OCL_class_diagram_generator
imports Main
begin

section{* ... *}

type_synonym str = "char list"

datatype oclTy = OclTy_base str | OclTy_object str
definition "str_of_ty = (\<lambda>object. case object of OclTy_base x \<Rightarrow> x | OclTy_object x \<Rightarrow> x)"

datatype univ =
 Mk_univ
   str (* name of the class *)
   "(str (* name *) \<times> oclTy) list" (* attribute *)
   "univ option" (* link to subclasses *)

fun get_class_hierarchy where
   "get_class_hierarchy (Mk_univ name l_attr dataty) =
    (name, l_attr) # (case dataty of None \<Rightarrow> [] | Some dataty \<Rightarrow> get_class_hierarchy dataty)"

datatype position = EQ | LT | GT

fun less_than_hierarchy where
  "less_than_hierarchy l item1 item2 =
    (case l of [] \<Rightarrow> None
             | x # xs \<Rightarrow>
               if x = item1 then
                 Some GT
               else if x = item2 then
                 Some LT
               else
                 less_than_hierarchy xs item1 item2)"
definition "compare_hierarchy = (\<lambda>l x1 x2. if x1 = x2 then Some EQ else less_than_hierarchy l x1 x2)"


fun flip where "flip (a,b) = (b,a)"
definition "rev_map f l = rev (map f l)"

section{* HOL deep embedding *}
subsection{* type definition *}

datatype simplety = Opt str | Raw str

datatype dataty = Datatype str (* name *)
                           "(str (* name *) \<times> simplety list (* arguments *)) list" (* constructors *)

datatype raw_ty = 
   Ty_apply raw_ty "raw_ty list"
 | Ty_base str

datatype ty_synonym = Type_synonym str (* name *) 
                                   raw_ty (* content *)

datatype expr = Expr_case expr (* value *)
                          "(expr (* pattern *) \<times> expr (* to return *)) list"
              | Expr_rewrite expr (* left *) str (* symb rewriting *) expr (* right *)
              | Expr_basic "str list"
              | Expr_binop expr str expr
              | Expr_annot expr str (* type *)
              | Expr_lambda str (* lambda var *) expr
              | Expr_lambdas "str list" expr
              | Expr_apply str "expr list"
              | Expr_some expr (* with annotation \<lfloor> ... \<rfloor> *)
              | Expr_postunary expr expr (* no parenthesis and separated with one space *)
              | Expr_warning_parenthesis expr (* optional parenthesis that can be removed but a warning will be raised *)
              | Expr_parenthesis expr (* mandatory parenthesis *)

datatype instantiation_class = Instantiation str (* name *)
                                             str (* name in definition *)
                                             expr 

datatype defs_overloaded = Defs_overloaded str (* name *) expr (* content *)

datatype consts_class = Consts str (* name *) str (* type output *) str (* ocl symbol1 *) str (* ocl symbol2 *)

datatype definition_hol = Definition expr
                        | Definition_abbrev str (* name *) "expr (* syntax extension *) \<times> int (* priority *)" expr

datatype lemmas_simp = Lemmas_simp "str list"

datatype tactic = Tac_rule str | Tac_simp | Tac_simp_add "str list" | Tac_simp_all | Tac_simp_all_add str

datatype lemma_by = Lemma_by str (* name *) "expr list" (* specification *) "tactic list" (* tactic separator : ',' *)

subsection{* ... *}

definition "wildcard = ''_''"

definition "escape_unicode c = concat ([Char Nibble5 NibbleC] # ''<'' # c # ''>'' # [])"

definition "isub_of_str str = concat (map (\<lambda> c. concat (escape_unicode ''^isub'' # [[c]])) str)"
definition "isup_of_str str = concat (map (\<lambda> c. concat (escape_unicode ''^isup'' # [[c]])) str)"

definition "mk_constr_name name = (\<lambda> x. isub_of_str name @ ''_'' @ isub_of_str x)"
definition "mk_dot = (\<lambda>s1 s2. concat (''.'' # s1 # s2 # []))"
definition "mk_dot_par = (\<lambda>dot s. concat (dot # ''('' # s # '')'' # []))"

subsection{* ... *}

definition "object = OclTy_object ''oid''"

definition "ty_boolean = ''Boolean''"

definition "unicode_equiv = escape_unicode ''equiv''"
definition "unicode_doteq = escape_unicode ''doteq''"
definition "unicode_tau = escape_unicode ''tau''"
definition "unicode_bottom = escape_unicode ''bottom''"
definition "unicode_AA = escape_unicode ''AA''"

definition "datatype_ext_name = ''type''"
definition "datatype_name = datatype_ext_name @ (str_of_ty object)"
definition "datatype_ext_constr_name = ''mk''"
definition "datatype_constr_name = datatype_ext_constr_name @ (str_of_ty object)"
definition "datatype_in = ''in''"

definition "const_oclastype = ''OclAsType''"
definition "const_oclistypeof = ''OclIsTypeOf''"
definition "const_ocliskindof = ''OclIsKindOf''"
definition "dot_oclastype = ''.oclAsType''"
definition "dot_oclistypeof = ''.oclIsTypeOf''"
definition "dot_ocliskindof = ''.oclIsKindOf''"
definition "dot_astype = mk_dot_par dot_oclastype"
definition "dot_istypeof = mk_dot_par dot_oclistypeof"
definition "dot_iskindof = mk_dot_par dot_ocliskindof"

definition "var_in_pre_state = ''in_pre_state''"
definition "var_in_post_state = ''in_post_state''"
definition "var_reconst_basetype = ''reconst_basetype''"
definition "var_eval_extract = ''eval_extract''"
definition "var_deref_oid = ''deref_oid''"
definition "var_select = ''select''"

section{* Model of OCL classes *}

fun map_class_gen where
   "map_class_gen f (Mk_univ name l_attr dataty) = 
  ((case dataty of None \<Rightarrow> [] | Some dataty \<Rightarrow> map_class_gen f dataty) @
   f (\<lambda>s. s @ isub_of_str name) name l_attr)"

definition "map_class f = map_class_gen (\<lambda>isub_name name l_attr. [f isub_name name l_attr])"
definition "add_hierarchy f x = (\<lambda>isub_name name _. f isub_name name (map fst (get_class_hierarchy x)))"
definition "add_hierarchy' f x = (\<lambda>isub_name name _. f isub_name name ((get_class_hierarchy x)))"
definition "map_class_gen_h f x = map_class_gen (add_hierarchy f x) x"
definition "map_class_gen_h' f x = map_class_gen (add_hierarchy' f x) x"
definition "map_class_h f x = map_class (add_hierarchy f x) x"
definition "map_class_arg_only f = map_class_gen (\<lambda> isub_name name l. case l of [] \<Rightarrow> [] | _ \<Rightarrow> f isub_name name l)"
definition "get_hierarchy f x = f (map fst (get_class_hierarchy x))"

subsection{* ... *}

fun print_datatype_class where
   "print_datatype_class (Mk_univ name l_attr dataty) =
  (let (l_cons, v) = (case dataty of None \<Rightarrow> ([],[]) | Some dataty \<Rightarrow> print_datatype_class dataty) in
   (name # l_cons, 
    v @
    (let isub_name = (\<lambda>s. s @ isub_of_str name) in
    [ Datatype
        (isub_name datatype_ext_name)
        ( (rev_map (\<lambda>x. (datatype_ext_constr_name @ mk_constr_name name x, [Raw (datatype_ext_name @ isub_of_str x)])) l_cons)
        @ [(isub_name datatype_ext_constr_name, map (\<lambda>(_, x). Opt (str_of_ty x)) l_attr)] )
    , Datatype
        (isub_name datatype_name)
        [ (isub_name datatype_constr_name, [ Raw (str_of_ty object)
                                           , Raw (isub_name datatype_ext_name) ] ) ] ])))"

definition "print_datatype_universe = 
  map_class (\<lambda>isub_name _ _. (isub_name datatype_in, [Raw (isub_name datatype_name)]))"

definition "print_type_synonym_class =
  map_class (\<lambda>isub_name name _.
    Type_synonym name (Ty_apply (Ty_base ''val'') [Ty_base unicode_AA, 
    let option = (\<lambda>x. Ty_apply (Ty_base ''option'') [x]) in
    option (option (Ty_base (isub_name datatype_name))) ]))"

definition "print_instantiation_class =
  map_class (\<lambda>isub_name _ _.
    let oid_of = ''oid_of'' in
    Instantiation
      (isub_name datatype_name)
      oid_of
      (let var_x = ''x'' in
       Expr_rewrite
        (Expr_basic [oid_of, var_x])
        ''=''
        (Expr_case (Expr_basic [var_x])
                   [ let oid = ''oid'' in
                     (Expr_basic [isub_name datatype_constr_name, oid, wildcard], Expr_basic [oid])])))"

definition "print_instantiation_universe oid_of =
  map_class (\<lambda>isub_name name _.
    let esc = (\<lambda>h. Expr_basic (h # [name])) in
    (esc (isub_name datatype_in), esc oid_of))"


definition "print_def_strictrefeq =
  map_class (\<lambda>isub_name name _.
    let mk_strict = (\<lambda>l. concat (''StrictRefEq'' # isub_of_str ''Object'' # l))
      ; s_strict = mk_strict [''_'', isub_of_str name]
      ; var_x = ''x''
      ; var_y = ''y'' in
    Defs_overloaded s_strict (Expr_rewrite (Expr_binop (Expr_annot (Expr_basic [var_x]) name)
                                                       unicode_doteq
                                                       (Expr_basic [var_y]))
                                           unicode_equiv
                                           (Expr_basic [mk_strict [], var_x, var_y])) )"

subsection{* AsType *}

definition "print_astype_consts =
  map_class (\<lambda>isub_name name _.
    Consts (isub_name const_oclastype) name dot_oclastype name)"

definition "print_astype_from_universe =
  map_class_h (\<lambda>isub_name name l_hierarchy. 
    let const_astype = concat (const_oclastype # isub_of_str name # ''_'' # unicode_AA # [])
      ; var_u = ''u'' in
    Definition (Expr_rewrite (Expr_basic [const_astype]) ''='' (Expr_lambda var_u 

   (let ((finish_with_some1, finish_with_some2), last_case_none) = 
     let (f, r) = (if hd l_hierarchy = name then (id, []) else (flip, [(Expr_basic [wildcard], Expr_basic [''None''])])) in
     (f (id, Expr_some), r) in
   finish_with_some2
   (Expr_case (Expr_basic [var_u]) (concat (map 
   (\<lambda>h_name. 
     let isub_h = (\<lambda> s. s @ isub_of_str h_name)
       ; var_oid = ''oid''
       ; pattern_complex = (\<lambda>h_name name. 
                            let isub_h = (\<lambda> s. s @ isub_of_str h_name)
                              ; isub_name = (\<lambda>s. s @ isub_of_str name) 
                              ; isub_n = (\<lambda>s. isub_name (concat (s # ''_'' # [])))
                              ; var_name = name in
                             Expr_apply (isub_h datatype_constr_name) 
                                        [Expr_basic [var_oid], Expr_apply (isub_n (isub_h datatype_ext_constr_name)) [Expr_basic [var_name]]])
       ; pattern_simple = (\<lambda> name.
                            let isub_name = (\<lambda>s. s @ isub_of_str name) 
                              ; var_name = name in
                             Expr_basic [isub_name datatype_constr_name, var_oid, var_name])
       ; case_branch = (\<lambda>pat res. (Expr_apply (isub_h datatype_in) [pat], finish_with_some1 res)) in
             case compare_hierarchy l_hierarchy h_name name
             of Some GT \<Rightarrow> case_branch (pattern_complex h_name name) (pattern_simple name)
              | Some EQ \<Rightarrow> let n = Expr_basic [name] in case_branch n n
              | Some LT \<Rightarrow> case_branch (pattern_simple h_name) (pattern_complex name h_name)) l_hierarchy
   # [last_case_none])))))))"

definition "print_astype_class =
  map_class_gen_h (\<lambda>isub_name name l_hierarchy.
    map
      (\<lambda> h_name.
        Defs_overloaded 
          (concat (isub_name const_oclastype # ''_'' # h_name # []))
          (let var_x = ''x'' in
           Expr_rewrite
             (Expr_postunary (Expr_annot (Expr_basic [var_x]) h_name) (Expr_basic [dot_astype name]))
             unicode_equiv
             (let x = compare_hierarchy l_hierarchy h_name name in 
              if x = Some EQ then
                Expr_basic [var_x]
              else
                let var_tau = unicode_tau
                  ; val_invalid = Expr_apply ''invalid'' [Expr_basic [var_tau]] in
                Expr_lambda var_tau 
                  (Expr_case
                    (Expr_apply var_x [Expr_basic [var_tau]])
                    ( (Expr_basic [unicode_bottom], val_invalid)
                    # (Expr_some (Expr_basic [unicode_bottom]), Expr_apply ''null'' [Expr_basic [var_tau]])
                    # (let var_oid = ''oid''
                         ; pattern_complex = (\<lambda>h_name name. 
                            let isub_h = (\<lambda> s. s @ isub_of_str h_name)
                              ; isub_name = (\<lambda>s. s @ isub_of_str name) 
                              ; isub_n = (\<lambda>s. isub_name (concat (s # ''_'' # [])))
                              ; var_name = name in
                             Expr_apply (isub_h datatype_constr_name) 
                                        [Expr_basic [var_oid], Expr_apply (isub_n (isub_h datatype_ext_constr_name)) [Expr_basic [var_name]]])
                         ; pattern_simple = (\<lambda> name.
                            let isub_name = (\<lambda>s. s @ isub_of_str name) 
                              ; var_name = name in
                             Expr_basic [isub_name datatype_constr_name, var_oid, var_name])
                         ; some_some = (\<lambda>x. Expr_some (Expr_some x)) in
                       if x = Some LT then
                         [ (some_some (pattern_simple h_name), some_some (pattern_complex name h_name)) ]
                       else 
                         [ (some_some (pattern_complex h_name name), some_some (pattern_simple name))
                         , (Expr_basic [wildcard], val_invalid) ]) ) ))) )
      l_hierarchy)"

definition "print_astype_lemmas_id =
  map_class (\<lambda>isub_name name _.
    concat (isub_name const_oclastype # ''_'' # name # []) )"

definition "print_astype_lemma_cp =
  get_hierarchy (\<lambda>l_hierarchy.
  concat (concat
  (map (\<lambda>name1. map (\<lambda>name2. map (\<lambda>name3. 
    Lemma_by
      (concat (''cp_'' # const_oclastype # isub_of_str name1 # ''_'' # name3 # ''_'' # name2 # []))
      (let var_p = ''p''; var_x = ''x'' in
       map
         (\<lambda>x. Expr_apply ''cp'' [x])
         [ Expr_basic [var_p]
         , Expr_lambda var_x
             (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_apply var_p [Expr_annot (Expr_basic [var_x]) name3]) name2)
               (Expr_basic [dot_astype name1])))])
      [Tac_rule ''cpI1'', if name1 = name2 then Tac_simp_all
                          else Tac_simp_all_add (concat (const_oclastype # isub_of_str name1 # ''_'' # name2 # []))]
  ) l_hierarchy) l_hierarchy) l_hierarchy)))"

definition "print_astype_lemmas_cp =
  get_hierarchy (\<lambda>l_hierarchy.
    [Lemmas_simp
      (concat (concat
        (map (\<lambda>name1. map (\<lambda>name2. map (\<lambda>name3. 
          (concat (''cp_'' # const_oclastype # isub_of_str name1 # ''_'' # name3 # ''_'' # name2 # []))
        ) l_hierarchy) l_hierarchy) l_hierarchy)))])"

definition "print_astype_lemma_strict = 
  get_hierarchy (\<lambda>l_hierarchy.
  concat (concat
  (map (\<lambda>name1. map (\<lambda>name2. map (\<lambda>name3. 
    Lemma_by
      (concat (const_oclastype # isub_of_str name1 # ''_'' # name3 # ''_'' # name2 # []))
      [ Expr_rewrite
             (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [name2]) name3)
               (Expr_basic [dot_astype name1])))
             ''=''
             (Expr_basic [name2])]
      (if name1 = name3 then [Tac_simp]
       else [Tac_rule ''ext'', Tac_simp_add (concat (const_oclastype # isub_of_str name1 # ''_'' # name3 # [])
                                            # ''bot_option_def''
                                            # (if name2 = ''invalid'' then [''invalid_def'']
                                               else [''null_fun_def'',''null_option_def'']))])
  ) l_hierarchy) [''invalid'',''null'']) l_hierarchy)))"

definition "print_astype_lemmas_strict =
  get_hierarchy (\<lambda>l_hierarchy.
  [ Lemmas_simp
      (concat (concat
      (map (\<lambda>name1. map (\<lambda>name2. map (\<lambda>name3. 
        (concat (const_oclastype # isub_of_str name1 # ''_'' # name3 # ''_'' # name2 # []))
      ) l_hierarchy) [''invalid'',''null'']) l_hierarchy)))])"

subsection{* IsTypeOf *}

definition "print_istypeof_consts =
  map_class (\<lambda>isub_name name _.
    Consts (isub_name const_oclistypeof) ty_boolean dot_oclistypeof name)"

definition "print_istypeof_from_universe =
  map_class_h (\<lambda>isub_name name l_hierarchy. 
    let const_istypeof = concat (const_oclistypeof # isub_of_str name # ''_'' # unicode_AA # [])
      ; var_u = ''u'' in
    Definition (Expr_rewrite (Expr_basic [const_istypeof]) ''='' (Expr_lambda var_u 

   (let ((finish_with_some1, finish_with_some2), last_case_none) = 
     let (f, r) = (if hd l_hierarchy = name then (id, []) else (flip, [(Expr_basic [wildcard], Expr_basic [''None''])])) in
     (f (id, Expr_some), r) in
   finish_with_some2
   (Expr_case (Expr_basic [var_u]) (concat (map 
   (\<lambda>h_name. 
     let isub_h = (\<lambda> s. s @ isub_of_str h_name)
       ; var_oid = ''oid''
       ; pattern_complex = (\<lambda>h_name name. 
                            let isub_h = (\<lambda> s. s @ isub_of_str h_name)
                              ; isub_name = (\<lambda>s. s @ isub_of_str name) 
                              ; isub_n = (\<lambda>s. isub_name (concat (s # ''_'' # [])))
                              ; var_name = name in
                             Expr_apply (isub_h datatype_constr_name) 
                                        [Expr_basic [var_oid], Expr_apply (isub_n (isub_h datatype_ext_constr_name)) [Expr_basic [var_name]]])
       ; pattern_simple = (\<lambda> name.
                            let isub_name = (\<lambda>s. s @ isub_of_str name) 
                              ; var_name = name in
                             Expr_basic [isub_name datatype_constr_name, var_oid, var_name])
       ; case_branch = (\<lambda>pat res. (Expr_apply (isub_h datatype_in) [pat], finish_with_some1 res)) in
             case compare_hierarchy l_hierarchy h_name name
             of Some GT \<Rightarrow> case_branch (pattern_complex h_name name) (pattern_simple name)
              | Some EQ \<Rightarrow> let n = Expr_basic [name] in case_branch n n
              | Some LT \<Rightarrow> case_branch (pattern_simple h_name) (pattern_complex name h_name)) l_hierarchy
   # [last_case_none])))))))"

definition "print_istypeof_class =
  map_class_gen_h' (\<lambda>isub_name name l_hierarchy.
    map
      (\<lambda> (h_name, l_attr).
        Defs_overloaded 
          (concat (isub_name const_oclistypeof # ''_'' # h_name # []))
          (let var_x = ''x'' in
           Expr_rewrite
             (Expr_postunary (Expr_annot (Expr_basic [var_x]) h_name) (Expr_basic [dot_istypeof name]))
             unicode_equiv
             (let var_tau = unicode_tau
                ; ocl_tau = (\<lambda>v. Expr_apply v [Expr_basic [var_tau]]) in
                Expr_lambda var_tau 
                  (Expr_case
                    (ocl_tau var_x)
                    ( (Expr_basic [unicode_bottom], ocl_tau ''invalid'')
                    # (Expr_some (Expr_basic [unicode_bottom]), ocl_tau ''true'')
                    # (let var_oid = wildcard
                         ; pattern_complex_gen = (\<lambda>f1 f2 h_name name. 
                            let isub_h = (\<lambda> s. s @ isub_of_str h_name)
                              ; isub_name = (\<lambda>s. s @ isub_of_str name) 
                              ; isub_n = (\<lambda>s. isub_name (concat (s # ''_'' # [])))
                              ; var_name = name in
                             Expr_apply (isub_h datatype_constr_name) 
                                        [Expr_basic [var_oid], Expr_apply (f2 isub_n (isub_h datatype_ext_constr_name)) (f1 var_name)])
                         ; pattern_complex = pattern_complex_gen (\<lambda>x. [Expr_basic [wildcard]]) (\<lambda> f x. f x)
                         ; some_some = (\<lambda>x. Expr_some (Expr_some x)) in
                       let l_false = [(Expr_basic [wildcard], ocl_tau ''false'')]
                         ; ret_true = (\<lambda>x. (some_some x, ocl_tau ''true'') # (if h_name = hd (rev_map fst l_hierarchy) then [] else l_false))
                         ; x = compare_hierarchy (map fst l_hierarchy) h_name name in
                       if x = Some EQ then
                         ret_true (pattern_complex_gen (\<lambda>_. map (\<lambda>_. Expr_basic [wildcard]) l_attr) (\<lambda>_ x. x) name h_name)
                       else if x = Some GT then
                         ret_true (pattern_complex h_name name)
                       else 
                         l_false) ) ))) )
      l_hierarchy)"

definition "print_istypeof_lemmas_id =
  map_class (\<lambda>isub_name name _.
    concat (isub_name const_oclistypeof # ''_'' # name # []) )"

definition "print_istypeof_lemma_cp =
  get_hierarchy (\<lambda>l_hierarchy.
  concat (concat
  (map (\<lambda>name1. map (\<lambda>name2. map (\<lambda>name3. 
    Lemma_by
      (concat (''cp_'' # const_oclistypeof # isub_of_str name1 # ''_'' # name3 # ''_'' # name2 # []))
      (let var_p = ''p''; var_x = ''x'' in
       map
         (\<lambda>x. Expr_apply ''cp'' [x])
         [ Expr_basic [var_p]
         , Expr_lambda var_x
             (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_apply var_p [Expr_annot (Expr_basic [var_x]) name3]) name2)
               (Expr_basic [dot_istypeof name1])))])
      [Tac_rule ''cpI1'', (*if name1 = name2 then Tac_simp_all
                          else*) Tac_simp_all_add (concat (const_oclistypeof # isub_of_str name1 # ''_'' # name2 # []))]
  ) l_hierarchy) l_hierarchy) l_hierarchy)))"

definition "print_istypeof_lemmas_cp =
  get_hierarchy (\<lambda>l_hierarchy.
    [Lemmas_simp
  (concat (concat
  (map (\<lambda>name1. map (\<lambda>name2. map (\<lambda>name3. 
      (concat (''cp_'' # const_oclistypeof # isub_of_str name1 # ''_'' # name3 # ''_'' # name2 # []))
  ) l_hierarchy) l_hierarchy) l_hierarchy)))])"

definition "print_istypeof_lemma_strict =
  get_hierarchy (\<lambda>l_hierarchy.
  concat (concat
  (map (\<lambda>name1. map (\<lambda>(name2,name2'). map (\<lambda>name3. 
    Lemma_by
      (concat (const_oclistypeof # isub_of_str name1 # ''_'' # name3 # ''_'' # name2 # []))
      [ Expr_rewrite
             (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [name2]) name3)
               (Expr_basic [dot_istypeof name1])))
             ''=''
             (Expr_basic [name2'])]
      ((*if name1 = name3 then [Tac_simp]
       else*) [Tac_rule ''ext'', Tac_simp_add (concat (const_oclistypeof # isub_of_str name1 # ''_'' # name3 # [])
                                            # ''bot_option_def''
                                            # (if name2 = ''invalid'' then [''invalid_def'']
                                               else [''null_fun_def'',''null_option_def'']))])
  ) l_hierarchy) [(''invalid'',''invalid''),(''null'',''true'')]) l_hierarchy)))"

definition "print_istypeof_lemmas_strict =
  get_hierarchy (\<lambda>l_hierarchy.
  [ Lemmas_simp
  (concat (concat
  (map (\<lambda>name1. map (\<lambda>name2. map (\<lambda>name3. 
      (concat (const_oclistypeof # isub_of_str name1 # ''_'' # name3 # ''_'' # name2 # []))
  ) l_hierarchy) [''invalid'',''null'']) l_hierarchy)))])"

subsection{* IsKindOf *}

definition "print_iskindof_consts =
  map_class (\<lambda>isub_name name _.
    Consts (isub_name const_ocliskindof) ty_boolean dot_ocliskindof name)"

definition "print_iskindof_from_universe =
  map_class_h (\<lambda>isub_name name l_hierarchy. 
    let const_iskindof = concat (const_ocliskindof # isub_of_str name # ''_'' # unicode_AA # [])
      ; var_u = ''u'' in
    Definition (Expr_rewrite (Expr_basic [const_iskindof]) ''='' (Expr_lambda var_u 

   (let ((finish_with_some1, finish_with_some2), last_case_none) = 
     let (f, r) = (if hd l_hierarchy = name then (id, []) else (flip, [(Expr_basic [wildcard], Expr_basic [''None''])])) in
     (f (id, Expr_some), r) in
   finish_with_some2
   (Expr_case (Expr_basic [var_u]) (concat (map 
   (\<lambda>h_name. 
     let isub_h = (\<lambda> s. s @ isub_of_str h_name)
       ; var_oid = ''oid''
       ; pattern_complex = (\<lambda>h_name name. 
                            let isub_h = (\<lambda> s. s @ isub_of_str h_name)
                              ; isub_name = (\<lambda>s. s @ isub_of_str name) 
                              ; isub_n = (\<lambda>s. isub_name (concat (s # ''_'' # [])))
                              ; var_name = name in
                             Expr_apply (isub_h datatype_constr_name) 
                                        [Expr_basic [var_oid], Expr_apply (isub_n (isub_h datatype_ext_constr_name)) [Expr_basic [var_name]]])
       ; pattern_simple = (\<lambda> name.
                            let isub_name = (\<lambda>s. s @ isub_of_str name) 
                              ; var_name = name in
                             Expr_basic [isub_name datatype_constr_name, var_oid, var_name])
       ; case_branch = (\<lambda>pat res. (Expr_apply (isub_h datatype_in) [pat], finish_with_some1 res)) in
             case compare_hierarchy l_hierarchy h_name name
             of Some GT \<Rightarrow> case_branch (pattern_complex h_name name) (pattern_simple name)
              | Some EQ \<Rightarrow> let n = Expr_basic [name] in case_branch n n
              | Some LT \<Rightarrow> case_branch (pattern_simple h_name) (pattern_complex name h_name)) l_hierarchy
   # [last_case_none])))))))"

fun print_iskindof_class_aux where
   "print_iskindof_class_aux l_hierarchy (Mk_univ name _ dataty) =
  (let (name_past, v) = (case dataty of None \<Rightarrow> (None, []) | Some dataty \<Rightarrow> print_iskindof_class_aux l_hierarchy dataty) in
   (Some name,
   v @
   (let isub_name = (\<lambda>s. s @ isub_of_str name) in
   map (\<lambda> h_name.
    Defs_overloaded 
          (concat (isub_name const_ocliskindof # ''_'' # h_name # []))
          (let var_x = ''x'' in
           Expr_rewrite
             (Expr_postunary (Expr_annot (Expr_basic [var_x]) h_name) (Expr_basic [dot_iskindof name]))
             unicode_equiv
             (let isof = (\<lambda>f name. Expr_warning_parenthesis (Expr_postunary (Expr_basic [var_x]) (Expr_basic [f name]))) in
              case name_past of None \<Rightarrow> isof dot_istypeof name
                              | Some name_past \<Rightarrow> Expr_binop (isof dot_istypeof name) ''or'' (isof dot_iskindof name_past))))
     l_hierarchy
    )))"
definition "print_iskindof_class = (\<lambda> x. snd (print_iskindof_class_aux (map fst (get_class_hierarchy x)) x))"

definition "print_iskindof_lemmas_id =
  map_class (\<lambda>isub_name name _.
    concat (isub_name const_ocliskindof # ''_'' # name # []) )"

definition "print_iskindof_lemma_cp =
  get_hierarchy (\<lambda>l_hierarchy.
  concat (concat
  (map (\<lambda>name1. map (\<lambda>name2. map (\<lambda>name3. 
    Lemma_by
      (concat (''cp_'' # const_ocliskindof # isub_of_str name1 # ''_'' # name3 # ''_'' # name2 # []))
      (let var_p = ''p''; var_x = ''x'' in
       map
         (\<lambda>x. Expr_apply ''cp'' [x])
         [ Expr_basic [var_p]
         , Expr_lambda var_x
             (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_apply var_p [Expr_annot (Expr_basic [var_x]) name3]) name2)
               (Expr_basic [dot_iskindof name1])))])
      [Tac_rule ''cpI1'', (*if name1 = name2 then Tac_simp_all
                          else*) Tac_simp_all_add (concat (const_ocliskindof # isub_of_str name1 # ''_'' # name2 # []))]
  ) l_hierarchy) l_hierarchy) l_hierarchy)))"

definition "print_iskindof_lemmas_cp =
  get_hierarchy (\<lambda>l_hierarchy.
    [Lemmas_simp
  (concat (concat
  (map (\<lambda>name1. map (\<lambda>name2. map (\<lambda>name3. 
      (concat (''cp_'' # const_ocliskindof # isub_of_str name1 # ''_'' # name3 # ''_'' # name2 # []))
  ) l_hierarchy) l_hierarchy) l_hierarchy)))])"

definition "print_iskindof_lemma_strict =
  get_hierarchy (\<lambda>l_hierarchy.
  concat (concat
  (map (\<lambda>name1. map (\<lambda>(name2,name2'). map (\<lambda>name3. 
    Lemma_by
      (concat (const_ocliskindof # isub_of_str name1 # ''_'' # name3 # ''_'' # name2 # []))
      [ Expr_rewrite
             (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [name2]) name3)
               (Expr_basic [dot_iskindof name1])))
             ''=''
             (Expr_basic [name2'])]
      ((*if name1 = name3 then [Tac_simp]
       else*) [Tac_rule ''ext'', Tac_simp_add (concat (const_ocliskindof # isub_of_str name1 # ''_'' # name3 # [])
                                            # ''bot_option_def''
                                            # (if name2 = ''invalid'' then [''invalid_def'']
                                               else [''null_fun_def'',''null_option_def'']))])
  ) l_hierarchy) [(''invalid'',''invalid''),(''null'',''true'')]) l_hierarchy)))"

definition "print_iskindof_lemmas_strict =
  get_hierarchy (\<lambda>l_hierarchy.
  [ Lemmas_simp
  (concat (concat
  (map (\<lambda>name1. map (\<lambda>name2. map (\<lambda>name3. 
      (concat (const_ocliskindof # isub_of_str name1 # ''_'' # name3 # ''_'' # name2 # []))
  ) l_hierarchy) [''invalid'',''null'']) l_hierarchy)))])"

subsection{* ... *}

definition "print_eval_extract =
  [ let var_x = ''x''
      ; var_f = ''f''
      ; var_tau = unicode_tau
      ; some_some = (\<lambda>x. Expr_some (Expr_some x))
      ; var_obj = ''obj'' in
    Definition (Expr_rewrite
                  (Expr_basic [var_eval_extract, var_x, var_f])
                  ''=''
                  (Expr_lambda
                     var_tau
                     (Expr_case (Expr_basic [var_x, var_tau])
                     [ (some_some (Expr_basic [var_obj]), Expr_apply var_f [Expr_apply ''oid_of'' [Expr_basic [var_obj]], Expr_basic [var_tau]])
                     , (Expr_basic [wildcard], Expr_basic [''invalid'', var_tau])])))
  , Definition (Expr_rewrite (Expr_basic [var_in_pre_state]) ''='' (Expr_basic [''fst'']))
  , Definition (Expr_rewrite (Expr_basic [var_in_post_state]) ''='' (Expr_basic [''snd'']))
  , Definition (Expr_rewrite (Expr_basic [var_reconst_basetype]) ''='' (let var1 = ''convert'' ; var2 = ''x'' in
                                                                        Expr_lambdas [var1, var2] (Expr_apply var1 [Expr_basic [var2]]))) ]"

definition "print_deref_oid =
  map_class (\<lambda>isub_name _ _.
    let var_fs = ''fst_snd''
      ; var_f = ''f''
      ; var_oid = ''oid''
      ; var_obj = ''obj''
      ; var_tau = unicode_tau in
    Definition (Expr_rewrite
                  (Expr_basic [isub_name var_deref_oid, var_fs, var_f, var_oid])
                  ''=''
                  (Expr_lambda
                     var_tau
                     (Expr_case (Expr_apply ''heap'' [Expr_basic [var_fs, var_tau], Expr_basic [var_oid]])
                     [ (Expr_some (Expr_basic [isub_name datatype_in, var_obj]), Expr_basic [var_f, var_obj, var_tau])
                     , (Expr_basic [wildcard], Expr_basic [''invalid'', var_tau]) ]))))"

definition "print_select =
  map_class_arg_only (\<lambda>isub_name name l_attr.
    let var_f = ''f''
      ; wildc = Expr_basic [wildcard] in
    let (_, _, l) = (foldl
      (\<lambda>(l_wildl, l_wildr, l_acc) (attr, _). 
        let isup_attr = (\<lambda>s. s @ isup_of_str attr) in
        ( wildc # l_wildl
        , tl l_wildr
        , Definition (Expr_rewrite
                       (Expr_basic [isup_attr (isub_name var_select), var_f])
                       ''=''
                       (let var_x = ''x''
                          ; var_attr = attr in 
                        Expr_lambda
                          var_x
                          (Expr_case
                            (Expr_basic [var_x])
                            (concat ((map (\<lambda>(lhs,rhs). ( Expr_apply
                                                           (isub_name datatype_constr_name)
                                                           [ wildc
                                                           , Expr_apply (isub_name datatype_ext_constr_name)
                                                                        (concat (l_wildl # [lhs] # l_wildr # []))]
                                                       , rhs))
                              [ ( Expr_basic [unicode_bottom], Expr_basic [''null''] )
                              , ( Expr_some (Expr_basic [var_attr])
                                , Expr_apply var_f [ let var_x = ''x'' in
                                                       Expr_lambdas [var_x, wildcard] (Expr_some (Expr_some (Expr_basic [var_x])))
                                                   , Expr_basic [var_attr]]) ]) # [(wildc, Expr_basic [''invalid''])] # []))))) # l_acc))
      ([], map (\<lambda>_. wildc) (tl l_attr), [])
      l_attr) in
    rev l)"

definition "print_dot =
  map_class_arg_only (\<lambda>isub_name name l_attr.
    concat (concat (
    map (\<lambda>(var_in_when_state, dot_at_when, attr_when).
      map (\<lambda>(attr_name, attr_ty).
            let isup_attr = (\<lambda>s. s @ isup_of_str attr_name)
              ; dot_attr = (\<lambda>s. Expr_postunary (Expr_parenthesis (Expr_basic [s])) (Expr_basic [mk_dot attr_name attr_when])) in
            [ Definition_abbrev
                (concat ((isup_attr (isub_name ''dot'')) # dot_at_when # []))
                (dot_attr wildcard, 50)
                (let var_x = ''x'' in
                 Expr_rewrite
                   (dot_attr var_x)
                   ''=''
                   (Expr_apply var_eval_extract [Expr_basic [var_x],
                    let deref_oid = (\<lambda>l. Expr_apply (isub_name var_deref_oid) (Expr_basic [var_in_when_state] # l)) in
                    deref_oid [Expr_apply (isup_attr (isub_name var_select))
                          [case attr_ty of OclTy_base _ \<Rightarrow> Expr_basic [var_reconst_basetype]
                                         | OclTy_object _ \<Rightarrow> deref_oid [] ] ] ])) ])
          l_attr)
        [ (var_in_post_state, '''', '''')
        , (var_in_pre_state, ''_at_pre'', ''@pre'')])))"

end
