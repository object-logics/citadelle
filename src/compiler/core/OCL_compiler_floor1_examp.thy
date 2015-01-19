(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_floor1_examp.thy ---
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

theory  OCL_compiler_floor1_examp
imports OCL_compiler_core_init
begin

section{* Translation of AST *}

subsection{* example *}

definition "print_examp_oclbase_gen = 
 (\<lambda> OclDefInteger nb \<Rightarrow>
        let name = var_OclInteger @@ nb
          ; b = \<lambda>s. Expr_basic [s]
          ; ab_name = b nb in
        (ab_name, Definition_abbrev0
          name
          (b (number_of_str nb))
          (Expr_rewrite (b name) ''='' (Expr_lambda wildcard (Expr_some (Expr_some ab_name)))))
  | OclDefReal (nb0, nb1) \<Rightarrow>
        let name = flatten [ var_OclReal, nb0, ''_'', nb1 ]
          ; b = \<lambda>s. Expr_basic [s]
          ; ab_name = b (flatten [nb0(*(* WARNING 
                                          uncomment this as soon as OCL_basic_type_Real.thy 
                                          is not implemented as 'nat' *), ''.'', nb1*)]) in
        (ab_name, Definition_abbrev0
          name
          (b (flatten [number_of_str nb0, ''.'', number_of_str nb1]))
          (Expr_rewrite (b name) ''='' (Expr_lambda wildcard (Expr_some (Expr_some ab_name)))))
  | OclDefString nb \<Rightarrow>
        let name = var_OclString @@ base255_of_str nb
          ; b = \<lambda>s. Expr_basic [s] in
        if nb \<noteq> [] & list_all (is_letter o nat_of_char) nb then
          let ab_name = b (let c = [Char Nibble2 Nibble7] in flatten [c,c, nb, c,c]) in
          (ab_name,
          Definition_abbrev0 name (b (text2_of_str nb))
            (Expr_rewrite (b name) ''='' (Expr_lambda wildcard (Expr_some (Expr_some ab_name)))))
        else
          let ab_name = b (text_of_str nb) in
          (ab_name,
          Definition
            (Expr_rewrite (b name) ''='' (Expr_lambda wildcard (Expr_some (Expr_some ab_name))))))"

definition "print_examp_oclbase = (\<lambda> OclDefBase l \<Rightarrow> (start_map Thy_definition_hol o List_map (snd o print_examp_oclbase_gen)) l)"

datatype print_examp_instance_draw_list_attr = Return_obj ocl_ty_class | Return_exp hol_expr

fun_quick print_examp_instance_draw_list_attr_aux where
   "print_examp_instance_draw_list_attr_aux f_oid_rec e = 
    (\<lambda>
     (* object case 2 *)
       (OclTy_collection _ ty, ShallB_list l) \<Rightarrow> Expr_list' (\<lambda>e. print_examp_instance_draw_list_attr_aux f_oid_rec (ty, e)) l
     | (OclTy_pair ty1 ty2, ShallB_list [e1, e2]) \<Rightarrow> Expr_pair (print_examp_instance_draw_list_attr_aux f_oid_rec (ty1, e1))
                                                               (print_examp_instance_draw_list_attr_aux f_oid_rec (ty2, e2))
     | (OclTy_class_pre _, shall) \<Rightarrow> f_oid_rec shall
     (* base cases *)
     | (_, ShallB_term s) \<Rightarrow> fst (print_examp_oclbase_gen s)
     (*| (* type error *) *)) e"

definition "print_examp_instance_draw_list_attr = (\<lambda>(f_oid, f_oid_rec).
  let b = \<lambda>s. Expr_basic [s] in
   List_map (\<lambda> obj.
     case
       case obj of
         (t_obj, None) \<Rightarrow> (case t_obj of Some ty_obj \<Rightarrow> Return_obj ty_obj
                                       | _ \<Rightarrow> Return_exp (b ''None''))
       (* object case 1 *)
       | (_, Some (OclTy_class ty_obj, _)) \<Rightarrow> Return_obj ty_obj
       (* *)
       | (_, Some v) \<Rightarrow> Return_exp (Expr_some (print_examp_instance_draw_list_attr_aux f_oid_rec v))
     of Return_obj ty_obj \<Rightarrow> f_oid ty_obj
      | Return_exp exp \<Rightarrow> exp))"

definition "print_examp_instance_app_constr_notmp f_oid = (\<lambda>isub_name app_x l_attr.
  Expr_apply
    (isub_name datatype_constr_name)
    ( app_x
    # print_examp_instance_draw_list_attr f_oid l_attr))"

definition "rbt_of_class ocl =
  (let rbt = (snd o fold_class_gen (\<lambda>_ name l_attr l_inh _ _ rbt.
     ( [()]
     , modify_def (empty, []) name
         (let fold = \<lambda>tag l rbt.
            let (rbt, _, n) = List.fold
                                   (\<lambda> (name_attr, ty) \<Rightarrow> \<lambda>(rbt, cpt, l_obj).
                                     (insert name_attr (ty, tag, OptIdent cpt) rbt, Succ cpt, (case ty of OclTy_class ty_obj \<Rightarrow> Some ty_obj | _ \<Rightarrow> None) # l_obj))
                                   l
                                   (rbt, 0, []) in
            (rbt, (tag, n)) in
          (\<lambda>(rbt, _).
           let (rbt, info_own) = fold OptOwn l_attr rbt in
           let (rbt, info_inh) = fold OptInh (flatten (map_class_inh l_inh)) rbt in
           (rbt, [info_own, info_inh])))
         rbt)) empty) (case D_class_spec ocl of Some c \<Rightarrow> c) in
   (\<lambda>name.
     let rbt = lookup rbt name in
     ( \<lambda> name_attr.
        Option_bind (\<lambda>(rbt, _). lookup rbt name_attr) rbt
     , \<lambda> v. Option_bind (\<lambda>(_, l).
        Option.map (\<lambda>l f accu.
          let (_, accu) =
            List.fold
              (let f_fold = \<lambda>b (n, accu). (Succ n, f b n accu) in
               if D_design_analysis ocl = Gen_only_design then
                 f_fold
               else
                 \<lambda> Some _ \<Rightarrow> (\<lambda>(n, accu). (Succ n, accu))
                 | None \<Rightarrow> f_fold None) (rev l) (0, accu) in
          accu) (List_assoc v l)) rbt)))"

definition "fill_blank f_blank =
  List_map (\<lambda> (attr_ty, l).
    case f_blank attr_ty of Some f_fold \<Rightarrow>
    let rbt = List.fold (\<lambda> ((ty, _, ident), shallow) \<Rightarrow> insert ident (ty, shallow)) l empty in
    (attr_ty, rev (f_fold (\<lambda>b n l. (b, lookup rbt (OptIdent n)) # l) [])))"

fun_quick split_inh_own where
   "split_inh_own f_class s_cast l_attr =
  (let (f_attr, f_blank) = f_class s_cast
     ; split = \<lambda>l. List.partition (\<lambda>((_, OptOwn, _), _) \<Rightarrow> True | _ \<Rightarrow> False) (List.map (\<lambda>(name_attr, data). (case f_attr name_attr of Some x \<Rightarrow> x, data)) l) in
   case l_attr of
     OclAttrNoCast l \<Rightarrow>
       let (l_own, l_inh) = split l in
       OclAttrNoCast (fill_blank f_blank [(OptOwn, l_own), (OptInh, l_inh)])
   | OclAttrCast s_cast l_attr l \<Rightarrow>
       case split l of (l_own, []) \<Rightarrow>
       OclAttrCast s_cast (split_inh_own f_class s_cast l_attr) (fill_blank f_blank [(OptOwn, l_own)]))"

fun_quick print_examp_instance_app_constr2_notmp where
   "print_examp_instance_app_constr2_notmp ty l_attr isub_name cpt f_oid =
  (let (l_inh, l_own) =
     let var_oid = Expr_oid var_oid_uniq (oidGetInh cpt) in
     case l_attr of
       OclAttrNoCast [(OptOwn, l_own), (OptInh, l_inh)] \<Rightarrow> (Expr_apply (isub_name datatype_ext_constr_name) (var_oid # print_examp_instance_draw_list_attr (f_oid isub_name cpt) l_inh), l_own)
     | OclAttrCast x l_attr [(OptOwn, l_own)] \<Rightarrow>
                      (Expr_apply
                        (datatype_ext_constr_name @@ mk_constr_name ty x)
                        [ let isub_name = \<lambda>s. s @@ isub_of_str x in
                          print_examp_instance_app_constr2_notmp x l_attr isub_name cpt f_oid ], l_own) in
   print_examp_instance_app_constr_notmp (f_oid isub_name cpt) isub_name l_inh l_own)"

fun_quick fold_list_attr where
   "fold_list_attr cast_from f l_attr accu = (case l_attr of
        OclAttrNoCast x \<Rightarrow> f cast_from x accu
      | OclAttrCast c_from l_attr x \<Rightarrow> fold_list_attr c_from f l_attr (f cast_from x accu))"

definition "fold_instance_single f ocli = fold_list_attr (Inst_ty ocli) f (Inst_attr ocli)"

definition "init_map_class ocl l =
  (let (rbt_nat, rbt_str, _, _) =
     List.fold
       (\<lambda> ocl (rbt_nat, rbt_str, oid_start, accu).
         ( insert (Oid accu) oid_start rbt_nat
         , insert (Inst_name ocl) oid_start rbt_str
         , oidSucInh oid_start
         , Succ accu))
       l
       (empty, empty, D_oid_start ocl, 0) in
   (rbt_of_class ocl, lookup rbt_nat, lookup rbt_str))"

definition "print_examp_def_st_assoc_build_rbt_gen f rbt map_self map_username l_assoc =
  List.fold
     (\<lambda> (ocli, cpt). fold_instance_single
       (\<lambda> ty l_attr.
         let (f_attr_ty, _) = rbt ty in
         f ty
         (List.fold (\<lambda>(name_attr, shall).
           case f_attr_ty name_attr of
             Some (OclTy_class ty_obj, _, _) \<Rightarrow>
               modify_def ([], ty_obj) name_attr
               (\<lambda>(l, accu). case let find_map = \<lambda> ShallB_str s \<Rightarrow> map_username s | ShallB_self s \<Rightarrow> map_self s in
                                 case shall of
                                   ShallB_list l \<Rightarrow> Some (List_map (\<lambda>shall. case find_map shall of Some cpt \<Rightarrow> cpt) l)
                                 | _ \<Rightarrow> Option.map (\<lambda>x. [x]) (find_map shall) of
                      None \<Rightarrow> (l, accu)
                    | Some oid \<Rightarrow> (List_map (List_map oidGetInh) [[cpt], oid] # l, accu))
           | _ \<Rightarrow> id) l_attr)) ocli) l_assoc empty"

definition "print_examp_def_st_assoc_build_rbt = print_examp_def_st_assoc_build_rbt_gen (modify_def empty)"
definition "print_examp_def_st_assoc_build_rbt2 = print_examp_def_st_assoc_build_rbt_gen (\<lambda>_. id)"

definition "print_examp_def_st_assoc rbt map_self map_username l_assoc =
  (let b = \<lambda>s. Expr_basic [s]
     ; rbt = print_examp_def_st_assoc_build_rbt rbt map_self map_username l_assoc in
   Expr_apply var_map_of_list [Expr_list (fold (\<lambda>name. fold (\<lambda>name_attr (l_attr, ty_obj) l_cons.
         let cpt_from = TyObjN_ass_switch (TyObj_from ty_obj) in
         Expr_pair
           (Expr_basic [print_access_oid_uniq_name cpt_from (\<lambda>s. s @@ isub_of_str name) name_attr])
           (Expr_apply ''List.map''
             [ Expr_binop (bug_ocaml_extraction (let var_x = ''x''
                             ; var_y = ''y'' in
                           Expr_lambdas0
                             (Expr_pair (b var_x) (b var_y))
                             (Expr_list [b var_x, b var_y])))
                          ''o''
                          (b (print_access_choose_name
                                (TyObj_ass_arity ty_obj)
                                cpt_from
                                (TyObjN_ass_switch (TyObj_to ty_obj))))
             , Expr_list' (Expr_list' (Expr_list' (Expr_oid var_oid_uniq))) l_attr ])
         # l_cons)) rbt [])])"

definition "print_examp_instance_oid l ocl =
  (\<lambda>(l, _). ((List_map Thy_definition_hol o flatten o flatten) l))
    (fold_list
      (\<lambda> (f1, f2) _.
        fold_list (\<lambda> o_ocli cpt.
          case o_ocli of None \<Rightarrow> ([], oidSucInh cpt)
          | Some ocli \<Rightarrow>
            ( let var_oid = Expr_oid var_oid_uniq (oidGetInh cpt)
                ; isub_name = \<lambda>s. s @@ isub_of_str (Inst_ty ocli) in
              if List.fold (\<lambda>(_, _, cpt0) b. b | cpt0 = oidGetInh cpt) (D_instance_rbt ocl) False
               | List.fold (\<lambda>(_, l). List.fold (\<lambda>(cpt0, _) b. b | cpt0 = cpt) l) (D_state_rbt ocl) False then
                   []
              else [Definition (Expr_rewrite (f1 var_oid isub_name ocli) ''='' (f2 ocli isub_name cpt))]
            , oidSucInh cpt)) l (D_oid_start ocl))
      [ (\<lambda> var_oid _ _. var_oid,
         \<lambda> _ _ cpt. Expr_oid '''' (oidGetInh cpt)) ]
      (D_oid_start ocl))"

definition "check_single = (\<lambda> (name_attr, oid, l_oid) l_mult l.
  let l = (keys o bulkload o List_map (\<lambda>x. (x, ()))) l
    ; assoc = \<lambda>x. case map_of l_oid x of Some s \<Rightarrow> s
    ; attr_len = natural_of_nat (length l)
    ; l_typed =
       List_map (\<lambda> (mult_min, mult_max0) \<Rightarrow>
         let mult_max = case mult_max0 of None \<Rightarrow> mult_min | Some mult_max \<Rightarrow> mult_max
           ; s_mult = \<lambda> Mult_nat n \<Rightarrow> natural_of_str n | Mult_star \<Rightarrow> ''*''
           ; f = \<lambda>s. flatten [ '' // ''
                             , s
                             , '' constraint [''
                             , s_mult mult_min
                             , if mult_max0 = None then '''' else flatten ['' .. '', s_mult mult_max]
                             , ''] not satisfied'' ] in
         List_map (\<lambda> (b, msg) \<Rightarrow> (b, flatten [ assoc oid
                                             , '' ''
                                             , case name_attr of None \<Rightarrow> ''/* unnamed attribute */'' | Some s \<Rightarrow> ''.'' @@ s
                                             , '' = Set{''
                                             , bug_ocaml_extraction (let l = List_map assoc l in
                                               if l = [] then '''' else '' '' @@ String_concatWith '' , '' l @@ '' '')
                                             , ''}''
                                             , if b then '''' else f msg ]))
                  [(case mult_min of Mult_nat mult_min \<Rightarrow> mult_min \<le> attr_len | _ \<Rightarrow> True, ''minimum'')
                  ,(case mult_max of Mult_nat mult_max \<Rightarrow> mult_max \<ge> attr_len | _ \<Rightarrow> True, ''maximum'')]) l_mult
    ; (stop, l_typed) =
       if list_ex (list_all fst) l_typed then
         ( Warning
         , if list_ex (list_ex (Not o fst)) l_typed then
             (* at least 1 warning *)
             List_map (filter (Not o fst)) l_typed
           else
             (* 0 warning *)
             [[hd (hd l_typed)]])
       else
         (Error, List_map (filter (Not o fst)) l_typed) in
  flatten (List_map (List_map (\<lambda> (b, s) \<Rightarrow> (if b then Writeln else stop, s))) l_typed))"

definition "check_export_code f_writeln f_warning f_error f_raise l_report msg_last =
 (let l_err =
        List.fold
          (\<lambda> (Writeln, s) \<Rightarrow> \<lambda>acc. case f_writeln s of () \<Rightarrow> acc
           | (Warning, s) \<Rightarrow> \<lambda>acc. case f_warning s of () \<Rightarrow> acc
           | (Error, s) \<Rightarrow> \<lambda>acc. case f_error s of () \<Rightarrow> s # acc)
          l_report
          [] in
  if l_err = [] then
    ()
  else
    f_raise (nat_of_str (length l_err) @@ msg_last))"

definition "print_examp_instance_defassoc_gen name l_ocli ocl =
 (case D_design_analysis ocl of Gen_only_analysis \<Rightarrow> [] | Gen_default \<Rightarrow> [] | Gen_only_design \<Rightarrow>
  let a = \<lambda>f x. Expr_apply f [x]
    ; b = \<lambda>s. Expr_basic [s]
    ; (rbt :: _ \<Rightarrow> _ \<times> (_ \<Rightarrow> ((_ \<Rightarrow> natural \<Rightarrow> _ \<Rightarrow> (ocl_ty \<times> ocl_data_shallow) option list) \<Rightarrow> _ \<Rightarrow> _) option)
      , (map_self, map_username)) =
        init_map_class ocl (List_map (\<lambda> Some ocli \<Rightarrow> ocli | None \<Rightarrow> \<lparr> Inst_name = [], Inst_ty = [], Inst_attr = OclAttrNoCast [] \<rparr>) l_ocli) in
  [Definition
     (Expr_rewrite name
     ''=''
     (bug_ocaml_extraction
     (let var_oid_class = ''oid_class''
        ; var_to_from = ''to_from''
        ; var_oid = ''oid''
        ; mk_ty = bug_scala_extraction (\<lambda>l. (flatten o flatten) (List_map (\<lambda>x. ['' '', x, '' '']) l))
        ; a_l = \<lambda>s. Ty_apply (Ty_base var_ty_list) [s] in
      Expr_lambdas
        [var_oid_class, var_to_from, var_oid]
        (Expr_annot0 (Expr_case
          (Expr_apply var_deref_assocs_list
            [ Expr_annot0 (b var_to_from) (Ty_arrow
                                            (a_l (a_l (Ty_base const_oid)))
                                            (let t = a_l (Ty_base const_oid) in
                                             Ty_times t t))
            , Expr_annot (b var_oid) const_oid
            , a ''drop''
              (Expr_applys (print_examp_def_st_assoc rbt map_self map_username
                             (flatten (fst (fold_list (\<lambda>ocli cpt. (case ocli of None \<Rightarrow> [] | Some ocli \<Rightarrow> [(ocli, cpt)], oidSucInh cpt)) l_ocli (D_oid_start ocl)))))
                           [Expr_annot (b var_oid_class) const_oid])])
          [ (b ''Nil'', b ''None'')
          , let b_l = b ''l'' in
            (b_l, a ''Some'' b_l)] ) (Ty_apply (Ty_base ''option'') [a_l (Ty_base const_oid)])))))])"

definition "check_single_ty rbt_init rbt' l_attr_gen l_oid x =
 (\<lambda> (ty1, mult1, role1) (ty2, mult2, role2).
  let s = (*01*) \<lambda> [x0, x1] \<Rightarrow> (x0, x1)
    ; s' = (*01*) \<lambda> [x0, x1] \<Rightarrow> (x0, x1)
    ; s'' = (*01*) \<lambda> [x0, x1] \<Rightarrow> (x0, x1)
    ; (name, (mult_from, mult_to), l) =
        case
          let f = \<lambda>g.
            \<lambda> None \<Rightarrow> None
            | Some role1 \<Rightarrow>
                Option.map
                  (\<lambda>_. let (ty1, role1, f_swap) = g role1 in
                       ( case fst (rbt_init ty1) role1 of Some (OclTy_class ty_obj, _, _) \<Rightarrow> ty_obj
                       , f_swap (TyObj_from, TyObj_to)))
                  (lookup rbt' role1) in
          case role2 of
             None \<Rightarrow> f (\<lambda>role1. (ty2, role1, \<lambda>(a, b). (b, a))) role1
           | Some role2 \<Rightarrow>
              (case lookup rbt' role2 of
                Some (_, ty_obj) \<Rightarrow> Some (ty_obj, (TyObj_from, TyObj_to))
              | None \<Rightarrow> f (\<lambda>_. (ty1, role2, id)) role1)
        of
          Some (ty_obj, (f_from, f_to)) \<Rightarrow>
            bug_ocaml_extraction (
            let (o_from, o_to) = (f_from ty_obj, f_to ty_obj) in
            ( case (TyObjN_role_name o_from, TyObjN_role_name o_to) of
                (name_from, name_to) \<Rightarrow> [name_from, name_to]
            , (TyObjN_role_multip o_from, TyObjN_role_multip o_to)
            , deref_assocs_list s x (List_map (if ( TyObjN_ass_switch o_from
                                                  , TyObjN_ass_switch o_to) = (0, 1) then(*01*) id else(*10*) rev)
                                              (case l_attr_gen (TyObj_ass_id ty_obj) of Some l_attr \<Rightarrow> l_attr))))
        | None \<Rightarrow> ([role1, role2], (mult1, mult2), []) in
  (\<lambda>acc.
    flatten [ acc
            , check_single
                ((snd o s'') name, x, l_oid)
                ((snd o s') (case (mult_from, mult_to) of (OclMult mult_from _, OclMult mult_to _) \<Rightarrow> [mult_from, mult_to]))
                l]))"

definition "print_examp_instance_defassoc_typecheck_gen name l_ocli ocl =
 (let l_assoc = flatten (fst (fold_list (\<lambda>ocli cpt. (case ocli of None \<Rightarrow> []
                                                                | Some ocli \<Rightarrow> [(ocli, cpt)], oidSucInh cpt)) l_ocli (D_oid_start ocl)))
    ; (rbt_init :: _ \<Rightarrow> _ \<times> (_ \<Rightarrow> ((_ \<Rightarrow> natural \<Rightarrow> _ \<Rightarrow> (ocl_ty \<times> ocl_data_shallow) option list) \<Rightarrow> _ \<Rightarrow> _) option)
                , (map_self, map_username)) =
              init_map_class ocl (List_map (\<lambda> Some ocli \<Rightarrow> ocli | None \<Rightarrow> \<lparr> Inst_name = [], Inst_ty = [], Inst_attr = OclAttrNoCast [] \<rparr>) l_ocli)
    ; rbt = print_examp_def_st_assoc_build_rbt2 rbt_init map_self map_username l_assoc
    ; l_attr_gen = map_of_list (fold (\<lambda>_ (l_attr, ty_obj).
           Cons ( TyObj_ass_id ty_obj
                , List_map ( (\<lambda>(x , y). [x , y])
                           o (if TyObjN_ass_switch (TyObj_from ty_obj) < TyObjN_ass_switch (TyObj_to ty_obj) then
                                (*01*) \<lambda> [x0, x1] \<Rightarrow> (x0, x1)
                              else
                                (*10*) \<lambda> [x0, x1] \<Rightarrow> (x1, x0)))
                           l_attr)) rbt [])
    ; l_spec = snd (arrange_ass (fst (find_class_ass ocl)))
    ; l_oid_gen = List_map
        (\<lambda> (ocli, oids).
          ( fst (hd (fold_instance_single (\<lambda>a b. Cons (a, b)) ocli []))
          , case oidGetInh oids of oid \<Rightarrow> oid
          , Inst_name ocli ))
        l_assoc in
  case List_split l_oid_gen of (_, l_oid) \<Rightarrow>
  let l_out =
    List.fold
      (\<lambda> (name, (x, _)).
        let f = \<lambda>(ty1, mult1, role1).
          if name = ty1 then
            check_single_ty rbt_init rbt l_attr_gen l_oid x (ty1, mult1, role1)
          else
            (\<lambda>_. id) in
        List.fold (\<lambda>ass.
                     case OclAss_relation ass of
                       [t1, t2] \<Rightarrow> f t2 t1 o f t1 t2
                     | _ \<Rightarrow> id)
                  l_spec)
      l_oid_gen
      [] in

  [ raise_ml l_out '' error(s) in multiplicity constraints'' ])"

definition "print_examp_instance_defassoc = (\<lambda> OclInstance l \<Rightarrow> \<lambda> ocl.
  (\<lambda>l_res.
    ( print_examp_instance_oid (List_map Some l) ocl
      @@ List_map Thy_definition_hol l_res
    , ocl))
  (print_examp_instance_defassoc_gen
    (Expr_oid var_inst_assoc (oidGetInh (D_oid_start ocl)))
    (List_map Some l)
    ocl))"

definition "print_examp_instance_defassoc_typecheck = (\<lambda> OclInstance l \<Rightarrow> \<lambda> ocl.
  (\<lambda>l_res. (List_map Thy_ml l_res, ocl \<lparr> D_import_compiler := True \<rparr>))
  (print_examp_instance_defassoc_typecheck_gen
    (Expr_oid var_inst_assoc (oidGetInh (D_oid_start ocl)))
    (List_map Some l)
    ocl))"

definition "print_examp_instance_app_constr2_notmp_norec = (\<lambda>(rbt, (map_self, map_username)) ocl cpt_start ocli isub_name cpt.
  print_examp_instance_app_constr2_notmp
    (Inst_ty ocli)
    (split_inh_own rbt (Inst_ty ocli) (Inst_attr ocli))
    isub_name
    cpt
    (\<lambda>isub_name oid.
      ( \<lambda> ty_obj.
        bug_ocaml_extraction
          (let b = \<lambda>s. Expr_basic [s] in
          Expr_applys
            cpt_start
            (bug_ocaml_extraction
            (let ty_objfrom = TyObj_from ty_obj
               ; ty_objto = TyObj_to ty_obj in
             [ b (print_access_oid_uniq_name (TyObjN_ass_switch ty_objfrom) isub_name (case TyObjN_role_name ty_objto of Some s \<Rightarrow> s))
             , b (print_access_choose_name (TyObj_ass_arity ty_obj) (TyObjN_ass_switch ty_objfrom) (TyObjN_ass_switch ty_objto))
             , Expr_oid var_oid_uniq (oidGetInh oid) ])))
      , \<lambda> base. 
           let cpt = case case base of ShallB_str s \<Rightarrow> map_username s
                                     | ShallB_self cpt1 \<Rightarrow> map_self cpt1 of Some cpt \<Rightarrow> cpt in
           Expr_oid var_oid_uniq (oidGetInh cpt))))"

definition "print_examp_instance_name = id"
definition "print_examp_instance = (\<lambda> OclInstance l \<Rightarrow> \<lambda> ocl.
  (\<lambda>((l_res, oid_start), instance_rbt).
    ((List_map Thy_definition_hol o flatten) l_res, ocl \<lparr> D_oid_start := oid_start, D_instance_rbt := instance_rbt \<rparr>))
    (let (rbt, (map_self, map_username)) = init_map_class ocl l in
    ( fold_list
      (\<lambda> (f1, f2) _.
        fold_list (\<lambda> ocli cpt.
          let var_oid = Expr_oid var_oid_uniq (oidGetInh cpt)
            ; isub_name = \<lambda>s. s @@ isub_of_str (Inst_ty ocli) in
          ( Definition (Expr_rewrite (f1 var_oid isub_name ocli) ''='' (f2 ocli isub_name cpt))
          , oidSucInh cpt)) l (D_oid_start ocl))
      (let a = \<lambda>f x. Expr_apply f [x]
         ; b = \<lambda>s. Expr_basic [s] in
       [ bug_ocaml_extraction (let var_inst_ass = ''inst_assoc'' in
         (\<lambda> _ isub_name ocli. Expr_basic (print_examp_instance_name isub_name (Inst_name ocli) # (if D_design_analysis ocl = Gen_only_design then [ var_inst_ass ] else [])),
          print_examp_instance_app_constr2_notmp_norec (rbt, (map_self, map_username)) ocl (b var_inst_ass)))
       , (\<lambda> _ _ ocli. Expr_annot (b (Inst_name ocli)) (Inst_ty ocli),
          \<lambda> ocli isub_name _. Expr_lambda wildcard (Expr_some (Expr_some (let name_pers = print_examp_instance_name isub_name (Inst_name ocli) in
                                                                          if D_design_analysis ocl = Gen_only_design then
                                                                            a name_pers (Expr_oid var_inst_assoc (oidGetInh (D_oid_start ocl)))
                                                                          else
                                                                            b name_pers)))) ])
      (D_oid_start ocl)
    , List.fold (\<lambda>ocli instance_rbt.
        let n = Inst_name ocli in
        (n, ocli, case map_username n of Some oid \<Rightarrow> oidGetInh oid) # instance_rbt) l (D_instance_rbt ocl))))"

definition "print_examp_def_st_mapsto_gen f ocl cpt_start rbt_map =
  List_map (\<lambda>(cpt, ocore).
    let a = \<lambda>f x. Expr_apply f [x]
      ; b = \<lambda>s. Expr_basic [s]
      ; (ocli, exp) = case ocore of
        OclDefCoreBinding (name, ocli) \<Rightarrow> (ocli, let name = print_examp_instance_name (\<lambda>s. s @@ isub_of_str (Inst_ty ocli)) name in
                                                 if D_design_analysis ocl = Gen_only_design then
                                                   a name cpt_start
                                                 else
                                                   b name)
      | OclDefCoreAdd ocli \<Rightarrow> (ocli, print_examp_instance_app_constr2_notmp_norec rbt_map ocl cpt_start ocli (\<lambda>s. s @@ isub_of_str (Inst_ty ocli)) cpt) in
    f ocore cpt ocli exp)"

definition "print_examp_def_st_mapsto =
  print_examp_def_st_mapsto_gen
    (\<lambda>_ cpt ocli exp.
      Expr_binop (Expr_oid var_oid_uniq (oidGetInh cpt)) unicode_mapsto (Expr_apply (datatype_in @@ isub_of_str (Inst_ty ocli)) [exp]))"

definition "print_examp_def_st_defassoc_name name = Expr_basic [flatten [var_inst_assoc, name]]"
definition "print_examp_def_st_defassoc = (\<lambda> OclDefSt name l \<Rightarrow> \<lambda>ocl.
 let ocl_old = ocl \<lparr> D_oid_start := oidReinitInh (D_oid_start ocl) \<rparr>
   ; l_ocli = List_map (\<lambda> OclDefCoreAdd ocli \<Rightarrow> Some ocli
                                       | OclDefCoreBinding name \<Rightarrow>
                                           (case List_assoc name (D_instance_rbt ocl_old) of Some (ocli, _) \<Rightarrow> Some ocli)
                                       | _ \<Rightarrow> None) l in
 (\<lambda>l. (print_examp_instance_oid l_ocli ocl_old @@ List_map Thy_definition_hol l, ocl))
  (print_examp_instance_defassoc_gen
    (print_examp_def_st_defassoc_name name)
    l_ocli
    ocl_old))"

definition "print_examp_def_st = (\<lambda> OclDefSt name l \<Rightarrow> \<lambda>ocl.
 let ocl_old = ocl \<lparr> D_oid_start := oidReinitInh (D_oid_start ocl) \<rparr>
   ; l_ocli = List_map (\<lambda> OclDefCoreAdd ocli \<Rightarrow> Some ocli
                                       | OclDefCoreBinding name \<Rightarrow>
                                           (case List_assoc name (D_instance_rbt ocl_old) of Some (ocli, _) \<Rightarrow> Some ocli)
                                       | _ \<Rightarrow> None) l in
 (\<lambda>(l, l_st). (List_map Thy_definition_hol l, ocl \<lparr> D_state_rbt := (name, l_st) # D_state_rbt ocl \<rparr>))
  (let ocl = ocl_old
     ; b = \<lambda>s. Expr_basic [s]
     ; (rbt, (map_self, map_username)) =
         init_map_class ocl (List_map (\<lambda> Some ocli \<Rightarrow> ocli | None \<Rightarrow> \<lparr> Inst_name = [], Inst_ty = [], Inst_attr = OclAttrNoCast [] \<rparr>) l_ocli)
     ; (l_st, cpt, l_assoc) = fold_list (\<lambda> ocore (cpt, l_assoc).
         let f = \<lambda>ocore ocli. ([( cpt, ocore )], Some ocli)
           ; (def, o_ocli) = case ocore of OclDefCoreSkip \<Rightarrow> ([], None)
                       | OclDefCoreBinding name \<Rightarrow>
                           case List_assoc name (D_instance_rbt ocl) of Some (ocli, cpt_registered) \<Rightarrow>
                           if oidGetInh cpt = cpt_registered then
                             f (OclDefCoreBinding (name, ocli)) ocli
                           else
                             ([], None) (* TODO
                                   check that all oid appearing in this expression-alias
                                   all appear in this defining state *)
                       | OclDefCoreAdd ocli \<Rightarrow> f (OclDefCoreAdd ocli) ocli in
         (def, oidSucInh cpt, case o_ocli of None \<Rightarrow> l_assoc | Some ocli \<Rightarrow> (ocli, cpt) # l_assoc)) l (D_oid_start ocl, [])
     ; l_st = flatten l_st
     ; expr_app = print_examp_def_st_mapsto ocl (print_examp_def_st_defassoc_name name) (rbt, (map_self, map_username)) l_st in

   ( [ let s_empty = ''Map.empty'' in
       Definition (Expr_rewrite (b name) ''='' (Expr_apply ''state.make''
        ( Expr_apply s_empty expr_app
        # [ if D_design_analysis ocl = Gen_only_design then
              b s_empty
            else
              print_examp_def_st_assoc rbt map_self map_username l_assoc ]))) ]
   , l_st)))"

definition "print_examp_def_st_inst_var_name ocli name = flatten [Inst_name ocli, name]"
definition "print_examp_def_st_inst_var = (\<lambda> OclDefSt name l \<Rightarrow> \<lambda> ocl.
 let ocl_old = ocl \<lparr> D_oid_start := oidReinitInh (D_oid_start ocl) \<rparr>
   ; l_ocli = List_map (\<lambda> OclDefCoreBinding name \<Rightarrow>
                            (case List_assoc name (D_instance_rbt ocl_old) of Some (ocli, _) \<Rightarrow> Some ocli)
                        | _ \<Rightarrow> None) l in
  (\<lambda>l_res. ((List_map Thy_definition_hol o flatten) l_res, ocl))
    (let ocl = ocl_old in
     case D_design_analysis ocl of Gen_only_analysis \<Rightarrow> [] | Gen_default \<Rightarrow> [] | Gen_only_design \<Rightarrow>
     fst (fold_list
      (\<lambda> (f1, f2) _.
        let (l, accu) =
        fold_list (\<lambda> ocli cpt.
          ( case ocli of None \<Rightarrow> [] | Some ocli \<Rightarrow> bug_ocaml_extraction (let var_oid = Expr_oid var_oid_uniq (oidGetInh cpt)
            ; isub_name = \<lambda>s. s @@ isub_of_str (Inst_ty ocli) in
            [Definition (Expr_rewrite (f1 var_oid isub_name ocli) ''='' (f2 ocli isub_name cpt))])
          , oidSucInh cpt)) l_ocli (D_oid_start ocl) in
          (flatten l, accu))
      (let a = \<lambda>f x. Expr_apply f [x]
         ; b = \<lambda>s. Expr_basic [s] in
       [ (\<lambda> _ _ ocli. Expr_annot (b (flatten [Inst_name ocli, name])) (Inst_ty ocli),
          \<lambda> ocli isub_name _. Expr_lambda wildcard (Expr_some (Expr_some (a (print_examp_instance_name isub_name (Inst_name ocli))
                                                                            (print_examp_def_st_defassoc_name name))))) ])
      (D_oid_start ocl))))"

definition "print_examp_def_st_dom_name name = flatten [''dom_'', name]"
definition "print_examp_def_st_dom = (\<lambda> _ ocl.
 (\<lambda> l. (List_map Thy_lemma_by l, ocl))
  (let (name, l_st) = hd (D_state_rbt ocl)
     ; a = \<lambda>f x. Expr_apply f [x]
     ; b = \<lambda>s. Expr_basic [s]
     ; d = hol_definition in
   [ Lemma_by
       (print_examp_def_st_dom_name name)
       [Expr_rewrite (a ''dom'' (a ''heap'' (b name))) ''='' (Expr_set (List_map (\<lambda>(cpt, _). Expr_oid var_oid_uniq (oidGetInh cpt)) l_st))]
       []
       (Tacl_by [Tac_auto_simp_add [d name]])]))"

definition "print_examp_def_st_dom_lemmas = (\<lambda> _ ocl.
 (\<lambda> l. (List_map Thy_lemmas_simp l, ocl))
  (let (name, _) = hd (D_state_rbt ocl) in
   [ Lemmas_simp ''''
       [Thm_str (print_examp_def_st_dom_name name)] ]))"

definition "print_examp_def_st_perm_name name = flatten [''perm_'', name]"
definition "print_examp_def_st_perm = (\<lambda> _ ocl.
 (\<lambda> l. (List_map Thy_lemma_by l, ocl))
  (let (name, l_st) = hd (D_state_rbt ocl)
     ; expr_app = let ocl = ocl \<lparr> D_oid_start := oidReinitInh (D_oid_start ocl) \<rparr> in
                  print_examp_def_st_mapsto
                    ocl
                    (print_examp_def_st_defassoc_name name)
                    (init_map_class ocl (List_map (\<lambda> (_, OclDefCoreAdd ocli) \<Rightarrow> ocli
                                                   | (_, OclDefCoreBinding (_, ocli)) \<Rightarrow> ocli
                                                   | _ \<Rightarrow> \<lparr> Inst_name = [], Inst_ty = [], Inst_attr = OclAttrNoCast [] \<rparr>) l_st))
                    (rev l_st)
     ; a = bug_scala_extraction (\<lambda>f x. Expr_apply f [x])
     ; b = \<lambda>s. Expr_basic [s]
     ; d = hol_definition
     ; (l_app, l_last) =
         case l_st of [] \<Rightarrow> ([], Tacl_by [Tac_simp_add [d name]])
         | [_] \<Rightarrow> ([], Tacl_by [Tac_simp_add [d name]])
         | _ \<Rightarrow>
           ( [ Tac_simp_add (List_map d (name # List_map (\<lambda>(cpt, _). var_oid_uniq @@ natural_of_str (case oidGetInh cpt of Oid i \<Rightarrow> i)) l_st))]
             # flatten (List_map (\<lambda>i_max. List_map (\<lambda>i. [Tac_subst_l (List_map nat_of_str [i_max - i]) (Thm_str ''fun_upd_twist''), Tac_simp]) (List.upt 0 i_max)) (List.upt 1 (List.length l_st)))
           , Tacl_by [Tac_simp]) in
   [ Lemma_by
       (print_examp_def_st_perm_name name)
       [Expr_rewrite (b name) ''='' (Expr_apply ''state.make''
          (let s_empty = ''Map.empty'' in
           Expr_apply s_empty expr_app # [Expr_apply var_assocs [b name]]))]
       l_app
       l_last ]))"

definition "extract_state ocl name_st l_st =
 (let b = \<lambda>s. Expr_basic [s]
    ; ocl = ocl \<lparr> D_oid_start := oidReinitInh (D_oid_start ocl) \<rparr> in
                  print_examp_def_st_mapsto_gen
                    (\<lambda>ocore cpt ocli exp.
                      ( ocore
                      , oidGetInh cpt
                      , ocli
                      , case ocore of
                          OclDefCoreBinding (name, ocli) \<Rightarrow>
                            b (if D_design_analysis ocl = Gen_only_design then
                                 print_examp_def_st_inst_var_name ocli name_st
                               else
                                 name)
                        | _ \<Rightarrow> Expr_lambda wildcard (Expr_some (Expr_some exp))))
                    ocl
                    (print_examp_def_st_defassoc_name name_st)
                    (init_map_class ocl (List_map (\<lambda> (_, OclDefCoreAdd ocli) \<Rightarrow> ocli
                                                   | (_, OclDefCoreBinding (_, ocli)) \<Rightarrow> ocli
                                                   | _ \<Rightarrow> \<lparr> Inst_name = [], Inst_ty = [], Inst_attr = OclAttrNoCast [] \<rparr>) l_st))
                    l_st)"

definition "print_examp_def_st_allinst = (\<lambda> _ ocl.
 (\<lambda> l. (List_map Thy_lemma_by l, ocl))
  (let (name_st, l_st) = hd (D_state_rbt ocl)
     ; b = \<lambda>s. Expr_basic [s]
     ; expr_app = extract_state ocl name_st l_st
     ; a = \<lambda>f x. Expr_apply f [x]
     ; d = hol_definition
     ; l_st_oid = List_map (\<lambda>(cpt, _). var_oid_uniq @@ natural_of_str (case oidGetInh cpt of Oid i \<Rightarrow> i)) l_st in
   map_class_gen_h'_inh (\<lambda> isub_name name compare.
     let expr_app = List_map (\<lambda>(ocore, cpt, ocli, exp).
              ( ocore
              , let exp_annot = [(Expr_postunary (case ocore of OclDefCoreBinding _ \<Rightarrow> exp | _ \<Rightarrow> Expr_annot exp (Inst_ty ocli)) (b (dot_astype name)), True, ocore, cpt)] in
                case compare (Inst_ty ocli) of
                  EQ \<Rightarrow> [(exp, False, ocore, cpt)]
                | LT \<Rightarrow> exp_annot
                | GT \<Rightarrow> (case Inst_attr ocli of OclAttrCast name2 _ _ \<Rightarrow>
                           if name = name2 then exp_annot
                           else [] | _ \<Rightarrow> [])
                | UN' \<Rightarrow> [])) expr_app
       ; (l_spec, l_body) = List_split (flatten (List_map snd expr_app)) in
     gen_pre_post
       (\<lambda>s. flatten [ name_st, ''_'', s, ''_exec_'', name ])
       (\<lambda>f_expr f_mk _. Expr_binop
            (f_mk (b name_st))
            unicode_Turnstile
            (Expr_binop (f_expr [b name]) unicode_doteq (Expr_oclset l_spec)))
       (\<lambda>lem_tit lem_spec var_pre_post var_mk _. Lemma_by_assum
         lem_tit
         [('''', True, Expr_And ''a'' (\<lambda>var_a. Expr_rewrite (a var_pre_post (a var_mk (b var_a))) ''='' (b var_a)))]
         lem_spec
         (List_map App
           (flatten
            [ [[Tac_subst (Thm_str (print_examp_def_st_perm_name name_st))]]
            , [[Tac_simp_only
                 (List_map
                   (Thm_str o d)
                   (flatten
                      [ [''state.make'']
                      , l_st_oid
                      , flatten (List_map (\<lambda>(_, ocore, _).
                          case ocore of
                            OclDefCoreBinding (n, ocli) \<Rightarrow>
                              [if D_design_analysis ocl = Gen_only_design then
                                 print_examp_def_st_inst_var_name ocli name_st
                               else
                                 n]
                          | _ \<Rightarrow> []) l_body)
                      , flatten (List_map (\<lambda>(cast, ocore, _).
                          if cast then
                            case
                              case ocore of OclDefCoreBinding (_, ocli) \<Rightarrow> Some ocli | OclDefCoreAdd _ \<Rightarrow> None
                            of Some ocli \<Rightarrow> [print_examp_instance_name (\<lambda>s. s @@ isub_of_str (Inst_ty ocli)) (Inst_name ocli)]
                             | None \<Rightarrow> []
                          else []) l_body) ]))]]
            , fst (fold_list (\<lambda> expr l_spec.
                let mk_StrictRefEq_including = \<lambda>l.
                      Tac_rule (Thm_str (flatten [''const_StrictRefEq'', isub_of_str ''Set'', ''_including'']))
                      # Tac_simp # Tac_simp # Tac_simp # l
                  ; (state_update_vs_allInstances_generic, l_spec, l_print_examp, l_OclIncluding_cong) =
                  case expr of (ocore, []) \<Rightarrow>
                    ( ''state_update_vs_allInstances_generic_ntc''
                    , l_spec
                    , case ocore of OclDefCoreBinding (_, ocli) \<Rightarrow> [print_examp_instance_name (\<lambda>s. s @@ isub_of_str (Inst_ty ocli)) (Inst_name ocli)] | _ \<Rightarrow> []
                    , if l_spec = [] then
                        [Tac_rule (Thm_str (flatten [''const_StrictRefEq'', isub_of_str ''Set'', ''_empty''])), Tac_simp]
                      else
                        mk_StrictRefEq_including [])
                  | _ \<Rightarrow>
                    ( ''state_update_vs_allInstances_generic_tc''
                    , tl l_spec
                    , []
                    , mk_StrictRefEq_including [ Tac_rule (Thm_str ''OclIncluding_cong''), Tac_simp, Tac_simp ]) in
                ( Tac_subst (Thm_str state_update_vs_allInstances_generic)
                  # Tac_simp # Tac_simp
                  # Tac_simp_add (List_map d ((flatten [isub_name const_oclastype, ''_'', unicode_AA]) # l_print_examp))
                  # Tac_simp
                  # l_OclIncluding_cong
                , l_spec) ) expr_app l_spec)
            , [[Tac_rule (Thm_str ''state_update_vs_allInstances_generic_empty'')]] ]))
         (Tacl_by [ if l_spec = [] then Tac_simp
                    else Tac_plus [Tac_simp_add [d (flatten [isub_name const_oclastype, ''_'', unicode_AA])]]]) )
       [Tac_simp])
     (case D_class_spec ocl of Some class_spec \<Rightarrow> class_spec)))"

definition "print_examp_def_st_defs = (\<lambda> _ \<Rightarrow> start_map Thy_lemmas_simp
  [ Lemmas_simps '''' [ ''state.defs'', ''const_ss'' ] ])"

definition "merge_unique_gen f l = List.fold (List.fold (\<lambda>x. case f x of Some (x, v) \<Rightarrow> insert x v | None \<Rightarrow> id)) l empty"
definition "merge_unique f l = entries (merge_unique_gen f l)"

definition "print_pre_post_wff = (\<lambda> OclDefPP s_pre s_post \<Rightarrow> \<lambda> ocl.
 (\<lambda> l. (List_map Thy_lemma_by l, ocl))
  (let a = \<lambda>f x. Expr_apply f [x]
     ; b = \<lambda>s. Expr_basic [s]
     ; d = hol_definition
     ; l_st = D_state_rbt ocl in
   case (List_assoc s_pre l_st, List_assoc s_post l_st) of (Some l_pre, Some l_post) \<Rightarrow>
   [ Lemma_by
      (flatten [''basic_'', s_pre, ''_'', s_post, ''_wff''])
      [a ''WFF'' (Expr_pair (b s_pre) (b s_post))]
      []
      (Tacl_by [Tac_simp_add (List_map d (flatten
        [ [ ''WFF'', s_pre, s_post, const_oid_of unicode_AA ]
        , List_map
            (\<lambda>(cpt, _). var_oid_uniq @@ natural_of_str (case cpt of Oid i \<Rightarrow> i))
            (merge_unique ((\<lambda>x. Some (x, ())) o oidGetInh o fst) [l_pre, l_post])
        , List_map fst (merge_unique (\<lambda>(_, ocore). case ocore of OclDefCoreBinding (_, ocli) \<Rightarrow> Some (print_examp_instance_name (\<lambda>s. s @@ isub_of_str (Inst_ty ocli)) (Inst_name ocli), ()) | _ \<Rightarrow> None) [l_pre, l_post])
        , List_map
            (\<lambda>(s_ty, _). const_oid_of (datatype_name @@ isub_of_str s_ty))
            (merge_unique (\<lambda>(_, ocore). case ocore of OclDefCoreBinding (_, ocli) \<Rightarrow> Some (Inst_ty ocli, ()) | _ \<Rightarrow> None) [l_pre, l_post]) ]))]) ] ))"

definition "print_pre_post_where = (\<lambda> OclDefPP s_pre s_post \<Rightarrow> \<lambda> ocl.
 (\<lambda> l. ((List_map Thy_lemma_by o flatten) l, ocl))
  (let a = \<lambda>f x. Expr_apply f [x]
     ; b = \<lambda>s. Expr_basic [s]
     ; d = hol_definition
     ; l_st = D_state_rbt ocl in
   case (List_assoc s_pre l_st, List_assoc s_post l_st) of (Some l_pre, Some l_post) \<Rightarrow>
   let f_name = \<lambda>(cpt, ocore). Some (oidGetInh cpt, ocore)
     ; rbt_pre = merge_unique_gen f_name [l_pre]
     ; rbt_post = merge_unique_gen f_name [l_post]
     ; filter_ocore = \<lambda>x_pers_oid. case (lookup rbt_pre x_pers_oid, lookup rbt_post x_pers_oid) of
             (Some ocore1, Some ocore2) \<Rightarrow> (''OclIsMaintained'', case (ocore1, ocore2) of (OclDefCoreBinding _, OclDefCoreBinding _) \<Rightarrow> [(ocore1, s_pre), (ocore2, s_post)] | (OclDefCoreBinding _, _) \<Rightarrow> [(ocore1, s_pre)] | _ \<Rightarrow> [(ocore2, s_post)])
           | (Some ocore, None) \<Rightarrow> (''OclIsDeleted'', [(ocore, s_pre)])
           | (None, Some ocore) \<Rightarrow> (''OclIsNew'', [(ocore, s_post)])
     ; rbt = union rbt_pre rbt_post
     ; l_oid_of = keys (fold (\<lambda>_. \<lambda> OclDefCoreBinding (_, ocli) \<Rightarrow> insert (const_oid_of (datatype_name @@ isub_of_str (Inst_ty ocli))) ()
                            | OclDefCoreAdd ocli \<Rightarrow> insert (const_oid_of (datatype_name @@ isub_of_str (Inst_ty ocli))) ()
                            | _ \<Rightarrow> id) rbt empty) in
   List_map
     (\<lambda>x_pers_oid.
       let (x_where, l_ocore) = filter_ocore x_pers_oid in
       List_map (\<lambda>(ocore, name_st).
         let (x_where, x_name, x_pers_expr) =
           ( x_where
           , case ocore of OclDefCoreBinding (name, ocli) \<Rightarrow>
               let name =
                 if D_design_analysis ocl = Gen_only_design then
                   print_examp_def_st_inst_var_name ocli name_st
                 else
                   name in
               (Some (name, print_examp_instance_name (\<lambda>s. s @@ isub_of_str (Inst_ty ocli)) (Inst_name ocli)), b name)) in
         Lemma_by (flatten [var_oid_uniq, natural_of_str (case x_pers_oid of Oid i \<Rightarrow> i), s_pre, s_post, ''_'', name_st, ''_'', x_where])
          [Expr_binop (Expr_pair (b s_pre) (b s_post)) unicode_Turnstile (a x_where (x_pers_expr))]
          []
          (Tacl_by [Tac_simp_add (List_map d (flatten
            [ case x_name of Some (x_pers, x_name) \<Rightarrow> [x_pers, x_name] | _ \<Rightarrow> []
            , [ x_where, ''OclValid'', s_pre, s_post, const_oid_of ''option'' ]
            , List_map
                (\<lambda>(cpt, _). var_oid_uniq @@ natural_of_str (case cpt of Oid i \<Rightarrow> i))
                (merge_unique ((\<lambda>x. Some (x, ())) o oidGetInh o fst) [l_pre, l_post])
            , l_oid_of ]))])) l_ocore)
     (filter (\<lambda>x_pers_oid. list_ex (\<lambda> (OclDefCoreBinding _, _) \<Rightarrow> True | _ \<Rightarrow> False)
       (snd (filter_ocore x_pers_oid)))
       (keys rbt)) ))"

end
