(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_class_diagram_static.thy ---
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

theory OCL_class_diagram_static
imports OCL_compiler_aux
        OCL_compiler_ast
        "~~/src/HOL/Library/Code_Char"
begin

section{* ... *}

definition "nat_raw_of_str = List_map (\<lambda>i. char_of_nat (nat_of_char (Char Nibble3 Nibble0) + i))"
fun nat_of_str_aux where
   "nat_of_str_aux l (n :: Nat.nat) = (if n < 10 then n # l else nat_of_str_aux (n mod 10 # l) (n div 10))"
definition "nat_of_str n = nat_raw_of_str (nat_of_str_aux [] n)"
definition "natural_of_str = nat_of_str o nat_of_natural"

section{* Multiplicity typechecking *}
subsection{* ... *}

definition "choose_0 = fst"
definition "choose_1 = snd"

definition "deref_assocs_list to_from oid S =
  flatten (List_map (choose_1 o to_from) (filter (\<lambda>p. List.member (choose_0 (to_from p)) oid) S))"

datatype reporting = Warning
                   | Error
                   | Writeln

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
                                             , let l = List_map assoc l in
                                               if l = [] then '''' else '' '' @@ String_concatWith '' , '' l @@ '' ''
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

definition "check f_writeln f_warning f_error f_raise l_oid l = 
 (let l_out =
        fold
          (\<lambda>_ l.
            case l of ((name_from, name_to), ((OclMult l_mult_from, OclMult l_mult_to), _)) # _ \<Rightarrow>
            let l = List_map (\<lambda> (a, b) \<Rightarrow> [a, b]) (flatten (List_map (snd o snd) l)) in
            List.fold
              (\<lambda> (x, _) acc.
                let s = (*01*) \<lambda> [x0, x1] \<Rightarrow> (x0, x1)
                  ; s' = (*01*) \<lambda> [x0, x1] \<Rightarrow> (x0, x1)
                  ; s'' = (*01*) \<lambda> [x0, x1] \<Rightarrow> (x0, x1)
                  ; l1 = check_single ((snd o s'') [name_from, name_to], x, l_oid) ((snd o s') [l_mult_from, l_mult_to]) (deref_assocs_list s x l)
                  ; s = (*10*) \<lambda> [x0, x1] \<Rightarrow> (x1, x0)
                  ; s' = (*10*) \<lambda> [x0, x1] \<Rightarrow> (x1, x0)
                  ; s'' = (*10*) \<lambda> [x0, x1] \<Rightarrow> (x1, x0)
                  ; l2 = check_single ((snd o s'') [name_from, name_to], x, l_oid) ((snd o s') [l_mult_from, l_mult_to]) (deref_assocs_list s x l) in
                flatten [acc, l1, l2])
              l_oid)
          (List.fold
            (\<lambda> ((oid, name_attr), l_o) \<Rightarrow>
              modify_def [] oid (\<lambda>l. (name_attr, l_o) # l))
            l
            empty)
          []
    ; l_err =
        List.fold
          (\<lambda> (Writeln, s) \<Rightarrow> \<lambda>acc. case f_writeln s of () \<Rightarrow> acc
           | (Warning, s) \<Rightarrow> \<lambda>acc. case f_warning s of () \<Rightarrow> acc
           | (Error, s) \<Rightarrow> \<lambda>acc. case f_error s of () \<Rightarrow> s # acc)
          l_out
          [] in
  if l_err = [] then
    ()
  else
    f_raise (nat_of_str (length l_err) @@ '' error(s) in multiplicity constraints''))"

subsection{* ... *}

definition "check_export_code (* polymorphism weakening needed by code_reflect *)
        f_writeln f_warning f_error f_raise (l_oid :: (string \<times> _) list) (l :: ((nat \<times> _) \<times> _) list) = 
  check f_writeln f_warning f_error f_raise l_oid l"

code_reflect Ty functions check_export_code map_pair

ML{*
structure Ty' = struct
fun check l_oid l =
  let val Mp = Ty.map_pair 
      val Me = String.explode
      val Mi = String.implode
      val Mo = Option.map
      val Ml = map in
  Ty.check_export_code
    (writeln o Mi)
    (warning o Mi)
    (writeln o Markup.markup Markup.bad o Mi)
    (error o Mi)
    (Ml (Mp Me Me)
      l_oid)
    (Ml (Mp (Mp I (Mp (Mo Me) (Mo Me))) (Mp I (Ml (Mp (Ml Me) (Ml Me)))))
      l)
  end
end
*}

end
