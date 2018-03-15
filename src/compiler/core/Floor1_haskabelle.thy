(******************************************************************************
 * Haskabelle --- Converting Haskell Source Files to Isabelle/HOL Theories.
 *                http://isabelle.in.tum.de/repos/haskabelle
 *
 * Copyright (c) 2007-2015 Technische Universität München, Germany
 *               2017-2018 Virginia Tech, USA
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

section\<open>Main Translation for: Haskabelle\<close>

theory  Floor1_haskabelle
imports Core_init
begin

definition "hsk_name = (\<lambda> l_name.
 \<lambda> Name n \<Rightarrow> n
 | QName (ThyName n0) n1 \<Rightarrow> 
    (case List.find (\<lambda>(n1, _). n0 \<triangleq> n1) l_name of
       None \<Rightarrow> S.flatten [n0, \<open>.\<close>, n1]
     | Some (_, Some n0) \<Rightarrow> S.flatten [n0, \<open>.\<close>, n1]
     | Some (_, None) \<Rightarrow> n1))"

definition "hsk_name' names = mk_quote o hsk_name names"

fun hsk_type where
   "hsk_type names e =
 (\<lambda> Type n [] \<Rightarrow> Typ_base (hsk_name names n)
  | Type n l \<Rightarrow> Typ_apply (Typ_base (hsk_name names n)) (map (hsk_type names) l)
  | Func t1 t2 \<Rightarrow> Typ_apply (hsk_type names t1) [hsk_type names t2]
  | TVar n \<Rightarrow> Typ_base (hsk_name' names n)) e"

definition "hsk_typespec names = (\<lambda> TypeSpec l n \<Rightarrow> (hsk_name names n, L.map (hsk_name' names) l))"

definition "hsk_stmt old_datatype names =
  List.map_filter
   (\<lambda> Meta_HKB.Datatype l \<Rightarrow>
        Some (O.datatype (Datatype old_datatype (L.map (map_prod (hsk_typespec names) (L.map (map_prod (hsk_name names) (L.map (hsk_type names))))) l)))
    | TypeSynonym [(t0, t1)] \<Rightarrow> Some (O.type_synonym (Type_synonym (hsk_typespec names t0) (hsk_type names t1)))
    | Function (Function_Stmt Primrec l1 l2) \<Rightarrow> None)"

definition "print_haskell = (\<lambda> IsaUnit old_datatype l_name name_new (l_mod, b_concat) \<Rightarrow>
  Pair (List.bind (if b_concat then l_mod else [last l_mod])
                  (\<lambda> Module (ThyName name_old) _ m _ \<Rightarrow>
                       hsk_stmt old_datatype ((name_old, Some name_new) # l_name) m)))"

end
