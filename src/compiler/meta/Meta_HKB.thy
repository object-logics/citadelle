(******************************************************************************
 * A Meta-Model for the Haskabelle API
 *
 * Copyright (c) 2007-2015 Technische Universität München, Germany
 *               2017-2018 Virginia Tech, USA
 *               2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
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

section\<open>Isabelle Meta-Model aka. AST definition of Isabelle\<close>

theory Meta_HKB
imports "../../compiler_generic/Init"
begin

section \<open>Miscellaneous\<close>

datatype gen_meta = Gen_apply_hol string (* HOL term to apply *)
                  | Gen_apply_sml string (* SML term to apply *)
                  | Gen_apply_sml_cmd string (* SML term to apply *)
                                      string (* SML term given to meta_command *)
                  | Gen_no_apply

section \<open>Isa.hs\<close>

(* Author: Tobias C. Rittweiler, TU Muenchen

Abstract representation of Isar/HOL theory.
*)

datatype ThyName = ThyName string
 
datatype Name = QName ThyName string
              | Name string
 
type_synonym Sort = "Name list"
 
datatype Type = Type Name "Type list"
              | Func Type Type
              | TVar Name
              | NoType
 
datatype Literal = Int nat (*FIXME 'int' to be supported instead of 'nat'*)
                 (*(*To be supported*)| Char char*)
                 | String string
 
datatype Term = Literal Literal
              | Const Name
              | Abs Name Term
              | App Term Term
              | If Term Term Term
              | Let "(Term * Term) list" Term
              | Case Term "(Term * Term) list"
              | ListCompr Term "ListComprFragment list"
              | RecConstr Name "(Name * Term) list"
              | RecUpdate Term "(Name * Term) list"
              | DoBlock string "DoBlockFragment list" string
              | Parenthesized Term
and      ListComprFragment = Generator "Term * Term"
                           | Guard Term
and      DoBlockFragment = DoGenerator Term Term
                         | DoQualifier Term
                         | DoLetStmt "(Term * Term) list"
 
type_synonym Pat = Term
 
datatype TypeSpec = TypeSpec "Name list" Name
 
datatype TypeSign = TypeSign Name "(Name * Sort) list" Type
 
datatype Function_Kind = Definition
                       | Primrec
                       | Fun
                       | Function_Sorry
 
datatype Function_Stmt = Function_Stmt Function_Kind "TypeSign list" "((Name * (Pat list)) * Term) list"
 
datatype Stmt = Datatype "(TypeSpec * ((Name * (Type list)) list)) list"
              | Record TypeSpec "(Name * Type) list"
              | TypeSynonym "(TypeSpec * Type) list"
              | Function Function_Stmt
              | Class Name "Name list" "TypeSign list"
              | Instance Name Name "(Name * Sort) list" "Function_Stmt list"
              | Comment string
              | SML Function_Stmt
 
datatype Module = Module ThyName "ThyName list" "Stmt list" bool

section \<open>Convert.hs\<close>

(* Author: Tobias C. Rittweiler, TU Muenchen

Conversion from abstract Haskell code to abstract Isar/HOL theory.
*)

datatype IsaUnit = IsaUnit "bool \<comment> \<open>\<^term>\<open>True\<close>: generate with \<^theory_text>\<open>old_datatype\<close> instead of \<^theory_text>\<open>datatype\<close>\<close> \<times> nat \<comment> \<open>\<^term>\<open>0\<close>: full datatype, \<^term>\<open>(\<le>) 1\<close>: more atomic\<close>" (* FIXME add a generic meta-command 'generation_syntax_params' to parameterize at any interleaving place the generating mode (i.e. datatype or old_datatype) *)
                           "(string \<comment> \<open>old prefix name to replace\<close> \<times> string option \<comment> \<open>new substitute (or \<^term>\<open>None\<close> to remove the prefix)\<close>) list"
                           gen_meta (* converting function to apply once the parsed value is created *)
                           string (* name of the current theory *) (* FIXME move that 'static value' to the global environment. In principle, each meta-command is evaluated within one "own" theory name, following the hierarchy of children theories... *)
                           "Module list \<times> bool \<comment> \<open>\<^term>\<open>True\<close>: treat as most the list as a single module\<close>"

end
