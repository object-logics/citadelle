(******************************************************************************
 * Orca: A Functional Correctness Verifier for Imperative Programs
 *       Based on Isabelle/UTP
 *
 * Copyright (c) 2016-2018 Virginia Tech, USA
 *               2016-2018 Technische Universität München, Germany
 *               2016-2018 University of York, UK
 *               2016-2018 Université Paris-Saclay, Univ. Paris-Sud, France
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

theory C_Model
  imports "$HASKABELLE_HOME_USER/default/Prelude"
          "../src/UML_Main"
          "../src/compiler/Generator_dynamic_parallel"
begin

section \<open>Initialization of the generator\<close>

declare [[syntax_ambiguity_warning = false]]

generation_syntax [ deep
                      (THEORY C_Model_generated)
                      (IMPORTS ["../src/UML_Main", "../src/compiler/Static", "HOL-Library.Old_Datatype"]
                               "../src/compiler/Generator_dynamic_parallel")
                      SECTION
                      [ in self ]
                      (output_directory "../doc")
                  , shallow (*SORRY*) ]

type_synonym int = integer
type_synonym string = String.literal
notation Some ("Just")
notation None ("Nothing")

section \<open>Type definition\<close>

End!

old_datatype 'a option = None | Some 'a
old_datatype ('a, 'b) Either = Left 'a | Right 'b

text \<open> \<^file>\<open>$HASKABELLE_HOME/ex/language-c/src/Language/C/Data/Name.hs\<close>
       \<^file>\<open>$HASKABELLE_HOME/ex/language-c/src/Language/C/Data/Position.hs\<close>
       \<^file>\<open>$HASKABELLE_HOME/ex/language-c/src/Language/C/Data/Node.hs\<close>
       \<^file>\<open>$HASKABELLE_HOME/ex/language-c/src/Language/C/Data/Ident.hs\<close>
       \<^file>\<open>$HASKABELLE_HOME/ex/language-c/src/Language/C/Syntax/Ops.hs\<close>
       \<^file>\<open>$HASKABELLE_HOME/ex/language-c/src/Language/C/Syntax/Constants.hs\<close> \<close>

Haskell_file datatype_old_atomic try_import only_types concat_modules
             base_path "$HASKABELLE_HOME/ex/language-c/src"
             [Prelude, Int, String, Option]
             (**)
             "$HASKABELLE_HOME/ex/language-c/src/Language/C/Syntax/AST.hs"

typ "CTranslUnit"

section \<open>Garbage Collection of Notations\<close>

hide_type (open) int
hide_type (open) string

end
