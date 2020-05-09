(******************************************************************************
 * A Meta-Model for the Language.C Haskell Library
 *
 * Copyright (c) 2016-2017 Nanyang Technological University, Singapore
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

theory C_Model_core
  imports "$HASKABELLE_HOME_USER/default/Prelude"
          OCL.UML_Main
          Citadelle.Generator_dynamic_concurrent
          Citadelle_C_init.C_Model_init
begin

section \<open>Acknowledgements\<close>

text \<open>\<^url>\<open>https://hackage.haskell.org/package/language-c\<close>\<close>
text \<open>\<^url>\<open>https://hackage.haskell.org/package/language-c-comments\<close>\<close>
text \<open>\<^file>\<open>$HASKABELLE_HOME/ex/language-c/AUTHORS.c2hs\<close>\<close>
text \<open>\<^file>\<open>$HASKABELLE_HOME/ex/language-c/AUTHORS\<close>\<close>

section \<open>Initialization of the generator\<close>

declare [[syntax_ambiguity_warning = false]]

generation_syntax [ deep
                      (THEORY Meta_C_generated)
                      (IMPORTS ["FOCL.UML_Main", "FOCL.Static", "Citadelle_C_init.C_Model_init"]
                               "Citadelle.Generator_dynamic_concurrent")
                      SECTION
                      SORRY
                      [ in self ]
                      (output_directory "../doc")
                  , shallow SORRY ]

section \<open>Type definition\<close>

End!

text \<open> \<^file>\<open>$HASKABELLE_HOME/ex/language-c/src/Language/C/Data/Name.hs\<close>
       \<^file>\<open>$HASKABELLE_HOME/ex/language-c/src/Language/C/Data/Position.hs\<close>
       \<^file>\<open>$HASKABELLE_HOME/ex/language-c/src/Language/C/Data/Node.hs\<close>
       \<^file>\<open>$HASKABELLE_HOME/ex/language-c/src/Language/C/Data/Ident.hs\<close>
       \<^file>\<open>$HASKABELLE_HOME/ex/language-c/src/Language/C/Syntax/Ops.hs\<close>
       \<^file>\<open>$HASKABELLE_HOME/ex/language-c/src/Language/C/Syntax/Constants.hs\<close> \<close>

hide_const (open) Name

Haskell_file datatype_old try_import only_types concat_modules
             base_path "$HASKABELLE_HOME/ex/language-c/src"
             [Prelude \<rightharpoonup> C_Model_init, Int, String, Option \<rightharpoonup> C_Model_init]
             (**)
             "$HASKABELLE_HOME/ex/language-c/src/Language/C/Syntax/AST.hs"

text \<open>@{typ CTranslUnit}\<close>

datatype CommentFormat = SingleLine | MultiLine
datatype Comment = Comment Position string CommentFormat

section \<open>Garbage Collection of Notations\<close>

hide_type (open) int
hide_type (open) string

end
