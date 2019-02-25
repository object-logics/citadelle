(******************************************************************************
 * Language.C
 * https://hackage.haskell.org/package/language-c
 *
 * Copyright (c) 1999-2017 Manuel M T Chakravarty
 *                         Duncan Coutts
 *                         Benedikt Huber
 * Portions Copyright (c) 1989,1990 James A. Roskind
 *
 *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *
 *
 * Language.C.Comments
 * https://hackage.haskell.org/package/language-c-comments
 *
 * Copyright (c) 2010-2014 Geoff Hulette
 *
 *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *
 *
 * Securify & Orca
 *
 * Copyright (c) 2016-2017 Nanyang Technological University, Singapore
 *               2017-2018 Virginia Tech, USA
 *
 *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *
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

theory C_Model_ml
  imports C_Model_core
begin

section \<open>Convert\<close>

definition translation_unit :: "CTranslUnit \<times> Comment list \<times> integer list \<Rightarrow> unit" where
          "translation_unit _ = ()"

section \<open>Run\<close>

definition "main = translation_unit"

declare [[default_code_width = 236]]

code_reserved SML Ident error

meta_command' \<comment>\<open>\<^theory_text>\<open>code_reflect' open C_ast_simple functions main String.to_list S.flatten\<close>\<close> \<open>
let
  open META
  fun meta_command {shallow, deep = _, syntax_print = _} =
    [(META_semi_theories o Theories_one o Theory_code_reflect)
      (Code_reflect
        ( true
        , From.string "C_ast_simple"
        , map From.string [ "main", "String.to_list", "S.flatten" ]
         @ (shallow
            |> hd
            |> fst
            |> d_hsk_constr
            |> map (flattenb (From.string "C_Model_core.") o to_String))))]
in meta_command
end
\<close>

ML\<open>
structure C_ast_simple = struct
  open C_ast_simple
  val Ident = Ident0
end
\<close>

section \<open>Language.C Haskell parsing in ML\<close>

ML\<open>open C_ast_simple\<close>

meta_command'\<open>
let
  open META
  fun b s = SML_basic [s]
  fun meta_command {shallow, deep = _, syntax_print = _} =
    [(META_semi_theories o Theories_one o Theory_ML o SMLa o SML_top)
      (shallow
       |> hd
       |> fst
       |> d_hsk_constr
       |> map_filter
            (fn s =>
              let val s' = s |> to_String |> To_string0 in
              if List.exists (fn s0 => s0 = s') ["Ident", "ClangCVersion", "CString"] then NONE
              else
                  SOME
                    (SML_val_fun
                      ( SOME Sval
                      , SML_rewrite ( b (to_String s)
                                    , From.string "="
                                    , b (case String.explode s' of
                                           c :: s => Char.toLower c :: s |> String.implode |> (fn x => "C_ast_simple." ^ x) |> From.string))))
              end))]
in meta_command
end
\<close>

end
