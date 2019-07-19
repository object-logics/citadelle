(******************************************************************************
 * Citadelle
 *
 * Copyright (c) 2011-2018 Université Paris-Saclay, Univ. Paris-Sud, France
 *               2013-2017 IRT SystemX, France
 *               2011-2015 Achim D. Brucker, Germany
 *               2016-2018 The University of Sheffield, UK
 *               2016-2017 Nanyang Technological University, Singapore
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

section\<open>Initializing the Printer\<close>

theory  Printer_init
imports "../Init"
        "../isabelle_home/src/Tools/Code/Isabelle_code_runtime"
begin

text\<open>At the time of writing, the following target languages supported
     by Isabelle are also supported by the meta-compiler:
     Haskell, OCaml, Scala, SML.\<close>

subsection\<open>Kernel Code for Target Languages\<close>

  (* We put in 'CodeConst' functions using characters
     not allowed in a Isabelle 'code_const' expr
     (e.g. '_', '"', ...) *)

ML \<open>
structure CodeType = struct
  type mlInt = string
  type 'a mlMonad = 'a option
end

structure CodeConst = struct
  structure Monad = struct
    val bind = fn
        NONE => (fn _ => NONE)
      | SOME a => fn f => f a
    val return = SOME
  end

  structure Printf = struct
    local
      fun sprintf s l =
        case String.fields (fn #"%" => true | _ => false) s of
          [] => ""
        | [x] => x
        | x :: xs =>
            let fun aux acc l_pat l_s =
              case l_pat of
                [] => rev acc
              | x :: xs => aux (String.extract (x, 1, NONE) :: hd l_s :: acc) xs (tl l_s) in
            String.concat (x :: aux [] xs l)
      end
    in
      fun sprintf0 s_pat = s_pat
      fun sprintf1 s_pat s1 = sprintf s_pat [s1]
      fun sprintf2 s_pat s1 s2 = sprintf s_pat [s1, s2]
      fun sprintf3 s_pat s1 s2 s3 = sprintf s_pat [s1, s2, s3]
      fun sprintf4 s_pat s1 s2 s3 s4 = sprintf s_pat [s1, s2, s3, s4]
      fun sprintf5 s_pat s1 s2 s3 s4 s5 = sprintf s_pat [s1, s2, s3, s4, s5]
    end
  end

  structure String = struct
    val concat = String.concatWith
  end

  structure Sys = struct
    val isDirectory2 = SOME o File.is_dir o Path.explode handle ERROR _ => K NONE
  end

  structure To = struct
    fun nat f = Int.toString o f
  end

  fun outFile1 f file =
    let
      val pfile = Path.explode file
      val () = if File.exists pfile then error ("File exists \"" ^ file ^ "\"\n") else ()
      val oc = Unsynchronized.ref []
      val _ = f (fn a => fn b => SOME (oc := Printf.sprintf1 a b :: (Unsynchronized.! oc))) in
      SOME (File.write_list pfile (rev (Unsynchronized.! oc))) handle ERROR _ => NONE
    end

  fun outStand1 _ = error "Not available in this version of theory file"
end
\<close>

subsection\<open>Interface with Types\<close>

datatype ml_int = ML_int
code_printing type_constructor ml_int \<rightharpoonup> (Haskell) "CodeType.MlInt" \<comment> \<open>syntax!\<close>
            | type_constructor ml_int \<rightharpoonup> (OCaml) "CodeType.mlInt"
            | type_constructor ml_int \<rightharpoonup> (Scala) "CodeType.mlInt"
            | type_constructor ml_int \<rightharpoonup> (SML) "CodeType.mlInt"

datatype 'a ml_monad = ML_monad 'a
code_printing type_constructor ml_monad \<rightharpoonup> (Haskell) "CodeType.MlMonad _" \<comment> \<open>syntax!\<close>
            | type_constructor ml_monad \<rightharpoonup> (OCaml) "_ CodeType.mlMonad"
            | type_constructor ml_monad \<rightharpoonup> (Scala) "CodeType.mlMonad [_]"
            | type_constructor ml_monad \<rightharpoonup> (SML) "_ CodeType.mlMonad"

(* *)

type_synonym ml_string = String.literal

subsection\<open>Interface with Constants\<close>

text\<open>module CodeConst\<close>

consts out_file1 :: "((ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> unit ml_monad) \<comment> \<open>fprintf\<close> \<Rightarrow> unit ml_monad) \<Rightarrow> ml_string \<Rightarrow> unit ml_monad"
code_printing constant out_file1 \<rightharpoonup> (Haskell) "CodeConst.outFile1"
            | constant out_file1 \<rightharpoonup> (OCaml) "CodeConst.outFile1"
            | constant out_file1 \<rightharpoonup> (Scala) "CodeConst.outFile1"
            | constant out_file1 \<rightharpoonup> (SML) "CodeConst.outFile1"

consts out_stand1 :: "((ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> unit ml_monad) \<comment> \<open>fprintf\<close> \<Rightarrow> unit ml_monad) \<Rightarrow> unit ml_monad"
code_printing constant out_stand1 \<rightharpoonup> (Haskell) "CodeConst.outStand1"
            | constant out_stand1 \<rightharpoonup> (OCaml) "CodeConst.outStand1"
            | constant out_stand1 \<rightharpoonup> (Scala) "CodeConst.outStand1"
            | constant out_stand1 \<rightharpoonup> (SML) "CodeConst.outStand1"

text\<open>module Monad\<close>

consts bind :: "'a ml_monad \<Rightarrow> ('a \<Rightarrow> 'b ml_monad) \<Rightarrow> 'b ml_monad"
code_printing constant bind \<rightharpoonup> (Haskell) "CodeConst.Monad.bind"
            | constant bind \<rightharpoonup> (OCaml) "CodeConst.Monad.bind"
            | constant bind \<rightharpoonup> (Scala) "CodeConst.Monad.bind"
            | constant bind \<rightharpoonup> (SML) "CodeConst.Monad.bind"

consts return :: "'a \<Rightarrow> 'a ml_monad"
code_printing constant return \<rightharpoonup> (Haskell) "CodeConst.Monad.return"
            | constant return \<rightharpoonup> (OCaml) "CodeConst.Monad.return"
            | constant return \<rightharpoonup> (Scala) "CodeConst.Monad.Return" \<comment> \<open>syntax!\<close>
            | constant return \<rightharpoonup> (SML) "CodeConst.Monad.return"

text\<open>module Printf\<close>

consts sprintf0 :: "ml_string \<Rightarrow> ml_string"
code_printing constant sprintf0 \<rightharpoonup> (Haskell) "CodeConst.Printf.sprintf0"
            | constant sprintf0 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf0"
            | constant sprintf0 \<rightharpoonup> (Scala) "CodeConst.Printf.sprintf0"
            | constant sprintf0 \<rightharpoonup> (SML) "CodeConst.Printf.sprintf0"

consts sprintf1 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> ml_string"
code_printing constant sprintf1 \<rightharpoonup> (Haskell) "CodeConst.Printf.sprintf1"
            | constant sprintf1 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf1"
            | constant sprintf1 \<rightharpoonup> (Scala) "CodeConst.Printf.sprintf1"
            | constant sprintf1 \<rightharpoonup> (SML) "CodeConst.Printf.sprintf1"

consts sprintf2 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> ml_string"
code_printing constant sprintf2 \<rightharpoonup> (Haskell) "CodeConst.Printf.sprintf2"
            | constant sprintf2 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf2"
            | constant sprintf2 \<rightharpoonup> (Scala) "CodeConst.Printf.sprintf2"
            | constant sprintf2 \<rightharpoonup> (SML) "CodeConst.Printf.sprintf2"

consts sprintf3 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> '\<alpha>3 \<Rightarrow> ml_string"
code_printing constant sprintf3 \<rightharpoonup> (Haskell) "CodeConst.Printf.sprintf3"
            | constant sprintf3 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf3"
            | constant sprintf3 \<rightharpoonup> (Scala) "CodeConst.Printf.sprintf3"
            | constant sprintf3 \<rightharpoonup> (SML) "CodeConst.Printf.sprintf3"

consts sprintf4 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> '\<alpha>3 \<Rightarrow> '\<alpha>4 \<Rightarrow> ml_string"
code_printing constant sprintf4 \<rightharpoonup> (Haskell) "CodeConst.Printf.sprintf4"
            | constant sprintf4 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf4"
            | constant sprintf4 \<rightharpoonup> (Scala) "CodeConst.Printf.sprintf4"
            | constant sprintf4 \<rightharpoonup> (SML) "CodeConst.Printf.sprintf4"

consts sprintf5 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> '\<alpha>3 \<Rightarrow> '\<alpha>4 \<Rightarrow> '\<alpha>5 \<Rightarrow> ml_string"
code_printing constant sprintf5 \<rightharpoonup> (Haskell) "CodeConst.Printf.sprintf5"
            | constant sprintf5 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf5"
            | constant sprintf5 \<rightharpoonup> (Scala) "CodeConst.Printf.sprintf5"
            | constant sprintf5 \<rightharpoonup> (SML) "CodeConst.Printf.sprintf5"

text\<open>module String\<close>

consts String_concat :: "ml_string \<Rightarrow> ml_string list \<Rightarrow> ml_string"
code_printing constant String_concat \<rightharpoonup> (Haskell) "CodeConst.String.concat"
            | constant String_concat \<rightharpoonup> (OCaml) "CodeConst.String.concat"
            | constant String_concat \<rightharpoonup> (Scala) "CodeConst.String.concat"
            | constant String_concat \<rightharpoonup> (SML) "CodeConst.String.concat"

text\<open>module Sys\<close>

consts Sys_is_directory2 :: "ml_string \<Rightarrow> bool ml_monad"
code_printing constant Sys_is_directory2 \<rightharpoonup> (Haskell) "CodeConst.Sys.isDirectory2"
            | constant Sys_is_directory2 \<rightharpoonup> (OCaml) "CodeConst.Sys.isDirectory2"
            | constant Sys_is_directory2 \<rightharpoonup> (Scala) "CodeConst.Sys.isDirectory2"
            | constant Sys_is_directory2 \<rightharpoonup> (SML) "CodeConst.Sys.isDirectory2"

text\<open>module To\<close>

consts ToNat :: "(nat \<Rightarrow> integer) \<Rightarrow> nat \<Rightarrow> ml_int"
code_printing constant ToNat \<rightharpoonup> (Haskell) "CodeConst.To.nat"
            | constant ToNat \<rightharpoonup> (OCaml) "CodeConst.To.nat"
            | constant ToNat \<rightharpoonup> (Scala) "CodeConst.To.nat"
            | constant ToNat \<rightharpoonup> (SML) "CodeConst.To.nat"

subsection\<open>Some Notations (I): Raw Translations\<close>

syntax "_sprint0" :: "_ \<Rightarrow> ml_string" ("sprint0 (_)\<acute>")
translations "sprint0 x\<acute>" \<rightleftharpoons> "CONST sprintf0 x"

syntax "_sprint1" :: "_ \<Rightarrow> _ \<Rightarrow> ml_string" ("sprint1 (_)\<acute>")
translations "sprint1 x\<acute>" \<rightleftharpoons> "CONST sprintf1 x"

syntax "_sprint2" :: "_ \<Rightarrow> _ \<Rightarrow> ml_string" ("sprint2 (_)\<acute>")
translations "sprint2 x\<acute>" \<rightleftharpoons> "CONST sprintf2 x"

syntax "_sprint3" :: "_ \<Rightarrow> _ \<Rightarrow> ml_string" ("sprint3 (_)\<acute>")
translations "sprint3 x\<acute>" \<rightleftharpoons> "CONST sprintf3 x"

syntax "_sprint4" :: "_ \<Rightarrow> _ \<Rightarrow> ml_string" ("sprint4 (_)\<acute>")
translations "sprint4 x\<acute>" \<rightleftharpoons> "CONST sprintf4 x"

syntax "_sprint5" :: "_ \<Rightarrow> _ \<Rightarrow> ml_string" ("sprint5 (_)\<acute>")
translations "sprint5 x\<acute>" \<rightleftharpoons> "CONST sprintf5 x"

subsection\<open>Some Notations (II): Polymorphic Cartouches\<close>

syntax "_cartouche_string'" :: String.literal
translations "_cartouche_string" \<rightleftharpoons> "_cartouche_string'"

parse_translation \<open>
  [( @{syntax_const "_cartouche_string'"}
   , parse_translation_cartouche
       @{binding cartouche_type'}
       (( "fun\<^sub>p\<^sub>r\<^sub>i\<^sub>n\<^sub>t\<^sub>f"
        , ( Cartouche_Grammar.nil1
          , Cartouche_Grammar.cons1
          , let fun f c x = Syntax.const c $ x in
            fn (0, x) => x
             | (1, x) => f @{const_syntax sprintf1} x
             | (2, x) => f @{const_syntax sprintf2} x
             | (3, x) => f @{const_syntax sprintf3} x
             | (4, x) => f @{const_syntax sprintf4} x
             | (5, x) => f @{const_syntax sprintf5} x
            end))
        :: Cartouche_Grammar.default)
       (fn 37 \<comment> \<open>\<^verbatim>\<open>#"%"\<close>\<close> => (fn x => x + 1)
         | _ => I)
       0)]
\<close>

subsection\<open>Generic Locale for Printing\<close>

locale Print =
  fixes To_string :: "string \<Rightarrow> ml_string"
  fixes To_nat :: "nat \<Rightarrow> ml_int"
begin
  declare[[cartouche_type' = "fun\<^sub>p\<^sub>r\<^sub>i\<^sub>n\<^sub>t\<^sub>f"]]
end

text\<open>As remark, printing functions (like @{term sprintf5}...) are currently
weakly typed in Isabelle, we will continue the typing using the type system of target languages.\<close>

end
