(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_class_diagram_generator.ml ---
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

open Employee_DesignModel_UMLPart_generator.M
open Printf

module To =
struct
  module M = struct
    let to_n = function
      Nibble0 -> 0x0 | Nibble1 -> 0x1 | Nibble2 -> 0x2 | Nibble3 -> 0x3 | Nibble4 -> 0x4 | Nibble5 -> 0x5 |
       Nibble6 -> 0x6 | Nibble7 -> 0x7 | Nibble8 -> 0x8 | Nibble9 -> 0x9 | NibbleA -> 0xA | NibbleB -> 0xB | NibbleC -> 0xC | NibbleD -> 0xD
      | NibbleE -> 0xE | NibbleF -> 0xF

    let to_c = function Char (n1, n2) -> char_of_int (to_n n1 lsl 4 + to_n n2)

    let to_s l = (String.concat "" (List.map (fun c -> String.make 1 (to_c c)) l))

    let to_num =
      let rec aux mot n = function
        | Bit0 p -> aux mot (succ n) p
        | bit ->
          let mot = mot + (1 lsl n) in
          match bit with
          | Bit1 p -> aux mot (succ n) p
          | _ -> mot in
      aux 0 0

    let to_i = function
      | Zero_int -> 0
      | Pos n -> to_num n
      | Neg n -> - (to_num n)
  end
  let s = M.to_s
  let i = M.to_i
end

module Unicode = struct
  let mk_u = sprintf "\\<%s>"
  let u_Rightarrow = mk_u "Rightarrow"
  let u_alpha = mk_u "alpha"
  let u_lambda = mk_u "lambda"
  let u_lfloor = mk_u "lfloor"
  let u_rfloor = mk_u "rfloor"
  let u_Longrightarrow = mk_u "Longrightarrow"
end

let concat f l =
  String.concat "\n" (List.rev (List.fold_left (fun acc x -> f x :: acc) [] l))


let s_of_datatype = function Datatype (n, l) ->
    sprintf "datatype %s = %s"
      (To.s n)
      (String.concat "\n                        | "
         (List.map
            (fun (n, l) ->
              sprintf "%s %s"
                (To.s n)
                (String.concat " "
                   (List.map
                      (function
                      | Opt o -> sprintf "\"%s option\"" (To.s o)
                      | Raw o -> sprintf  "%s" (To.s o))
                      l)))
            l))

let rec s_of_rawty = function
  | Ty_base s -> To.s s
  | Ty_apply (name, l) -> sprintf "%s %s" (let s = (String.concat ", " (List.map s_of_rawty l)) in
                                           match l with
                                           | [_] -> s
                                           | _ -> sprintf "(%s)" s) (s_of_rawty name)

let s_of_tsynonym = function Type_synonym (n, l) ->
    sprintf "type_synonym %s = \"%s\"" (To.s n) (s_of_rawty l)

let rec s_of_expr = function
  | Expr_case (e, l) -> sprintf "(case %s of %s)" (s_of_expr e) (String.concat "\n    | " (List.map (fun (s1, s2) -> sprintf "%s %s %s" (s_of_expr s1) Unicode.u_Rightarrow (s_of_expr s2)) l))
  | Expr_rewrite (e1, symb, e2) -> sprintf "%s %s %s" (s_of_expr e1) (To.s symb) (s_of_expr e2)
  | Expr_basic l -> sprintf "%s" (String.concat " " (List.map To.s l))
  | Expr_binop (e1, s, e2) -> sprintf "%s %s %s" (s_of_expr e1) (s_of_expr (Expr_basic [s])) (s_of_expr e2)
  | Expr_annot (e, s) -> sprintf "(%s::%s)" (s_of_expr e) (To.s s)
  | Expr_lambda (s, e) -> sprintf "(%s%s. %s)" Unicode.u_lambda (To.s s) (s_of_expr e)
  | Expr_lambdas (l, e) -> sprintf "(%s%s. %s)" Unicode.u_lambda (String.concat " " (List.map To.s l)) (s_of_expr e)
  (*| Expr_apply (s, [e]) -> sprintf "(%s %s)" (To.s s) (s_of_expr e)*)
  | Expr_apply (s, l) -> sprintf "(%s %s)" (To.s s) (String.concat " " (List.map (fun e -> sprintf "(%s)" (s_of_expr e)) l))
  | Expr_some e -> sprintf "%s%s%s" Unicode.u_lfloor (s_of_expr e) Unicode.u_rfloor
  | Expr_postunary (e1, e2) -> sprintf "%s %s" (s_of_expr e1) (s_of_expr e2)
  | Expr_warning_parenthesis e -> sprintf "(%s)" (s_of_expr e)
  | Expr_parenthesis e -> sprintf "(%s)" (s_of_expr e)

let s_of_instantiation = function Instantiation (n, n_def, expr) ->
    let name = To.s n in
    sprintf "instantiation %s :: object\nbegin\n  definition %s_%s_def : \"%s\"\n  instance ..\nend"
      name
      (To.s n_def)
      name
      (s_of_expr expr)

let s_of_defs_overloaded = function Defs_overloaded (n, e) ->
    sprintf "defs(overloaded) %s : \"%s\"" (To.s n) (s_of_expr e)

let s_of_consts_class = function Consts (n, ty_out, symb1, symb2) ->
    sprintf "consts %s :: \"'%s %s %s\" (\"(_) %s'(%s')\")" (To.s n) Unicode.u_alpha Unicode.u_Rightarrow (To.s ty_out) (To.s symb1) (To.s symb2)

let s_of_definition_hol = function
  | Definition e -> sprintf "definition \"%s\"" (s_of_expr e)
  | Definition_abbrev (name, (abbrev, prio), e) -> sprintf "definition %s (\"(1%s)\" %d)\n  where \"%s\"" (To.s name) (s_of_expr abbrev) (To.i prio) (s_of_expr e)

let s_of_lemmas_simp = function Lemmas_simp l ->
    sprintf "lemmas [simp] = %s" (String.concat "\n                " (List.map (To.s) l))

let s_of_tactic = function
  | Tac_rule s -> sprintf "rule %s" (To.s s)
  | Tac_simp -> sprintf "simp"
  | Tac_simp_add l -> sprintf "simp add: %s" (String.concat " " (List.map To.s l))
  | Tac_simp_all -> sprintf "simp_all"
  | Tac_simp_all_add s -> sprintf "simp_all add: %s" (To.s s)

let s_of_lemma_by = function Lemma_by (n, l_spec, l_apply) ->
    sprintf "lemma %s : \"%s\"\nby(%s)"
      (To.s n)
      (String.concat (sprintf " %s " Unicode.u_Longrightarrow) (List.map s_of_expr l_spec))
      (String.concat ", " (List.map s_of_tactic l_apply))

