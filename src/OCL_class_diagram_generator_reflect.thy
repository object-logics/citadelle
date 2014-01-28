(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_class_diagram_generator_reflect.thy ---
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2014      Universite Paris-Sud, France
 *               2014      IRT SystemX, France
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

theory OCL_class_diagram_generator_reflect
  imports OCL_class_diagram_generator
  keywords "attr_base" "attr_object" "child"
       and "Class.end" :: thy_decl
       and "Class" :: thy_decl
begin

definition "fold_thy f univ = fold (\<lambda>x. fold f (x univ)) thy_object"

code_reflect OCL
   functions nat_rec nibble_rec char_rec
             fold_thy

ML{*
structure To = struct
  datatype nat = Zero_nat | Suc of nat

  datatype nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 |
    Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC | NibbleD
    | NibbleE | NibbleF

  datatype char = Char of nibble * nibble

  structure M = struct
    val to_nibble = fn
      Nibble0 => 0x0 | Nibble1 => 0x1 | Nibble2 => 0x2 | Nibble3 => 0x3 | Nibble4 => 0x4 | Nibble5 => 0x5 |
       Nibble6 => 0x6 | Nibble7 => 0x7 | Nibble8 => 0x8 | Nibble9 => 0x9 | NibbleA => 0xA | NibbleB => 0xB | NibbleC => 0xC | NibbleD => 0xD
      | NibbleE => 0xE | NibbleF => 0xF

    val to_char = fn Char (n1, n2) => Char.chr ((to_nibble n1) * 16 + to_nibble n2)

    fun to_string l = (String.concat (map (fn c => str (to_char c)) l))

    val to_nat =
      let fun aux n = fn Zero_nat => n | Suc xs => aux (n + 1) xs in
      aux 0
      end
  end

  fun string nibble_rec char_rec =
    let val ofN = nibble_rec
      Nibble0 Nibble1 Nibble2 Nibble3 Nibble4 Nibble5
      Nibble6 Nibble7 Nibble8 Nibble9 NibbleA NibbleB
      NibbleC NibbleD NibbleE NibbleF in
    M.to_string o List.map (char_rec (fn c1 => fn c2 => Char (ofN c1, ofN c2)))
    end

  fun nat nat_rec =
    M.to_nat o nat_rec Zero_nat (fn _ => Suc)
end

*}

ML{*
 val To_string = To.string OCL.nibble_rec OCL.char_rec
 val To_nat = To.nat OCL.nat_rec
 fun To_binding s = Binding.make (s, Position.none)
 val To_sbinding = To_binding o To_string
 fun s_of_rawty rawty = case rawty of
    OCL.Ty_base s => To_string s
  | OCL.Ty_apply (name, l) => (let val s = String.concatWith ", " (map s_of_rawty l) in
                                                 case l of [_] => s | _ => "(" ^ s ^ ")" end)
                              ^ " " ^
                              (s_of_rawty name)

val STR = I

val Unicode_mk_u = fn s => (STR ("\\" ^ "<" ^ s ^ ">"))
val Unicode_u_Rightarrow = Unicode_mk_u (STR "Rightarrow")
val Unicode_u_alpha = Unicode_mk_u (STR "alpha")
val Unicode_u_lambda = Unicode_mk_u (STR "lambda")
val Unicode_u_lfloor = Unicode_mk_u (STR "lfloor")
val Unicode_u_rfloor = Unicode_mk_u (STR "rfloor")
val Unicode_u_Longrightarrow = Unicode_mk_u (STR "Longrightarrow")

fun s_of_expr expr = let open OCL in
  case expr of
    Expr_case (e, l) => let val s1 =
 (s_of_expr e)
val s2 = (String.concatWith (STR "\n    | ") (map (fn (s1, s2) => String.concatWith (STR " ")
 [(s_of_expr s1), Unicode_u_Rightarrow, (s_of_expr s2)]) l)) in
(STR "(case " ^ s1 ^ " of " ^ s2 ^ ")") end
  | Expr_rewrite (e1, symb, e2) => String.concatWith (STR " ") [(s_of_expr e1), (To_string symb), (s_of_expr e2)]
  | Expr_basic l =>  (String.concatWith (STR " ") (map To_string l))
  | Expr_binop (e1, s, e2) => String.concatWith (STR " ") [(s_of_expr e1), (s_of_expr (Expr_basic [s])), (s_of_expr e2)]
  | Expr_annot (e, s) => (STR "(" ^ (s_of_expr e)  ^ "::" ^ (To_string s) ^ ")")
  | Expr_lambda (s, e) =>  (STR "(" ^ Unicode_u_lambda  ^ "" ^ (To_string s)  ^ ". " ^ (s_of_expr e) ^ ")")
  | Expr_lambdas (l, e) => (STR "(" ^ Unicode_u_lambda ^ "" ^ (String.concatWith (STR " ") (map To_string l)) ^ ". " ^ (s_of_expr e) ^ ")")
  | Expr_function l =>  (STR "(" ^ Unicode_u_lambda  ^ " " ^ (String.concatWith (STR "\n    | ") (map (fn (s1, s2) => String.concatWith (STR " ") [ (s_of_expr s1),Unicode_u_Rightarrow, (s_of_expr s2)]) l)) ^ ")")
  (*| Expr_apply s [e] => sprintf2 (STR "(" ^ s ^ " " ^ s ^ ")") (To_string s) (s_of_expr e)*)
  | Expr_apply (s, l) =>  let val s1 = (To_string s) val s2 = (String.concatWith (STR " ") (map (fn e => (STR "(" ^ (s_of_expr e) ^ ")") ) l)) in
(STR "(" ^ s1 ^ " " ^ s2 ^ ")") end
  | Expr_applys (e, l) => let val s1 = (s_of_expr e) val s2 = (String.concatWith (STR " ") (map (fn e => (STR "(" ^ (s_of_expr e) ^ ")") ) l)) in
 (STR "((" ^ s1 ^ ") " ^ s2 ^ ")") end
  | Expr_some (Expr_function l) => let val s1 = Unicode_u_lfloor val s2 = Unicode_u_lambda val s3 = (String.concatWith (STR "\n    | ") (map (fn (s1, s2) => String.concatWith (STR " ") [ (s_of_expr s1), Unicode_u_Rightarrow, (s_of_expr s2)]) l)) val s4 = Unicode_u_rfloor in
(STR "" ^ s1 ^ "" ^ s2 ^ " " ^ s3 ^ "" ^ s4 ^ "") end
  | Expr_some e => String.concatWith (STR "") [Unicode_u_lfloor, (s_of_expr e), Unicode_u_rfloor]
  | Expr_postunary (e1, e2) =>  (s_of_expr e1) ^ " " ^ (s_of_expr e2)
  | Expr_preunary (e1, e2) =>  (s_of_expr e1) ^ " " ^ (s_of_expr e2)
  | Expr_warning_parenthesis e =>  (STR "(" ^ (s_of_expr e) ^ ")")
  | Expr_parenthesis e => (STR "(" ^ (s_of_expr e) ^ ")")
end

fun simp_tac f = Method.Basic (fn ctxt => SIMPLE_METHOD (asm_full_simp_tac (f ctxt) 1))

fun m_of_tactic expr = let open OCL in let open Method in case expr of
    Tac_rule s => Basic (fn ctxt => rule [Proof_Context.get_thm ctxt (To_string s)])
  | Tac_rule_where (s, l) => Basic (fn ctxt => rule [read_instantiate ctxt (map (fn (var, expr) => ((To_string var, 0), s_of_expr expr)) l) (Proof_Context.get_thm ctxt (To_string s))])
  | Tac_plus t => Repeat1 (m_of_tactic t)
  | Tac_simp => simp_tac I
  | Tac_simp_add l => simp_tac (fn ctxt => ctxt addsimps (map (Proof_Context.get_thm ctxt o To_string) l))
  | Tac_simp_only l => simp_tac (fn ctxt => clear_simpset ctxt addsimps (map (Proof_Context.get_thm ctxt o To_string) l))
  | Tac_simp_all => m_of_tactic (Tac_plus Tac_simp)
  | Tac_simp_all_add s => m_of_tactic (Tac_plus (Tac_simp_add [s]))
end end
*}

ML{*
fun perform_instantiation thy tycos vs f_eq add_def tac (*add_eq_thms*) =
    thy
    |> Class.instantiation (tycos, vs, f_eq)
    |> fold_map add_def tycos
    |-> Class.prove_instantiation_exit_result (map o Morphism.thm) (fn _ => tac)
(*    |-> fold Code.del_eqn
    |> fold add_eq_thms tycos*)
    |-> K I
local
fun read_abbrev b ctxt raw_rhs =
  let
    val rhs = Proof_Context.read_typ_syntax (ctxt |> Proof_Context.set_defsort []) raw_rhs;
    val ignored = Term.fold_atyps_sorts (fn (_, []) => I | (T, _) => insert (op =) T) rhs [];
    val _ =
      if null ignored then ()
      else Context_Position.if_visible ctxt warning
        ("Ignoring sort constraints in type variables(s): " ^
          commas_quote (map (Syntax.string_of_typ ctxt) (rev ignored)) ^
          "\nin type abbreviation " ^ (case b of NONE => "" | SOME b => Binding.print b));
  in rhs end
in
fun read_typ_syntax b = read_abbrev b
                      o Proof_Context.init_global
end
fun in_local decl thy =
  thy
  |> Named_Target.init I ""
  |> decl
  |> Local_Theory.exit_global

fun s_of_tactic l = (Method.Then (map m_of_tactic l), (Position.none, Position.none))

fun apply_results l =
  fn p => p |> Proof.apply_results (s_of_tactic l)
            |> Seq.the_result ""

fun global_terminal_proof o_by = case o_by of
   NONE => Proof.global_done_proof
 | SOME l_apply => Proof.global_terminal_proof (s_of_tactic l_apply, NONE)
*}

ML{*
val OCL_main = let open OCL in fold_thy ((*let val f = *)fn
  Thy_dataty (Datatype (n, l)) =>
    (snd oo Datatype.add_datatype_cmd Datatype_Aux.default_config)
      [((To_sbinding n, [], NoSyn),
       map (fn (n, l) => (To_sbinding n, map (fn OCL.Opt o_ => To_string o_ ^ " option"
                                             |   Raw o_ => To_string o_) l, NoSyn)) l)]
| Thy_ty_synonym (Type_synonym (n, l)) =>
    (fn thy =>
     let val s_bind = To_sbinding n in
     (snd o Typedecl.abbrev_global (s_bind, [], NoSyn)
                                   (read_typ_syntax (SOME s_bind) thy (s_of_rawty l))) thy
     end)
| Thy_instantiation_class (Instantiation (n, n_def, expr)) =>
    (fn thy =>
     let val name = To_string n in
     perform_instantiation
       thy
       [ let val Type (s, _) = (read_typ_syntax NONE thy name) in s end ]
       []
       (Syntax.read_sort (Proof_Context.init_global thy) "object")
       (fn _ => fn thy =>
        let val ((_, (_, ty)), thy) = Specification.definition_cmd
           (NONE, ((To_binding (To_string n_def ^ "_" ^ name ^ "_def"), []), s_of_expr expr)) false thy in
         (ty, thy)
        end)
       (fn thms => Class.intro_classes_tac [] THEN ALLGOALS (Proof_Context.fact_tac thms))
     end)
| Thy_defs_overloaded (Defs_overloaded (n, e)) =>
    Isar_Cmd.add_defs ((false, true), [((To_sbinding n, s_of_expr e), [])])
| Thy_consts_class (Consts (n, ty_out, symb1, symb2)) =>
    Sign.add_consts [( To_sbinding n
                     , String.concatWith " " [ "'" ^ Unicode_u_alpha, Unicode_u_Rightarrow, (To_string ty_out) ]
                     , Mixfix ("(_) " ^ (To_string symb1) ^ "'(" ^ (To_string symb2) ^ "')", [], 1000))]
| Thy_definition_hol def =>
    let val (def, e) = case def of
        Definition e => (NONE, e)
      | Definition_abbrev (name, (abbrev, prio), e) =>
          (SOME ( To_sbinding name
                , NONE
                , Mixfix ("(1" ^ s_of_expr abbrev ^ ")", [], To_nat prio)), e) in
    in_local (snd o Specification.definition_cmd (def, ((@{binding ""}, []), s_of_expr e)) false)
    end
| Thy_lemmas_simp (Lemmas_simp l) =>
    in_local (snd o Specification.theorems_cmd Thm.lemmaK
      [((@{binding ""}, [Args.src (("simp", []), Position.none)]),
        map (fn s => (Facts.Named ((To_string s, Position.none), NONE), [])) l)]
      []
      false)
| Thy_lemma_by (Lemma_by (n, l_spec, l_apply, o_by)) =>
      in_local (fn lthy =>
           Specification.theorem_cmd Thm.lemmaK NONE (K I)
             (@{binding ""}, []) [] [] (Element.Shows [((To_sbinding n, []), [((String.concatWith ((STR " " ^ Unicode_u_Longrightarrow ^ " ")) (map s_of_expr l_spec)), [])])])
             false lthy
        |> fold apply_results l_apply
        |> global_terminal_proof o_by)
(*in fn t => fn thy => f t thy handle ERROR s => (warning s; thy)
 end*)
)
end
*}

ML{*
type class_inline = { attr_base : (binding * binding) list
                    , attr_object : binding list
                    , child : binding list
                    , univ : OCL.univ option }

structure Data = Theory_Data
  (type T = class_inline Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true))

structure From = struct local
 open OCL
 val from_nibble = fn
       0x0 => Nibble0 | 0x1 => Nibble1 | 0x2 => Nibble2 | 0x3 => Nibble3 | 0x4 => Nibble4 | 0x5 => Nibble5 |
        0x6 => Nibble6 | 0x7 => Nibble7 | 0x8 => Nibble8 | 0x9 => Nibble9 | 0xA => NibbleA | 0xB => NibbleB | 0xC => NibbleC | 0xD => NibbleD
       | 0xE => NibbleE | 0xF => NibbleF
 fun from_string n = map (fn c => let val c = Char.ord c in OCL.Char (from_nibble (c div 16), from_nibble (c mod 16)) end) (String.explode n)
 val from_binding = from_string o Binding.name_of
 in
 fun mk_univ (n, ({attr_base = attr_base, attr_object = attr_object, child = child, ...}:class_inline)) t = 
   Mk_univ ( from_string n
           , List.concat [ map (fn (b, ty) => (from_binding b, OclTy_base (from_binding ty))) attr_base
                         , map (fn b => (from_binding b, object)) attr_object]
           , case child of [] => NONE | [x] => SOME (mk_univ (let val x = Binding.name_of x in (x, let val SOME v = Symtab.lookup t x in v end) end) t))
end end

val () =
  Outer_Syntax.command @{command_spec "Class"} "Class definition"
    ((Parse.binding --| Parse.$$$ "=") --
      Scan.repeat (@{keyword "attr_base"} |-- Parse.!!! (Parse.binding -- (Parse.$$$ "::" |-- Parse.!!! Parse.binding))) --
      Scan.repeat (@{keyword "attr_object"} |-- Parse.!!! Parse.binding) --
      Scan.repeat (@{keyword "child"} |-- Parse.!!! Parse.binding)
        >> (fn (((binding, attr_base), attr_object), child) => fn x =>
              x |> Toplevel.theory (fn thy => thy |> Data.map (fn t =>
                                                     let val name = Binding.name_of binding
                                                     fun mk univ = { attr_base = attr_base
                                                                   , attr_object = attr_object
                                                                   , child = child
                                                                   , univ = univ } in
                                                     Symtab.insert (op =) (name, mk (SOME (From.mk_univ (name, mk NONE) t))) t
                                                     end))))

val () =
  Outer_Syntax.command @{command_spec "Class.end"} "Class generation"
    (Parse.binding >> (fn name =>
      let val name = Binding.name_of name in
      Toplevel.theory (fn thy => OCL_main (let val SOME { attr_base = attr_base
                                                        , attr_object = attr_object
                                                        , child = child
                                                        , univ = SOME univ} = Symtab.lookup (Data.get thy) name in
                                           univ
                                           end) thy)
      end))

(*val _ = print_depth 100*)
*}

end
