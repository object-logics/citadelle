(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_generator_dynamic.thy ---
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

theory OCL_compiler_generator_dynamic
imports OCL_compiler_printer
  keywords (* ocl (USE tool) *)
           "Between" "End"
           "Attributes" "Operations" "Constraints"
           "Role"
           "Ordered" "Subsets" "Union" "Redefines" "Derived" "Qualifier"
           "Existential" "Inv" "Pre" "Post"
           (* ocl (added) *)
           "skip" "self"

           (* hol syntax *)
           "output_directory"
           "THEORY" "IMPORTS" "SECTION"
           "deep" "shallow" "syntax_print" "skip_export"
           "generation_semantics"
           "flush_all"

           (* hol semantics *)
           "design" "analysis" "oid_start"

       and (* ocl (USE tool) *)
           "Abstract_class" "Class"
           "Association" "Composition" "Aggregation"
           "Abstract_associationclass" "Associationclass"
           "Context"
           (* ocl (added) *)
           "Class.end" "Instance" "Define_base" "Define_state" "Define_pre_post"

           (* hol syntax *)
           "generation_syntax"

           :: thy_decl
begin

section{* Generation to Shallow Form: SML *}

subsection{* global *}

apply_code_printing_reflect {*
  (* this variable is not used but needed for well typechecking the reflected SML code *)
  val stdout_file = Unsynchronized.ref ""
*}
code_reflect OCL
   functions (* OCL compiler as monadic combinators for deep and shallow *)
             fold_thy_deep fold_thy_shallow

             (* printing the HOL AST to (shallow Isabelle) string *)
             write_file

             (* manipulating the compiling environment *)
             ocl_compiler_config_reset_all oidInit D_file_out_path_dep_update map2_ctxt_term check_export_code

             (* printing the OCL AST to (deep Isabelle) string *)
             isabelle_apply isabelle_of_ocl_embed

ML{*
 val To_string = implode o map str
 fun To_nat (Code_Numeral.Nat i) = i
*}

ML{*
structure From = struct
 open OCL
 val from_char = I
 val from_string = String.explode
 val from_binding = from_string o Binding.name_of
 fun from_term ctxt s = from_string (XML.content_of (YXML.parse_body (Syntax.string_of_term ctxt s)))
 val from_nat = Code_Numeral.Nat
 val from_internal_oid = Oid
 val from_bool = I
 val from_unit = I
 val from_option = Option.map
 val from_list = List.map
 fun from_pair f1 f2 (x, y) = (f1 x, f2 y)
 fun from_pair3 f1 f2 f3 (x, y, z) = (f1 x, f2 y, f3 z)
 val from_design_analysis = fn NONE => Gen_design | _ => Gen_analysis

 val from_pure_indexname = OCL.PureIndexname o from_pair from_string from_nat
 val from_pure_class = OCL.PureClass o from_string
 val from_pure_sort = OCL.PureSort o from_list from_pure_class
 fun from_pure_typ e = (fn
     Type (s, l) => (OCL.PureType o from_pair from_string (from_list from_pure_typ)) (s, l)
   | TFree (s, sort) => (OCL.PureTFree o from_pair from_string from_pure_sort) (s, sort)
   | TVar (i, sort) => (OCL.PureTVar o from_pair from_pure_indexname from_pure_sort) (i, sort)
  ) e
 fun from_pure_term e = (fn
     Const (s, typ) => (OCL.PureConst o from_pair from_string from_pure_typ) (s, typ)
   | Free (s, typ) => (OCL.PureConst o from_pair from_string from_pure_typ) (s, typ)
   | Var (i, typ) => (OCL.PureVar o from_pair from_pure_indexname from_pure_typ) (i, typ)
   | Bound i => (OCL.PureBound o from_nat) i
   | Abs (s, typ, term) => (OCL.PureAbs o from_pair3 from_string from_pure_typ from_pure_term) (s, typ, term)
   | op $ (term1, term2) => (OCL.PureApp o from_pair from_pure_term from_pure_term) (term1, term2)
  ) e

 fun from_p_term thy expr =
   OCL.T_pure (from_pure_term (Syntax.read_term (Proof_Context.init_global thy) expr))
end
*}

ML{*
fun in_local decl thy =
  thy
  |> Named_Target.init I ""
  |> decl
  |> Local_Theory.exit_global
*}

ML{* fun List_mapi f = OCL.list_mapi (f o To_nat) *}

ML{*
structure Ty' = struct
fun check l_oid l =
  let val Mp = OCL.map_pair
      val Me = String.explode
      val Mi = String.implode
      val Ml = map in
  OCL.check_export_code
    (writeln o Mi)
    (warning o Mi)
    (writeln o Markup.markup Markup.bad o Mi)
    (error o Mi)
    (Ml (Mp I Me) l_oid)
    (Me l)
  end
end
*}

subsection{* General Compiling Process: Deep (with reflection) *}

ML{*
structure Deep0 = struct

fun apply_hs_code_identifiers ml_module thy =
  let fun mod_hs (fic, ml_module) = Code_Symbol.Module (fic, [("Haskell", SOME ml_module)]) in
  fold (Code_Target.set_identifiers o mod_hs)
    ( ( case Properties.get (snd (Theory.get_markup thy)) "name" of
                 SOME s => s
      , ml_module)
    :: map (fn x => (x, ml_module))
         (* list of .hs files that will be merged together in "ml_module" *)
         [ "OCL_compiler_core_access"
         , "OCL_compiler_core_allinst"
         , "OCL_compiler_core_astype"
         , "OCL_compiler_core_ctxt"
         , "OCL_compiler_core_examp"
         , "OCL_compiler_core"
         , "OCL_compiler_core_infra"
         , "OCL_compiler_core_init"
         , "OCL_compiler_core_iskindof"
         , "OCL_compiler_core_istypeof"
         , "OCL_compiler_init"
         , "OCL_compiler_init_rbt"
         , "OCL_compiler_meta_Isabelle"
         , "OCL_compiler_meta_META"
         , "OCL_compiler_meta_oid"
         , "OCL_compiler_meta_Pure"
         , "OCL_compiler_meta_SML"
         , "OCL_compiler_meta_UML_extended"
         , "OCL_compiler_meta_UML"
         , "OCL_compiler_parser_init"
         , "OCL_compiler_parser_META"
         , "OCL_compiler_parser_oid"
         , "OCL_compiler_parser_Pure"
         , "OCL_compiler_parser_UML_extended"
         , "OCL_compiler_parser_UML"
         , "OCL_compiler_printer"
         , "OCL_compiler_printer_Isabelle"
         , "OCL_compiler_printer_META"
         , "OCL_compiler_printer_oid"
         , "OCL_compiler_printer_Pure"
         , "OCL_compiler_printer_SML"
         , "OCL_compiler_static" ]) thy end

val gen_empty = ""

structure Export_code_env = struct
  structure Isabelle = struct
    val function = "write_file"
    val argument_main = "main"
  end

  structure Haskell = struct
    val function = "Function"
    val argument = "Argument"
    val main = "Main"
    structure Filename = struct
      fun hs_function ext = function ^ "." ^ ext
      fun hs_argument ext = argument ^ "." ^ ext
      fun hs_main ext = main ^ "." ^ ext
    end
  end

  structure OCaml = struct
    val make = "write"
    structure Filename = struct
      fun function ext = "function." ^ ext
      fun argument ext = "argument." ^ ext
      fun main_fic ext = "main." ^ ext
      fun makefile ext = make ^ "." ^ ext
    end
  end

  structure Scala = struct
    structure Filename = struct
      fun function ext = "Function." ^ ext
      fun argument ext = "Argument." ^ ext
    end
  end

  structure SML = struct
    val main = "Run"
    structure Filename = struct
      fun function ext = "Function." ^ ext
      fun argument ext = "Argument." ^ ext
      fun stdout ext = "Stdout." ^ ext
      fun main_fic ext = main ^ "." ^ ext
    end
  end

  datatype file_input = File
                      | Directory
end

fun compile l cmd =
  let val (l, rc) = fold (fn cmd => (fn (l, 0) =>
                                         let val {out, err, rc, ...} = Bash.process cmd in
                                         ((out, err) :: l, rc) end
                                     | x => x)) l ([], 0)
      val l = rev l in
  if rc = 0 then
    (l, Isabelle_System.bash_output cmd)
  else
    let val () = fold (fn (out, err) => K (warning err; writeln out)) l () in
    error "Compilation failed"
    end
  end

val check =
  fold (fn (cmd, msg) => fn () =>
    let val (out, rc) = Isabelle_System.bash_output cmd in
    if rc = 0 then
      ()
    else
      ( writeln out
      ; error msg)
    end)

val compiler = let open Export_code_env in
  [ let val ml_ext = "hs" in
    ( "Haskell", ml_ext, Directory, Haskell.Filename.hs_function
    , check [("ghc --version", "ghc is not installed (required for compiling a Haskell project)")]
    , (fn mk_fic => fn ml_module => fn mk_free => fn thy =>
        File.write (mk_fic ("Main." ^ ml_ext))
          (String.concatWith "; " [ "import qualified Unsafe.Coerce"
                         , "import qualified " ^ Haskell.function
                         , "import qualified " ^ Haskell.argument
                         , "main :: IO ()"
                         , "main = " ^ Haskell.function ^ "." ^ Isabelle.function ^ " (Unsafe.Coerce.unsafeCoerce " ^ Haskell.argument ^ "." ^
                           mk_free (Proof_Context.init_global thy) Isabelle.argument_main ([]: (string * string) list) ^
                           ")"]))
    , fn tmp_export_code => fn tmp_file =>
        compile [ "mv " ^ tmp_file ^ "/" ^ Haskell.Filename.hs_argument ml_ext ^ " " ^ Path.implode tmp_export_code
                , "cd " ^ Path.implode tmp_export_code ^
                  " && ghc -outputdir _build " ^ Haskell.Filename.hs_main ml_ext ]
                (Path.implode (Path.append tmp_export_code (Path.make [Haskell.main]))))
    end
  , let val ml_ext = "ml" in
    ( "OCaml", ml_ext, File, OCaml.Filename.function
    , check [("ocp-build -version", "ocp-build is not installed (required for compiling an OCaml project)")
            ,("ocamlopt -version", "ocamlopt is not installed (required for compiling an OCaml project)")]
    , fn mk_fic => fn ml_module => fn mk_free => fn thy =>
         let val () = File.write (mk_fic (OCaml.Filename.makefile "ocp"))
                              (String.concat [ "comp += \"-g\" link += \"-g\" "
                                             , "begin generated = true begin library \"nums\" end end "
                                             , "begin program \"", OCaml.make, "\" sort = true files = [ \"", OCaml.Filename.function ml_ext
                                             , "\" \"", OCaml.Filename.argument ml_ext
                                             , "\" \"", OCaml.Filename.main_fic ml_ext
                                             , "\" ]"
                                             , "requires = [\"nums\"] "
                                             , "end" ]) in
         File.write (mk_fic (OCaml.Filename.main_fic ml_ext))
           ("let _ = Function." ^ ml_module ^ "." ^ Isabelle.function ^ " (Obj.magic (Argument." ^ ml_module ^ "." ^
            mk_free (Proof_Context.init_global thy) Isabelle.argument_main ([]: (string * string) list) ^ "))")
         end
    , fn tmp_export_code => fn tmp_file =>
        compile [ "mv " ^ tmp_file ^ " " ^ Path.implode (Path.append tmp_export_code (Path.make [OCaml.Filename.argument ml_ext]))
                , "cd " ^ Path.implode tmp_export_code ^
                  " && ocp-build -init -scan -no-bytecode 2>&1" ]
                (Path.implode (Path.append tmp_export_code (Path.make [ "_obuild", OCaml.make, OCaml.make ^ ".asm"]))))
    end
  , let val ml_ext = "scala"
        val ml_module = Unsynchronized.ref ("", "") in
    ( "Scala", ml_ext, File, Scala.Filename.function
    , check [("scala -e 0", "scala is not installed (required for compiling a Scala project)")]
    , (fn _ => fn ml_mod => fn mk_free => fn thy =>
        ml_module := (ml_mod, mk_free (Proof_Context.init_global thy) Isabelle.argument_main ([]: (string * string) list)))
    , fn tmp_export_code => fn tmp_file =>
        let val l = File.read_lines (Path.explode tmp_file)
            val (ml_module, ml_main) = Unsynchronized.! ml_module
            val () = File.write_list
                       (Path.append tmp_export_code (Path.make [Scala.Filename.argument ml_ext]))
                       (List.map
                         (fn s => s ^ "\n")
                         ("object " ^ ml_module ^ " { def main (__ : Array [String]) = " ^ ml_module ^ "." ^ Isabelle.function ^ " (" ^ ml_module ^ "." ^ ml_main ^ ")" :: l @ ["}"])) in
        compile []
                ("scala -nowarn " ^ Path.implode (Path.append tmp_export_code (Path.make [Scala.Filename.argument ml_ext])))
        end)
    end
  , let val ml_ext_thy = "thy"
        val ml_ext_ml = "ML" in
    ( "SML", ml_ext_ml, File, SML.Filename.function
    , check [ let val isa = "isabelle" in
              ( Path.implode (Path.expand (Path.append (Path.variable "ISABELLE_HOME") (Path.make ["bin", isa]))) ^ " version"
              , isa ^ " is not installed (required for compiling a SML project)")
              end ]
    , fn mk_fic => fn ml_module => fn mk_free => fn thy =>
         let val esc_star = "*"
             val esc_accol1 = "{" ^ esc_star
             val esc_accol2 = esc_star ^ "}" in
         File.write_list (mk_fic (SML.Filename.main_fic ml_ext_thy))
           (map (fn s => s ^ "\n") (List.concat
           [ [ "theory " ^ SML.main
             , "imports Main"
             , "begin"
             , "ML" ^ esc_accol1]
           , map (fn s => s ^ ";")
             let val arg = "argument" in
             [ "val stdout_file = Unsynchronized.ref (File.read (Path.make [\"" ^ SML.Filename.stdout ml_ext_ml ^ "\"]))"
             , "print_depth 500" (* any large number so that @{make_string} displays all the expression *)
             , "use \"" ^ SML.Filename.argument ml_ext_ml ^ "\""
             , "val " ^ arg ^ " = XML.content_of (YXML.parse_body (@{make_string} (" ^ ml_module ^ "." ^
               mk_free (Proof_Context.init_global thy) Isabelle.argument_main ([]: (string * string) list) ^ ")))"
             , "use \"" ^ SML.Filename.function ml_ext_ml ^ "\""
             , "ML_Context.eval_text false Position.none (\"let open " ^ ml_module ^ " in " ^ Isabelle.function ^ " (\" ^ " ^ arg ^ " ^ \") end\")" ]
             end
           , [ esc_accol2
             , "end"] ]))
         end
    , fn tmp_export_code => fn tmp_file =>
        let val stdout_file = Isabelle_System.create_tmp_path "stdout_file" "thy"
            val () = File.write (Path.append tmp_export_code (Path.make [SML.Filename.stdout ml_ext_ml])) (Path.implode (Path.expand stdout_file))
            val (l, (_, exit_st)) =
              compile [ "mv " ^ tmp_file ^ " " ^ Path.implode (Path.append tmp_export_code (Path.make [SML.Filename.argument ml_ext_ml]))
                      , "cd " ^ Path.implode tmp_export_code ^
                        " && cat " ^ SML.Filename.main_fic ml_ext_thy ^
                        " | " ^
                        Path.implode (Path.expand (Path.append (Path.variable "ISABELLE_HOME") (Path.make ["bin", "isabelle"]))) ^ " tty" ]
                      "true"
            val stdout =
              case SOME (File.read stdout_file) handle _ => NONE of
                SOME s => let val () = File.rm stdout_file in s end
              | NONE => "" in
            (l, (stdout, if List.exists (fn (err, _) =>
                              List.exists (fn "*** Error" => true | _ => false)
                                (String.tokens (fn #"\n" => true | _ => false) err)) l then
                           let val () = fold (fn (out, err) => K (warning err; writeln out)) l () in
                           1
                           end
                         else exit_st))
        end)
    end ]
end

fun find_ext ml_compiler =
  case List.find (fn (ml_compiler0, _, _, _, _, _, _) => ml_compiler0 = ml_compiler) compiler of
    SOME (_, ext, _, _, _, _, _) => ext

fun find_export_mode ml_compiler =
  case List.find (fn (ml_compiler0, _, _, _, _, _, _) => ml_compiler0 = ml_compiler) compiler of
    SOME (_, _, mode, _, _, _, _) => mode

fun find_function ml_compiler =
  case List.find (fn (ml_compiler0, _, _, _, _, _, _) => ml_compiler0 = ml_compiler) compiler of
    SOME (_, _, _, f, _, _, _) => f

fun find_check_compil ml_compiler =
  case List.find (fn (ml_compiler0, _, _, _, _, _, _) => ml_compiler0 = ml_compiler) compiler of
    SOME (_, _, _, _, build, _, _) => build

fun find_init ml_compiler =
  case List.find (fn (ml_compiler0, _, _, _, _, _, _) => ml_compiler0 = ml_compiler) compiler of
    SOME (_, _, _, _, _, build, _) => build

fun find_build ml_compiler =
  case List.find (fn (ml_compiler0, _, _, _, _, _, _) => ml_compiler0 = ml_compiler) compiler of
    SOME (_, _, _, _, _, _, build) => build


end
*}

ML{*
structure Deep = struct

fun prep_destination "" = NONE
  | prep_destination "-" = (legacy_feature "drop \"file\" argument entirely instead of \"-\""; NONE)
  | prep_destination s = SOME (Path.explode s)

fun produce_code thy cs seris =
  let
    val (names_cs, (naming, program)) = Code_Thingol.consts_program thy false cs in
    map (fn (((target, module_name), some_path), args) =>
      (some_path, Code_Target.produce_code_for thy (*some_path*) target NONE module_name args naming program names_cs)) seris
  end

fun absolute_path filename thy = Path.implode (Path.append (Thy_Load.master_directory thy) (Path.explode filename))

fun export_code_cmd_gen raw_cs thy seris =
  Code_Target.export_code
                  thy
                  (Code_Target.read_const_exprs thy raw_cs)
                  ((map o apfst o apsnd) prep_destination seris)

fun export_code_tmp_file seris g =
  fold
    (fn ((ml_compiler, ml_module), export_arg) => fn f => fn g =>
      f (fn accu =>
        let val tmp_name = "OCL_compiler_generator_dynamic" in
        (if Deep0.find_export_mode ml_compiler = Deep0.Export_code_env.Directory then
           Isabelle_System.with_tmp_dir tmp_name
         else
           Isabelle_System.with_tmp_file tmp_name (Deep0.find_ext ml_compiler))
          (fn filename =>
             g (((((ml_compiler, ml_module), Path.implode filename), export_arg) :: accu)))
        end))
    seris
    (fn f => f [])
    (g o rev)

fun mk_path_export_code tmp_export_code ml_compiler i =
  Path.append tmp_export_code (Path.make [ml_compiler ^ Int.toString i])

fun export_code_cmd' seris tmp_export_code f_err filename_thy raw_cs thy =
  export_code_tmp_file seris
    (fn seris =>
      let val mem_scala = List.exists (fn ((("Scala", _), _), _) => true | _ => false) seris
          val _ = export_code_cmd_gen
        (if mem_scala then Deep0.Export_code_env.Isabelle.function :: raw_cs else raw_cs)
        (let val v = Deep0.apply_hs_code_identifiers Deep0.Export_code_env.Haskell.argument thy in
         if mem_scala then Code_printing.apply_code_printing v else v end)
        seris in
      List_mapi
        (fn i => fn seri => case seri of (((ml_compiler, _), filename), _) =>
          let val (l, (out, err)) =
                Deep0.find_build
                  ml_compiler
                  (mk_path_export_code tmp_export_code ml_compiler i)
                  filename
              val _ = f_err seri err in
          (l, out)
          end) seris
      end)

fun mk_term ctxt s = fst (Scan.pass (Context.Proof ctxt) Args.term (Outer_Syntax.scan Position.none s))

fun mk_free ctxt s l =
  let val t_s = mk_term ctxt s in
  if Term.is_Free t_s then s else
    let val l = (s, "") :: l in
    mk_free ctxt (fst (hd (Term.variant_frees t_s l))) l
    end
  end

val list_all_eq = fn x0 :: xs =>
  List.all (fn x1 => x0 = x1) xs

end
*}

subsection{* ... *}

ML{*
fun parse_l f = Parse.$$$ "[" |-- Parse.!!! (Parse.list f --| Parse.$$$ "]")
fun parse_l' f = Parse.$$$ "[" |-- Parse.list f --| Parse.$$$ "]"
fun parse_l1' f = Parse.$$$ "[" |-- Parse.list1 f --| Parse.$$$ "]"
fun annot_ty f = Parse.$$$ "(" |-- f --| Parse.$$$ "::" -- Parse.binding --| Parse.$$$ ")"
*}

ML{*
structure Generation_mode = struct
datatype 'a generation_mode = Gen_deep of unit OCL.ocl_compiler_config_ext
                                        * (string * (string list (* imports *) * string (* import optional (bootstrap) *))) option
                                        * ((bstring (* compiler *) * bstring (* main module *) ) * Token.T list) list (* seri_args *)
                                        * bstring option (* filename_thy *)
                                        * Path.T (* tmp dir export_code *)
                                        * bool (* true: skip preview of code exportation *)
                            | Gen_shallow of unit OCL.ocl_compiler_config_ext
                                           * 'a (* theory init *)
                            | Gen_syntax_print

structure Data_gen = Theory_Data
  (type T = theory generation_mode list Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true))

val code_expr_argsP = Scan.optional (@{keyword "("} |-- Args.parse --| @{keyword ")"}) []

val parse_scheme = @{keyword "design"} >> K NONE || @{keyword "analysis"} >> K (SOME 1)

val parse_deep =
     Scan.optional (@{keyword "skip_export"} >> K true) false
  -- Scan.optional (((Parse.$$$ "(" -- @{keyword "THEORY"}) |-- Parse.name -- ((Parse.$$$ ")" -- Parse.$$$ "(" -- @{keyword "IMPORTS"}) |-- parse_l' Parse.name -- Parse.name) --| Parse.$$$ ")") >> SOME) NONE
  -- Scan.optional (@{keyword "SECTION"} >> K true) false
  -- (* code_expr_inP *) parse_l1' (@{keyword "in"} |-- (Parse.name
        -- Scan.optional (@{keyword "module_name"} |-- Parse.name) ""
        -- code_expr_argsP))
  -- Scan.optional ((Parse.$$$ "(" -- @{keyword "output_directory"}) |-- Parse.name --| Parse.$$$ ")" >> SOME) NONE

val parse_sem_ocl =
      (Parse.$$$ "(" -- @{keyword "generation_semantics"} -- Parse.$$$ "[")
  |-- parse_scheme -- Scan.optional ((Parse.$$$ "," -- @{keyword "oid_start"}) |-- Parse.nat) 0
  --| (Parse.$$$ "]" -- Parse.$$$ ")")

val mode =
  let fun mk_ocl disable_thy_output file_out_path_dep oid_start design_analysis =
    OCL.ocl_compiler_config_empty
                    (From.from_bool disable_thy_output)
                    (From.from_option (From.from_pair From.from_string (From.from_pair (From.from_list From.from_string) From.from_string)) file_out_path_dep)
                    (OCL.oidInit (From.from_internal_oid (From.from_nat oid_start)))
                    (From.from_design_analysis design_analysis) in

     @{keyword "deep"} |-- parse_sem_ocl -- parse_deep >> (fn ((design_analysis, oid_start), ((((skip_exportation, file_out_path_dep), disable_thy_output), seri_args), filename_thy)) =>
       Gen_deep ( mk_ocl (not disable_thy_output) file_out_path_dep oid_start design_analysis
                , file_out_path_dep, seri_args, filename_thy, Isabelle_System.create_tmp_path "deep_export_code" "", skip_exportation))
  || @{keyword "shallow"} |-- parse_sem_ocl >> (fn (design_analysis, oid_start) =>
       Gen_shallow (mk_ocl true NONE oid_start design_analysis, ()))
  || @{keyword "syntax_print"} >> K Gen_syntax_print
  end


fun f_command l_mode =
      Toplevel.theory (fn thy =>
        let val (l_mode, thy) = OCL.fold_list
          (fn Gen_shallow (ocl, ()) => let val thy0 = thy in
                                       fn thy => (Gen_shallow (ocl, thy0), thy) end
            | Gen_syntax_print => (fn thy => (Gen_syntax_print, thy))
            | Gen_deep (ocl, file_out_path_dep, seri_args, filename_thy, tmp_export_code, skip_exportation) => fn thy =>
                let val _ = warning ("remove the directory (at the end): " ^ Path.implode tmp_export_code)
                    val seri_args' = List_mapi (fn i => fn ((ml_compiler, ml_module), export_arg) =>
                      let val tmp_export_code = Deep.mk_path_export_code tmp_export_code ml_compiler i
                          fun mk_fic s = Path.append tmp_export_code (Path.make [s])
                          val () = Deep0.find_check_compil ml_compiler ()
                          val () = Isabelle_System.mkdirs tmp_export_code in
                      ((( (ml_compiler, ml_module)
                        , Path.implode (if Deep0.find_export_mode ml_compiler = Deep0.Export_code_env.Directory then
                                          tmp_export_code
                                        else
                                          mk_fic (Deep0.find_function ml_compiler (Deep0.find_ext ml_compiler))))
                        , export_arg), mk_fic)
                      end) seri_args
                    val _ = Deep.export_code_cmd_gen
                              [Deep0.Export_code_env.Isabelle.function]
                              (Code_printing.apply_code_printing (Deep0.apply_hs_code_identifiers Deep0.Export_code_env.Haskell.function thy))
                              (List.map fst seri_args')
                    val () = fold (fn ((((ml_compiler, ml_module), _), _), mk_fic) => fn _ =>
                      Deep0.find_init ml_compiler mk_fic ml_module Deep.mk_free thy) seri_args' () in
                (Gen_deep (ocl, file_out_path_dep, seri_args, filename_thy, tmp_export_code, skip_exportation), thy) end) l_mode thy in
        Data_gen.map (Symtab.map_default (Deep0.gen_empty, l_mode) (fn _ => l_mode)) thy
        end)

fun update_compiler_config f =
  Data_gen.map
    (Symtab.map_entry
      Deep0.gen_empty
      (fn l_mode =>
        map (fn Gen_deep (ocl, file_out_path_dep, seri_args, filename_thy, tmp_export_code, skip_exportation) =>
                  Gen_deep (f ocl, file_out_path_dep, seri_args, filename_thy, tmp_export_code, skip_exportation)
              | Gen_shallow (ocl, thy) => Gen_shallow (f ocl, thy)
              | Gen_syntax_print => Gen_syntax_print) l_mode))
end
*}

subsection{* General Compiling Process: Shallow *}

ML{*
structure OCL_overload = struct
  val s_of_rawty = OCL.s_of_rawty To_string
  val s_of_expr = OCL.s_of_expr To_string (Int.toString o To_nat)
  val s_of_sexpr = OCL.s_of_sexpr To_string (Int.toString o To_nat)
  val fold = fold
end
*}

ML{*
structure Shallow_conv = struct
 fun To_binding s = Binding.make (s, Position.none)
 val To_sbinding = To_binding o To_string

fun simp_tac f = Method.Basic (fn ctxt => SIMPLE_METHOD (asm_full_simp_tac (f ctxt) 1))

fun m_of_ntheorem ctxt s = let open OCL open OCL_overload in case s of
    Thm_str s => Proof_Context.get_thm ctxt (To_string s)
  | Thm_THEN (e1, e2) => m_of_ntheorem ctxt e1 RSN (1, m_of_ntheorem ctxt e2)
  | Thm_simplified (e1, e2) => asm_full_simplify (clear_simpset ctxt addsimps [m_of_ntheorem ctxt e2]) (m_of_ntheorem ctxt e1)
  | Thm_OF (e1, e2) => [m_of_ntheorem ctxt e2] MRS m_of_ntheorem ctxt e1
  | Thm_where (nth, l) => read_instantiate ctxt (List.map (fn (var, expr) => ((To_string var, 0), s_of_expr expr)) l) (m_of_ntheorem ctxt nth)
  | Thm_symmetric s => m_of_ntheorem ctxt (Thm_THEN (s, Thm_str (From.from_string "sym")))
  | Thm_of (nth, l) =>
      let val thm = m_of_ntheorem ctxt nth
          fun zip_vars _ [] = []
            | zip_vars (_ :: xs) (NONE :: rest) = zip_vars xs rest
            | zip_vars ((x, _) :: xs) (SOME t :: rest) = (x, t) :: zip_vars xs rest
            | zip_vars [] _ = error "More instantiations than variables in theorem" in
      read_instantiate ctxt (List.map (fn (v, expr) => (v, s_of_expr expr))
                                 (zip_vars (rev (Term.add_vars (Thm.full_prop_of thm) []))
                                           (List.map SOME l))) thm
      end
end

fun addsimp (l1, l2) ctxt0 = 
  fold (fn a => fn ctxt => ctxt addsimps ((Proof_Context.get_thms ctxt0 o To_string) a)) l1
  (ctxt0 addsimps (List.map (Proof_Context.get_thm ctxt0 o To_string) l2))

fun m_of_ntheorems ctxt = fn OCL.Thms_single thy => [m_of_ntheorem ctxt thy]
                           | OCL.Thms_mult thy => Proof_Context.get_thms ctxt (To_string thy)

fun m_of_ntheorems_l ctxt l = List.concat (map (m_of_ntheorems ctxt) l)

fun m_of_tactic expr = let open OCL open Method open OCL_overload in case expr of
    Tact_rule s => Basic (fn ctxt => rule [m_of_ntheorem ctxt s])
  | Tact_drule s => Basic (fn ctxt => drule 0 [m_of_ntheorem ctxt s])
  | Tact_erule s => Basic (fn ctxt => erule 0 [m_of_ntheorem ctxt s])
  | Tact_elim s => Basic (fn ctxt => elim [m_of_ntheorem ctxt s])
  | Tact_intro l => Basic (fn ctxt => intro (map (m_of_ntheorem ctxt) l))
  | Tact_subst_l (l, s) => Basic (fn ctxt => SIMPLE_METHOD' (EqSubst.eqsubst_tac ctxt (map (fn s => case Int.fromString (To_string s) of SOME i => i) l) [m_of_ntheorem ctxt s]))
  | Tact_insert l => Basic (fn ctxt => insert (m_of_ntheorems_l ctxt l))
  | Tact_plus t => Repeat1 (Then (List.map m_of_tactic t))
  | Tact_option t => Try (Then (List.map m_of_tactic t))
  | Tact_one (Simp_only l) => simp_tac (fn ctxt => clear_simpset ctxt addsimps (m_of_ntheorems_l ctxt l))
  | Tact_one (Simp_add_del (l_add, l_del)) => simp_tac (fn ctxt => ctxt addsimps (m_of_ntheorems_l ctxt l_add)
                                                                        delsimps (m_of_ntheorems_l ctxt l_del))
  | Tact_auto_simp_add_split (l_simp, l_split) =>
      Basic (fn ctxt => SIMPLE_METHOD (auto_tac (fold (fn (f, l) => fold f l)
              [(Simplifier.add_simp, m_of_ntheorems_l ctxt l_simp)
              ,(Splitter.add_split, List.map (Proof_Context.get_thm ctxt o To_string) l_split)]
              ctxt)))
  | Tact_rename_tac l => Basic (K (SIMPLE_METHOD' (rename_tac (List.map To_string l))))
  | Tact_case_tac e => Basic (fn ctxt => SIMPLE_METHOD' (Induct_Tacs.case_tac ctxt (s_of_expr e)))
  | Tact_blast n => Basic (case n of NONE => SIMPLE_METHOD' o blast_tac
                                   | SOME lim => fn ctxt => SIMPLE_METHOD' (depth_tac ctxt (To_nat lim)))
end

end

structure Shallow_ml = struct open Shallow_conv
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

fun then_tactic l = (Method.Then (map m_of_tactic l), (Position.none, Position.none))

fun local_terminal_proof o_by = let open OCL in case o_by of
   Tacl_done => Proof.local_done_proof
 | Tacl_sorry => Proof.local_skip_proof true
 | Tacl_by l_apply => Proof.local_terminal_proof (then_tactic l_apply, NONE)
end

fun global_terminal_proof o_by = let open OCL in case o_by of
   Tacl_done => Proof.global_done_proof
 | Tacl_sorry => Proof.global_skip_proof true
 | Tacl_by l_apply => Proof.global_terminal_proof (then_tactic l_apply, NONE)
end

fun proof_show f st = st
  |> Proof.enter_forward
  |> f
  |> Isar_Cmd.show [((@{binding ""}, []), [("?thesis", [])])] true

val apply_results = let open OCL_overload in fn OCL.App l => (fn st => st |> (Proof.apply_results (then_tactic l)) |> Seq.the_result "")
                     | OCL.App_using0 l => (fn st =>
                         let val ctxt = Proof.context_of st in
                         Proof.using [map (fn s => ([ s], [])) (m_of_ntheorems_l ctxt l)] st
                         end)
                     | OCL.App_unfolding0 l => (fn st =>
                         let val ctxt = Proof.context_of st in
                         Proof.unfolding [map (fn s => ([s], [])) (m_of_ntheorems_l ctxt l)] st
                         end)
                     | OCL.App_let (e1, e2) => proof_show (Proof.let_bind_cmd [([s_of_expr e1], s_of_expr e2)])
                     | OCL.App_have (n, e, e_pr) => proof_show (fn st => st
                         |> Isar_Cmd.have [((To_sbinding n, []), [(s_of_expr e, [])])] true
                         |> local_terminal_proof e_pr)
                     | OCL.App_fix l => proof_show (Proof.fix_cmd (List.map (fn i => (To_sbinding i, NONE, NoSyn)) l))
end

end

structure Shallow_main = struct open Shallow_conv open Shallow_ml
val OCL_main_thy = let open OCL open OCL_overload in (*let val f = *)fn
  Theory_dataty (Datatype (n, l)) =>
    (snd oo Datatype.add_datatype_cmd Datatype_Aux.default_config)
      [((To_sbinding n, [], NoSyn),
       List.map (fn (n, l) => (To_sbinding n, List.map (fn OCL.Opt o_ => To_string o_ ^ " option"
                                             |   Raw o_ => To_string o_) l, NoSyn)) l)]
| Theory_ty_synonym (Type_synonym (n, l)) =>
    (fn thy =>
     let val s_bind = To_sbinding n in
     (snd o Typedecl.abbrev_global (s_bind, [], NoSyn)
                                   (read_typ_syntax (SOME s_bind) thy (s_of_rawty l))) thy
     end)
| Theory_instantiation_class (Instantiation (n, n_def, expr)) =>
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
| Theory_defs_overloaded (Defs_overloaded (n, e)) =>
    Isar_Cmd.add_defs ((false, true), [((To_sbinding n, s_of_expr e), [])])
| Theory_consts_class (Consts_raw (n, ty, symb)) =>
    Sign.add_consts [( To_sbinding n
                     , s_of_rawty ty
                     , Mixfix ("(_) " ^ To_string symb, [], 1000))]
| Theory_definition_hol def =>
    let val (def, e) = case def of
        Definition e => (NONE, e)
      | Definition_abbrev (name, (abbrev, prio), e) =>
          (SOME ( To_sbinding name
                , NONE
                , Mixfix ("(1" ^ s_of_expr abbrev ^ ")", [], To_nat prio)), e)
      | Definition_abbrev0 (name, abbrev, e) =>
          (SOME ( To_sbinding name
                , NONE
                , Mixfix ("(" ^ s_of_expr abbrev ^ ")", [], 1000)), e) in
    in_local (snd o Specification.definition_cmd (def, ((@{binding ""}, []), s_of_expr e)) false)
    end
| Theory_lemmas_simp (Lemmas_simp_opt (simp, s, l)) =>
    in_local (fn lthy => (snd o Specification.theorems Thm.lemmaK
      [((To_sbinding s, List.map (fn s => Attrib.intern_src (Proof_Context.theory_of lthy) (Args.src ((s, []), Position.none)))
                          (if simp then ["simp", "code_unfold"] else [])),
        List.map (fn x => ([m_of_ntheorem lthy x], [])) l)]
      []
      false) lthy)
| Theory_lemmas_simp (Lemmas_simps (s, l)) =>
    in_local (fn lthy => (snd o Specification.theorems Thm.lemmaK
      [((To_sbinding s, List.map (fn s => Attrib.intern_src (Proof_Context.theory_of lthy) (Args.src ((s, []), Position.none)))
                          ["simp", "code_unfold"]),
        List.map (fn x => (Proof_Context.get_thms lthy (To_string x), [])) l)]
      []
      false) lthy)
| Theory_lemma_by (Lemma_by (n, l_spec, l_apply, o_by)) =>
      in_local (fn lthy =>
           Specification.theorem_cmd Thm.lemmaK NONE (K I)
             (@{binding ""}, []) [] [] (Element.Shows [((To_sbinding n, [])
                                                       ,[((String.concatWith (" " ^ (To_string OCL.unicode_Longrightarrow) ^ " ")
                                                             (List.map s_of_expr l_spec)), [])])])
             false lthy
        |> fold (apply_results o OCL.App) l_apply
        |> global_terminal_proof o_by)
| Theory_lemma_by (Lemma_by_assum (n, l_spec, concl, l_apply, o_by)) =>
      in_local (fn lthy =>
           Specification.theorem_cmd Thm.lemmaK NONE (K I)
             (To_sbinding n, [])
             []
             (List.map (fn (n, (b, e)) => Element.Assumes [((To_sbinding n, if b then [Args.src (("simp", []), Position.none)] else []), [(s_of_expr e, [])])]) l_spec)
             (Element.Shows [((@{binding ""}, []),[(s_of_expr concl, [])])])
             false lthy
        |> fold apply_results l_apply
        |> (case filter (fn OCL.App_let _ => true | OCL.App_have _ => true | OCL.App_fix _ => true | _ => false) l_apply of
              [] => global_terminal_proof o_by
            | _ :: l => let val arg = (NONE, true) in fn st => st
              |> local_terminal_proof o_by
              |> fold (K (Proof.local_qed arg)) l
              |> Proof.global_qed arg end))
| Theory_axiom (Axiom (n, e)) => #2 o Specification.axiomatization_cmd
                                     []
                                     [((To_sbinding n, []), [s_of_expr e])]
| Theory_section_title _ => I
| Theory_text _ => I
| Theory_ml ml => Code_printing.reflect_ml (case ml of Ml ml => s_of_sexpr ml)
| Theory_thm (Thm thm) => in_local (fn lthy =>
    let val () = writeln (Pretty.string_of (Proof_Context.pretty_fact lthy ("", List.map (m_of_ntheorem lthy) thm))) in
    lthy
    end)
(*in fn t => fn thy => f t thy handle ERROR s => (warning s; thy)
 end*)
end

fun OCL_main aux ret = let open OCL open OCL_overload in fn
  Isab_thy thy => ret o (OCL_main_thy thy)
| Isab_thy_generation_syntax _ => ret o I
| Isab_thy_ml_extended _ => ret o I
| Isab_thy_ocl_deep_embed_ast ocl => fn thy => aux (map2_ctxt_term (fn T_to_be_parsed s => From.from_p_term thy (String.implode s)
                                                                     | x => x) ocl) thy
end

end
(*val _ = print_depth 100*)
*}

subsection{* ... *}

ML{*

fun exec_deep (ocl, file_out_path_dep, seri_args, filename_thy, tmp_export_code, l_obj) thy0 =
  let open Generation_mode in
  let val i_of_arg = OCL.isabelle_of_ocl_embed OCL.isabelle_apply I in
  let fun def s = in_local (snd o Specification.definition_cmd (NONE, ((@{binding ""}, []), s)) false) in
  let val name_main = Deep.mk_free (Proof_Context.init_global thy0) Deep0.Export_code_env.Isabelle.argument_main [] in
  thy0 |> def (String.concatWith " " (  "(" (* polymorphism weakening needed by export_code *)
                                        ^ name_main ^ " :: (_ \<times> char list option) ocl_compiler_config_scheme)"
                                    :: "="
                                    :: To_string (i_of_arg (OCL.ocl_compiler_config_more_map (fn () => (l_obj, From.from_option From.from_string (Option.map (fn filename_thy => Deep.absolute_path filename_thy thy0) filename_thy))) ocl))
                                    :: []))
       |> Deep.export_code_cmd' seri_args tmp_export_code
            (fn (((_, _), msg), _) => fn err => if err <> 0 then error msg else ()) filename_thy [name_main]
       |> (fn l =>
             let val (l_warn, l) = (map fst l, map snd l) in
             if Deep.list_all_eq l then (List.concat l_warn, hd l) else error "There is an extracted language which does not produce a similar Isabelle content as the others"
             end)
       |> (fn (l_warn, s) =>
             let val () = writeln
               (case (file_out_path_dep, filename_thy) of
                  (SOME _, SOME _) => s
                | _ => String.concat (map ((fn s => s ^ "\n") o Active.sendback_markup [Markup.padding_command] o trim_line)
                   (String.tokens (fn c => From.from_char c = OCL.char_escape) s))) in
             fold (fn (out, err) => K ( writeln (Markup.markup Markup.keyword2 err)
                                      ; case trim_line out of
                                          "" => ()
                                        | out => writeln (Markup.markup Markup.keyword1 out))) l_warn () end)

  end end end end

fun outer_syntax_command mk_string cmd_spec cmd_descr parser get_oclclass =
  let open Generation_mode in
  Outer_Syntax.command cmd_spec cmd_descr
    (parser >> (fn name =>
      Toplevel.theory (fn thy =>
        let val (ocl, thy) =
        OCL.fold_list

          let val get_oclclass = get_oclclass name in
          fn Gen_syntax_print => (fn thy => let val _ = writeln (mk_string name) in (Gen_syntax_print, thy) end)
           | Gen_deep (ocl, file_out_path_dep, seri_args, filename_thy, tmp_export_code, skip_exportation) =>
              (fn thy0 =>
                let val obj = get_oclclass thy0
                  ; val l_obj = [obj] in
                thy0 |> (if skip_exportation then
                           K ()
                         else
                           exec_deep (OCL.d_file_out_path_dep_update (fn _ => NONE) ocl, file_out_path_dep, seri_args, NONE, tmp_export_code, l_obj))
                     |> K (Gen_deep (OCL.fold_thy_deep l_obj ocl, file_out_path_dep, seri_args, filename_thy, tmp_export_code, skip_exportation), thy0)
                end)
           | Gen_shallow (ocl, thy0) => fn thy =>
             let fun aux (ocl, thy) x =
                  OCL.fold_thy_shallow
                   (fn f => f () handle ERROR e =>
                     ( warning "Shallow Backtracking: HOL declarations occuring among OCL ones are ignored (if any)"
                       (* TODO automatically determine if there is such HOL declarations,
                               for raising earlier a specific error message *)
                     ; error e))
                   (fn _ => fn _ => thy0)
                   (fn l => fn (ocl, thy) =>
                     Shallow_main.OCL_main (fn x => fn thy => aux (ocl, thy) x) (pair ocl) l thy)
                   [x]
                   (ocl, thy)
                 val (ocl, thy) = aux (ocl, thy) (get_oclclass thy) in
             (Gen_shallow (ocl, thy0), thy)
             end
          end

          (case Symtab.lookup (Data_gen.get thy) Deep0.gen_empty of SOME l => l | _ => [Gen_syntax_print])
          thy
        in
        Data_gen.map (Symtab.update (Deep0.gen_empty, ocl)) thy end)))
  end
*}

subsection{* ... *}

ML{*
val () = let open Generation_mode in
  Outer_Syntax.command @{command_spec "generation_syntax"} "set the generating list"
    ((   parse_l' mode >> SOME
     || @{keyword "deep"} -- @{keyword "flush_all"} >> K NONE) >>
    (fn SOME x => f_command x
      | NONE =>
      Toplevel.theory (fn thy =>
        let val l = case Symtab.lookup (Data_gen.get thy) Deep0.gen_empty of SOME l => l | _ => []
            val l = List.concat (List.map (fn Gen_deep x => [x] | _ => []) l)
            val _ = case l of [] => warning "Nothing to perform." | _ => ()
            val thy =
        fold
          (fn (ocl, file_out_path_dep, seri_args, filename_thy, tmp_export_code, _) => fn thy0 =>
                thy0 |> let val (ocl, l_exec) = OCL.ocl_compiler_config_reset_all ocl in
                        exec_deep (ocl, file_out_path_dep, seri_args, filename_thy, tmp_export_code, l_exec) end
                     |> K thy0)
          l
          thy
        in
        thy end)))
end
*}

subsection{* ... *}

ML{*
structure USE_parse = struct
 fun optional f = Scan.optional (f >> SOME) NONE
 val colon = Parse.$$$ ":"
 fun repeat2 scan = scan ::: Scan.repeat1 scan

 fun outer_syntax_command2 mk_string cmd_spec cmd_descr parser v_true v_false get_oclclass =
   outer_syntax_command mk_string cmd_spec cmd_descr
     (optional (Parse.$$$ "[" |-- @{keyword "shallow"} --| Parse.$$$ "]") -- parser)
     (fn (is_shallow, use) => fn thy =>
        get_oclclass
          (if is_shallow = NONE then
             (OCL.T_to_be_parsed o From.from_string, v_true)
           else
             (From.from_p_term thy, v_false))
          use)
 (* *)
 datatype use_oclty = OclTypeBaseVoid
                    | OclTypeBaseBoolean
                    | OclTypeBaseInteger
                    | OclTypeBaseUnlimitednatural
                    | OclTypeBaseReal
                    | OclTypeBaseString
                    | OclTypeCollectionSet of use_oclty
                    | OclTypeCollectionSequence of use_oclty
                    | OclTypeRaw of binding (* FIXME use 'string' and Parse.typ *)

 datatype use_opt = Ordered | Subsets of binding | Union | Redefines of binding | Derived of string | Qualifier of (binding * use_oclty) list
 datatype use_operation_def = Expression of string | BlockStat

 fun from_oclty v = (fn OclTypeBaseVoid    => OCL.OclTy_base_void
                      | OclTypeBaseBoolean => OCL.OclTy_base_boolean
                      | OclTypeBaseInteger => OCL.OclTy_base_integer
                      | OclTypeBaseUnlimitednatural => OCL.OclTy_base_unlimitednatural
                      | OclTypeBaseReal    => OCL.OclTy_base_real
                      | OclTypeBaseString  => OCL.OclTy_base_string
                      | OclTypeCollectionSet l      => OCL.OclTy_collection (OCL.Set, from_oclty l)
                      | OclTypeCollectionSequence l => OCL.OclTy_collection (OCL.Sequence, from_oclty l)
                      | OclTypeRaw s       => OCL.OclTy_raw (From.from_binding s)) v

 val ident_dot_dot = Parse.sym_ident -- Parse.sym_ident (* "\<bullet>\<bullet>" *)
 val ident_star = Parse.sym_ident (* "*" *)
 (* *)
 fun use_type v = ((* collection *)
                   Parse.reserved "Set" |-- Parse.$$$ "(" |-- use_type --| Parse.$$$ ")" >> OclTypeCollectionSet
                || Parse.reserved "Sequence" |-- Parse.$$$ "(" |-- use_type --| Parse.$$$ ")" >> OclTypeCollectionSequence

                   (* base *)
                || Parse.reserved "Void" >> K OclTypeBaseVoid
                || Parse.reserved "Boolean" >> K OclTypeBaseBoolean
                || Parse.reserved "Integer" >> K OclTypeBaseInteger
                || Parse.reserved "UnlimitedNatural" >> K OclTypeBaseUnlimitednatural
                || Parse.reserved "Real" >> K OclTypeBaseReal
                || Parse.reserved "String" >> K OclTypeBaseString

                   (* *)
                || Parse.sym_ident (* "\<acute>" *) |-- Parse.binding --| Parse.sym_ident (* "\<acute>" *) >> OclTypeRaw) v

 val use_expression = Parse.alt_string
 val use_variableDeclaration = Parse.binding --| colon -- use_type
 val use_paramList = Parse.$$$ "(" |-- Parse.list use_variableDeclaration --| Parse.$$$ ")"
 val use_multiplicitySpec = ident_star || Parse.number
 val use_multiplicity = use_multiplicitySpec -- optional (ident_dot_dot |-- use_multiplicitySpec)
 val use_associationEnd =
      Parse.binding
   -- parse_l1' use_multiplicity
   -- optional (@{keyword "Role"} |-- Parse.binding)
   -- Scan.repeat (   @{keyword "Ordered"} >> K Ordered
                   || @{keyword "Subsets"} |-- Parse.binding >> Subsets
                   || @{keyword "Union"} >> K Union
                   || @{keyword "Redefines"} |-- Parse.binding >> Redefines
                   || @{keyword "Derived"} -- Parse.$$$ "=" |-- use_expression >> Derived
                   || @{keyword "Qualifier"} |-- use_paramList >> Qualifier)
   --| optional Parse.semicolon
 val use_blockStat = Parse.alt_string
 val use_prePostClause =
      (@{keyword "Pre"} || @{keyword "Post"})
   -- optional Parse.binding
   --| colon
   -- use_expression
 val use_invariantClause = Scan.optional (@{keyword "Existential"} >> K true) false
   --| @{keyword "Inv"}
   -- Parse.binding
   --| colon
   -- use_expression
 (* *)
 val class_def_list = Scan.optional (Parse.$$$ "<" |-- Parse.list1 Parse.binding) []
 val class_def_attr = Scan.optional (@{keyword "Attributes"}
   |-- Scan.repeat (Parse.binding --| colon -- use_type
                    --| optional Parse.semicolon)) []
 val class_def_oper = Scan.optional (@{keyword "Operations"}
   |-- Scan.repeat (   Parse.binding
                    -- use_paramList
                    -- optional (colon |-- use_type)
                    -- optional (Parse.$$$ "=" |-- use_expression || use_blockStat)
                    -- Scan.repeat use_prePostClause
                    --| optional Parse.semicolon)) []
 val class_def_constr = Scan.optional (@{keyword "Constraints"}
   |-- Scan.repeat use_invariantClause) []
end
*}

subsection{* Outer Syntax: (abstract) class *}

ML{*
datatype use_classDefinition = USE_class | USE_class_abstract

structure Outer_syntax_Pre_Post = struct
  fun make from_expr name_ty name_fun ty_arg ty_out expr =
        OCL.Ocl_ctxt_pre_post_ext
          ( From.from_binding name_ty
          , From.from_binding name_fun
          , From.from_list (From.from_pair From.from_binding USE_parse.from_oclty) ty_arg
          , From.from_option USE_parse.from_oclty ty_out
          , From.from_list (fn ((s_pre_post, _), expr) => ( if s_pre_post = "Pre" then OCL.OclCtxtPre else OCL.OclCtxtPost
                                                          , from_expr expr)) expr
          , ())

  fun make2 from_expr name_ty =
    map (fn ((((name_fun, ty_arg), ty_out), _), expr) =>
              make from_expr name_ty name_fun ty_arg ty_out expr)
end

structure Outer_syntax_Inv = struct
  fun make from_expr name l =
        OCL.Ocl_ctxt_inv_ext
          ( From.from_binding name
          , From.from_list (fn ((_, s), e) => (From.from_binding s, from_expr e)) l
          , ())
  fun make2 from_expr name_ty = map (fn l => make from_expr name_ty [l])
end

structure Outer_syntax_Class = struct
  fun make from_expr binding child attribute oper constr =
    (OCL.Ocl_class_raw_ext
         ( From.from_binding binding
         , From.from_list (From.from_pair From.from_binding USE_parse.from_oclty) attribute
         , Outer_syntax_Pre_Post.make2 from_expr binding oper
         , Outer_syntax_Inv.make2 from_expr binding constr
         , case child of [] => NONE | [x] => SOME (From.from_binding x)
         , From.from_unit ()))
end

local
 open USE_parse

 fun mk_classDefinition _ cmd_spec =
   outer_syntax_command2 @{make_string} cmd_spec "Class generation"
    (   Parse.binding
     -- class_def_list
     -- class_def_attr
     -- class_def_oper
     -- class_def_constr
     --| @{keyword "End"})
    OCL.OclAstClassRaw
    OCL.Ocl2AstClassRaw
    (fn (from_expr, OclAstClassRaw) =>
     fn ((((binding, child), attribute), oper), constr) =>
       OclAstClassRaw (Outer_syntax_Class.make from_expr binding child attribute oper constr))
in
val () = mk_classDefinition USE_class @{command_spec "Class"}
val () = mk_classDefinition USE_class_abstract @{command_spec "Abstract_class"}
end
*}

subsection{* Outer Syntax: association, composition, aggregation *}

ML{*
structure Outer_syntax_Association = struct
  val mk_mult = fn "*" => OCL.Mult_star
                 | s => OCL.Mult_nat (case Int.fromString s of SOME i => From.from_nat i)

  fun make ass_ty l =
    OCL.Ocl_association_ext
        ( ass_ty
        , List.map (fn (((cl_from, cl_mult), o_cl_attr), _) =>
            (From.from_binding cl_from, (OCL.OclMult (List.map (From.from_pair mk_mult (From.from_option mk_mult)) cl_mult), From.from_option From.from_binding o_cl_attr))) l
        , From.from_unit ())
end

local
 open USE_parse

 fun mk_associationDefinition ass_ty cmd_spec =
  outer_syntax_command @{make_string} cmd_spec ""
    (    Parse.binding
     --| @{keyword "Between"}
     -- repeat2 use_associationEnd
     --| @{keyword "End"})
    (fn (_, l) => fn _ =>
      OCL.OclAstAssociation (Outer_syntax_Association.make ass_ty l))
in
val () = mk_associationDefinition OCL.OclAssTy_association @{command_spec "Association"}
val () = mk_associationDefinition OCL.OclAssTy_composition @{command_spec "Composition"}
val () = mk_associationDefinition OCL.OclAssTy_aggregation @{command_spec "Aggregation"}
end
*}

subsection{* Outer Syntax: (abstract) associationclass *}

ML{*
datatype use_associationClassDefinition = USE_associationclass | USE_associationclass_abstract

local
 open USE_parse

 fun mk_associationClassDefinition f cmd_spec =
  outer_syntax_command2 @{make_string} cmd_spec ""
    (   Parse.binding
     -- class_def_list
     -- (Scan.optional (@{keyword "Between"}
                        |-- repeat2 use_associationEnd >> SOME) NONE)
     -- class_def_attr
     -- class_def_oper
     -- class_def_constr
     -- optional Parse.alt_string
     --| @{keyword "End"})
    OCL.OclAstAssClass
    OCL.Ocl2AstAssClass
    (fn (from_expr, OclAstAssClass) =>
     fn ((((((binding, child), o_l), attribute), oper), constr), _) =>
        OclAstAssClass (OCL.OclAssClass ( Outer_syntax_Association.make OCL.OclAssTy_association (case o_l of NONE => [] | SOME l => l)
                                          , Outer_syntax_Class.make from_expr binding child attribute oper constr)))
in
val () = mk_associationClassDefinition USE_associationclass @{command_spec "Associationclass"}
val () = mk_associationClassDefinition USE_associationclass_abstract @{command_spec "Abstract_associationclass"}
end
*}

subsection{* Outer Syntax: context *}

ML{*
datatype ('a, 'b) use_context = USE_context_invariant of 'a
                              | USE_context_pre_post of 'b
local
 open USE_parse
in
val () =
  outer_syntax_command2 @{make_string} @{command_spec "Context"} ""
    (
    ((* use_prePost *)
         Parse.binding
     --| Parse.$$$ "::"
     -- Parse.binding
     -- use_paramList
     -- optional (colon |-- use_type)
     -- Scan.repeat1 use_prePostClause) >> USE_context_pre_post
    ||
    ((* use_invariant *)
        optional (Parse.list1 Parse.binding --| colon)
     -- Parse.binding
     -- Scan.repeat use_invariantClause
     >> USE_context_invariant)
    )
    (OCL.OclAstCtxtPrePost, OCL.OclAstCtxtInv)
    (OCL.Ocl2AstCtxtPrePost, OCL.Ocl2AstCtxtInv)
    (fn (from_expr, (OclAstCtxtPrePost, OclAstCtxtInv)) =>
     fn USE_context_pre_post ((((name_ty, name_fun), ty_arg), ty_out), expr) =>
        OclAstCtxtPrePost (Outer_syntax_Pre_Post.make from_expr name_ty name_fun ty_arg ty_out expr)
      | USE_context_invariant ((_, name), l) =>
        OclAstCtxtInv (Outer_syntax_Inv.make from_expr name l))
end
*}

subsection{* Outer Syntax: Class.end *}

ML{*
val () =
  outer_syntax_command @{make_string} @{command_spec "Class.end"} "Class generation"
    (Scan.optional (Parse.binding >> SOME) NONE)
    (fn _ => fn _ =>
       OCL.OclAstFlushAll (OCL.OclFlushAll))
*}

subsection{* Outer Syntax: \text{Define\_base}, Instance, \text{Define\_state} *}

ML{*

datatype ocl_term = OclTermBase of OCL.ocl_def_base
                  | OclTerm of binding
                  | OclOid of int
(*
datatype 'a ocl_l_attr = Ocl_l_attr of 'a
                    | Ocl_l_attr_cast of 'a ocl_prop * binding

and 'a ocl_prop = Ocl_prop of 'a ocl_l_attr (* l_inh *) * 'a (* l_attr *)

datatype ocl_prop_main = Ocl_prop_main of ((binding * ocl_term) list) ocl_prop
*)

val ocl_term0 =
     Parse.number >> (OCL.OclDefInteger o From.from_string)
  || Parse.float_number >> (OCL.OclDefReal o (From.from_pair From.from_string From.from_string o
       (fn s => case String.tokens (fn #"." => true | _ => false) s of [l1,l2] => (l1,l2))))
  || Parse.string >> (OCL.OclDefString o From.from_string)
val ocl_term = ocl_term0 >> OclTermBase
  || Parse.binding >> OclTerm
  || @{keyword "self"} |-- Parse.nat >> OclOid
val list_attr0 = Parse.binding -- (Parse.$$$ "=" |--
  (ocl_term >> (fn x => [x])
  || parse_l' ocl_term))
val list_attr00 = parse_l list_attr0
val list_attr = list_attr00 >> (fn res => (res, [] : binding list))
fun list_attr_cast00 e =
  (annot_ty list_attr00 >> (fn (res, x) => (res, [x]))
  || annot_ty list_attr_cast00 >> (fn ((res, xs), x) => (res, x :: xs))) e
val list_attr_cast = list_attr_cast00 >> (fn (res, l) => (res, rev l))

val () =
  outer_syntax_command @{make_string} @{command_spec "Define_base"} ""
    (parse_l' ocl_term0)
    (K o OCL.OclAstDefBaseL o OCL.OclDefBase)

datatype state_content = ST_l_attr of (binding * ocl_term list) list * binding (* ty *)
                       | ST_skip
                       | ST_binding of binding

val state_parse =
  (@{keyword "defines"} |-- parse_l' (list_attr_cast00 >> (fn (res, [x]) => ST_l_attr (res, x))
                                     || Parse.binding >> ST_binding))
  || @{keyword "skip"} >> K [ST_skip]

local
  fun get_oclinst l _ =
    OCL.OclInstance (map (fn ((name,typ), (l_attr, is_cast)) =>
        let val of_base = fn OclTermBase s => OCL.ShallB_term s
                           | OclTerm s => OCL.ShallB_str (From.from_binding s)
                           | OclOid n => OCL.ShallB_self (From.from_internal_oid (From.from_nat n))
            val f = map (fn (attr, ocl) => (From.from_binding attr,
                      case ocl of [x] => OCL.Shall_base (of_base x)
                                | l => OCL.Shall_list (map of_base l)))
            val l_attr =
              fold
                (fn b => fn acc => OCL.OclAttrCast (From.from_binding b, acc, []))
                is_cast
                (OCL.OclAttrNoCast (f l_attr)) in
        OCL.Ocl_instance_single_ext
          (From.from_binding name, From.from_binding typ, l_attr, From.from_unit ()) end) l)
in
val () =
  outer_syntax_command @{make_string} @{command_spec "Instance"} ""
    (Parse.and_list1 (Parse.binding --| @{keyword "::"}
                      -- Parse.binding --| @{keyword "="}
                      -- (list_attr || list_attr_cast)))
    (OCL.OclAstInstance oo get_oclinst)

val () =
  outer_syntax_command @{make_string} @{command_spec "Define_state"} ""
    (Parse.binding --| @{keyword "="}
     -- parse_l' state_parse)
     (fn (name, l) => fn thy =>
      OCL.OclAstDefState (OCL.OclDefSt (From.from_binding name,
        map (fn ST_l_attr (l, ty) => OCL.OclDefCoreAdd (case get_oclinst [((@{binding ""}, ty), (l, []))] thy of OCL.OclInstance [x] => x)
              | ST_skip => OCL.OclDefCoreSkip
              | ST_binding b => OCL.OclDefCoreBinding (From.from_binding b)) (List.concat l))))
end
*}

subsection{* Outer Syntax: \text{Define\_pre\_post} *}

ML{*
val () =
  outer_syntax_command @{make_string} @{command_spec "Define_pre_post"} ""
    (Parse.binding -- Parse.binding)
    (fn (s_pre, s_post) => fn _ =>
      OCL.OclAstDefPrePost (OCL.OclDefPP (From.from_binding s_pre, From.from_binding s_post)))

(*val _ = print_depth 100*)
*}

end
