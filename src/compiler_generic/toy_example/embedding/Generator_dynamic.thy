(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Generator_dynamic.thy ---
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013-2015 Université Paris-Sud, France
 *               2013-2015 IRT SystemX, France
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

theory Generator_dynamic
imports Printer
        "../../isabelle_home/src/HOL/Isabelle_Main2"
  keywords (* ocl (USE tool) *)
           "Between"
           "Attributes" "Operations" "Constraints"
           "Role"
           "Ordered" "Subsets" "Union" "Redefines" "Derived" "Qualifier"
           "Existential" "Inv" "Pre" "Post"
           (* ocl (added) *)
           "self"
           "Nonunique" "Sequence_"

           (* hol syntax *)
           "output_directory"
           "THEORY" "IMPORTS" "SECTION" "SORRY" "no_dirty"
           "deep" "shallow" "syntax_print" "skip_export"
           "generation_semantics"
           "flush_all"

           (* hol semantics *)
           "design" "analysis" "oid_start"

       and (* ocl (USE tool) *)
           "Enum"
           "Abstract_class" "record'"
           "record_link" "Composition" "Aggregation"
           "Abstract_associationclass" "Associationclass"
           "set_cartouche_type"
           (* ocl (added) *)
           "End" "def_record" "BaseType" "def_record'" "binary_record"

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
code_reflect' open OCL
   functions (* OCL compiler as monadic combinators for deep and shallow *)
             fold_thy_deep fold_thy_shallow

             (* printing the HOL AST to (shallow Isabelle) string *)
             write_file

             (* manipulating the compiling environment *)
             compiler_env_config_reset_all compiler_env_config_update oidInit D_output_header_thy_update map2_ctxt_term check_export_code

             (* printing the OCL AST to (deep Isabelle) string *)
             isabelle_apply isabelle_of_ocl_embed

ML{*
 val To_string0 = String.implode o OCL.to_list
 fun To_nat (Code_Numeral.Nat i) = i
*}

ML{*
structure From = struct
 open OCL
 val from_char = I
 val from_string = OCL.SS_base o OCL.ST
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

 val from_pure_indexname = OCL.Pure_Indexname o from_pair from_string from_nat
 val from_pure_class = OCL.Pure_Class o from_string
 val from_pure_sort = OCL.Pure_Sort o from_list from_pure_class
 fun from_pure_typ e = (fn
     Type (s, l) => (OCL.Pure_Type o from_pair from_string (from_list from_pure_typ)) (s, l)
   | TFree (s, sort) => (OCL.Pure_TFree o from_pair from_string from_pure_sort) (s, sort)
   | TVar (i, sort) => (OCL.Pure_TVar o from_pair from_pure_indexname from_pure_sort) (i, sort)
  ) e
 fun from_pure_term e = (fn
     Const (s, typ) => (OCL.Pure_Const o from_pair from_string from_pure_typ) (s, typ)
   | Free (s, typ) => (OCL.Pure_Free o from_pair from_string from_pure_typ) (s, typ)
   | Var (i, typ) => (OCL.Pure_Var o from_pair from_pure_indexname from_pure_typ) (i, typ)
   | Bound i => (OCL.Pure_Bound o from_nat) i
   | Abs (s, typ, term) => (OCL.Pure_Abs o from_pair3 from_string from_pure_typ from_pure_term) (s, typ, term)
   | op $ (term1, term2) => (OCL.Pure_App o from_pair from_pure_term from_pure_term) (term1, term2)
  ) e

 fun from_p_term thy expr =
   OCL.T_pure (from_pure_term (Syntax.read_term (Proof_Context.init_global thy) expr))
end
*}

ML{*
fun in_local decl thy =
  thy
  |> Named_Target.theory_init
  |> decl
  |> Local_Theory.exit_global
*}

ML{* fun List_mapi f = OCL.mapi (f o To_nat) *}

ML{*
structure Ty' = struct
fun check l_oid l =
  let val Mp = OCL.map_prod
      val Me = String.explode
      val Mi = String.implode
      val Ml = map in
  OCL.check_export_code
    (writeln o Mi)
    (warning o Mi)
    (writeln o Markup.markup Markup.bad o Mi)
    (error o To_string0)
    (Ml (Mp I Me) l_oid)
    ((OCL.SS_base o OCL.ST) l)
  end
end
*}

subsection{* General Compiling Process: Deep (with reflection) *}

ML{*
structure Deep0 = struct

fun apply_hs_code_identifiers ml_module thy =
  let fun mod_hs (fic, ml_module) = Code_Symbol.Module (fic, [("Haskell", SOME ml_module)]) in
  fold (Code_Target.set_identifiers o mod_hs)
    (map (fn x => (Context.theory_name x, ml_module))
         (* list of .hs files that will be merged together in "ml_module" *)
         ( thy
           :: (* we over-approximate the set of compiler files *)
              Context.ancestors_of thy)) thy end

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
             fun ml l =
               List.concat
               [ [ "ML{" ^ esc_star ]
               , map (fn s => s ^ ";") l
               , [ esc_star ^ "}"] ]
             val () = 
               let val fic = mk_fic (SML.Filename.function ml_ext_ml)
                   val _ = if File.exists fic then () else error "zzzzzz" in
               (* replace ("\\" ^ "<") by ("\\\060") in 'fic' *)
               File.write_list fic
                 (map (fn s => 
                         (if s = "" then
                           ""
                         else
                           String.concatWith "\\"
                             (map (fn s => 
                                     let val l = String.size s in
                                     if l > 0 andalso String.sub (s,0) = #"<" then
                                       "\\060" ^ String.substring (s, 1, String.size s - 1)
                                     else
                                       s end)
                                  (String.fields (fn c => c = #"\\") s))) ^ "\n")
                      (File.read_lines fic))
               end in
         File.write_list (mk_fic (SML.Filename.main_fic ml_ext_thy))
           (map (fn s => s ^ "\n") (List.concat
             [ [ "theory " ^ SML.main
               , "imports Main"
               , "begin"
               , "declare [[ML_print_depth = 500]]" (* any large number so that @{make_string} displays all the expression *) ]
             , ml [ "val stdout_file = Unsynchronized.ref (File.read (Path.make [\"" ^ SML.Filename.stdout ml_ext_ml ^ "\"]))"
                  , "use \"" ^ SML.Filename.argument ml_ext_ml ^ "\"" ]
             , ml let val arg = "argument" in
                  [ "val " ^ arg ^ " = XML.content_of (YXML.parse_body (@{make_string} (" ^ ml_module ^ "." ^
                    mk_free (Proof_Context.init_global thy) Isabelle.argument_main ([]: (string * string) list) ^ ")))"
                  , "use \"" ^ SML.Filename.function ml_ext_ml ^ "\""
                  , "ML_Context.eval_source (ML_Compiler.verbose false ML_Compiler.flags) (Input.source false (\"let open " ^ ml_module ^ " in " ^ Isabelle.function ^ " (\" ^ " ^ arg ^ " ^ \") end\") (Position.none, Position.none) )" ]
                  end
             , [ "end" ]]))
         end
    , fn tmp_export_code => fn tmp_file =>
        let val stdout_file = Isabelle_System.create_tmp_path "stdout_file" "thy"
            val () = File.write (Path.append tmp_export_code (Path.make [SML.Filename.stdout ml_ext_ml])) (Path.implode (Path.expand stdout_file))
            val (l, (_, exit_st)) =
              compile [ "mv " ^ tmp_file ^ " " ^ Path.implode (Path.append tmp_export_code (Path.make [SML.Filename.argument ml_ext_ml]))
                      , "cd " ^ Path.implode tmp_export_code ^
                        " && echo 'use_thy \"" ^ SML.main ^
                        "\";' | " ^
                        Path.implode (Path.expand (Path.append (Path.variable "ISABELLE_HOME") (Path.make ["bin", "isabelle"]))) ^ " console" ]
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

fun absolute_path filename thy = Path.implode (Path.append (Resources.master_directory thy) (Path.explode filename))

fun export_code_tmp_file seris g =
  fold
    (fn ((ml_compiler, ml_module), export_arg) => fn f => fn g =>
      f (fn accu =>
        let val tmp_name = Context.theory_name @{theory} in
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
          val _ = Isabelle_Code_Target.export_code_cmd
        false
        (if mem_scala then Deep0.Export_code_env.Isabelle.function :: raw_cs else raw_cs)
        seris
        (Proof_Context.init_global
           let val v = Deep0.apply_hs_code_identifiers Deep0.Export_code_env.Haskell.argument thy in
           if mem_scala then Code_printing.apply_code_printing v else v end) in
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

fun scan thy pos str =
  Source.of_string str
  |> Symbol.source
  |> Token.source (Thy_Header.get_keywords' thy) pos
  |> Source.exhaust;

fun mk_term ctxt s = fst (Scan.pass (Context.Proof ctxt) Args.term (scan ctxt Position.none s))

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
fun p_gen f g =  f "[" "]" g
              (*|| f "{" "}" g*)
              || f "(" ")" g
fun paren f = p_gen (fn s1 => fn s2 => fn f => Parse.$$$ s1 |-- f --| Parse.$$$ s2) f
fun parse_l f = Parse.$$$ "[" |-- Parse.!!! (Parse.list f --| Parse.$$$ "]")
fun parse_l' f = Parse.$$$ "[" |-- Parse.list f --| Parse.$$$ "]"
fun parse_l1' f = Parse.$$$ "[" |-- Parse.list1 f --| Parse.$$$ "]"
fun annot_ty f = Parse.$$$ "(" |-- f --| Parse.$$$ "::" -- Parse.binding --| Parse.$$$ ")"
*}

ML{*
structure Generation_mode = struct

datatype internal_deep = Internal_deep of (string * (string list (* imports *) * string (* import optional (bootstrap) *))) option
                                        * ((bstring (* compiler *) * bstring (* main module *) ) * Token.T list) list (* seri_args *)
                                        * bstring option (* filename_thy *)
                                        * Path.T (* tmp dir export_code *)
                                        * bool (* true: skip preview of code exportation *)

datatype 'a generation_mode = Gen_deep of unit OCL.compiler_env_config_ext
                                        * internal_deep
                            | Gen_shallow of unit OCL.compiler_env_config_ext
                                           * 'a (* theory init *)
                            | Gen_syntax_print of int option

structure Data_gen = Theory_Data
  (type T = theory generation_mode list Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true))

val code_expr_argsP = Scan.optional (@{keyword "("} |-- Parse.args --| @{keyword ")"}) []

val parse_scheme = @{keyword "design"} >> K OCL.Gen_only_design || @{keyword "analysis"} >> K OCL.Gen_only_analysis

val parse_sorry_mode = 
  Scan.optional (  @{keyword "SORRY"} >> K (SOME OCL.Gen_sorry)
                || @{keyword "no_dirty"} >> K (SOME OCL.Gen_no_dirty)) NONE

val parse_deep =
     Scan.optional (@{keyword "skip_export"} >> K true) false
  -- Scan.optional (((Parse.$$$ "(" -- @{keyword "THEORY"}) |-- Parse.name -- ((Parse.$$$ ")" -- Parse.$$$ "(" -- @{keyword "IMPORTS"}) |-- parse_l' Parse.name -- Parse.name) --| Parse.$$$ ")") >> SOME) NONE
  -- Scan.optional (@{keyword "SECTION"} >> K true) false
  -- parse_sorry_mode
  -- (* code_expr_inP *) parse_l1' (@{keyword "in"} |-- (Parse.name
        -- Scan.optional (@{keyword "module_name"} |-- Parse.name) ""
        -- code_expr_argsP))
  -- Scan.optional ((Parse.$$$ "(" -- @{keyword "output_directory"}) |-- Parse.name --| Parse.$$$ ")" >> SOME) NONE

val parse_sem_ocl =
  let val z = 0 in
      Scan.optional (paren (@{keyword "generation_semantics"}
                     |-- paren (parse_scheme
                                -- Scan.optional ((Parse.$$$ "," -- @{keyword "oid_start"}) |-- Parse.nat) z)))
                    (OCL.Gen_default, z)
  end

val mode =
  let fun mk_ocl output_disable_thy output_header_thy oid_start design_analysis sorry_mode dirty =
    OCL.compiler_env_config_empty
                    (From.from_bool output_disable_thy)
                    (From.from_option (From.from_pair From.from_string (From.from_pair (From.from_list From.from_string) From.from_string)) output_header_thy)
                    (OCL.oidInit (From.from_internal_oid (From.from_nat oid_start)))
                    design_analysis
                    (sorry_mode, dirty) in

     @{keyword "deep"} |-- parse_sem_ocl -- parse_deep >> (fn ((design_analysis, oid_start), (((((skip_exportation, output_header_thy), output_disable_thy), sorry_mode), seri_args), filename_thy)) =>
       fn ctxt =>
         Gen_deep ( mk_ocl (not output_disable_thy) output_header_thy oid_start design_analysis sorry_mode (Config.get ctxt quick_and_dirty)
                  , Internal_deep (output_header_thy, seri_args, filename_thy, Isabelle_System.create_tmp_path "deep_export_code" "", skip_exportation)))
  || @{keyword "shallow"} |-- parse_sem_ocl -- parse_sorry_mode >> (fn ((design_analysis, oid_start), sorry_mode) =>
       fn ctxt =>
       Gen_shallow (mk_ocl true NONE oid_start design_analysis sorry_mode (Config.get ctxt quick_and_dirty), ()))
  || (@{keyword "syntax_print"} |-- Scan.optional (Parse.number >> SOME) NONE) >> (fn n => K (Gen_syntax_print (case n of NONE => NONE | SOME n => Int.fromString n)))
  end


fun f_command l_mode =
      Toplevel.theory (fn thy =>
        let val (l_mode, thy) = OCL.mapM
          (fn Gen_shallow (ocl, ()) => let val thy0 = thy in
                                       fn thy => (Gen_shallow (ocl, thy0), thy) end
            | Gen_syntax_print n => (fn thy => (Gen_syntax_print n, thy))
            | Gen_deep (ocl, Internal_deep (output_header_thy, seri_args, filename_thy, tmp_export_code, skip_exportation)) => fn thy =>
                let val _ = warning ("remove the directory (at the end): " ^ Path.implode (Path.expand tmp_export_code))
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
                    val _ = Isabelle_Code_Target.export_code_cmd
                              (List.exists (fn (((("SML", _), _), _), _) => true | _ => false) seri_args')
                              [Deep0.Export_code_env.Isabelle.function]
                              (List.map fst seri_args')
                              (Proof_Context.init_global (Code_printing.apply_code_printing (Deep0.apply_hs_code_identifiers Deep0.Export_code_env.Haskell.function thy)))
                    val () = fold (fn ((((ml_compiler, ml_module), _), _), mk_fic) => fn _ =>
                      Deep0.find_init ml_compiler mk_fic ml_module Deep.mk_free thy) seri_args' () in
                (Gen_deep (ocl, Internal_deep (output_header_thy, seri_args, filename_thy, tmp_export_code, skip_exportation)), thy) end)
          let val ctxt = Proof_Context.init_global thy in
              map (fn f => f ctxt) l_mode
          end
          thy in
        Data_gen.map (Symtab.map_default (Deep0.gen_empty, l_mode) (fn _ => l_mode)) thy
        end)

fun update_compiler_config f =
  Data_gen.map
    (Symtab.map_entry
      Deep0.gen_empty
      (fn l_mode =>
        map (fn Gen_deep (ocl, d) => Gen_deep (OCL.compiler_env_config_update f ocl, d)
              | Gen_shallow (ocl, thy) => Gen_shallow (OCL.compiler_env_config_update f ocl, thy)
              | Gen_syntax_print n => Gen_syntax_print n) l_mode))
end
*}

subsection{* General Compiling Process: Shallow *}

ML{*
structure OCL_overload = struct
  val s_of_rawty = OCL.s_of_rawty To_string0
  val s_of_expr = OCL.s_of_expr To_string0 (Int.toString o To_nat)
  val s_of_sexpr = OCL.s_of_sexpr To_string0 (Int.toString o To_nat)
  val fold = fold
end
*}

ML{*
structure Shallow_conv = struct
 fun To_binding s = Binding.make (s, Position.none)
 val To_sbinding = To_binding o To_string0

fun simp_meth_gen g f = Method.Basic (fn ctxt => SIMPLE_METHOD (g (asm_full_simp_tac (f ctxt))))
val simp_tac = simp_meth_gen (fn f => f 1)
val simp_all_tac = simp_meth_gen (CHANGED_PROP o PARALLEL_GOALS o ALLGOALS)

datatype ty_thm = Thm_single of thm
                | Thm_mult of thm list

fun m_of_ntheorem0 ctxt = let open OCL open OCL_overload val S = fn Thm_single t => t
                                                         val M = fn Thm_mult t => t in
 fn Thm_thm s => Thm_single (Proof_Context.get_thm ctxt (To_string0 s))
  | Thm_thms s => Thm_mult (Proof_Context.get_thms ctxt (To_string0 s))
  | Thm_THEN (e1, e2) => 
      (case (m_of_ntheorem0 ctxt e1, m_of_ntheorem0 ctxt e2) of
         (Thm_single e1, Thm_single e2) => Thm_single (e1 RSN (1, e2))
       | (Thm_mult e1, Thm_mult e2) => Thm_mult (e1 RLN (1, e2)))
  | Thm_simplified (e1, e2) => Thm_single (asm_full_simplify (clear_simpset ctxt addsimps [S (m_of_ntheorem0 ctxt e2)]) (S (m_of_ntheorem0 ctxt e1)))
  | Thm_OF (e1, e2) => Thm_single ([S (m_of_ntheorem0 ctxt e2)] MRS (S (m_of_ntheorem0 ctxt e1)))
  | Thm_where (nth, l) => Thm_single (Rule_Insts.where_rule ctxt (List.map (fn (var, expr) => (((To_string0 var, 0), Position.none), s_of_expr expr)) l) [] (S (m_of_ntheorem0 ctxt nth)))
  | Thm_symmetric e1 => 
      let val e2 = S (m_of_ntheorem0 ctxt (Thm_thm (From.from_string "sym"))) in
        case m_of_ntheorem0 ctxt e1 of
          Thm_single e1 => Thm_single (e1 RSN (1, e2))
        | Thm_mult e1 => Thm_mult (e1 RLN (1, [e2]))
      end
  | Thm_of (nth, l) => Thm_single (Rule_Insts.of_rule ctxt (List.map (SOME o s_of_expr) l, []) [] (S (m_of_ntheorem0 ctxt nth)))
end

fun m_of_ntheorem ctxt s = case (m_of_ntheorem0 ctxt s) of Thm_single t => t

fun addsimp (l1, l2) ctxt0 = 
  fold (fn a => fn ctxt => ctxt addsimps ((Proof_Context.get_thms ctxt0 o To_string0) a)) l1
  (ctxt0 addsimps (List.map (Proof_Context.get_thm ctxt0 o To_string0) l2))

fun m_of_ntheorems ctxt =
  let fun f thy = case (m_of_ntheorem0 ctxt thy) of Thm_mult t => t
                                                  | Thm_single t => [t] in
  fn OCL.Thms_single thy => f thy
   | OCL.Thms_mult thy => f thy
  end

fun m_of_ntheorems' ctxt = m_of_ntheorems ctxt o OCL.Thms_single

fun m_of_ntheorems_l ctxt l = List.concat (map (m_of_ntheorems ctxt) l)

fun s_simp_only l ctxt = clear_simpset ctxt addsimps (m_of_ntheorems_l ctxt l)
fun s_simp_add_del_split (l_add, l_del, l_split) ctxt =
  fold Splitter.add_split (m_of_ntheorems_l ctxt l_split)
                          (ctxt addsimps (m_of_ntheorems_l ctxt l_add)
                                delsimps (m_of_ntheorems_l ctxt l_del))

fun m_of_tactic expr = let open OCL open Method open OCL_overload in case expr of
    Method_rule o_s => Basic (fn ctxt => METHOD (HEADGOAL o Isabelle_Classical.rule_tac ctxt
                                                  (case o_s of NONE => []
                                                             | SOME s => [m_of_ntheorem ctxt s])))
  | Method_drule s => Basic (fn ctxt => drule ctxt 0 [m_of_ntheorem ctxt s])
  | Method_erule s => Basic (fn ctxt => erule ctxt 0 [m_of_ntheorem ctxt s])
  | Method_elim s => Basic (fn ctxt => elim ctxt [m_of_ntheorem ctxt s])
  | Method_intro l => Basic (fn ctxt => intro ctxt (map (m_of_ntheorem ctxt) l))
  | Method_subst (asm, l, s) => Basic (fn ctxt => 
      SIMPLE_METHOD' ((if asm then
                         EqSubst.eqsubst_asm_tac
                       else
                         EqSubst.eqsubst_tac) ctxt (map (fn s => case Int.fromString (To_string0 s) of
                                                                   SOME i => i) l) [m_of_ntheorem ctxt s]))
  | Method_insert l => Basic (fn ctxt => insert (m_of_ntheorems_l ctxt l))
  | Method_plus t => Combinator (no_combinator_info, Repeat1, [Combinator (no_combinator_info, Then, List.map m_of_tactic t)])
  | Method_option t => Combinator (no_combinator_info, Try, [Combinator (no_combinator_info, Then, List.map m_of_tactic t)])
  | Method_or t => Combinator (no_combinator_info, Orelse, List.map m_of_tactic t)
  | Method_one (Method_simp_only l) => simp_tac (s_simp_only l)
  | Method_one (Method_simp_add_del_split l) => simp_tac (s_simp_add_del_split l)
  | Method_all (Method_simp_only l) => simp_all_tac (s_simp_only l)
  | Method_all (Method_simp_add_del_split l) => simp_all_tac (s_simp_add_del_split l)
  | Method_auto_simp_add_split (l_simp, l_split) =>
      Basic (fn ctxt => SIMPLE_METHOD (auto_tac (fold (fn (f, l) => fold f l)
              [(Simplifier.add_simp, m_of_ntheorems_l ctxt l_simp)
              ,(Splitter.add_split, List.map (Proof_Context.get_thm ctxt o To_string0) l_split)]
              ctxt)))
  | Method_rename_tac l => Basic (K (SIMPLE_METHOD' (Tactic.rename_tac (List.map To_string0 l))))
  | Method_case_tac e => Basic (fn ctxt => SIMPLE_METHOD' (Induct_Tacs.case_tac ctxt (s_of_expr e) [] NONE))
  | Method_blast n => Basic (case n of NONE => SIMPLE_METHOD' o blast_tac
                                   | SOME lim => fn ctxt => SIMPLE_METHOD' (depth_tac ctxt (To_nat lim)))
  | Method_clarify => Basic (fn ctxt => (SIMPLE_METHOD' (fn i => CHANGED_PROP (clarify_tac ctxt i))))
  | Method_metis (l_opt, l) =>
      Basic (fn ctxt => (METHOD oo Isabelle_Metis_Tactic.metis_method)
                          ( (if l_opt = [] then NONE else SOME (map To_string0 l_opt), NONE)
                          , map (m_of_ntheorem ctxt) l)
                          ctxt)
end

end

structure Shallow_ml = struct open Shallow_conv
fun perform_instantiation thy tycos vs f_eq add_def tac (*add_eq_thms*) =
    thy
    |> Class.instantiation (tycos, vs, f_eq)
    |> fold_map add_def tycos
    |-> Class.prove_instantiation_exit_result (map o Morphism.thm) tac
(*    |-> fold Code.del_eqn
    |> fold add_eq_thms tycos*)
    |-> K I

fun then_tactic l = let open Method in (Combinator (no_combinator_info, Then, map m_of_tactic l), (Position.none, Position.none)) end

fun local_terminal_proof o_by = let open OCL in case o_by of
   Command_done => Proof.local_done_proof
 | Command_sorry => Proof.local_skip_proof true
 | Command_by l_apply => Proof.local_terminal_proof (then_tactic l_apply, NONE)
end

fun global_terminal_proof o_by = let open OCL in case o_by of
   Command_done => Proof.global_done_proof
 | Command_sorry => Proof.global_skip_proof true
 | Command_by l_apply => Proof.global_terminal_proof (then_tactic l_apply, NONE)
end

fun proof_show_gen f thes st = st
  |> Proof.enter_forward
  |> f
  |> Isar_Cmd.show [((@{binding ""}, []), [(thes, [])])] true

val applyE_results = let open OCL_overload in
                     fn OCL.Command_apply_end l => (fn st => st |> (Proof.apply_end_results (then_tactic l)) |> Seq.the_result "")
end

val apply_results = let open OCL_overload
                        val thesis = "?thesis"
                        fun proof_show f = proof_show_gen f thesis in
                    fn OCL.Command_apply l => (fn st => st |> (Proof.apply_results (then_tactic l)) |> Seq.the_result "")
                     | OCL.Command_using l => (fn st =>
                         let val ctxt = Proof.context_of st in
                         Proof.using [map (fn s => ([ s], [])) (m_of_ntheorems_l ctxt l)] st
                         end)
                     | OCL.Command_unfolding l => (fn st =>
                         let val ctxt = Proof.context_of st in
                         Proof.unfolding [map (fn s => ([s], [])) (m_of_ntheorems_l ctxt l)] st
                         end)
                     | OCL.Command_let (e1, e2) => proof_show (Proof.let_bind_cmd [([s_of_expr e1], s_of_expr e2)])
                     | OCL.Command_have (n, b, e, e_pr) => proof_show (fn st => st
                         |> Isar_Cmd.have [( (To_sbinding n, if b then [Token.src ("simp", Position.none) []] else [])
                                           , [(s_of_expr e, [])])] true
                         |> local_terminal_proof e_pr)
                     | OCL.Command_fix_let (l, l_let, o_exp, _) =>
                         proof_show_gen ( fold (fn (e1, e2) =>
                                                  Proof.let_bind_cmd [([s_of_expr e1], s_of_expr e2)])
                                               l_let
                                        o Proof.fix_cmd (List.map (fn i => (To_sbinding i, NONE, NoSyn)) l))
                                        (case o_exp of NONE => thesis | SOME l_spec => 
                                          (String.concatWith (" \<Longrightarrow> ")
                                                             (List.map s_of_expr l_spec)))
end

end

structure Shallow_main = struct open Shallow_conv open Shallow_ml
fun OCL_main_thy in_theory in_local = let open OCL open OCL_overload in (*let val f = *)fn
  Theory_datatype (Datatype (n, l)) => in_local
   (Isabelle_BNF_FP_Def_Sugar.co_datatype_cmd
      BNF_Util.Least_FP
      BNF_LFP.construct_lfp
      (Ctr_Sugar.default_ctr_options_cmd,
       [( ( ( (([], To_sbinding n), NoSyn)
            , List.map (fn (n, l) => ( ( (To_binding "", To_sbinding n)
                                       , List.map (fn s => (To_binding "", s_of_rawty s)) l)
                                     , NoSyn)) l)
          , (To_binding "", To_binding ""))
        , [])]))
| Theory_type_synonym (Type_synonym (n, v, l)) => in_theory
   (fn thy =>
     let val s_bind = To_sbinding n in
     (snd o Typedecl.abbrev_global (s_bind, map To_string0 v, NoSyn)
                                   (Isabelle_Typedecl.abbrev_cmd0 (SOME s_bind) thy (s_of_rawty l))) thy
     end)
| Theory_type_notation (Type_notation (n, e)) => in_local
   (Specification.type_notation_cmd true ("", true) [(To_string0 n, Mixfix (To_string0 e, [], 1000))])
| Theory_instantiation (Instantiation (n, n_def, expr)) => in_theory
   (fn thy =>
     let val name = To_string0 n in
     perform_instantiation
       thy
       [ let val Type (s, _) = (Isabelle_Typedecl.abbrev_cmd0 NONE thy name) in s end ]
       []
       (Syntax.read_sort (Proof_Context.init_global thy) "object")
       (fn _ => fn thy =>
        let val ((_, (_, ty)), thy) = Specification.definition_cmd
           (NONE, ((To_binding (To_string0 n_def ^ "_" ^ name ^ "_def"), []), s_of_expr expr)) false thy in
         (ty, thy)
        end)
       (fn ctxt => fn thms => Class.intro_classes_tac ctxt [] THEN ALLGOALS (Proof_Context.fact_tac ctxt thms))
     end)
| Theory_defs (Defs_overloaded (n, e)) => in_theory
   (Isar_Cmd.add_defs ((false, true), [((To_sbinding n, s_of_expr e), [])]))
| Theory_consts (Consts (n, ty, symb)) => in_theory
   (Sign.add_consts_cmd [( To_sbinding n
                        , s_of_rawty ty
                        , Mixfix ("(_) " ^ To_string0 symb, [], 1000))])
| Theory_definition def => in_local
    let val (def, e) = case def of
        Definition e => (NONE, e)
      | Definition_where1 (name, (abbrev, prio), e) =>
          (SOME ( To_sbinding name
                , NONE
                , Mixfix ("(1" ^ s_of_expr abbrev ^ ")", [], To_nat prio)), e)
      | Definition_where2 (name, abbrev, e) =>
          (SOME ( To_sbinding name
                , NONE
                , Mixfix ("(" ^ s_of_expr abbrev ^ ")", [], 1000)), e) in
    (snd o Specification.definition_cmd (def, ((@{binding ""}, []), s_of_expr e)) false)
    end
| Theory_lemmas (Lemmas_simp_thm (simp, s, l)) => in_local
   (fn lthy => (snd o Specification.theorems Thm.lemmaK
      [((To_sbinding s, List.map (fn s => Attrib.check_src lthy (Token.src (s, Position.none) []))
                          (if simp then ["simp", "code_unfold"] else [])),
        List.map (fn x => ([m_of_ntheorem lthy x], [])) l)]
      []
      false) lthy)
| Theory_lemmas (Lemmas_simp_thms (s, l)) => in_local
   (fn lthy => (snd o Specification.theorems Thm.lemmaK
      [((To_sbinding s, List.map (fn s => Attrib.check_src lthy (Token.src (s, Position.none) []))
                          ["simp", "code_unfold"]),
        List.map (fn x => (Proof_Context.get_thms lthy (To_string0 x), [])) l)]
      []
      false) lthy)
| Theory_lemma (Lemma (n, l_spec, l_apply, o_by)) => in_local
   (fn lthy =>
           Specification.theorem_cmd Thm.lemmaK NONE (K I)
             (@{binding ""}, []) [] [] (Element.Shows [((To_sbinding n, [])
                                                       ,[((String.concatWith (" \<Longrightarrow> ")
                                                             (List.map s_of_expr l_spec)), [])])])
             false lthy
        |> fold (apply_results o OCL.Command_apply) l_apply
        |> global_terminal_proof o_by)
| Theory_lemma (Lemma_assumes (n, l_spec, concl, l_apply, o_by)) => in_local
   (fn lthy => lthy
        |> Specification.theorem_cmd Thm.lemmaK NONE (K I)
             (To_sbinding n, [])
             []
             (List.map (fn (n, (b, e)) => Element.Assumes [((To_sbinding n, if b then [Token.src ("simp", Position.none) []] else []), [(s_of_expr e, [])])]) l_spec)
             (Element.Shows [((@{binding ""}, []),[(s_of_expr concl, [])])])
             false
        |> fold apply_results l_apply
        |> (case map_filter (fn OCL.Command_let _ => SOME [] | OCL.Command_have _ => SOME [] | OCL.Command_fix_let (_, _, _, l) => SOME l | _ => NONE) (rev l_apply) of
              [] => global_terminal_proof o_by
            | _ :: l => let val arg = (NONE, true) in fn st => st
              |> local_terminal_proof o_by
              |> fold (fn l => fold applyE_results l o Proof.local_qed arg) l
              |> Proof.global_qed arg end))
| Theory_axiomatization (Axiomatization (n, e)) => in_theory
   (#2 o Specification.axiomatization_cmd
                                     []
                                     [((To_sbinding n, []), [s_of_expr e])])
| Theory_section _ => in_theory I
| Theory_text _ => in_theory I
| Theory_ML ml => in_theory (Code_printing.reflect_ml (Input.source false (case ml of SML ml => s_of_sexpr ml) (Position.none, Position.none)))
| Theory_thm (Thm thm) => in_local
   (fn lthy =>
    let val () = writeln (Pretty.string_of (Proof_Context.pretty_fact lthy ("", List.map (m_of_ntheorem lthy) thm))) in
    lthy
    end)
| Theory_interpretation (Interpretation (n, loc_n, loc_param, o_by)) => in_local
   (fn lthy => lthy
    |> Expression.interpretation_cmd ( [ ( (To_string0 loc_n, Position.none)
                                         , ( (To_string0 n, true)
                                           , if loc_param = [] then
                                               Expression.Named []
                                             else
                                               Expression.Positional (map (SOME o s_of_expr) loc_param)))]
                                     , [])
                                     []
    |> global_terminal_proof o_by)
(*in fn t => fn thy => f t thy handle ERROR s => (warning s; thy)
 end*)
end

fun OCL_main aux ret = let open OCL open OCL_overload in fn
  Isab_thy thy =>
    ret o (case thy of H_thy_simple thy => OCL_main_thy I in_local thy
                     | H_thy_locale (data, l) => fn thy => thy
                       |> (   Expression.add_locale_cmd
                                (To_sbinding (OCL.holThyLocale_name data))
                                Binding.empty
                                ([], [])
                                (List.concat
                                  (map
                                    (fn (fixes, assumes) => List.concat
                                      [ map (fn (e,ty) => Element.Fixes [(To_binding (s_of_expr e), SOME (s_of_rawty ty), NoSyn)]) fixes
                                      , case assumes of NONE => []
                                                      | SOME (n, e) => [Element.Assumes [((To_sbinding n, []), [(s_of_expr e, [])])]]])
                                    (OCL.holThyLocale_header data)))
                           #> snd)
                       |> fold (fold (OCL_main_thy Local_Theory.background_theory
                                                   (fn f => fn lthy => lthy
                                                     |> Local_Theory.new_group
                                                     |> f
                                                     |> Local_Theory.reset_group
                                                     |> Local_Theory.restore))) l
                       |> Local_Theory.exit_global)
| Isab_thy_generation_syntax _ => ret o I
| Isab_thy_ml_extended _ => ret o I
| Isab_thy_all_meta_embedding ocl => fn thy =>
  aux
    (map2_ctxt_term
      (fn T_pure x => T_pure x
        | e =>
          let fun aux e = case e of 
            T_to_be_parsed (s, _) => SOME let val t = Syntax.read_term (Proof_Context.init_global thy) (To_string0 s) in
                                          (t, Term.add_frees t [])
                                          end
          | T_lambda (a, e) =>
            Option.map
              (fn (e, l_free) => 
               let val a = To_string0 a 
                   val (t, l_free) = case List.partition (fn (x, _) => x = a) l_free of
                                       ([], l_free) => (TFree ("'a", ["HOL.type"]), l_free)
                                     | ([(_, t)], l_free) => (t, l_free) in
               (lambda (Free (a, t)) e, l_free)
               end)
              (aux e)
          | _ => NONE in
          case aux e of
            NONE => error "nested pure expression not expected"
          | SOME (e, _) => OCL.T_pure (From.from_pure_term e)
          end) ocl) thy
end

end
(*val _ = print_depth 100*)
*}

subsection{* ... *}

setup{* ML_Antiquotation.inline @{binding mk_string} (Scan.succeed "(fn ctxt => fn x => Pretty.string_of (Pretty.from_ML (pretty_ml (PolyML.prettyRepresentation (x, Config.get ctxt ML_Options.print_depth)))))") *}

ML{*

fun exec_deep (ocl, output_header_thy, seri_args, filename_thy, tmp_export_code, l_obj) thy0 =
  let open Generation_mode in
  let val i_of_arg = OCL.isabelle_of_ocl_embed OCL.isabelle_apply I in
  let fun def s = in_local (snd o Specification.definition_cmd (NONE, ((@{binding ""}, []), s)) false) in
  let val name_main = Deep.mk_free (Proof_Context.init_global thy0) Deep0.Export_code_env.Isabelle.argument_main [] in
  thy0 |> def (String.concatWith " " (  "(" (* polymorphism weakening needed by export_code *)
                                        ^ name_main ^ " :: (_ \<times> abr_string option) compiler_env_config_scheme)"
                                    :: "="
                                    :: To_string0 (i_of_arg (OCL.compiler_env_config_more_map (fn () => (l_obj, From.from_option From.from_string (Option.map (fn filename_thy => Deep.absolute_path filename_thy thy0) filename_thy))) ocl))
                                    :: []))
       |> Deep.export_code_cmd' seri_args tmp_export_code
            (fn (((_, _), msg), _) => fn err => if err <> 0 then error msg else ()) filename_thy [name_main]
       |> (fn l =>
             let val (l_warn, l) = (map fst l, map snd l) in
             if Deep.list_all_eq l then (List.concat l_warn, hd l) else error "There is an extracted language which does not produce a similar Isabelle content as the others"
             end)
       |> (fn (l_warn, s) =>
             let val () = writeln
               (case (output_header_thy, filename_thy) of
                  (SOME _, SOME _) => s
                | _ => String.concat (map ((fn s => s ^ "\n") o Active.sendback_markup [Markup.padding_command] o trim_line)
                   (String.tokens (fn c => From.from_char c = OCL.char_escape) s))) in
             fold (fn (out, err) => K ( writeln (Markup.markup Markup.keyword2 err)
                                      ; case trim_line out of
                                          "" => ()
                                        | out => writeln (Markup.markup Markup.keyword1 out))) l_warn () end)

  end end end end

fun outer_syntax_command0 mk_string cmd_spec cmd_descr parser get_oclclass =
  let open Generation_mode in
  Outer_Syntax.command cmd_spec cmd_descr
    (parser >> (fn name =>
      Toplevel.theory (fn thy =>
        let val (ocl, thy) =
        OCL.mapM

          let val get_oclclass = get_oclclass name in
          fn Gen_syntax_print n =>
               (fn thy =>
                  let val _ = writeln
                                (mk_string
                                  (Proof_Context.init_global
                                    (case n of NONE => thy
                                             | SOME n => Config.put_global ML_Options.print_depth n thy))
                                  name) in
                  (Gen_syntax_print n, thy)
                  end)
           | Gen_deep (ocl, Internal_deep (output_header_thy, seri_args, filename_thy, tmp_export_code, skip_exportation)) =>
              (fn thy0 =>
                let val l_obj = get_oclclass thy0 in
                thy0 |> (if skip_exportation then
                           K ()
                         else
                           exec_deep (OCL.d_output_header_thy_update (fn _ => NONE) ocl, output_header_thy, seri_args, NONE, tmp_export_code, l_obj))
                     |> K (Gen_deep (OCL.fold_thy_deep l_obj ocl, Internal_deep (output_header_thy, seri_args, filename_thy, tmp_export_code, skip_exportation)), thy0)
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
                     Shallow_main.OCL_main (fn x => fn thy => aux (ocl, thy) [x]) (pair ocl) l thy)
                   x
                   (ocl, thy)
                 val (ocl, thy) = aux (ocl, thy) (get_oclclass thy) in
             (Gen_shallow (ocl, thy0), thy)
             end
          end

          (case Symtab.lookup (Data_gen.get thy) Deep0.gen_empty of SOME l => l | _ => [Gen_syntax_print NONE])
          thy
        in
        Data_gen.map (Symtab.update (Deep0.gen_empty, ocl)) thy end)))
  end

fun outer_syntax_command mk_string cmd_spec cmd_descr parser get_oclclass =
 outer_syntax_command0 mk_string cmd_spec cmd_descr parser (fn a => fn thy => [get_oclclass a thy])

*}

subsection{* ... *}

ML{*
val () = let open Generation_mode in
  Outer_Syntax.command @{command_keyword generation_syntax} "set the generating list"
    ((   mode >> (fn x => SOME [x])
      || parse_l' mode >> SOME
      || @{keyword "deep"} -- @{keyword "flush_all"} >> K NONE) >>
    (fn SOME x => f_command x
      | NONE =>
      Toplevel.theory (fn thy =>
        let val l = case Symtab.lookup (Data_gen.get thy) Deep0.gen_empty of SOME l => l | _ => []
            val l = List.concat (List.map (fn Gen_deep x => [x] | _ => []) l)
            val _ = case l of [] => warning "Nothing to perform." | _ => ()
            val thy =
        fold
          (fn (ocl, Internal_deep (output_header_thy, seri_args, filename_thy, tmp_export_code, _)) => fn thy0 =>
                thy0 |> let val (ocl, l_exec) = OCL.compiler_env_config_reset_all ocl in
                        exec_deep (ocl, output_header_thy, seri_args, filename_thy, tmp_export_code, l_exec) end
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
  datatype ('a, 'b) use_context = USE_context_invariant of 'a
                                | USE_context_pre_post of 'b

  fun optional f = Scan.optional (f >> SOME) NONE
  val colon = Parse.$$$ ":"
  fun repeat2 scan = scan ::: Scan.repeat1 scan

  fun xml_unescape s = (XML.content_of (YXML.parse_body s), Position.none)
                       |> Symbol_Pos.explode |> Symbol_Pos.implode |> From.from_string

  fun outer_syntax_command2 mk_string cmd_spec cmd_descr parser v_true v_false get_oclclass =
    outer_syntax_command mk_string cmd_spec cmd_descr
      (optional (paren @{keyword "shallow"}) -- parser)
      (fn (is_shallow, use) => fn thy =>
         get_oclclass
           (if is_shallow = NONE then
              ( fn s =>
                  OCL.T_to_be_parsed ( From.from_string s
                                     , xml_unescape s)
              , v_true)
            else
              (From.from_p_term thy, v_false))
           use)

  (* *)

  val ident_dot_dot = let val f = Parse.sym_ident >> (fn "\<bullet>" => "\<bullet>" | _ => Scan.fail "Syntax error") in f -- f end
  val ident_star = Parse.sym_ident (* "*" *)

  (* *)

  val unlimited_natural =  ident_star >> (fn "*" => OCL.Mult_star
                                           | "\<infinity>" => OCL.Mult_infinity
                                           | _ => Scan.fail "Syntax error")
                        || Parse.number >> (fn s => OCL.Mult_nat (case Int.fromString s of SOME i => From.from_nat i
                                                                                         | NONE => Scan.fail "Syntax error"))
  val term_base =
       Parse.number >> (OCL.OclDefInteger o From.from_string)
    || Parse.float_number >> (OCL.OclDefReal o (From.from_pair From.from_string From.from_string o
         (fn s => case String.tokens (fn #"." => true | _ => false) s of [l1,l2] => (l1,l2)
                                                                       | _ => Scan.fail "Syntax error")))
    || Parse.string >> (OCL.OclDefString o From.from_string)

  val multiplicity = parse_l' (unlimited_natural -- optional (ident_dot_dot |-- unlimited_natural))

  fun uml_term x =
   (   term_base >> OCL.ShallB_term
    || Parse.binding >> (OCL.ShallB_str o From.from_binding)
    || @{keyword "self"} |-- Parse.nat >> (fn n => OCL.ShallB_self (From.from_internal_oid (From.from_nat n)))
    || paren (Parse.list uml_term) >> (* untyped, corresponds to Set, Sequence or Pair *)
                                      (* WARNING for Set: we are describing a finite set *)
                                      OCL.ShallB_list) x

  val name_object = optional (Parse.list1 Parse.binding --| colon) -- Parse.binding

  val type_object_weak = 
    let val name_object = Parse.binding >> (fn s => (NONE, s)) in
                    name_object -- Scan.repeat (Parse.$$$ "<" |-- Parse.list1 name_object) >>
    let val f = fn (_, s) => OCL.OclTyCore_pre (From.from_binding s) in
    fn (s, l) => OCL.OclTyObj (f s, map (map f) l)
    end
    end

  val type_object = name_object -- Scan.repeat (Parse.$$$ "<" |-- Parse.list1 name_object) >>
    let val f = fn (_, s) => OCL.OclTyCore_pre (From.from_binding s) in
    fn (s, l) => OCL.OclTyObj (f s, map (map f) l)
    end

  val category = 
       multiplicity
    -- optional (@{keyword "Role"} |-- Parse.binding)
    -- Scan.repeat (   @{keyword "Ordered"} >> K OCL.Ordered0
                    || @{keyword "Subsets"} |-- Parse.binding >> K OCL.Subsets0
                    || @{keyword "Union"} >> K OCL.Union0
                    || @{keyword "Redefines"} |-- Parse.binding >> K OCL.Redefines0
                    || @{keyword "Derived"} -- Parse.$$$ "=" |-- Parse.term >> K OCL.Derived0
                    || @{keyword "Qualifier"} |-- Parse.term >> K OCL.Qualifier0
                    || @{keyword "Nonunique"} >> K OCL.Nonunique0
                    || @{keyword "Sequence_"} >> K OCL.Sequence) >>
    (fn ((l_mult, role), l) =>
       OCL.Ocl_multiplicity_ext (l_mult, From.from_option From.from_binding role, l, ()))

  val type_base =   Parse.reserved "Void" >> K OCL.OclTy_base_void
                 || Parse.reserved "Boolean" >> K OCL.OclTy_base_boolean
                 || Parse.reserved "Integer" >> K OCL.OclTy_base_integer
                 || Parse.reserved "UnlimitedNatural" >> K OCL.OclTy_base_unlimitednatural
                 || Parse.reserved "Real" >> K OCL.OclTy_base_real
                 || Parse.reserved "String" >> K OCL.OclTy_base_string

  fun use_type_gen type_object v =
                   ((* collection *)
                    Parse.reserved "Set" |-- use_type >> 
                      (fn l => OCL.OclTy_collection (OCL.Ocl_multiplicity_ext ([], NONE, [OCL.Set], ()), l))
                 || Parse.reserved "Sequence" |-- use_type >>
                      (fn l => OCL.OclTy_collection (OCL.Ocl_multiplicity_ext ([], NONE, [OCL.Sequence], ()), l))
                 || category -- use_type >> OCL.OclTy_collection

                    (* pair *)
                 || Parse.reserved "Pair" |-- (   use_type -- use_type
                                               || Parse.$$$ "(" |-- use_type --| Parse.$$$ "," -- use_type --| Parse.$$$ ")") >> OCL.OclTy_pair

                    (* base *)
                 || type_base

                    (* raw HOL *)
                 || Parse.sym_ident (* "\<acute>" *) |-- Parse.typ --| Parse.sym_ident (* "\<acute>" *) >>
                      (OCL.OclTy_raw o xml_unescape)

                    (* object type *)
                 || type_object >> OCL.OclTy_object

                 || ((Parse.$$$ "(" |-- Parse.list (   (Parse.binding --| colon >> (From.from_option From.from_binding o SOME))
                                                    -- (   Parse.$$$ "(" |-- use_type --| Parse.$$$ ")"
                                                        || use_type_gen type_object_weak) >> OCL.OclTy_binding
                                                    ) --| Parse.$$$ ")"
                      >> (fn ty_arg => case rev ty_arg of
                            [] => OCL.OclTy_base_void
                          | ty_arg => fold (fn x => fn acc => OCL.OclTy_pair (x, acc))
                                           (tl ty_arg)
                                           (hd ty_arg)))
                     -- optional (colon |-- use_type))
                    >> (fn (ty_arg, ty_out) => case ty_out of NONE => ty_arg
                                                            | SOME ty_out => OCL.OclTy_arrow (ty_arg, ty_out))
                 || (Parse.$$$ "(" |-- use_type --| Parse.$$$ ")" >> (fn s => OCL.OclTy_binding (NONE, s)))) v
  and use_type x = use_type_gen type_object x

  val use_prop =    (optional (optional (Parse.binding >> From.from_binding) --| Parse.$$$ ":") >> (fn NONE => NONE | SOME x => x))
                 -- Parse.term --| optional (Parse.$$$ ";") >> (fn (n, e) => fn from_expr => OCL.OclProp_ctxt (n, from_expr e))

  (* *)

  val association_end =
       type_object
    -- category
    --| optional (Parse.$$$ ";")

  val association = optional @{keyword "Between"} |-- Scan.optional (repeat2 association_end) []

  val invariant = 
         optional @{keyword "Constraints"}
     |-- Scan.optional (@{keyword "Existential"} >> K true) false
     --| @{keyword "Inv"}
     --  use_prop

  structure Outer_syntax_Association = struct
    fun make ass_ty l = OCL.Ocl_association_ext (ass_ty, OCL.OclAssRel l, ())
  end

  (* *)

  val context =
    Scan.repeat
      ((   optional (@{keyword "Operations"} || Parse.$$$ "::")
        |-- Parse.binding
        -- use_type
        --| optional (Parse.$$$ "=" |-- Parse.term || Parse.term)
        -- Scan.repeat
              (      (@{keyword "Pre"} || @{keyword "Post"})
                  -- use_prop >> USE_context_pre_post
               || invariant >> USE_context_invariant)
        --| optional (Parse.$$$ ";")) >>
              (fn ((name_fun, ty), expr) => fn from_expr =>
                OCL.Ctxt_pp
                  (OCL.Ocl_ctxt_pre_post_ext
                    ( From.from_binding name_fun
                    , ty
                    , From.from_list (fn USE_context_pre_post (pp, expr) =>
                                           OCL.T_pp (if pp = "Pre" then OCL.OclCtxtPre else OCL.OclCtxtPost, expr from_expr)
                                       | USE_context_invariant (b, expr) => OCL.T_invariant (OCL.T_inv (b, expr from_expr))) expr
                    , ())))
       ||
       invariant >> (fn (b, expr) => fn from_expr => OCL.Ctxt_inv (OCL.T_inv (b, expr from_expr))))

  val class =
        optional @{keyword "Attributes"}
    |-- Scan.repeat (Parse.binding --| colon -- use_type
                     --| optional (Parse.$$$ ";"))
    -- context

  datatype use_classDefinition = USE_class | USE_class_abstract
  datatype ('a, 'b) use_classDefinition_content = USE_class_content of 'a | USE_class_synonym of 'b
  
  structure Outer_syntax_Class = struct
    fun make from_expr abstract ty_object attribute oper =
      OCL.Ocl_class_raw_ext
        ( ty_object
        , From.from_list (From.from_pair From.from_binding I) attribute
        , From.from_list (fn f => f from_expr) oper
        , abstract
        , ())
  end

  (* *)

  val term_object = parse_l (   optional (    Parse.$$$ "("
                                          |-- Parse.binding
                                          --| Parse.$$$ ","
                                          -- Parse.binding
                                          --| Parse.$$$ ")"
                                          --| (Parse.sym_ident >> (fn "|=" => Scan.succeed | _ => Scan.fail "")))
                             -- Parse.binding
                             -- (    Parse.$$$ "="
                                 |-- uml_term))

  val list_attr' = term_object >> (fn res => (res, [] : binding list))
  fun object_cast e =
    (   annot_ty term_object
     -- Scan.repeat (    (Parse.sym_ident >> (fn "->" => Scan.succeed
                                               | "\<leadsto>" => Scan.succeed
                                               | "\<rightarrow>" => Scan.succeed
                                               | _ => Scan.fail ""))
                     |-- (   Parse.reserved "oclAsType"
                             |-- Parse.$$$ "("
                             |-- Parse.binding
                             --| Parse.$$$ ")"
                          || Parse.binding)) >> (fn ((res, x), l) => (res, rev (x :: l)))) e
  val object_cast' = object_cast >> (fn (res, l) => (res, rev l))

  fun get_oclinst l _ =
    OCL.OclInstance (map (fn ((name,typ), (l_attr, is_cast)) =>
        let val f = map (fn ((pre_post, attr), ocl) =>
                              ( From.from_option (From.from_pair From.from_binding From.from_binding) pre_post
                              , ( From.from_binding attr
                                , ocl)))
            val l_attr =
              fold
                (fn b => fn acc => OCL.OclAttrCast (From.from_binding b, acc, []))
                is_cast
                (OCL.OclAttrNoCast (f l_attr)) in
        OCL.Ocl_instance_single_ext
          (From.from_option From.from_binding name, From.from_option From.from_binding typ, l_attr, From.from_unit ()) end) l)

  val parse_instance = (Parse.binding >> SOME)
                     -- optional (@{keyword "::"} |-- Parse.binding) --| @{keyword "="}
                     -- (list_attr' || object_cast')

  (* *)

  datatype state_content = ST_l_attr of (((binding * binding) option * binding) * OCL.ocl_data_shallow) list * binding list
                         | ST_binding of binding
  
  val state_parse = parse_l' (   object_cast >> ST_l_attr
                              || Parse.binding >> ST_binding)

  fun mk_state thy = map (fn ST_l_attr l => OCL.OclDefCoreAdd (case get_oclinst (map (fn (l_i, l_ty) => ((NONE, SOME (hd l_ty)), (l_i, rev (tl l_ty)))) [l]) thy of
                                                                 OCL.OclInstance [x] => x)
                           | ST_binding b => OCL.OclDefCoreBinding (From.from_binding b))

  (* *)

  datatype state_pp_content = ST_PP_l_attr of state_content list
                            | ST_PP_binding of binding
  
  val state_pp_parse = state_parse >> ST_PP_l_attr
                       || Parse.binding >> ST_PP_binding

  fun mk_pp_state thy = fn ST_PP_l_attr l => OCL.OclDefPPCoreAdd (mk_state thy l)
                         | ST_PP_binding s => OCL.OclDefPPCoreBinding (From.from_binding s)
end
*}

subsection{* Outer Syntax: enum *}

ML{*
val () =
  outer_syntax_command @{mk_string} @{command_keyword Enum} ""
    (Parse.binding -- parse_l1' Parse.binding)
    (fn (n1, n2) => 
      K (OCL.META_enum (OCL.OclEnum (From.from_binding n1, From.from_list From.from_binding n2))))
*}

subsection{* Outer Syntax: (abstract) class *}

ML{*
local
  open USE_parse

  fun mk_classDefinition abstract cmd_spec =
    outer_syntax_command2 @{mk_string} cmd_spec "Class generation"
      (   Parse.binding --| Parse.$$$ "=" -- USE_parse.type_base >> USE_class_synonym
       ||    type_object
          -- class >> USE_class_content)
      (curry OCL.META_class_raw OCL.Floor1)
      (curry OCL.META_class_raw OCL.Floor2)
      (fn (from_expr, META_class_raw) =>
       fn USE_class_content (ty_object, (attribute, oper)) =>
            META_class_raw (Outer_syntax_Class.make from_expr (abstract = USE_class_abstract) ty_object attribute oper)
        | USE_class_synonym (n1, n2) => 
            OCL.META_class_synonym (OCL.OclClassSynonym (From.from_binding n1, n2)))
in
val () = mk_classDefinition USE_class @{command_keyword record'}
val () = mk_classDefinition USE_class_abstract @{command_keyword Abstract_class}
end
*}

subsection{* Outer Syntax: association, composition, aggregation *}

ML{*
local
  open USE_parse

  fun mk_associationDefinition ass_ty cmd_spec =
    outer_syntax_command @{mk_string} cmd_spec ""
      (   repeat2 association_end
       ||     optional Parse.binding
          |-- association)
      (fn l => fn _ =>
        OCL.META_association (Outer_syntax_Association.make ass_ty l))
in
val () = mk_associationDefinition OCL.OclAssTy_association @{command_keyword record_link}
val () = mk_associationDefinition OCL.OclAssTy_composition @{command_keyword Composition}
val () = mk_associationDefinition OCL.OclAssTy_aggregation @{command_keyword Aggregation}
end
*}

subsection{* Outer Syntax: (abstract) associationclass *}

ML{*

local
  open USE_parse

  datatype use_associationClassDefinition = USE_associationclass | USE_associationclass_abstract

  fun mk_associationClassDefinition abstract cmd_spec =
    outer_syntax_command2 @{mk_string} cmd_spec ""
      (   type_object
       -- association
       -- class
       -- optional (Parse.reserved "aggregation" || Parse.reserved "composition"))
      (curry OCL.META_ass_class OCL.Floor1)
      (curry OCL.META_ass_class OCL.Floor2)
      (fn (from_expr, META_ass_class) =>
       fn (((ty_object, l_ass), (attribute, oper)), assty) =>
          META_ass_class (OCL.OclAssClass ( Outer_syntax_Association.make (case assty of SOME "aggregation" => OCL.OclAssTy_aggregation
                                                                                       | SOME "composition" => OCL.OclAssTy_composition
                                                                                       | _ => OCL.OclAssTy_association)
                                                                          l_ass
                                          , Outer_syntax_Class.make from_expr (abstract = USE_associationclass_abstract) ty_object attribute oper)))
in
val () = mk_associationClassDefinition USE_associationclass @{command_keyword Associationclass}
val () = mk_associationClassDefinition USE_associationclass_abstract @{command_keyword Abstract_associationclass}
end
*}

subsection{* Outer Syntax: context *}

ML{*
local
 open USE_parse
in
val () =
  outer_syntax_command2 @{mk_string} @{command_keyword set_cartouche_type} ""
    (optional (Parse.list1 Parse.binding --| colon)
     -- Parse.binding
     -- context)
    (curry OCL.META_ctxt OCL.Floor1)
    (curry OCL.META_ctxt OCL.Floor2)
    (fn (from_expr, META_ctxt) =>
    (fn ((l_param, name), l) => 
    META_ctxt
      (OCL.Ocl_ctxt_ext
        ( case l_param of NONE => [] | SOME l => From.from_list From.from_binding l
        , OCL.OclTyObj (OCL.OclTyCore_pre (From.from_binding name), [])
        , From.from_list (fn f => f from_expr) l
        , ()))))
end
*}

subsection{* Outer Syntax: End *}

ML{*
val () =
  outer_syntax_command0 @{mk_string} @{command_keyword End} "Class generation"
    (Scan.optional ( Parse.$$$ "[" -- Parse.reserved "forced" -- Parse.$$$ "]" >> K true
                    || Parse.$$$ "!" >> K true) false)
    (fn b => fn _ =>
       if b then
         [OCL.META_flush_all OCL.OclFlushAll]
       else
         [])
*}

subsection{* Outer Syntax: BaseType, def_record, def_record' *}

ML{*
val () =
  outer_syntax_command @{mk_string} @{command_keyword BaseType} ""
    (parse_l' USE_parse.term_base)
    (K o OCL.META_def_base_l o OCL.OclDefBase)

local
  open USE_parse
in
val () =
  outer_syntax_command @{mk_string} @{command_keyword def_record} ""
    (Scan.optional (parse_instance -- Scan.repeat (optional @{keyword "and"} |-- parse_instance) >> (fn (x, xs) => x :: xs)) [])
    (OCL.META_instance oo get_oclinst)

val () =
  outer_syntax_command @{mk_string} @{command_keyword def_record'} ""
    (USE_parse.optional (paren @{keyword "shallow"}) -- Parse.binding --| @{keyword "="}
     -- state_parse)
     (fn ((is_shallow, name), l) => fn thy =>
      OCL.META_def_state
        ( if is_shallow = NONE then OCL.Floor1 else OCL.Floor2
        , OCL.OclDefSt (From.from_binding name, mk_state thy l)))
end
*}

subsection{* Outer Syntax: binary_record *}

ML{*
local
  open USE_parse
in
val () =
  outer_syntax_command @{mk_string} @{command_keyword binary_record} ""
    (USE_parse.optional (paren @{keyword "shallow"})
     -- USE_parse.optional (Parse.binding --| @{keyword "="})
     -- state_pp_parse
     -- USE_parse.optional state_pp_parse)
    (fn (((is_shallow, n), s_pre), s_post) => fn thy =>
      OCL.META_def_pre_post
        ( if is_shallow = NONE then OCL.Floor1 else OCL.Floor2
        , OCL.OclDefPP ( From.from_option From.from_binding n
                       , mk_pp_state thy s_pre
                       , From.from_option (mk_pp_state thy) s_post)))
end
(*val _ = print_depth 100*)
*}

end
