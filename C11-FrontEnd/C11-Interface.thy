theory "C11-Interface"
  imports "src/C_Model_ml_lex"
  keywords "C" :: thy_decl
       and "C_file" :: thy_load % "ML"

begin



ML\<open>
(*  Title:      Pure/ML/ml_file.ML
    Author:     Makarius

Commands to load ML files.
*)

structure C_File =
struct

fun command SML debug files = Toplevel.generic_theory (fn gthy =>
  let
    val [{src_path, lines, digest, pos}: Token.file] = files (Context.theory_of gthy);
    val provide = Resources.provide (src_path, digest);
    val source = Input.source true (cat_lines lines) (pos, pos);
    val flags =
      {SML = SML, exchange = false, redirect = true, verbose = true,
        debug = debug, writeln = writeln, warning = warning};
  in
    gthy
    |> ML_Context.exec (fn () => C_Context.eval_source flags source)
    |> Local_Theory.propagate_ml_env
    |> Context.mapping provide (Local_Theory.background_theory provide)
  end);

val C : bool option ->
      (theory -> Token.file list) ->
        Toplevel.transition -> Toplevel.transition = command false;

end;
\<close>

section \<open>\<close>

ML\<open>

structure C_Outer_Syntax =
struct
val _ =
  Outer_Syntax.command @{command_keyword C} ""
    (Parse.input (Parse.group (fn () => "C source") Parse.text) >> (fn source =>
      Toplevel.generic_theory
        (ML_Context.exec (fn () =>
            C_Context.eval_source (ML_Compiler.verbose true ML_Compiler.flags) source) #>
          Local_Theory.propagate_ml_env)));

local

val semi = Scan.option @{keyword ";"};

val _ =
  Outer_Syntax.command @{command_keyword C_file} "read and evaluate C file"
    (Resources.parse_files "C_file" --| semi >> C_File.C NONE);

in end
end
\<close>



end
