theory "C11-Interface"
  imports "src/C_Model_ml_lex"
  keywords "C" :: thy_decl
       and "C_file" :: thy_load % "ML"
begin

section\<open>The Global C11-Module State\<close>
ML\<open>
structure C11_core = 
struct
  datatype id_kind = cpp_id        of Position.T * serial
                   | cpp_macro     of Position.T * serial
                   | builtin_id  
                   | builtin_func 
                   | imported_id   of Position.T * serial
                   | imported_func of Position.T * serial 
                   | global_id     of Position.T * serial
                   | local_id      of Position.T * serial
                   | global_func   of Position.T * serial

  type c_file_name      = string
  type C11_struct       = { tab  : CTranslUnit list Symtab.table,
                            env  : id_kind list Symtab.table }
  val  C11_struct_empty = { tab  = Symtab.empty, env = Symtab.empty}

  fun map_tab f {tab, env} = {tab = f tab, env=env}
  fun map_env f {tab, env} = {tab = tab, env=f env}

  (* registrating data of the Isa_DOF component *)
  structure Data = Generic_Data
  (
    type T =     C11_struct
    val empty = C11_struct_empty
    val extend =  I
    fun merge(t1,t2) = { tab = Symtab.merge (op =)(#tab t1, #tab t2),
                         env =  Symtab.merge (op =)(#env t1, #env t2)}
  );

  val get_global      = Data.get o Context.Theory
  fun put_global x    = Data.put x;
  val map_data        = Context.theory_map o Data.map;
  val map_data_global = Context.theory_map o Data.map
  
  val trans_tab_of    = #tab o get_global
  val dest_list       = Symtab.dest_list o trans_tab_of

  fun push_env(k,a) tab = case Symtab.lookup tab k of
                        NONE => Symtab.update(k,[a])(tab)
                     |  SOME S => Symtab.update(k,a::S)(tab)
  fun pop_env(k) tab = case Symtab.lookup tab k of
                       SOME (a::S) => Symtab.update(k,S)(tab)
                     | _ => error("internal error - illegal break of scoping rules")
  
  fun push_global (k,a) =  (map_data_global o map_env) (push_env (k,a)) 
  fun push (k,a)        =  (map_data        o map_env) (push_env (k,a)) 
  fun pop_global (k)    =  (map_data_global o map_env) (pop_env k) 
  fun pop (k)           =  (map_data        o map_env) (pop_env k) 

end
\<close>

ML\<open>
open C11_core;


\<close>

ML\<open>
structure C_Context = struct
val eval_source =
  C_Context.eval_source
    (fn _ => fn (_, (res, _, _)) => fn context => 
      (Context.theory_name (Context.theory_of context), res)
      |> Symtab.update_list (op =)
      |> C11_core.map_tab
      |> (fn res => C11_core.Data.map res context))
end
\<close>

section\<open>Definition of the Command "C_file"\<close>

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

section \<open>The Isar Binding to the C11 Interface.\<close>

ML\<open>

structure C_Outer_Syntax =
struct

val C = C_Context.eval_source (ML_Compiler.verbose true ML_Compiler.flags)

val _ =
  Outer_Syntax.command @{command_keyword C} ""
    (Parse.input (Parse.group (fn () => "C source") Parse.text) >> (fn source =>
      Toplevel.generic_theory
        (ML_Context.exec (fn () =>
            C source) #>
          Local_Theory.propagate_ml_env)));

local

val semi = Scan.option @{keyword ";"};

val _ =
  Outer_Syntax.command @{command_keyword C_file} "read and evaluate C file"
    (Resources.parse_files "C_file" --| semi >> C_File.C NONE);

in end
end
\<close>

ML\<open>
fun hook make_string f (_, (value, pos1, pos2)) thy =
  let
    val () = writeln (make_string value)
    val () = Position.reports_text [((Position.range (pos1, pos2) 
                                    |> Position.range_position, Markup.intensify), "")]
  in f thy end
\<close>
setup\<open>ML_Antiquotation.inline @{binding hook} (Args.context >> K ("hook " ^ ML_Pretty.make_string_fn ^ " I"))\<close>


end
