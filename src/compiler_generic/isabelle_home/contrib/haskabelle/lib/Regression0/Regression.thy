theory Regression imports "Main" begin

ML \<open>
  val thy_path = getenv_strict "REGRESSION_THY_PATH"
  val thy_name = getenv_strict "REGRESSION_THY_NAME"
  val dst = Path.variable "REGRESSION_DST"
  val _ = use_thy thy_path
  val ctxt = Proof_Context.init_global (Thy_Info.get_theory thy_name)
  val export_consts = Code_Thingol.read_const_exprs ctxt [thy_name ^ "._"]
  val _ = Code_Target.export_code ctxt false export_consts [(((("Haskell", thy_name), SOME dst)), [])]
\<close>

end