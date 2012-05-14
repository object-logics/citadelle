theory 
  OCL_core_experiments
imports
  OCL_core (* Testing *)
begin

section{* OCL Core Definitions *}

nitpick_params
 [timeout = 30, tac_timeout = 0.5, show_datatypes,assms=true]
lemma ocl_and_defargs: 
"\<tau> \<Turnstile> (P and Q) \<Longrightarrow> (\<tau> \<Turnstile> \<delta> P) \<and> (\<tau> \<Turnstile> \<delta> Q)"
by(auto dest: foundation5 foundation6)

(*
nitpick_params
nitpick_params
 [timeout = 30, tac_timeout = 0.5, show_datatypes]
lemma ocl_and_defargs: 
"\<tau> \<Turnstile> ((P and Q)  \<triangleq>  (P or Q))"
nitpick[show_all]

oops
lemma "P & Q = Q"
nitpick
*)


end