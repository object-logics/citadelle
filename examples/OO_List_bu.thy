theory 
  OO_List
imports
  Main (* Testing *)
begin

section{* Mini-OCL *}



section{* OCL Core Definitions *}

types oid = ind

fun    drop :: "'\<alpha> option \<Rightarrow> '\<alpha>" ("|^(_)^|")
where "drop (Some v) = v "

syntax
  "lift"        :: "'\<alpha> \<Rightarrow> '\<alpha> option"   ("|.(_).|")
translations
  "|.a.|" == "CONST Some a"



types ('\<AA>) state = "oid \<rightharpoonup> '\<AA> "

types ('\<AA>)st = "'\<AA> state \<times> '\<AA> state"

types ('\<AA>,'\<alpha>) val = "('\<AA> st \<Rightarrow> '\<alpha> option option)"

definition invalid :: "('\<AA>,'\<alpha>) val" 
where     "invalid \<equiv> \<lambda> \<tau>. None"

definition null :: "('\<AA>,'\<alpha>) val" 
where     "null \<equiv> \<lambda> \<tau>. |. None .| "


types      ('\<AA>)Boolean = "('\<AA>,bool) val"
           ('\<AA>)Integer = "('\<AA>,int) val"

definition true :: "('\<AA>)Boolean"
where     "true \<equiv> \<lambda> st. |. |. True .| .|"

definition false :: "('\<AA>)Boolean"
where     "false \<equiv>  \<lambda> \<tau>. |. |. False .| .|"

definition StrongEq::"[('\<AA>,'\<alpha>)val,('\<AA>,'\<alpha>)val] \<Rightarrow> ('\<AA>)Boolean"  (infixl "\<cong>" 30)
where     "X \<cong> Y \<equiv>  \<lambda> \<tau>. |. |. X \<tau> = Y \<tau> .| .|"

lemma StrongEq_refl [simp]: "(X \<cong> X) = true"
by(rule ext, simp add: null_def invalid_def true_def false_def StrongEq_def)

lemma StrongEq_sym [simp]: "(X \<cong> Y) = (Y \<cong> X)"
by(rule ext, simp add: eq_sym_conv invalid_def true_def false_def StrongEq_def)

lemma StrongEq_trans_strong [simp]:
  assumes A: "(X \<cong> Y) = true"
  and     B: "(Y \<cong> Z) = true"
  shows   "(X \<cong> Z) = true"
  apply(insert A B) apply(rule ext)
  apply(simp add: null_def invalid_def true_def false_def StrongEq_def)
  apply(drule_tac x=x in fun_cong)+
  by auto

definition not :: "('\<AA>)Boolean \<Rightarrow> ('\<AA>)Boolean"
where     "not X \<equiv>  \<lambda> \<tau> . case X \<tau> of
                             None \<Rightarrow> None
                           | |. None .| \<Rightarrow> None
                           | |. |. x .| .| \<Rightarrow> |. |. \<not> x .| .|"

lemma not1[simp]: "not invalid = invalid"
  by(rule ext,simp add: not_def null_def invalid_def true_def false_def)

lemma not2[simp]: "not null = invalid"
  by(rule ext,simp add: not_def null_def invalid_def true_def false_def)

lemma not3[simp]: "not true = false"
  by(rule ext,simp add: not_def null_def invalid_def true_def false_def)

lemma not4[simp]: "not false = true"
  by(rule ext,simp add: not_def null_def invalid_def true_def false_def)


lemma not_not[simp]: "not (not X) = X"
  apply(rule ext,simp add: not_def null_def invalid_def true_def false_def)
  apply(case_tac "X x", simp_all)
  apply(case_tac "a", simp_all)
  sorry

definition ocl_and :: "[('\<AA>)Boolean, ('\<AA>)Boolean] \<Rightarrow> ('\<AA>)Boolean"
                                                         (infixl "and" 30)
where     "X and Y \<equiv>  (\<lambda> \<tau> . case X \<tau> of
                             None \<Rightarrow> (case Y \<tau> of
                                              None \<Rightarrow>  None
                                          | |.None.| \<Rightarrow> None
                                          | |.|.True.|.| \<Rightarrow>  None
                                          | |.|.False.|.| \<Rightarrow>  |.|.False.|.|)
                        | |. None .| \<Rightarrow> (case Y \<tau> of
                                              None \<Rightarrow>  None
                                          | |.None.| \<Rightarrow> None
                                          | |.|.True.|.| \<Rightarrow>  None
                                          | |.|.False.|.| \<Rightarrow>  |.|.False.|.|)
                        | |. |. True .| .| \<Rightarrow> (case Y \<tau> of
                                              None \<Rightarrow>  None
                                          | |.None.| \<Rightarrow> None
                                          | |.|.y.|.| \<Rightarrow>  |.|. y .|.|)
                        | |. |. False .| .| \<Rightarrow>  |.|. False .|.|)"

lemma and1[simp]: "(invalid and true) = invalid"
  by(rule ext,simp add: ocl_and_def null_def invalid_def true_def false_def)
lemma and2[simp]: "(invalid and false) = false"
  by(rule ext,simp add: ocl_and_def null_def invalid_def true_def false_def)
lemma and3[simp]: "(invalid and null) = invalid"
  by(rule ext,simp add: ocl_and_def null_def invalid_def true_def false_def)
lemma and4[simp]: "(invalid and invalid) = invalid"
  by(rule ext,simp add: ocl_and_def null_def invalid_def true_def false_def)

lemma and5[simp]: "(null and true) = invalid"
  by(rule ext,simp add: ocl_and_def null_def invalid_def true_def false_def)
lemma and6[simp]: "(null and false) = false"
  by(rule ext,simp add: ocl_and_def null_def invalid_def true_def false_def)
lemma and7[simp]: "(null and null) = invalid"
  by(rule ext,simp add: ocl_and_def null_def invalid_def true_def false_def)
lemma and8[simp]: "(null and invalid) = invalid"
  by(rule ext,simp add: ocl_and_def null_def invalid_def true_def false_def)

lemma and9[simp]: "(false and true) = false"
  by(rule ext,simp add: ocl_and_def null_def invalid_def true_def false_def)
lemma and10[simp]: "(false and false) = false"
  by(rule ext,simp add: ocl_and_def null_def invalid_def true_def false_def)
lemma and11[simp]: "(false and null) = false"
  by(rule ext,simp add: ocl_and_def null_def invalid_def true_def false_def)
lemma and12[simp]: "(false and invalid) = false"
  by(rule ext,simp add: ocl_and_def null_def invalid_def true_def false_def)

lemma and13[simp]: "(false and true) = false"
  by(rule ext,simp add: ocl_and_def null_def invalid_def true_def false_def)
lemma and14[simp]: "(false and false) = false"
  by(rule ext,simp add: ocl_and_def null_def invalid_def true_def false_def)
lemma and15[simp]: "(false and null) = false"
  by(rule ext,simp add: ocl_and_def null_def invalid_def true_def false_def)
lemma and16[simp]: "(false and invalid) = false"
  by(rule ext,simp add: ocl_and_def null_def invalid_def true_def false_def)

lemma and_idem[simp]: "(X and X) = X"
  apply(rule ext,simp add: ocl_and_def null_def invalid_def true_def false_def)
  apply(case_tac "X x", simp_all)
  apply(case_tac "a", simp_all)
  sorry
(*
  apply(case_tac "a", simp_all)
  big problem here : the definition is not commutative for null
*)

definition OclValid  :: "[('\<AA>)st, ('\<AA>)Boolean] \<Rightarrow> bool" ("(1(_)/|=(_))" 50)
where     "\<tau> |= P \<equiv> ((P \<tau>) = true \<tau>)"


section{* Example Data-Universe *}
datatype node = Node int oid


fun at_next:: "node val \<Rightarrow> node val"  ("(1(_).next)" 50)
  where "X .next = (\<lambda> \<tau>. case X \<tau> of
                        None \<Rightarrow> None
                      | |. None .| \<Rightarrow> None
                      | |. |. Node i next .| .| \<Rightarrow> if next \<in> dom (fst \<tau>)
                                                   then |. (fst \<tau>) next .|
                                                   else None)"



fun at_nextATpre:: "node val \<Rightarrow> node val"  ("(1(_).next@pre)" 50)
  where "X .next@pre = (\<lambda> \<tau>. case X \<tau> of
                        None \<Rightarrow> None
                      | |. None .| \<Rightarrow> None
                      | |. |. Node i next .| .| \<Rightarrow> if next \<in> dom (snd \<tau>)
                                                   then |. (snd \<tau>) next .|
                                                   else None)"


lemma at_next_nullstrict [simp]: "null .next = invalid"
by(rule ext, simp add: null_def invalid_def)

lemma at_nextATpre_nullstrict [simp] : "null .next@pre = invalid"
by(rule ext, simp add: null_def invalid_def)

lemma at_next_strict[simp] : "invalid .next = invalid"
by(rule ext, simp add: null_def invalid_def)

lemma at_nextATpre_strict[simp] : "invalid .next@pre = invalid"
by(rule ext, simp add: null_def invalid_def)




coinductive inv :: "'a state \<Rightarrow> 'a oid \<Rightarrow> bool" where
"st x = Some (Node i None) \<Longrightarrow> inv st x"  |
"st x = Some (Node i (Some next)) \<and> st next = Some (Node next_i next_next) \<and> i > next_i \<and> inv st next \<Longrightarrow> inv st x"

fun contents_contract :: "('a state \<Rightarrow> ('a oid option) \<Rightarrow> int set) \<Rightarrow> 'a state \<Rightarrow> ('a oid option) \<Rightarrow> bool" where
"contents_contract f st None = True" |
"contents_contract f st (Some s) = (case st s of None \<Rightarrow> True 
  | Some (Node i next) \<Rightarrow> f st (Some s) = (case next of None \<Rightarrow> {i} | Some n \<Rightarrow> f st (Some n) \<union> {i}))"

definition contents :: "'a state \<Rightarrow> ('a oid option) \<Rightarrow> int set" where
contents_post: "contents = (SOME f . \<forall> st s . contents_contract f st s)"

definition contents_at_pre :: "'a state \<Rightarrow> ('a oid option) \<Rightarrow> int set" where
contents_post2: "contents_at_pre = (SOME f . \<forall> st s . contents_contract f st s)"

lemma contents_def: "contents_at_pre st (Some s) = (case st s of None \<Rightarrow> undefined
  | Some (Node i next) \<Rightarrow> (case next of None \<Rightarrow> {i} | Some n \<Rightarrow> contents_at_pre st (Some n) \<union> {i}))"
apply(auto simp: contents_post2)
apply(case_tac "st s", simp_all)
prefer 2
apply(case_tac "a", simp_all)
apply(case_tac "option", simp_all)
sorry

declare OO_List.inv.simps [testgen_OO_eqs]
declare contents_def [testgen_OO_eqs]

test_spec "inv pre_state s \<longrightarrow> contents (post_state pre_state x) (Some s) = contents_at_pre pre_state (Some s) \<union> {x}"
apply(gen_test_cases "post_state" simp del: contents_post contents_post2)
store_test_thm "oo_test"

gen_test_data "oo_test"

thm oo_test.test_data

ML {*

val test_tac = alias_closure_tac @{context} @{typ "'a option"}

*}

lemma "(at_next st y) = (at_next st (at_next st y))" 
apply(tactic "test_tac 1")
apply(simp_all)
oops

lemma rewr: "id (x::int) = id x + id x - id x"
apply(simp)
done

lemma "(x::int) = id x"
(* apply(tactic "EqSubst.eqsubst_tac @{context} [1] [@{thm rewr}] 1") *)
apply(tactic "bounded_unfold_tac @{context} 3 @{thm rewr} 1")
oops

end