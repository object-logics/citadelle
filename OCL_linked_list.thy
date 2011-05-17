theory 
  OCL_linked_list
imports
  Mini_OCL (* Testing *)
begin


section{* Example Data-Universe *}
datatype node = Node int oid


fun at_next:: "(node,node)val \<Rightarrow> (node,node)val"  ("(1(_).next)" 50)
  where "X .next = (\<lambda> \<tau>. case X \<tau> of
                        None \<Rightarrow> None
                      | |. None .| \<Rightarrow> None
                      | |. |. Node i next .| .| \<Rightarrow> if next \<in> dom (fst \<tau>)
                                                   then |. (fst \<tau>) next .|
                                                   else None)"



fun at_nextATpre:: "(node,node)val \<Rightarrow> (node,node)val"  ("(1(_).next@pre)" 50)
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