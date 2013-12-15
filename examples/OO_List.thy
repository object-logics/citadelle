theory 
  OO_List
imports
  Testing
begin

ML {*

fun bounded_unfold_tac ctxt bound eq n thm = let
  val s = size_of_term (prop_of thm)
  fun tac k = EqSubst.eqsubst_tac ctxt (1 upto k) [eq]
  val step_tac = FIRST' (map tac (s downto 1))
in
  REPEAT_DETERM_N bound (step_tac n) thm
end

structure OO_eqs
  = Named_Thms(val name = "testgen_OO_eqs" val description = "Equations for deriving object-oriented tests");

fun bounded_unfold_all_tac ctxt = 
  EVERY' (map (fn eq => bounded_unfold_tac ctxt (Config.get ctxt TestEnv.depth) eq) (OO_eqs.get ctxt)) 

fun fold_terms f (t as (u $ v)) = f t #> fold_terms f u #> fold_terms f v
  | fold_terms f (t as (Abs (_, _, u))) = f t #> fold_terms f u
  (* | fold_terms _ (Bound _) = I *)
  | fold_terms f a = f a;

fun alias_closure_tac ctxt ref_typ = 
    Subgoal.FOCUS_PREMS(fn {context, ...} => 
                           (fn thm => let
  val thy = ProofContext.theory_of context
  val prem = Logic.nth_prem(1, prop_of thm)
  val refs = fold_terms (fn t => (if type_of t = ref_typ then insert (op =) t else I) handle Term.TYPE _ => I) prem []
  fun pairs (x::xs) = (map (fn y => (x,y)) xs) @ (pairs xs)
  | pairs [] = []

  val eqs = map ((cterm_of thy) o HOLogic.mk_eq) (pairs refs)
  val P = cterm_of thy (Var (("P",0), @{typ "bool"}))
  fun tac eq = ALLGOALS (TacticPatch.res_terminst_tac [] [(P, eq)] @{thm "case_split"})
in
  (EVERY (map tac eqs)) thm
end)) ctxt 

*}

setup {*
OO_eqs.setup
*}

setup{* TestEnv.map_data_global (TestEnv.add_test_derivation_rule (
                fn ctxt => fn n => fn thm =>
  ([(200, TestGen.ALLCASES (bounded_unfold_all_tac ctxt))])))
*}

setup{* TestEnv.map_data_global (TestEnv.add_test_derivation_rule (
                fn ctxt => fn n => fn thm =>
  ([(30, TestGen.ALLCASES (alias_closure_tac ctxt @{typ "'a option"}))])))
*}

type_synonym 'a oid = 'a

datatype 'a node = Node int "('a oid option)"

type_synonym 'a state = "'a oid \<rightharpoonup> 'a node"

fun at_next:: "'a state \<Rightarrow> ('a oid option) \<rightharpoonup> 'a oid" where
"at_next st None = None"  
| "at_next st (Some x) = (if x \<in> dom st then (case the (st x) of (Node i next) \<Rightarrow> next) 
                                        else None)"

fun at_next2:: "'a state \<Rightarrow> ('a oid option) \<rightharpoonup> 'a oid" where
"at_next2 st None = None" 
| "at_next2 st (Some x) = (case st x of (Some (Node i next)) \<Rightarrow> next | None \<Rightarrow> None)"

lemma strict : "at_next st None = None"
apply(simp)
done

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
