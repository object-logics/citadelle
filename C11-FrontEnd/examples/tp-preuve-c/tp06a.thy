theory tp06a
imports AutoCorres "~~/src/HOL/Number_Theory/Number_Theory"
begin

(* Parse the C file into the SIMPL language. *)
install_C_file "tp06a.c"
  
find_theorems (140)  name:"tp06"

context tp06a begin

thm is_prime_impl       (* The specification \<Gamma> maps names to program terms. *)
thm is_prime_body_def   (* This is the SIMPL model of the imported C function. *)

end

(* Abstract the SIMPL model into a monadic model. *)
autocorres[ts_rules = nondet, unsigned_word_abs = is_prime is_prime] "tp06a.c"
print_theorems

context tp06a begin
typ "('a,'b) nondet_monad"
thm is_prime'_def       (* This is the monadic model of the C function. *)
thm is_prime'_ac_corres (* This lemma relates monadic and SIMP models. *)

(* Loop invariant for "is_prime". *)
definition
  is_prime_inv :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "is_prime_inv i n \<equiv> i>1 \<and> 2 \<le> n \<and> n \<ge> i \<and> (\<forall>k<i. k>1 \<longrightarrow> n mod k \<noteq> 0) "

(* The loop invariant holds coming into the loop. *)
lemma is_prime_precond_implies_inv:
  "\<lbrakk> 2 \<le> n; n \<le> UINT_MAX \<rbrakk> \<Longrightarrow> is_prime_inv 2 n"
  by(auto simp: is_prime_inv_def)

    
(* The loop invariant holds for each loop iteration. *)
lemma is_prime_body_obeys_inv:
  "\<lbrakk> is_prime_inv i n; n mod i \<noteq> 0 \<rbrakk> \<Longrightarrow> is_prime_inv (i + 1) n"
  unfolding is_prime_inv_def apply auto
  using less_SucE apply auto
  by (metis Suc_leI le_neq_implies_less mod_self neq0_conv)
    
find_theorems (205) "prime (_::nat) = _"
thm prime_nat_simp

find_theorems "_ dvd _" "_ mod _"
thm dvd_eq_mod_eq_0[symmetric]

(* Q4. The loop invariant implies the post-condition. *)
lemma is_prime_inv_implies_postcondition:
  "\<lbrakk> is_prime_inv i n; n mod i = 0 \<rbrakk> \<Longrightarrow> (i = n) \<longleftrightarrow> prime n"
unfolding is_prime_inv_def 
proof (rule iffI, elim conjE, hypsubst) 
  assume "2 \<le> n"  and  "\<forall>k<n. 1 < k \<longrightarrow> n mod k \<noteq> 0" 
  show   "prime n"  
         by (metis Suc_eq_plus1 Suc_le_eq \<open>2 \<le> n\<close> \<open>\<forall>k<n. 1 < k \<longrightarrow> n mod k \<noteq> 0\<close> 
                  add.left_neutral dvd_eq_mod_eq_0 gr_implies_not0 less_one linorder_neqE_nat 
                  nat_dvd_not_less numeral_2_eq_2 prime_factor_nat prime_gt_1_nat)
next
  assume "1 < i \<and> 2 \<le> n \<and> i \<le> n \<and> (\<forall>k<i. 1 < k \<longrightarrow> n mod k \<noteq> 0)"
          and "n mod i = 0" and  "prime n "
  have *:  "1 < i" 
          using \<open>1 < i \<and> 2 \<le> n \<and> i \<le> n \<and> (\<forall>k<i. 1 < k \<longrightarrow> n mod k \<noteq> 0)\<close> by blast
  show "i = n"
         apply(insert `prime n` *)
         apply(subst (asm)  prime_nat_iff, clarify)
         apply(subst (asm) Divides.semiring_div_class.dvd_eq_mod_eq_0)
         apply(erule_tac x=i in allE)
         by(simp only: `n mod i = 0`,auto)
qed
        
(* Measure function for "is_prime". Must be strictly decreasing
 * for each loop iteration. *)
definition
  is_prime_measure :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "is_prime_measure i n \<equiv> (n-i) (*** Q5. TODO ***)"

(* The loop measure decrements each loop iteration. *)
lemma is_prime_body_obeys_measure:
  "\<lbrakk> is_prime_inv i n; n mod i \<noteq> 0 \<rbrakk>
      \<Longrightarrow> is_prime_measure i n > is_prime_measure (i + 1) n"
  unfolding is_prime_measure_def is_prime_inv_def
  apply auto using le_eq_less_or_eq by auto

(*
 * Show that "is_prime' n" is correct.
 *
 * AutoCorres has applied "word abstraction" to this function,
 * meaning that you are able to reason using "nats" instead of
 * "word32" data types, at the price of having to reason that
 * your values do not overflow UINT_MAX.
 *)
lemma is_prime_correct:
  "\<lbrace>\<lambda>s. n \<le> UINT_MAX \<rbrace> is_prime' n \<lbrace>\<lambda>r s. r = (if prime n then 1 else 0) \<rbrace>!"
  (* Move the precondition into the assumptions. *)
  apply (rule validNF_assume_pre)
  (* Unfold the program body. *)
  apply (unfold is_prime'_def)

  (* Annotate the loop with an invariant and measure. *)
  apply (subst whileLoop_add_inv [
               where I="\<lambda>r s. is_prime_inv r n"
               and M="(\<lambda>(r, s). Suc n - r)"])

  (*
   * Run "wp" to generate verification conditions.
   *)
proof (wp, intro conjI, elim conjE,simp_all)
  (* 1. The loop body obeys the invariant; *)
  fix s r 
  assume "n \<le> UINT_MAX"  and "is_prime_inv r n" and "0 < n mod r"  
  then show "is_prime_inv (Suc r) n"
       using is_prime_body_obeys_inv by auto
next
  (* 2. The loop body causes the measure to decrease; *)
  fix r fix sa sb::lifted_globals
    assume "n \<le> UINT_MAX" and "is_prime_inv r n \<and> 0 < n mod r \<and> sb = sa"
  then show "n - r < Suc n - r"
       by (simp add: Suc_diff_le tp06a.is_prime_inv_def)
next
  (* The loop counter never exceeds UINT_MAX. *) 
  fix r fix sa sb::lifted_globals  (* very ugly that this pops up ... *)
    assume "n \<le> UINT_MAX" and "is_prime_inv r n \<and> 0 < n mod r \<and> sb = sa"
  then show "Suc r \<le> UINT_MAX"
       by (metis Suc_eq_plus1 dual_order.trans gr_implies_not0 is_prime_body_obeys_inv 
                 tp06a.is_prime_inv_def)
next
  fix r 
    assume "n \<le> UINT_MAX" and "is_prime_inv r n" and "n mod r = 0"
  then show " (r = n \<longrightarrow> prime n) \<and> (r \<noteq> n \<longrightarrow> \<not> prime n)"   
       by (simp add: tp06a.is_prime_inv_implies_postcondition)
next
  (* The invariant implies the post-condition of the function. *) 
  assume " n \<le> UINT_MAX"
  then show " (n < 2 \<longrightarrow> \<not> prime n) \<and> (\<not> n < 2 \<longrightarrow> is_prime_inv 2 n)"
    by (metis le_antisym nat_le_linear nat_less_le prime_ge_2_nat 
              tp06a.is_prime_precond_implies_inv)
qed
  
  
end

end

