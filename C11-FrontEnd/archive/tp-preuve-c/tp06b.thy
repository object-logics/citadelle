theory tp06b
imports "AutoCorres.AutoCorres" "~~/src/HOL/Number_Theory/Number_Theory"
begin

(* Parse the C file into SIMPL. *)
install_C_file "tp06a.c"

(* Note: The autocorres tool is not applied.
         Here we reason on the SIMPL model directly *)

context tp06a begin

thm is_prime_impl       (* The specification \<Gamma> maps names to program terms. *)
thm is_prime_body_def   (* This is the SIMPL model of the imported C function. *)

term "unat"
(* with associated tactic: apply unat_arith *)

(* Nat version of is_prime_inv. *)
definition
  is_prime_inv' :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "is_prime_inv' i n \<equiv> 2 \<le> i \<and> i \<le> n \<and> (\<forall>m < i. 2 \<le> m \<longrightarrow> n mod m \<noteq> 0)"
  
(* Loop invariant for "is_prime". *)
definition
  is_prime_inv :: "word32 \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> bool"
where
  "is_prime_inv i init_n curr_n \<equiv> is_prime_inv' (unat i) (unat init_n) \<and> init_n = curr_n"

(* Measure function for "is_prime". Must be strictly decreasing
 * for each loop iteration. *)
definition
  is_prime_measure :: "word32 \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> nat"
where
  "is_prime_measure i init_n curr_n \<equiv> unat init_n - unat i"

declare is_prime_inv_def [simp]

(* The loop invariant holds coming into the loop. *)
lemma is_prime_precond_implies_inv:
  assumes "n \<ge> 2"
  shows   "is_prime_inv 2 n n"
proof - 
  have "unat n \<ge> 2" using assms  by unat_arith
  then show ?thesis by (clarsimp simp: is_prime_inv'_def )
qed


lemma is_prime_body_obeys_inv':
  assumes "is_prime_inv' i n" 
    and   "n mod i \<noteq> 0"
  shows "is_prime_inv' (i + 1) n"
unfolding is_prime_inv'_def 
proof(clarsimp , intro conjI)
  show "Suc 0 \<le> i"  using assms(1) is_prime_inv'_def by auto
next
  show "Suc i \<le> n" by (metis Suc_leI assms(1) assms(2) le_neq_implies_less mod_self 
                              tp06a.is_prime_inv'_def)
next
  have * :"\<forall>m<i. 2 \<le> m  \<longrightarrow> 0 < n mod m"   using assms(1) tp06a.is_prime_inv'_def by blast 
  show "\<forall>m<Suc i. 2 \<le> m \<longrightarrow> 0 < n mod m"  using "*" assms(2) less_antisym by blast
qed 

(* The loop invariant holds for each loop iteration. *)
lemma is_prime_body_obeys_inv:
  "\<lbrakk> is_prime_inv i init_n curr_n; curr_n mod i \<noteq> 0 \<rbrakk> \<Longrightarrow> is_prime_inv (i + 1) init_n curr_n"
  apply clarsimp
  apply (drule is_prime_body_obeys_inv')
   apply (metis unat_eq_zero unat_mod)
  apply (clarsimp simp: is_prime_inv'_def)
proof -
  assume a1: "curr_n mod i \<noteq> 0"
  assume a2: "Suc 0 \<le> unat i"
  assume a3: "Suc (unat i) \<le> unat curr_n"
  assume a4: "\<forall>m<Suc (unat i). 2 \<le> m \<longrightarrow> 0 < unat curr_n mod m"
  { fix nn :: nat
    have ff1: "\<And>n na. (n::nat) < na \<or> \<not> n + 1 \<le> na"
      by presburger
    have ff2: "of_nat (unat curr_n mod unat i) \<noteq> (0::32 word)"
      using a1 by (metis word_arith_nat_defs(7))
    have ff3: "unat (1::32 word) = 1 \<or> (1::32 word) = 0"
      by (metis (no_types) Groups.add_ac(2) Suc_eq_plus1 add.right_neutral unatSuc unat_0)
    have ff4: "unat i \<noteq> 0"
      using a2 by linarith
    have "unat (1 + i) = 1 + unat i \<or> (0::32 word) = 1"
      using ff3 a3 by (metis (no_types) Groups.add_ac(2) Suc_eq_plus1 le_simps(2) 
                       less_Suc_unat_less_bound unat_add_lem)
    then have "unat i \<noteq> 1 \<and> 1 + i \<noteq> 0"
        using ff4 ff2 by (metis Groups.add_ac(2) Suc_eq_plus1 add_0_left mod_less_divisor nat.simps(3) 
                                neq0_conv not_less_eq semiring_1_class.of_nat_simps(1) unat_0)
    then have "2 \<le> unat (i + 1) \<and> unat (i + 1) \<le> unat curr_n \<and> 
                 (\<not> nn < unat (i + 1) \<or> \<not> 2 \<le> nn \<or> 0 < unat curr_n mod nn)"
        using ff4 ff1 a4 a3 by (metis (no_types) Divides.mod_less Groups.add_ac(2) Suc_eq_plus1 
                                      le_less linorder_not_less mod2_gr_0 neq0_conv unatSuc) }
    then show "2 \<le> unat (i + 1) \<and> unat (i + 1) \<le> unat curr_n \<and> 
               (\<forall>n<unat (i + 1). 2 \<le> n \<longrightarrow> 0 < unat curr_n mod n)"
      
    by blast
  qed
  

lemma unat_plus_one:
    "a < (b :: 'a::len word) \<Longrightarrow> unat (a + 1) = unat a + 1"
  using less_is_non_zero_p1 word_overflow_unat by blast

(* The loop measure decrements each loop iteration. *)
lemma is_prime_body_obeys_measure:
  "\<lbrakk> is_prime_inv i init_n curr_n; curr_n mod i \<noteq> 0 \<rbrakk>
      \<Longrightarrow> is_prime_measure i init_n curr_n > is_prime_measure (i + 1) init_n curr_n"
  apply (clarsimp simp: is_prime_inv'_def is_prime_measure_def)
  apply (case_tac "curr_n = i")
   apply clarsimp
   apply (metis mod_self unat_eq_zero unat_mod)
  apply (subst unat_plus_one [where b=curr_n])
   apply (metis word_le_less_eq word_le_nat_alt)
  apply (metis One_nat_def add.commute add_Suc diff_less_mono2 le_neq_implies_less
               lessI monoid_add_class.add.left_neutral word_unat.Rep_inject)
  done

(* The loop invariant implies the post-condition. *)
lemma is_prime_inv_implies_postcondition:
  "\<lbrakk> is_prime_inv i init_n curr_n; curr_n mod i = 0 \<rbrakk>
      \<Longrightarrow> prime (unat init_n) \<longleftrightarrow> (i = curr_n)"
proof -
  have prime_nat_code: "(prime :: nat \<Rightarrow> bool) = (\<lambda>p. p > 1 \<and> (\<forall>n \<in> {1<..<p}. ~ n dvd p))"
    apply (rule ext)
  using prime_nat_naive by auto
show "\<lbrakk> is_prime_inv i init_n curr_n; curr_n mod i = 0 \<rbrakk> \<Longrightarrow> ?thesis"
  apply (clarsimp simp: is_prime_inv'_def)
  apply (rule iffI)
   apply (clarsimp simp: prime_nat_code)
   apply (metis (no_types, hide_lams) greaterThanLessThan_iff le_neq_implies_less less_eq_Suc_le 
                less_numeral_extra(3) mod_greater_zero_iff_not_dvd numeral_2_eq_2 unat_0 unat_mod 
                word_unat.Rep_inject)
  apply (clarsimp simp: prime_nat_iff')
  apply (drule_tac x=n in spec)
  apply (metis Suc_1 arith_is_1  dvd_imp_mod_0  eq_iff less_eq_Suc_le  not_less_eq_eq )
  done
qed

(*
 * Show that "is_prime' n" is correct.
 *
 * Note that there are two ways of writing variables: \<acute>n and
 * (n_' s). The first fetches the value "n" from an implicitly
 * specified state, while the second fetches the value "n" from state
 * "s". While less pretty, it is generally easier to use the latter.
 *)
lemma is_prime_correct:
   "\<Gamma> \<turnstile>\<^sub>t {s. n_' s = n }
          \<acute>ret__unsigned :== PROC is_prime(n)
        {t. ret__unsigned_' t = (if prime (unat n) then 1 else 0) }"
  (* Unfold the program's body. *)
  apply (hoare_rule HoareTotal.ProcNoRec1)
  apply (unfold creturn_def)

  (* Annotate the loop with an invariant and measure. *)
  apply (subst whileAnno_def)
  apply (subst whileAnno_def [symmetric, where
       I="{s. is_prime_inv (i_' s) n (n_' s) }" and
       V="measure (\<lambda>s. is_prime_measure (i_' s) n (n_' s))"])

  (*
   * Run the VCG.
   *
   * You will need to prove (i) the function's precondition implies your
   * loop's invariant; (ii) the loop invariant holds each time the loop
   * executes; (iii) the measure decreases each time the loop exceutes;
   * and (iv) when the loop has finished, the loop invariant implies the
   * functions post-condition.
   *
   * Spend some time looking at the vcg's output to make sure you know
   * what the goals it is leaving you correspond to.
   *)
  apply vcg
    apply (clarsimp simp del: is_prime_inv_def)
    apply rule
     apply (fastforce dest: x_less_2_0_1)
    apply (clarsimp simp del: is_prime_inv_def)
    apply (rule is_prime_precond_implies_inv, simp)
   apply (clarsimp simp del: is_prime_inv_def)
   apply (intro conjI)
    apply (clarsimp simp: is_prime_inv'_def)
    apply (metis le_eq_less_or_eq less_is_non_zero_p1 mod_self
        unat_eq_zero unat_mod word_less_nat_alt word_unat.Rep_inject)
   apply (erule (1) is_prime_body_obeys_measure)
   apply (erule (1) is_prime_body_obeys_inv)
  apply (drule is_prime_inv_implies_postcondition)
   apply simp
  apply clarsimp
  done

    
lemma is_prime_correct_structured:
   "\<Gamma> \<turnstile>\<^sub>t {s. n_' s = n }
          \<acute>ret__unsigned :== PROC is_prime(n)
        {t. ret__unsigned_' t = (if prime (unat n) then 1 else 0) }"
  (* Unfold the program's body. *)
  apply (hoare_rule HoareTotal.ProcNoRec1,unfold creturn_def)

  (* Annotate the loop with an invariant and measure. *)
  apply (subst whileAnno_def)
  apply (subst whileAnno_def [symmetric, where
                                           I="{s. is_prime_inv (i_' s) n (n_' s) }" and
                                           V="measure (\<lambda>s. is_prime_measure (i_' s) n (n_' s))"])

  proof vcg  (* run vcg, the verification condition generator *)
     text{* prove (i) the function's precondition implies your loop's invariant *}
     fix n::"32 word"
     show "(n < scast (2::32 signed word) 
                \<longrightarrow> scast (0::32 signed word) = (if prime (unat n) then 1 else 0)) \<and> 
            (\<not> n < scast (2::32 signed word) 
                \<longrightarrow> scast (2::32 signed word) \<noteq> (0::32  word) 
                    \<and> is_prime_inv (scast (2::32 signed word)) n n)" 
          apply (clarsimp simp del: is_prime_inv_def, rule)
           apply (fastforce dest: x_less_2_0_1, rule)
          by (rule is_prime_precond_implies_inv, simp)
  next
    text{* prove  loop correctness: *}     
     fix n' i ::"32 word" 
     assume *:"is_prime_inv i n n'"
      and   **:"n' mod i \<noteq> scast (0::32 signed word)"
      have  ***:  "i + 1 \<noteq> 0" apply (insert * **, clarsimp simp del: is_prime_inv_def)
                              apply (clarsimp simp: is_prime_inv'_def)
                               by (metis le_eq_less_or_eq less_is_non_zero_p1 mod_self
                                         unat_eq_zero unat_mod word_less_nat_alt word_unat.Rep_inject)
     show   "i + scast (1::32 signed word) \<noteq> (0::32 word) 
             \<and> is_prime_measure (i + scast (1::32 signed word)) n n' < is_prime_measure i n n' 
             \<and> is_prime_inv (i + scast (1::32 signed word)) n n'"   
            proof(auto simp: *** simp del: is_prime_inv_def)
              text{* This breaks down to prove (ii) the loop measure decreases *}
              show "is_prime_measure (i + 1) n n' < is_prime_measure i n n'"
                using "*" "**" is_prime_body_obeys_measure by auto
            next
              text{* and to prove (iii) invariant holds each time the loop executes*}
              show "is_prime_inv (i + 1) n n'"
                using "*" "**" is_prime_body_obeys_inv by auto
            qed
  next
     text{* prove (iv) when the loop has finished, the loop invariant implies the  post-condition*}        
     fix n' i ::"32 word" 
     assume *:"is_prime_inv i n n'"
      and   **:"\<not> n' mod i \<noteq> scast (0::32 signed word)"
     show    "scast (if i = n' then 1 else (0::32 signed word)) = 
              (if prime (unat n) then 1 else 0)"
             by (insert * **,drule is_prime_inv_implies_postcondition) clarsimp+
  qed    

text{* The comparison of these two styles is interesting: one the one hand, the apply style is
much shorter since all the hairy details of typing words and constants 0 and 1's were implicitly
and safely inferred from prior proof states; on the other hand, a fine eye for these gory details
reveals much of the underlying semantic complexity going on in this proof. *}

    
end

end

