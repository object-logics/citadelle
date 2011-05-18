theory 
  Mini_OCL
imports
  Main (* Testing *)
begin

section{* OCL Core Definitions *}

subsection{* State, State Transitions, Well-formed States *}
type_synonym oid = ind

fun    drop :: "'\<alpha> option \<Rightarrow> '\<alpha>" ("|^(_)^|")
where "drop (Some v) = v "

syntax
  "lift"        :: "'\<alpha> \<Rightarrow> '\<alpha> option"   ("|.(_).|")
translations
  "|.a.|" == "CONST Some a"

type_synonym ('\<AA>) state = "oid \<rightharpoonup> '\<AA> "

type_synonym ('\<AA>)st = "'\<AA> state \<times> '\<AA> state"


class object =
  fixes oid_of :: "'a \<Rightarrow> oid"

text{* A key-concept for linking strict referential equality to
       logical equality: in well-formed states (i.e. those
       states where the self (oid-of) field contains the pointer
       to which the object is associated to in the state), 
       referential equality coincides with logical equality. *}

definition WFF :: "('\<AA>::object)st \<Rightarrow> bool"
where "WFF \<tau> = ((\<forall> x \<in> dom(fst \<tau>). x = oid_of(the(fst \<tau> x))) \<and>
                (\<forall> x \<in> dom(snd \<tau>). x = oid_of(the(snd \<tau> x))))"

text{* This is a generic definition of referential equality:
Equality on objects in a state is reduced to equality on the
references to these objects. As in HOL-OCL, we will store
the reference of an object inside the object in a (ghost) field.
By establishing certain invariants ("consistent state"), it can
be assured that there is a "one-to-one-correspondance" of objects
to their references --- and therefore the definition below
behaves as we expect. *}
text{* Generic Referential Equality enjoys the usual properties:
(quasi) reflexivity, symmetry, transitivity, substitutivity for
defined values. For type-technical reasons, for each concrete
object type, the equality \<doteq> is defined by generic referential
equality. *}

subsection{* Valuations *}

type_synonym ('\<AA>,'\<alpha>) val = "'\<AA> st \<Rightarrow> '\<alpha> option option"

definition invalid :: "('\<AA>,'\<alpha>) val" 
where     "invalid \<equiv> \<lambda> \<tau>. None"

definition null :: "('\<AA>,'\<alpha>) val" 
where     "null \<equiv> \<lambda> \<tau>. |. None .| "


subsection{* Boolean Type and Logic *}

type_synonym ('\<AA>)Boolean = "('\<AA>,bool) val"
type_synonym ('\<AA>)Integer = "('\<AA>,int) val"

definition true :: "('\<AA>)Boolean"
where     "true \<equiv> \<lambda> \<tau>. |. |. True .| .|"

definition false :: "('\<AA>)Boolean"
where     "false \<equiv>  \<lambda> \<tau>. |. |. False .| .|"

lemma bool_split: "X \<tau> = invalid \<tau> \<or> X \<tau> = null \<tau> \<or> 
                   X \<tau> = true \<tau> \<or> X \<tau> = false \<tau>"
apply(simp add: invalid_def null_def true_def false_def)
apply(case_tac "X \<tau>",simp)
apply(case_tac "a",simp)
apply(case_tac "aa",simp)
apply auto
done


lemma [simp]: "false (a, b) = |.|.False.|.|"
by(simp add:false_def)

lemma [simp]: "true (a, b) = |.|.True.|.|"
by(simp add:true_def)


section{* Logical (Strong) Equality and Definedness *}

definition StrongEq::"[('\<AA>,'\<alpha>)val,('\<AA>,'\<alpha>)val] \<Rightarrow> ('\<AA>)Boolean"  (infixl "\<triangleq>" 30)
where     "X \<triangleq> Y \<equiv>  \<lambda> \<tau>. |. |. X \<tau> = Y \<tau> .| .|"

lemma cp_StrongEq: "(X \<triangleq> Y) \<tau> = ((\<lambda> _. X \<tau>) \<triangleq> (\<lambda> _. Y \<tau>)) \<tau>"
by(simp add: StrongEq_def)

lemma StrongEq_refl [simp]: "(X \<triangleq> X) = true"
by(rule ext, simp add: null_def invalid_def true_def false_def StrongEq_def)

lemma StrongEq_sym [simp]: "(X \<triangleq> Y) = (Y \<triangleq> X)"
by(rule ext, simp add: eq_sym_conv invalid_def true_def false_def StrongEq_def)

lemma StrongEq_trans_strong [simp]:
  assumes A: "(X \<triangleq> Y) = true"
  and     B: "(Y \<triangleq> Z) = true"
  shows   "(X \<triangleq> Z) = true"
  apply(insert A B) apply(rule ext)
  apply(simp add: null_def invalid_def true_def false_def StrongEq_def)
  apply(drule_tac x=x in fun_cong)+
  by auto

(* Build class for referential equality *)
(* However this does not work - too many type-vars \<dots>
class ref_eq =
   fixes RefEq :: "[('\<AA>,'\<alpha>)val,('\<AA>,'\<alpha>)val] \<Rightarrow> ('\<AA>)Boolean" (infixl "\<doteq>" 30)
*)
definition defined :: "('\<AA>,'a)val \<Rightarrow> ('\<AA>)Boolean" ("\<delta> _" [100]100)
where   "\<delta> X \<equiv>  \<lambda> \<tau> . case X \<tau> of
                            None \<Rightarrow> false \<tau>
                       | |. None .| \<Rightarrow> false \<tau>
                       | |. |. x .| .| \<Rightarrow> true \<tau>"

lemma cp_defined:"(\<delta> X)\<tau> = (\<delta> (\<lambda> _. X \<tau>)) \<tau>"
by(simp add: defined_def)

lemma defined1[simp]: "\<delta> invalid = false"
  by(rule ext,simp add: defined_def null_def invalid_def true_def false_def)

lemma defined2[simp]: "\<delta> null = false"
  by(rule ext,simp add: defined_def null_def invalid_def true_def false_def)

lemma defined3[simp]: "\<delta> \<delta> X = true"
  apply(rule ext,simp add: defined_def null_def invalid_def true_def false_def)
  apply(case_tac "X x", simp_all add: true_def false_def)
  apply(case_tac "a", simp_all add: true_def false_def)
  done

lemma defined4[simp]: "\<delta> (X \<triangleq> Y) = true"
  by(rule ext,
     simp add: defined_def null_def invalid_def StrongEq_def true_def false_def)


section{* Logical Connectives and their Universal Properties *}

definition not :: "('\<AA>)Boolean \<Rightarrow> ('\<AA>)Boolean"
where     "not X \<equiv>  \<lambda> \<tau> . case X \<tau> of
                             None \<Rightarrow> None
                           | |. None .| \<Rightarrow> |. None .|
                           | |. |. x .| .| \<Rightarrow> |. |. \<not> x .| .|"

lemma cp_not: "(not X)\<tau> = (not (\<lambda> _. X \<tau>)) \<tau>"
by(simp add: not_def)

lemma not1[simp]: "not invalid = invalid"
  by(rule ext,simp add: not_def null_def invalid_def true_def false_def)

lemma not2[simp]: "not null = null"
  by(rule ext,simp add: not_def null_def invalid_def true_def false_def)

lemma not3[simp]: "not true = false"
  by(rule ext,simp add: not_def null_def invalid_def true_def false_def)

lemma not4[simp]: "not false = true"
  by(rule ext,simp add: not_def null_def invalid_def true_def false_def)


lemma not_not[simp]: "not (not X) = X"
  apply(rule ext,simp add: not_def null_def invalid_def true_def false_def)
  apply(case_tac "X x", simp_all)
  apply(case_tac "a", simp_all)
  done

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
                                          | |.None.| \<Rightarrow> |.None.|
                                          | |.|.True.|.| \<Rightarrow>  None
                                          | |.|.False.|.| \<Rightarrow>  |.|.False.|.|)
                        | |. |. True .| .| \<Rightarrow> (case Y \<tau> of
                                              None \<Rightarrow>  None
                                          | |.None.| \<Rightarrow> None
                                          | |.|.y.|.| \<Rightarrow>  |.|. y .|.|)
                        | |. |. False .| .| \<Rightarrow>  |.|. False .|.|)"


definition ocl_or :: "[('\<AA>)Boolean, ('\<AA>)Boolean] \<Rightarrow> ('\<AA>)Boolean"
                                                         (infixl "or" 25)
where    "X or Y \<equiv> not(not X and not Y)"

definition ocl_implies :: "[('\<AA>)Boolean, ('\<AA>)Boolean] \<Rightarrow> ('\<AA>)Boolean"
                                                         (infixl "implies" 25)
where    "X implies Y \<equiv> not X or Y"

lemma cp_ocl_and:"(X and Y) \<tau> = ((\<lambda> _. X \<tau>) and (\<lambda> _. Y \<tau>)) \<tau>"
by(simp add: ocl_and_def)

lemma cp_ocl_or:"((X::('\<AA>)Boolean) or Y) \<tau> = ((\<lambda> _. X \<tau>) or (\<lambda> _. Y \<tau>)) \<tau>"
apply(simp add: ocl_or_def)
apply(subst cp_not[of "not (\<lambda>_. X \<tau>) and not (\<lambda>_. Y \<tau>)"])
apply(subst cp_ocl_and[of "not (\<lambda>_. X \<tau>)" "not (\<lambda>_. Y \<tau>)"])
by(simp add: cp_not[symmetric] cp_ocl_and[symmetric] )

(*
proof(unfold ocl_or_def)
   fix X::"('\<AA>)Boolean" and Y::"('\<AA>)Boolean"
   assume A : "not (not X and not Y) \<tau> = not (not (\<lambda>_. X \<tau>) and not (\<lambda>_. Y \<tau>)) \<tau> "
   have 1: "not (not X and not Y) \<tau> = 
               not (\<lambda> _. ( (\<lambda> _. not (\<lambda> _. X \<tau>) \<tau>)  and (\<lambda> _. not (\<lambda> _. Y \<tau>) \<tau>)) \<tau>) \<tau>"
           by(simp add: cp_not[symmetric] cp_ocl_and[symmetric] )
   have 2: "not (not (\<lambda>_. X \<tau>) and not (\<lambda>_. Y \<tau>)) \<tau> =
               not (\<lambda> _. ( (\<lambda> _. not (\<lambda> _. X \<tau>) \<tau>)  and (\<lambda> _. not (\<lambda> _. Y \<tau>) \<tau>)) \<tau>) \<tau>"
           by(simp add: cp_ocl_and[symmetric], subst cp_not, simp)
   show ?thesis 
Why the heck does this not work !!!
*)

lemma cp_ocl_implies:"(X implies Y) \<tau> = ((\<lambda> _. X \<tau>) implies (\<lambda> _. Y \<tau>)) \<tau>"
apply(simp add: ocl_implies_def)
apply(subst cp_ocl_or[of "not (\<lambda>_. X \<tau>)" "(\<lambda>_. Y \<tau>)"])
by(simp add: cp_not[symmetric] cp_ocl_or[symmetric] )


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
lemma and7[simp]: "(null and null) = null"
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

lemma and13[simp]: "(true and true) = true"
  by(rule ext,simp add: ocl_and_def null_def invalid_def true_def false_def)
lemma and14[simp]: "(true and false) = false"
  by(rule ext,simp add: ocl_and_def null_def invalid_def true_def false_def)
lemma and15[simp]: "(true and null) = invalid"
  by(rule ext,simp add: ocl_and_def null_def invalid_def true_def false_def)
lemma and16[simp]: "(true and invalid) = invalid"
  by(rule ext,simp add: ocl_and_def null_def invalid_def true_def false_def)

lemma and_idem[simp]: "(X and X) = X"
  apply(rule ext,simp add: ocl_and_def null_def invalid_def true_def false_def)
  apply(case_tac "X x", simp_all)
  apply(case_tac "a", simp_all)
  apply(case_tac "aa", simp_all)
  done

lemma and_commute: "(X and Y) = (Y and X)"
  by(rule ext,auto simp:true_def false_def ocl_and_def invalid_def 
                   split: option.split option.split_asm
                          bool.split bool.split_asm)


lemma and_false1[simp]: "(false and X) = false"
  apply(rule ext, simp add: ocl_and_def)
  apply(auto simp:true_def false_def invalid_def 
             split: option.split option.split_asm)
  done

lemma and_false2[simp]: "(X and false) = false"
  by(simp add: and_commute) 

(* gilt nicht: true and null.
lemma and_false1[simp]: "(true and X) = X"
  apply(rule ext, simp add: ocl_and_def)
  apply(auto simp:true_def false_def invalid_def 
             split: option.split option.split_asm)
  done
*)

lemma or_idem[simp]: "(X or X) = X"
  by(simp add: ocl_or_def)

lemma or_commute: "(X or Y) = (Y or X)"
  by(simp add: ocl_or_def and_commute)

lemma and_assoc: "(X and (Y and Z)) = (X and Y and Z)"
  apply(rule ext, simp add: ocl_and_def)
  apply(auto simp:true_def false_def invalid_def 
                            split: option.split option.split_asm
                                   bool.split bool.split_asm)
done




lemma or_assoc: "(X or (Y or Z)) = (X or Y or Z)"
  by(simp add: ocl_or_def and_assoc)

lemma deMorgan1: "not(X and Y) = ((not X) or (not Y))"
  by(simp add: ocl_or_def)

lemma deMorgan2: "not(X or Y) = ((not X) and (not Y))"
  by(simp add: ocl_or_def)
 
section{* Logical Equality and Referential Equality *}

text{* Construction by overloading: for each base type, there is an equality.*}

consts StrictRefEq :: "[('\<AA>,'a)val,('\<AA>,'a)val] \<Rightarrow> ('\<AA>)Boolean" (infixl "\<doteq>" 30)

defs   StrictRefEq_int : "(x::('\<AA>,int)val) \<doteq> y \<equiv>
                             \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                                  then (x \<triangleq> y)\<tau>
                                  else invalid \<tau>"

lemma StrictRefEq_int_strict1[simp] : "((x::('\<AA>,int)val) \<doteq> invalid) = invalid"
by(rule ext, simp add: StrictRefEq_int true_def false_def)

lemma StrictRefEq_int_strict2[simp] : "(invalid \<doteq> (x::('\<AA>,int)val)) = invalid"
by(rule ext, simp add: StrictRefEq_int true_def false_def)

lemma StrictRefEq_int_strict3[simp] : "((x::('\<AA>,int)val) \<doteq> null) = invalid"
by(rule ext, simp add: StrictRefEq_int true_def false_def)

lemma StrictRefEq_int_strict4[simp] : "(null \<doteq> (x::('\<AA>,int)val)) = invalid"
by(rule ext, simp add: StrictRefEq_int true_def false_def)


lemma StrictRefEq_int_strict :
  assumes A: "\<delta> (x::('\<AA>,int)val) = true"
  and     B: "\<delta> y = true"
  shows   "\<delta> (x \<doteq> y) = true"
  apply(insert A B)
  apply(rule ext, simp add: StrongEq_def StrictRefEq_int true_def defined_def)
  done


lemma StrictRefEq_int_strict' :
  assumes A: "\<delta> ((x::('\<AA>,int)val) \<doteq> y) = true"
  shows      "\<delta> x = true \<and> \<delta> y = true"
  apply(insert A, rule conjI) 
  apply(rule ext, drule_tac x=xa in fun_cong)
  prefer 2
  apply(rule ext, drule_tac x=xa in fun_cong)
  apply(simp_all add: StrongEq_def StrictRefEq_int 
                            false_def true_def defined_def)
  apply(case_tac "y xa", auto)
  apply(simp_all add: true_def invalid_def)
  apply(case_tac "aa", auto simp:true_def false_def invalid_def 
                            split: option.split option.split_asm)
  done



defs   StrictRefEq_bool : "(x::('\<AA>,bool)val) \<doteq> y \<equiv>
                             \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                                  then (x \<triangleq> y)\<tau>
                                  else invalid \<tau>"

lemma StrictRefEq_bool_strict1[simp] : "((x::('\<AA>,bool)val) \<doteq> invalid) = invalid"
by(rule ext, simp add: StrictRefEq_bool true_def false_def)

lemma StrictRefEq_bool_strict2[simp] : "(invalid \<doteq> (x::('\<AA>,bool)val)) = invalid"
by(rule ext, simp add: StrictRefEq_bool true_def false_def)

lemma StrictRefEq_bool_strict3[simp] : "((x::('\<AA>,bool)val) \<doteq> null) = invalid"
by(rule ext, simp add: StrictRefEq_bool true_def false_def)

lemma StrictRefEq_bool_strict4[simp] : "(null \<doteq> (x::('\<AA>,bool)val)) = invalid"
by(rule ext, simp add: StrictRefEq_bool true_def false_def)

lemma cp_StrictRefEq_bool: 
"((X::('\<AA>,bool)val) \<doteq> Y) \<tau> = ((\<lambda> _. X \<tau>) \<doteq> (\<lambda> _. Y \<tau>)) \<tau>"
by(auto simp: StrictRefEq_bool StrongEq_def invalid_def  cp_defined[symmetric])

lemma cp_StrictRefEq_int: 
"((X::('\<AA>,int)val) \<doteq> Y) \<tau> = ((\<lambda> _. X \<tau>) \<doteq> (\<lambda> _. Y \<tau>)) \<tau>"
by(auto simp: StrictRefEq_int StrongEq_def invalid_def  cp_defined[symmetric])


lemma StrictRefEq_strict :
  assumes A: "\<delta> (x::('\<AA>,int)val) = true"
  and     B: "\<delta> y = true"
  shows   "\<delta> (x \<doteq> y) = true"
  apply(insert A B)
  apply(rule ext, simp add: StrongEq_def StrictRefEq_int true_def defined_def)
  done

text{* Generic referential equality - to be used for instantiations
 with concrete object types ... *}
definition "gen_ref_eq (x::('\<AA>,'a::object)val) y
            \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                   then |.|. (oid_of |^|^(x \<tau>)^|^|) = (oid_of |^|^(y \<tau>)^|^|) .|.|
                   else invalid \<tau>"

lemma gen_ref_eq_object_strict1[simp] : "(gen_ref_eq (x::('\<AA>,'a::object)val) invalid) = invalid"
by(rule ext, simp add: gen_ref_eq_def true_def false_def)

lemma gen_ref_eq_object_strict2[simp] : "(gen_ref_eq invalid (x::('\<AA>,'a::object)val)) = invalid"
by(rule ext, simp add: gen_ref_eq_def true_def false_def)

lemma gen_ref_eq_object_strict3[simp] : "(gen_ref_eq (x::('\<AA>,'a::object)val) null) = invalid"
by(rule ext, simp add: gen_ref_eq_def true_def false_def)

lemma gen_ref_eq_object_strict4[simp] : "(gen_ref_eq null (x::('\<AA>,'a::object)val)) = invalid"
by(rule ext, simp add: gen_ref_eq_def true_def false_def)

lemma cp_gen_ref_eq_object: 
"(gen_ref_eq x (y::('\<AA>,'a::object)val)) \<tau> = 
 (gen_ref_eq (\<lambda>_. x \<tau>) (\<lambda>_. y \<tau>)) \<tau>"
by(auto simp: gen_ref_eq_def StrongEq_def invalid_def  cp_defined[symmetric])



section{* Local Validity *}
definition OclValid  :: "[('\<AA>)st, ('\<AA>)Boolean] \<Rightarrow> bool" ("(1(_)/ \<Turnstile> (_))" 50)
where     "\<tau> \<Turnstile> P \<equiv> ((P \<tau>) = true \<tau>)"

section{* Global vs. Local Judgements*}
lemma transform1: "P = true \<Longrightarrow> \<tau> \<Turnstile> P"
by(simp add: OclValid_def)

lemma transform2: "(P = Q) \<Longrightarrow> ((\<tau> \<Turnstile> P) = (\<tau> \<Turnstile> Q))"
by(auto simp: OclValid_def)

lemma transform2_rev: "\<forall> \<tau>. (\<tau> \<Turnstile> \<delta> P) \<and> (\<tau> \<Turnstile> \<delta> Q) \<and> (\<tau> \<Turnstile> P) = (\<tau> \<Turnstile> Q) \<Longrightarrow> P = Q"
apply(rule ext,auto simp: OclValid_def true_def defined_def)
apply(erule_tac x=a in allE)
apply(erule_tac x=b in allE)
apply(auto simp: false_def true_def defined_def
                 split: option.split option.split_asm)
done
(* Something stronger is possible here (consider P null, Q invalid),
   but this thingi should do for our purpose *)

text{* However, certain properties (like transitivity) can not
       be \emph{transformed} from the global level to the local one, 
       they have to be re-proven on the local level. *}

lemma transform3: 
assumes H : "P = true \<Longrightarrow> Q = true"
shows "\<tau> \<Turnstile> P \<Longrightarrow> \<tau> \<Turnstile> Q"
apply(simp add: OclValid_def)
apply(rule H[THEN fun_cong])
apply(rule ext)
oops

section{* Local Validity and Meta-logic*}

lemma foundation1[simp]: "\<tau> \<Turnstile> true"
by(auto simp: OclValid_def)

lemma foundation2[simp]: "\<not>(\<tau> \<Turnstile> false)"
by(auto simp: OclValid_def true_def false_def)

lemma foundation3[simp]: "\<not>(\<tau> \<Turnstile> invalid)"
by(auto simp: OclValid_def true_def false_def invalid_def)

lemma foundation4[simp]: "\<not>(\<tau> \<Turnstile> null)"
by(auto simp: OclValid_def true_def false_def null_def)

lemma bool_split_local[simp]: 
"(\<tau> \<Turnstile> (x \<triangleq> invalid)) \<or> (\<tau> \<Turnstile> (x \<triangleq> null)) \<or> (\<tau> \<Turnstile> (x \<triangleq> true)) \<or> (\<tau> \<Turnstile> (x \<triangleq> false))" 
apply(insert bool_split[of x \<tau>], auto)
apply(simp_all add: OclValid_def StrongEq_def true_def null_def invalid_def)
done

lemma def_split_local: 
"(\<tau> \<Turnstile> \<delta> x) = ((\<not>(\<tau> \<Turnstile> (x \<triangleq> invalid))) \<and> (\<not> (\<tau> \<Turnstile> (x \<triangleq> null))))"
apply(simp add:defined_def true_def false_def invalid_def null_def 
               StrongEq_def OclValid_def)
apply(case_tac "x \<tau>",simp,simp add:false_def)
apply(case_tac "a",simp only:)
apply(simp_all add:false_def true_def)
done

lemma foundation5: 
"\<tau> \<Turnstile> (P and Q) \<Longrightarrow> (\<tau> \<Turnstile> P) \<and> (\<tau> \<Turnstile> Q)"
by(simp add: ocl_and_def OclValid_def true_def false_def defined_def
             split: option.split option.split_asm bool.split bool.split_asm)

lemma foundation6: 
"\<tau> \<Turnstile> P \<Longrightarrow> \<tau> \<Turnstile> \<delta> P"
by(simp add: not_def OclValid_def true_def false_def defined_def
             split: option.split option.split_asm)


lemma foundation7[simp]: 
"(\<tau> \<Turnstile> not (\<delta> x)) = (\<not> (\<tau> \<Turnstile> \<delta> x))"
by(simp add: not_def OclValid_def true_def false_def defined_def
             split: option.split option.split_asm)

text{* Key theorem for the Delta-closure: either an expression
is defined, or it can be replaced (substituted via StrongEq_L_subst2; see
below) by invalid or null. Strictness-reduction rules will usually 
reduce these substituted terms drastically.  *}
lemma foundation8: 
"(\<tau> \<Turnstile> \<delta> x) \<or> (\<tau> \<Turnstile> (x \<triangleq> invalid)) \<or> (\<tau> \<Turnstile> (x \<triangleq> null))"
proof -
  have 1 : "(\<tau> \<Turnstile> \<delta> x) \<or> (\<not>(\<tau> \<Turnstile> \<delta> x))" by auto
  have 2 : "(\<not>(\<tau> \<Turnstile> \<delta> x)) = ((\<tau> \<Turnstile> (x \<triangleq> invalid)) \<or> (\<tau> \<Turnstile> (x \<triangleq> null)))"
           by(simp only: def_split_local, simp) 
  show ?thesis by(insert 1, simp add:2)
qed

lemma foundation9:
"\<tau> \<Turnstile> \<delta> x \<Longrightarrow> (\<tau> \<Turnstile> not x) = (\<not> (\<tau> \<Turnstile> x))"
apply(simp add: def_split_local)
by(auto simp: not_def OclValid_def invalid_def true_def null_def StrongEq_def)


lemma foundation10:
"\<tau> \<Turnstile> \<delta> x \<Longrightarrow> \<tau> \<Turnstile> \<delta> y \<Longrightarrow> (\<tau> \<Turnstile> (x and y)) = ( (\<tau> \<Turnstile> x) \<and> (\<tau> \<Turnstile> y))"
apply(simp add: def_split_local)
by(auto simp: ocl_and_def OclValid_def invalid_def 
              true_def null_def StrongEq_def
        split:bool.split_asm)


lemma foundation11:
"\<tau> \<Turnstile> \<delta> x \<Longrightarrow>  \<tau> \<Turnstile> \<delta> y \<Longrightarrow> (\<tau> \<Turnstile> (x or y)) = ( (\<tau> \<Turnstile> x) \<or> (\<tau> \<Turnstile> y))"
apply(simp add: def_split_local)
by(auto simp: not_def ocl_or_def ocl_and_def OclValid_def invalid_def 
              true_def null_def StrongEq_def
        split:bool.split_asm bool.split)



lemma foundation12:
"\<tau> \<Turnstile> \<delta> x \<Longrightarrow>  \<tau> \<Turnstile> \<delta> y \<Longrightarrow> (\<tau> \<Turnstile> (x implies y)) = ( (\<tau> \<Turnstile> x) \<longrightarrow> (\<tau> \<Turnstile> y))"
apply(simp add: def_split_local)
by(auto simp: not_def ocl_or_def ocl_and_def ocl_implies_def 
              OclValid_def invalid_def true_def null_def StrongEq_def
        split:bool.split_asm bool.split)


lemma strictEqBool_vs_strongEq: 
"\<tau> \<Turnstile>(\<delta> x) \<Longrightarrow> \<tau> \<Turnstile>(\<delta> y) \<Longrightarrow> (\<tau> \<Turnstile> ((x::('\<AA>,bool)val) \<doteq> y)) = (\<tau> \<Turnstile> (x \<triangleq> y))"
by(simp add: StrictRefEq_bool OclValid_def)

lemma strictEqInt_vs_strongEq: 
"\<tau> \<Turnstile>(\<delta> x) \<Longrightarrow> \<tau> \<Turnstile>(\<delta> y) \<Longrightarrow> (\<tau> \<Turnstile> ((x::('\<AA>,int)val) \<doteq> y)) = (\<tau> \<Turnstile> (x \<triangleq> y))"
by(simp add: StrictRefEq_int OclValid_def)

lemma strictEqGen_vs_strongEq: 
"WFF \<tau> \<Longrightarrow> \<tau> \<Turnstile>(\<delta> x) \<Longrightarrow> \<tau> \<Turnstile>(\<delta> y) \<Longrightarrow> 
 (\<tau> \<Turnstile> (gen_ref_eq (x::('b::object,'a::object)val) y)) = (\<tau> \<Turnstile> (x \<triangleq> y))"
apply(auto simp: gen_ref_eq_def OclValid_def WFF_def StrongEq_def true_def)
sorry


section{* Local Judgements and Strong Equality *}

lemma StrongEq_L_refl: "\<tau> \<Turnstile> (x \<triangleq> x)"
by(simp add: OclValid_def StrongEq_def)


lemma StrongEq_L_sym: "\<tau> \<Turnstile> (x \<triangleq> y) \<Longrightarrow> \<tau> \<Turnstile> (y \<triangleq> x)"
by(simp add: OclValid_def StrongEq_def)

lemma StrongEq_L_trans: "\<tau> \<Turnstile> (x \<triangleq> y) \<Longrightarrow> \<tau> \<Turnstile> (y \<triangleq> z) \<Longrightarrow> \<tau> \<Turnstile> (x \<triangleq> z)"
by(simp add: OclValid_def StrongEq_def true_def)

text{* In order to establish substitutivity (which does not
hold in general HOL-formulas we introduce the following 
predicate that allows for a calculus of the necessary side-conditions.*}
definition cp   :: "(('\<AA>,'\<alpha>) val \<Rightarrow> ('\<AA>,'\<beta>) val) \<Rightarrow> bool"
where     "cp P \<equiv> (\<exists> f. \<forall> X \<tau>. P X \<tau> = f (X \<tau>) \<tau>)"


text{* The rule of substitutivity in HOL-OCL holds only 
for context-passing expressions - i.e. those, that pass
the context \<tau> without changing it. Fortunately, all 
operators of the OCL language satisfy this property 
(but not all HOL operators).*}

lemma StrongEq_L_subst1: "!! \<tau>. cp P \<Longrightarrow> \<tau> \<Turnstile> (x \<triangleq> y) \<Longrightarrow> \<tau> \<Turnstile> (P x \<triangleq> P y)"
by(auto simp: OclValid_def StrongEq_def true_def cp_def)

lemma StrongEq_L_subst2: 
"!! \<tau>.  cp P \<Longrightarrow> \<tau> \<Turnstile> (x \<triangleq> y) \<Longrightarrow> \<tau> \<Turnstile> (P x) \<Longrightarrow> \<tau> \<Turnstile> (P y)"
by(auto simp: OclValid_def StrongEq_def true_def cp_def)

lemma cpI1:
"(\<forall> X \<tau>. f X \<tau> = f(\<lambda>_. X \<tau>) \<tau>) \<Longrightarrow> cp P \<Longrightarrow> cp(\<lambda>X. f (P X))"
apply(auto simp: true_def cp_def)
apply(rule exI, (rule allI)+)
by(erule_tac x="P X" in allE, auto)

lemma cpI2:
"(\<forall> X Y \<tau>. f X Y \<tau> = f(\<lambda>_. X \<tau>)(\<lambda>_. Y \<tau>) \<tau>) \<Longrightarrow> 
 cp P \<Longrightarrow> cp Q \<Longrightarrow> cp(\<lambda>X. f (P X) (Q X))"
apply(auto simp: true_def cp_def)
apply(rule exI, (rule allI)+)
by(erule_tac x="P X" in allE, auto)


lemma cp_const : "cp(\<lambda>_. c)"
  by (simp add: cp_def, fast)

lemma cp_id :    "cp(\<lambda>X. X)"
  by (simp add: cp_def, fast)

lemmas cp_intro[simp,intro!] = 
       cp_const 
       cp_id
       cp_defined[THEN allI[THEN allI[THEN cpI1], of defined]]
       cp_not[THEN allI[THEN allI[THEN cpI1], of not]]
       cp_ocl_and[THEN allI[THEN allI[THEN allI[THEN cpI2]], of "op and"]]
       cp_ocl_or[THEN allI[THEN allI[THEN allI[THEN cpI2]], of "op or"]]
       cp_ocl_implies[THEN allI[THEN allI[THEN allI[THEN cpI2]], of "op implies"]]
       cp_StrongEq[THEN allI[THEN allI[THEN allI[THEN cpI2]], 
             of "StrongEq"]]
       cp_StrictRefEq_bool[THEN allI[THEN allI[THEN allI[THEN cpI2]], 
             of "StrictRefEq"]]
       cp_StrictRefEq_int[THEN allI[THEN allI[THEN allI[THEN cpI2]], 
             of "StrictRefEq"]]
       cp_gen_ref_eq_object[THEN allI[THEN allI[THEN allI[THEN cpI2]], 
             of "gen_ref_eq"]]

section{* Laws to Establish Definedness (Delta-Closure) *}

text{* For the logical connectives, we have --- beyond
@{thm foundation6} --- the followinf facts:  *}
lemma ocl_not_defargs: 
"\<tau> \<Turnstile> (not P) \<Longrightarrow> \<tau> \<Turnstile> \<delta> P"
by(auto simp: not_def OclValid_def true_def invalid_def defined_def false_def
        split: bool.split_asm HOL.split_if_asm option.split option.split_asm)


lemma ocl_and_defargs: 
"\<tau> \<Turnstile> (P and Q) \<Longrightarrow> (\<tau> \<Turnstile> \<delta> P) \<and> (\<tau> \<Turnstile> \<delta> Q)"
by(auto dest: foundation5 foundation6)

text{* So far, we have only one strict Boolean predicate (-family):
The strict equality. *}

lemma strictEqBool_defargs: 
"\<tau> \<Turnstile> ((x::('\<AA>,bool)val) \<doteq> y) \<Longrightarrow> (\<tau> \<Turnstile>(\<delta> x)) \<and> (\<tau> \<Turnstile>(\<delta> y))"
by(simp add: StrictRefEq_bool OclValid_def true_def invalid_def
           split: bool.split_asm HOL.split_if_asm)

lemma strictEqInt_defargs: 
"\<tau> \<Turnstile> ((x::('\<AA>,int)val) \<doteq> y)\<Longrightarrow> (\<tau> \<Turnstile>(\<delta> x)) \<and> (\<tau> \<Turnstile>(\<delta> y))"
by(simp add: StrictRefEq_int OclValid_def true_def invalid_def
           split: bool.split_asm HOL.split_if_asm)

lemma gen_ref_eq_defargs: 
"\<tau> \<Turnstile> (gen_ref_eq x (y::('\<AA>,'a::object)val))\<Longrightarrow> (\<tau> \<Turnstile>(\<delta> x)) \<and> (\<tau> \<Turnstile>(\<delta> y))"
by(simp add: gen_ref_eq_def OclValid_def true_def invalid_def
           split: bool.split_asm HOL.split_if_asm)

end