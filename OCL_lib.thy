theory OCL_lib
imports OCL_core
begin

section{* Simple, Basic Types like Boolean and Integer *}

text{* Note that the strict equality on basic types (actually on all types) 
must be exceptionally defined on null --- otherwise the entire concept of 
null in the language does not make much sense. This is an important exception
from the general rule that null arguments --- especially if passed as "self"-argument ---
lead to invalid results. *}

defs   StrictRefEq_int : "(x::('\<AA>)Integer) \<doteq> y \<equiv>
                             \<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                  then (x \<triangleq> y)\<tau>
                                  else invalid \<tau>"

defs   StrictRefEq_bool : "(x::('\<AA>)Boolean) \<doteq> y \<equiv>
                             \<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                  then (x \<triangleq> y)\<tau>
                                  else invalid \<tau>"

lemma StrictRefEq_int_strict1[simp] : "((x::('\<AA>)Integer) \<doteq> invalid) = invalid"
by(rule ext, simp add: StrictRefEq_int true_def false_def)

lemma StrictRefEq_int_strict2[simp] : "(invalid \<doteq> (x::('\<AA>)Integer)) = invalid"
by(rule ext, simp add: StrictRefEq_int true_def false_def)



lemma strictEqBool_vs_strongEq: 
"\<tau> \<Turnstile>(\<upsilon> x) \<Longrightarrow> \<tau> \<Turnstile>(\<upsilon> y) \<Longrightarrow> (\<tau> \<Turnstile> ((x::('\<AA>)Boolean) \<doteq> y)) = (\<tau> \<Turnstile> (x \<triangleq> y))"
by(simp add: StrictRefEq_bool OclValid_def)

lemma strictEqInt_vs_strongEq: 
"\<tau> \<Turnstile>(\<upsilon> x) \<Longrightarrow> \<tau> \<Turnstile>(\<upsilon> y) \<Longrightarrow> (\<tau> \<Turnstile> ((x::('\<AA>)Integer) \<doteq> y)) = (\<tau> \<Turnstile> (x \<triangleq> y))"
by(simp add: StrictRefEq_int OclValid_def)

lemma strictEqBool_defargs:
"\<tau> \<Turnstile> ((x::('\<AA>)Boolean) \<doteq> y) \<Longrightarrow> (\<tau> \<Turnstile> (\<upsilon> x)) \<and> (\<tau> \<Turnstile>(\<upsilon> y))"
by(simp add: StrictRefEq_bool OclValid_def true_def invalid_def
           split: bool.split_asm HOL.split_if_asm)

lemma strictEqInt_defargs:
"\<tau> \<Turnstile> ((x::('\<AA>)Integer) \<doteq> y) \<Longrightarrow> (\<tau> \<Turnstile> (\<upsilon> x)) \<and> (\<tau> \<Turnstile> (\<upsilon> y))"
by(simp add: StrictRefEq_int OclValid_def true_def invalid_def
           split: bool.split_asm HOL.split_if_asm)

lemma strictEqBool_valid_args_valid: 
"(\<tau> \<Turnstile> \<upsilon>((x::('\<AA>)Boolean) \<doteq> y)) = ((\<tau> \<Turnstile>(\<upsilon> x)) \<and> (\<tau> \<Turnstile>(\<upsilon> y)))"
by(auto simp: StrictRefEq_bool OclValid_def true_def valid_def false_def StrongEq_def 
                 defined_def invalid_def
           split: bool.split_asm HOL.split_if_asm option.split)

lemma strictEqInt_valid_args_valid: 
"(\<tau> \<Turnstile> \<upsilon>((x::('\<AA>)Integer) \<doteq> y)) = ((\<tau> \<Turnstile>(\<upsilon> x)) \<and> (\<tau> \<Turnstile>(\<upsilon> y)))"
by(auto simp: StrictRefEq_int OclValid_def true_def valid_def false_def StrongEq_def 
                 defined_def invalid_def
           split: bool.split_asm HOL.split_if_asm option.split)

lemma gen_ref_eq_defargs: 
"\<tau> \<Turnstile> (gen_ref_eq x (y::('\<AA>,'a::object)val))\<Longrightarrow> (\<tau> \<Turnstile>(\<delta> x)) \<and> (\<tau> \<Turnstile>(\<delta> y))"
by(simp add: gen_ref_eq_def OclValid_def true_def invalid_def
           split: bool.split_asm HOL.split_if_asm)


lemma StrictRefEq_int_strict :
  assumes A: "\<upsilon> (x::('\<AA>)Integer) = true"
  and     B: "\<upsilon> y = true"
  shows   "\<upsilon> (x \<doteq> y) = true"
  apply(insert A B)
  apply(rule ext, simp add: StrongEq_def StrictRefEq_int true_def valid_def defined_def)
  done


lemma StrictRefEq_int_strict' :
  assumes A: "\<upsilon> (((x::('\<AA>)Integer)) \<doteq> y) = true"
  shows      "\<upsilon> x = true \<and> \<upsilon> y = true"
  apply(insert A, rule conjI) 
  apply(rule ext, drule_tac x=xa in fun_cong)
  prefer 2
  apply(rule ext, drule_tac x=xa in fun_cong)
  apply(simp_all add: StrongEq_def StrictRefEq_int 
                            false_def true_def valid_def defined_def)
  apply(case_tac "y xa", auto)
  apply(simp_all add: true_def invalid_def)
  apply(case_tac "aa", auto simp:true_def false_def invalid_def 
                            split: option.split option.split_asm)
  done



lemma StrictRefEq_bool_strict1[simp] : "((x::('\<AA>)Boolean) \<doteq> invalid) = invalid"
by(rule ext, simp add: StrictRefEq_bool true_def false_def)

lemma StrictRefEq_bool_strict2[simp] : "(invalid \<doteq> (x::('\<AA>)Boolean)) = invalid"
by(rule ext, simp add: StrictRefEq_bool true_def false_def)

lemma cp_StrictRefEq_bool: 
"((X::('\<AA>)Boolean) \<doteq> Y) \<tau> = ((\<lambda> _. X \<tau>) \<doteq> (\<lambda> _. Y \<tau>)) \<tau>"
by(auto simp: StrictRefEq_bool StrongEq_def defined_def valid_def  cp_defined[symmetric])

lemma cp_StrictRefEq_int: 
"((X::('\<AA>,int)val) \<doteq> Y) \<tau> = ((\<lambda> _. X \<tau>) \<doteq> (\<lambda> _. Y \<tau>)) \<tau>"
by(auto simp: StrictRefEq_int StrongEq_def valid_def  cp_defined[symmetric])


lemmas cp_intro[simp,intro!] = 
       cp_intro
       cp_StrictRefEq_bool[THEN allI[THEN allI[THEN allI[THEN cpI2]], of "StrictRefEq"]]
       cp_StrictRefEq_int[THEN allI[THEN allI[THEN allI[THEN cpI2]],  of "StrictRefEq"]]


lemma StrictRefEq_strict :
  assumes A: "\<upsilon> (x::('\<AA>,int)val) = true"
  and     B: "\<upsilon> y = true"
  shows   "\<upsilon> (x \<doteq> y) = true"
  apply(insert A B)
  apply(rule ext, simp add: StrongEq_def StrictRefEq_int true_def valid_def)
  done


definition ocl_zero ::"('\<AA>)Integer" ("\<zero>")
where      "\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>0::int\<rfloor>\<rfloor>)"

definition ocl_one ::"('\<AA>)Integer" ("\<one> ")
where      "\<one>  = (\<lambda> _ . \<lfloor>\<lfloor>1::int\<rfloor>\<rfloor>)"

definition ocl_two ::"('\<AA>)Integer" ("\<two>")
where      "\<two> = (\<lambda> _ . \<lfloor>\<lfloor>2::int\<rfloor>\<rfloor>)"

definition ocl_three ::"('\<AA>)Integer" ("\<three>")
where      "\<three> = (\<lambda> _ . \<lfloor>\<lfloor>3::int\<rfloor>\<rfloor>)"

definition ocl_four ::"('\<AA>)Integer" ("\<four>")
where      "\<four> = (\<lambda> _ . \<lfloor>\<lfloor>4::int\<rfloor>\<rfloor>)"

definition ocl_five ::"('\<AA>)Integer" ("\<five>")
where      "\<five> = (\<lambda> _ . \<lfloor>\<lfloor>5::int\<rfloor>\<rfloor>)"

definition ocl_six ::"('\<AA>)Integer" ("\<six>")
where      "\<six> = (\<lambda> _ . \<lfloor>\<lfloor>6::int\<rfloor>\<rfloor>)"

definition ocl_seven ::"('\<AA>)Integer" ("\<seven>")
where      "\<seven> = (\<lambda> _ . \<lfloor>\<lfloor>7::int\<rfloor>\<rfloor>)"

definition ocl_eight ::"('\<AA>)Integer" ("\<eight>")
where      "\<eight> = (\<lambda> _ . \<lfloor>\<lfloor>8::int\<rfloor>\<rfloor>)"

definition ocl_nine ::"('\<AA>)Integer" ("\<nine>")
where      "\<nine> = (\<lambda> _ . \<lfloor>\<lfloor>9::int\<rfloor>\<rfloor>)"

definition ten_nine ::"('\<AA>)Integer" ("\<one>\<zero>")
where      "\<one>\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>10::int\<rfloor>\<rfloor>)"

text{* Here is a way to cast in standard operators 
via the type class system of Isabelle. *}

lemma  "\<delta> null = false" by simp (* recall *)
lemma  "\<upsilon> null = true"  by simp (* recall *)

lemma [simp]:"\<delta> \<zero> = true" 
by(simp add:ocl_zero_def defined_def true_def)

lemma [simp]:"\<upsilon> \<zero> = true" 
by(simp add:ocl_zero_def valid_def true_def)

lemma [simp]:"\<delta> \<one> = true" 
by(simp add:ocl_one_def defined_def true_def)

lemma [simp]:"\<upsilon> \<one> = true" 
by(simp add:ocl_one_def valid_def true_def)

lemma [simp]:"\<delta> \<two> = true" 
by(simp add:ocl_two_def defined_def true_def)

lemma [simp]:"\<upsilon> \<two> = true" 
by(simp add:ocl_two_def valid_def true_def)


lemma one_non_null[simp]: "\<zero> \<noteq> null"
apply(auto simp:ocl_zero_def  null_def ) 
apply(drule_tac x=x in fun_cong, simp)
done

lemma zero_non_null[simp]: "\<one> \<noteq> null"
apply(auto simp:ocl_one_def  null_def ) 
apply(drule_tac x=x in fun_cong, simp)
done

(* plus all the others ...*)

text{* Here is a common case of a built-in operation on built-in types.
Note that the arguments must be both defined (non-null, non-bottom). *}
definition ocl_less_int ::"('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer \<Rightarrow> ('\<AA>)Boolean" (infix "\<prec>" 40) 
where "x \<prec> y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> < \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                else invalid \<tau> "   

definition ocl_le_int ::"('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer \<Rightarrow> ('\<AA>)Boolean" (infix "\<preceq>" 40) 
where "x \<preceq> y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> \<le> \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                else invalid \<tau> "   

(* ... and the usual rules on strictness, definedness propoagation, and cp ... *)

section{*Collection Types*}

subsection {* Prerequisite: An Abstract Interface for OCL Types *}

text {* In order to have the possibility to nest collection types,
such that we can give semantics to expressions like @{text "Set{Set{\<two>},null}"},
it is necessary to introduce a uniform interface for types having
the @{text "invalid"} (= bottom) element. The reason is that we impose
a data-invariant on raw-collection types_code which assures
that the @{text "invalid"} element is not allowed inside the collection;
all raw-collections of this form were identified with the @{text "invalid"} element
itself. The construction requires that the new collection type is
un-comparable with the raw-types (consisting of nested option type constructions),
such that the data-invariant mussed be expressed in terms of the interface.
In a second step, our base-types will be shown to be instances of this interface.
 *}

text{* This uniform interface consists in a type class requiring the existence
of a bottom and a null element. The construction proceeds by
 abstracting the null (which is defined by @{text "\<lfloor> \<bottom> \<rfloor>"} on 
@{text "'a option option"} to a NULL - element, which may
have an abritrary semantic structure, and an undefinedness element @{text "\<bottom> "}
to an abstract undefinedness element @{text "UU"} (also written  
@{text "\<bottom> "} whenever no confusion arises). As a consequence, it is necessary  
to redefine the notions of invalid, defined, valuation etc.
on top of this interface. *}

text{* This interface consists in two abstract type classes @{text bottom} 
and @{text null} for the class of all types comprising a bottom and a 
distinct null element.  *}

instance option   :: (plus) plus  by intro_classes
instance "fun"    :: (type, plus) plus by intro_classes

class   bottom = 
   fixes  UU :: "'a"
   assumes nonEmpty : "\<exists> x. x \<noteq> UU"


begin
   notation (xsymbols)  UU ("\<bottom>")
end

class      null = bottom +
   fixes   NULL :: "'a"
   assumes null_is_valid : "NULL \<noteq> UU"

(* TOO MUCH SYNTACTIC AMBIGUITIES ...
begin
   notation (xsymbols)  NULL ("\<null>")
end
*)

subsection {* Accomodation of Basic Types to the Abstract Interface *}

text{* In the following it is shown that the option-option type type is
in fact in the @{text null} class and that function spaces over these 
classes again "live" in these classes. *}

instantiation   option  :: (type)bottom
begin 

   definition UU_option_def: "(UU::'a option) \<equiv> (None::'a option)"

   instance proof 
              show "\<exists>x\<Colon>'a option. x \<noteq> UU"  (* notation for \<bottom> which is too 
                                              heavily overloaded here *)
              by(rule_tac x="Some x" in exI, simp add:UU_option_def)
            qed
end

instantiation   option  :: (bottom)null
begin 
   definition NULL_option_def: "(NULL::'a\<Colon>bottom option) \<equiv>  \<lfloor> UU \<rfloor>"

   instance proof  show "(NULL::'a\<Colon>bottom option) \<noteq> UU"
                   by( simp add:NULL_option_def UU_option_def)
            qed
end


instantiation "fun"  :: (type,bottom) bottom 
begin
   definition UU_fun_def: "UU \<equiv> (\<lambda> x. UU)"

   instance proof  show "\<exists>(x::'a \<Rightarrow> 'b). x \<noteq> UU"
                   apply(rule_tac x="\<lambda> _. (SOME y. y \<noteq> UU)" in exI, auto)
                   apply(drule_tac x=x in fun_cong,auto simp:UU_fun_def)
                   apply(erule contrapos_pp, simp)
                   apply(rule some_eq_ex[THEN iffD2])
                   apply(simp add: nonEmpty)
                   done
            qed
end


instantiation "fun"  :: (type,null) null 
begin
 definition NULL_fun_def: "(NULL::'a \<Rightarrow> 'b::null) \<equiv> (\<lambda> x. NULL)"

 instance proof 
              show "(NULL::'a \<Rightarrow> 'b::null) \<noteq> \<bottom>"
              apply(auto simp: NULL_fun_def UU_fun_def)
              apply(drule_tac x=x in fun_cong)
              apply(erule contrapos_pp, simp add: null_is_valid)
            done
          qed
end

text{* A trivial consequence of this adaption of the interface is that
abstract and concrete versions of NULL are the same on base types
(as could be expected). *}

lemma conc_bot_eq_abs_UU_int: "\<bottom> = (UU::('a)Integer)"
by(rule ext,simp add: UU_option_def NULL_option_def null_def NULL_fun_def)

lemma conc_bot_eq_abs_UU_bool: "\<bottom> = (UU::('a)Boolean)"
by(rule ext,simp add: UU_option_def NULL_option_def null_def NULL_fun_def)


lemma conc_null_eq_abs_null_int: "null = (NULL::('a)Integer)"
by(rule ext,simp add: UU_option_def NULL_option_def null_def NULL_fun_def)

lemma conc_null_eq_abs_null_bool: "null = (NULL::('a)Boolean)"
by(rule ext,simp add: UU_option_def NULL_option_def null_def NULL_fun_def)

subsection {* Redefining the concept of Valuation *}

text{* Now, on this basis we generalize the concept of a valuation: we do no
longer care that the @{text "\<bottom>"} and @{text "NULL"} were actually constructed
by the type constructor option; rather, we require that the type is just from
the null-class:*}

type_synonym ('\<AA>,'\<alpha>) val' = "'\<AA> st \<Rightarrow> '\<alpha>::null"

text{* However, this has also the consequence that core concepts like definedness, 
validness and even cp have to be redefined on this type class:*}

definition valid' :: "('\<AA>,'a::null)val' \<Rightarrow> ('\<AA>)Boolean" ("\<upsilon>' _" [100]100)
where   "\<upsilon>' X \<equiv>  \<lambda> \<tau> . if X \<tau> = UU \<tau> then false \<tau> else true \<tau>"

definition defined' :: "('\<AA>,'a::null)val' \<Rightarrow> ('\<AA>)Boolean" ("\<delta>' _" [100]100)
where   "\<delta>' X \<equiv>  \<lambda> \<tau> . if X \<tau> = UU \<tau>  \<or> X \<tau> = NULL \<tau> then false \<tau> else true \<tau>"

text{* The generalized definitions of invalid and definedness have the same
properties as the old ones : *}
lemma defined1[simp]: "\<delta>' invalid = false"
  by(rule ext,simp add: defined'_def UU_fun_def UU_option_def 
                           null_def invalid_def true_def false_def)

lemma defined2[simp]: "\<delta>' null = false"
  by(rule ext,simp add: defined'_def bot_fun_def UU_option_def 
                           null_def NULL_option_def NULL_fun_def invalid_def true_def false_def)


lemma defined3[simp]: "\<delta>' \<delta>' X = true"
  by(rule ext,auto simp: defined'_def   true_def false_def 
                           UU_fun_def UU_option_def NULL_option_def NULL_fun_def)

lemma valid4[simp]: "\<upsilon>' (X \<triangleq> Y) = true"
  by(rule ext,
     auto simp: valid'_def  true_def false_def StrongEq_def
                           UU_fun_def UU_option_def NULL_option_def NULL_fun_def)


lemma defined4[simp]: "\<delta>' (X \<triangleq> Y) = true"
  by(rule ext,
     auto simp: valid'_def  defined'_def true_def false_def StrongEq_def
                           UU_fun_def UU_option_def NULL_option_def NULL_fun_def)

lemma defined5[simp]: "\<delta>' \<upsilon>' X = true"
  by(rule ext,
     auto simp: valid'_def  defined'_def true_def false_def StrongEq_def
                           UU_fun_def UU_option_def NULL_option_def NULL_fun_def)

lemma valid5[simp]: "\<upsilon>' \<delta>' X = true"
  by(rule ext,
     auto simp: valid'_def  defined'_def true_def false_def StrongEq_def
                           UU_fun_def UU_option_def NULL_option_def NULL_fun_def)

 
lemma cp_valid': "(\<upsilon>' X) \<tau> = (\<upsilon>' (\<lambda> _. X \<tau>)) \<tau>"
by(simp add: valid'_def)


lemma cp_defined':"(\<delta>' X)\<tau> = (\<delta>' (\<lambda> _. X \<tau>)) \<tau>"
by(simp add: defined'_def)

lemmas cp_intro'[simp,intro!] = 
       cp_intro
       cp_defined'[THEN allI[THEN allI[THEN cpI1], of defined']]
       cp_valid'  [THEN allI[THEN allI[THEN cpI1], of valid']]

text{* In fact, it can be proven for the base types that both versions of undefined
and invalid are actually the same: *}

lemma defined_is_defined' [simp] : "\<delta> X = \<delta>' X"
by(rule ext,
   auto simp: defined'_def defined_def true_def false_def false_def true_def
              UU_fun_def UU_option_def NULL_option_def NULL_fun_def)

lemma valid_is_valid' [simp] : "\<upsilon> X = \<upsilon>' X"
by(rule ext,
   auto simp: valid'_def valid_def  false_def  true_def
              UU_fun_def UU_option_def NULL_option_def NULL_fun_def
        split: option.split)

definition cp'   :: "(('\<AA>,'\<alpha>::null) val' \<Rightarrow> ('\<AA>,'\<beta>::null) val') \<Rightarrow> bool"
where     "cp' P \<equiv> (\<exists> f. \<forall> X \<tau>. P X \<tau> = f (X \<tau>) \<tau>)"


lemma cp'I1:
"(\<forall> X \<tau>. f X \<tau> = f(\<lambda>_. X \<tau>) \<tau>) \<Longrightarrow> cp' P \<Longrightarrow> cp'(\<lambda>X. f (P X))"
apply(auto simp: true_def cp'_def)
apply(rule exI, (rule allI)+)
by(erule_tac x="P X" in allE, auto)

lemma cp'I2:
"(\<forall> X Y \<tau>. f X Y \<tau> = f(\<lambda>_. X \<tau>)(\<lambda>_. Y \<tau>) \<tau>) \<Longrightarrow> 
 cp' P \<Longrightarrow> cp' Q \<Longrightarrow> cp'(\<lambda>X. f (P X) (Q X))"
apply(auto simp: true_def cp'_def)
apply(rule exI, (rule allI)+)
by(erule_tac x="P X" in allE, auto)

lemma defined_charn: "\<tau> \<Turnstile> (\<delta>' X) = (X \<tau> \<noteq> UU \<and> X \<tau> \<noteq> (NULL \<tau>))"
by(auto simp: OclValid_def defined'_def false_def true_def cp'_def UU_fun_def
        split:split_if_asm)

lemmas definedD = defined_charn[THEN iffD1,standard]

lemma valid_charn: "\<tau> \<Turnstile> (\<upsilon>' X) = (X \<tau> \<noteq> UU)"
by(auto simp: OclValid_def valid'_def false_def true_def cp'_def UU_fun_def
        split:split_if_asm)

lemmas validD = valid_charn[THEN iffD1,standard]

lemma valid_implies_defined : "\<tau> \<Turnstile> (\<delta>' X) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon>' X"
by(simp add: valid_charn defined_charn) 

subsection {* Example: The Set-Collection Type on the Abstract Interface *}

text{* For the semantic construction of the collection types, we have two goals:
\begin{enumerate}
\item we want the types to be \emph{fully abstract}, i.e. the type should not
      contain junk-elements that are not representable by OCL expressions.
\item We want a possibility to nest collection types (so, we want the 
      potential to talking about @{text "Set(Set(Sequences(Pairs(X,Y))))"}), and
\end{enumerate}
The former principe rules out the option to define @{text "'\<alpha> Set"} just by 
 @{text "('\<AA>, ('\<alpha> option option) set) val"}. This would allow sets to contain
junk elements such as @{text "{\<bottom>}"} which we need to identify with undefinedness
itself. Abandoning fully abstractness of rules would later on produce all sorts
of problems when quantifying over the elements of a type.
However, if we build an own type, then it must conform to our abstract interface
in order to have nested types: arguments of type-constructors must conform to our
abstract interface, and the result type too.
*}

text{* The core of an own type construction is done via a type definition which
provides the raw-type @{text "'\<alpha> Set_0"}. it is shown that this type "fits" indeed
into the abstract type interface discussed in the previous section. *}

typedef  '\<alpha> Set_0 = "{X::('\<alpha>\<Colon>null) set option option.
                      X = UU \<or> X = NULL \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> UU)}"
          by (rule_tac x="UU" in exI, simp)

instantiation   Set_0  :: (null)bottom
begin 

   definition bot_Set_0_def: "(UU::('a::null) Set_0) \<equiv> Abs_Set_0 None"

   instance proof show "\<exists>x\<Colon>'a Set_0. x \<noteq> \<bottom>"
                  apply(rule_tac x="Abs_Set_0 \<lfloor>None\<rfloor>" in exI)
                  apply(simp add:bot_Set_0_def)
                  apply(subst Abs_Set_0_inject) 
                  apply(simp_all add: Set_0_def bot_Set_0_def 
                                      NULL_option_def UU_option_def)
                  done
            qed
end


instantiation   Set_0  :: (null)null
begin 
 
   definition NULL_Set_0_def: "(NULL::('a::null) Set_0) \<equiv> Abs_Set_0 \<lfloor> None \<rfloor>"

   instance proof show "(NULL::('a::null) Set_0) \<noteq> \<bottom>"
                  apply(simp add:NULL_Set_0_def bot_Set_0_def)
                  apply(subst Abs_Set_0_inject) 
                  apply(simp_all add: Set_0_def bot_Set_0_def 
                                      NULL_option_def UU_option_def)
                  done
            qed
end


text{* ...  and lifting this type to the format of a valuation gives us:*}
type_synonym    ('\<AA>,'\<alpha>) Set  = "('\<AA>, '\<alpha> Set_0) val'"

lemma Set_inv_lemma: "\<tau> \<Turnstile> (\<delta>' X) \<Longrightarrow> (X \<tau> = Abs_Set_0 \<lfloor>UU\<rfloor>) \<or> (\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. x \<noteq> UU)"
apply(insert OCL_lib.Set_0.Rep_Set_0 [of "X \<tau>"], simp add:Set_0_def)
apply(auto simp: OclValid_def defined'_def false_def true_def cp'_def 
                 UU_fun_def bot_Set_0_def NULL_Set_0_def NULL_fun_def
           split:split_if_asm)
apply(erule contrapos_pp [of "Rep_Set_0 (X \<tau>) = UU"]) 
apply(subst Abs_Set_0_inject[symmetric], simp add:Rep_Set_0)
apply(simp add: Set_0_def)
apply(simp add: Rep_Set_0_inverse bot_Set_0_def UU_option_def)
apply(erule contrapos_pp [of "Rep_Set_0 (X \<tau>) = NULL"]) 
apply(subst Abs_Set_0_inject[symmetric], simp add:Rep_Set_0)
apply(simp add: Set_0_def)
apply(simp add: Rep_Set_0_inverse  NULL_option_def)
done


text{* ... which means that we can have a type @{text "('\<AA>,('\<AA>,('\<AA>) Integer) Set) Set"}
corresponding exactly to Set(Set(Integer)) in OCL notation. Note that the parameter
@{text "\<AA>"} still refers to the object universe; making the OCL semantics entirely parametric
in the object universe makes it possible to study (and prove) its properties 
independently from a concrete class diagram. *}


definition mtSet::"('\<AA>,'\<alpha>::null) Set"  ("Set{}")
where "Set{} \<equiv> (\<lambda> \<tau>.  Abs_Set_0 \<lfloor>\<lfloor>{}::'\<alpha> set\<rfloor>\<rfloor> )"


lemma mtSet_defined[simp]:"\<delta>'(Set{}) = true"  
apply(rule ext, auto simp: mtSet_def defined'_def NULL_Set_0_def 
                           bot_Set_0_def UU_fun_def NULL_fun_def)
apply(simp_all add: Abs_Set_0_inject Set_0_def UU_option_def NULL_Set_0_def NULL_option_def)
done

lemma mtSet_valid[simp]:"\<upsilon>'(Set{}) = true" 
apply(rule ext,auto simp: mtSet_def valid'_def NULL_Set_0_def 
                          bot_Set_0_def UU_fun_def NULL_fun_def)
apply(simp_all add: Abs_Set_0_inject Set_0_def UU_option_def NULL_Set_0_def NULL_option_def)
done

text{* Note that the collection types in OCL allow for NULL to be included;
  however, there is the NULL-collection into which inclusion yields invalid. *}

text{* The case of the size definition is somewhat special, we admit
explicitly in Essential OCL the possibility of infinite sets. For
the size definition, this requires an extra condition that assures
that the cardinality of the set is actually a defined integer. *}

definition OclSize     :: "('\<AA>,'\<alpha>::null)Set \<Rightarrow> '\<AA> Integer"    
where     "OclSize x = (\<lambda> \<tau>. if (\<delta>' x) \<tau> = true \<tau> \<and> finite(\<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>)
                             then \<lfloor>\<lfloor> int(card \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>) \<rfloor>\<rfloor>
                             else UU )"


definition OclIncluding   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val'] \<Rightarrow> ('\<AA>,'\<alpha>) Set"
where     "OclIncluding x y = (\<lambda> \<tau>. if (\<delta>' x) \<tau> = true \<tau> \<and> (\<upsilon>' y) \<tau> = true \<tau>
                                    then Abs_Set_0 \<lfloor>\<lfloor> \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>  \<union> {y \<tau>} \<rfloor>\<rfloor> 
                                    else UU )"


definition OclIncludes   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val'] \<Rightarrow> '\<AA> Boolean"
where     "OclIncludes x y = (\<lambda> \<tau>.   if (\<delta>' x) \<tau> = true \<tau> \<and> (\<upsilon>' y) \<tau> = true \<tau> 
                                     then \<lfloor>\<lfloor>(y \<tau>) \<in> \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil> \<rfloor>\<rfloor>
                                     else UU  )"

definition OclExcluding   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val'] \<Rightarrow> ('\<AA>,'\<alpha>) Set"
where     "OclExcluding x y = (\<lambda> \<tau>.  if (\<delta>' x) \<tau> = true \<tau> \<and> (\<upsilon>' y) \<tau> = true \<tau>
                                     then Abs_Set_0 \<lfloor>\<lfloor> \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil> - {y \<tau>} \<rfloor>\<rfloor> 
                                     else UU )"

definition OclExcludes   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val'] \<Rightarrow> '\<AA> Boolean"
where     "OclExcludes x y = (not(OclIncludes x y))"


definition OclIsEmpty   :: "('\<AA>,'\<alpha>::null) Set \<Rightarrow> '\<AA> Boolean"
where     "OclIsEmpty x =  ((OclSize x) \<doteq> \<zero>)"

definition OclNotEmpty   :: "('\<AA>,'\<alpha>::null) Set \<Rightarrow> '\<AA> Boolean"
where     "OclNotEmpty x =  not(OclIsEmpty x)"


consts (* abstract set collection operations *)
 (* OclSize        :: " ('\<AA>,'\<alpha>::null) Set \<Rightarrow> '\<AA> Integer"      *) 
 (* OclIncludes    :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val'] \<Rightarrow> '\<AA> Boolean"    *)
 (* OclExcludes    :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val'] \<Rightarrow> '\<AA> Boolean"    *)   
 (* OclIncluding   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val'] \<Rightarrow> ('\<AA>,'\<alpha>) Set"   *)
 (* OclExcluding   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val'] \<Rightarrow> ('\<AA>,'\<alpha>) Set"   *)
 (* OclIsEmpty     :: " ('\<AA>,'\<alpha>::null) Set \<Rightarrow> '\<AA> Boolean" *)
 (* OclNotEmpty    :: " ('\<AA>,'\<alpha>::null) Set \<Rightarrow> '\<AA> Boolean"*)
    OclUnion       :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> ('\<AA>,'\<alpha>) Set"
    OclIntersection:: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> ('\<AA>,'\<alpha>) Set"
    OclIncludesAll :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> '\<AA> Boolean"
    OclExcludesAll :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> '\<AA> Boolean"
    OclComplement  :: " ('\<AA>,'\<alpha>::null) Set \<Rightarrow> ('\<AA>,'\<alpha>) Set"
    OclSum         :: " ('\<AA>,'\<alpha>::null) Set \<Rightarrow> '\<AA> Integer"
    OclCount       :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> '\<AA> Integer"    

  
notation  (* standard ascii syntax *)
    OclSize        ("_->size'(')" [66])
and
    OclCount       ("_->count'(_')" [66,65]65)
and
    OclIncludes    ("_->includes'(_')" [66,65]65)
and
    OclExcludes    ("_->excludes'(_')" [66,65]65)
and
    OclSum         ("_->sum'(')" [66])
and
    OclIncludesAll ("_->includesAll'(_')" [66,65]65)
and
    OclExcludesAll ("_->excludesAll'(_')" [66,65]65)
and
    OclIsEmpty     ("_->isEmpty'(')" [66])
and
    OclNotEmpty    ("_->notEmpty'(')" [66])
and
    OclIncluding   ("_->including'(_')")
and
    OclExcluding   ("_->excluding'(_')")
and
    OclComplement  ("_->complement'(')")
and
    OclUnion       ("_->union'(_')"          [66,65]65)
and
    OclIntersection("_->intersection'(_')"   [71,70]70)

lemma cp_OclIncluding: 
"(X->including(x)) \<tau> = ((\<lambda> _. X \<tau>)->including(\<lambda> _. x \<tau>)) \<tau>"
by(auto simp: OclIncluding_def StrongEq_def invalid_def  
                 cp_defined'[symmetric] cp_valid'[symmetric])

lemma cp_OclExcluding: 
"(X->excluding(x)) \<tau> = ((\<lambda> _. X \<tau>)->excluding(\<lambda> _. x \<tau>)) \<tau>"
by(auto simp: OclExcluding_def StrongEq_def invalid_def  
                 cp_defined'[symmetric] cp_valid'[symmetric])

lemma cp_OclIncludes: 
"(X->includes(x)) \<tau> = (OclIncludes (\<lambda> _. X \<tau>) (\<lambda> _. x \<tau>) \<tau>)"
by(auto simp: OclIncludes_def StrongEq_def invalid_def  
                 cp_defined'[symmetric] cp_valid'[symmetric])
(* Why does this not work syntactically ???
   lemma cp_OclIncludes: "(X->includes(x)) \<tau> = (((\<lambda> _. X \<tau>)->includes( \<lambda> _. x \<tau>)) \<tau>)" *)



lemmas cp_intro''[simp,intro!] = 
       cp_intro'
       cp_OclIncludes  [THEN allI[THEN allI[THEN allI[THEN cp'I2]], of "OclIncludes"]]
       cp_OclIncluding [THEN allI[THEN allI[THEN allI[THEN cp'I2]], of "OclIncluding"]]


lemma including_strict1[simp]:"(\<bottom>->including(x)) = \<bottom>"
by(simp add: UU_fun_def OclIncluding_def defined'_def valid'_def false_def true_def)

lemma including_strict2[simp]:"(X->including(\<bottom>)) = \<bottom>"
by(simp add: OclIncluding_def UU_fun_def defined'_def valid'_def false_def true_def)

lemma including_strict3[simp]:"(NULL->including(x)) = \<bottom>"
by(simp add: OclIncluding_def UU_fun_def defined'_def valid'_def false_def true_def)

lemma including_valid_args_valid: 
"(\<tau> \<Turnstile> \<delta>'(X->including(x))) = ((\<tau> \<Turnstile>(\<delta>' X)) \<and> (\<tau> \<Turnstile>(\<upsilon>' x)))"
proof -
 have A : "bottom \<in> Set_0" by(simp add: Set_0_def UU_option_def)
 have B : "\<lfloor>bottom\<rfloor> \<in> Set_0" by(simp add: Set_0_def NULL_option_def UU_option_def)
 have C : "(\<tau> \<Turnstile>(\<delta>' X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon>' x)) \<Longrightarrow> \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> Set_0"
          apply(frule Set_inv_lemma) 
          apply(simp add: Set_0_def UU_option_def NULL_Set_0_def NULL_fun_def valid_charn defined_charn) 
          done
 have D: "(\<tau> \<Turnstile> \<delta>'(X->including(x))) \<Longrightarrow> ((\<tau> \<Turnstile>(\<delta>' X)) \<and> (\<tau> \<Turnstile>(\<upsilon>' x)))" 
          by(auto simp: OclIncluding_def OclValid_def true_def valid_def false_def StrongEq_def 
                        defined'_def invalid_def valid'_def UU_fun_def NULL_fun_def
                  split: bool.split_asm HOL.split_if_asm option.split)
 have E: "(\<tau> \<Turnstile>(\<delta>' X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon>' x)) \<Longrightarrow> (\<tau> \<Turnstile> \<delta>'(X->including(x)))" 
          apply(frule C, simp)
          apply(auto simp: OclIncluding_def OclValid_def true_def valid_def false_def StrongEq_def 
                           defined'_def invalid_def valid'_def UU_fun_def NULL_fun_def
                     split: bool.split_asm HOL.split_if_asm option.split)
          by(simp_all add: NULL_Set_0_def bot_Set_0_def Abs_Set_0_inject A B) 
show ?thesis by(auto dest:D intro:E)
qed
 

lemma excluding_strict1[simp]:"(\<bottom>->excluding(x)) = \<bottom>"
by(simp add: UU_fun_def OclExcluding_def defined'_def valid'_def false_def true_def)

lemma excluding_strict2[simp]:"(X->excluding(\<bottom>)) = \<bottom>"
by(simp add: OclExcluding_def UU_fun_def defined'_def valid'_def false_def true_def)

lemma excluding_strict3[simp]:"(NULL->excluding(x)) = \<bottom>"
by(simp add: OclExcluding_def UU_fun_def defined'_def valid'_def false_def true_def)

(* and many more *) 

subsection{* Some computational laws:*}

lemma including_charn0[simp]:
assumes val_x:"\<tau> \<Turnstile> (\<upsilon>' x)"
shows         "\<tau> \<Turnstile> not(Set{}->includes(x))"
using val_x
apply(auto simp: OclValid_def OclIncludes_def not_def false_def true_def)
apply(auto simp: mtSet_def OCL_lib.Set_0.Abs_Set_0_inverse Set_0_def)
done

(*declare [[names_long,show_types,show_sorts]]*)
lemma including_charn1:
assumes def_X:"\<tau> \<Turnstile> (\<delta>' X)"
assumes val_x:"\<tau> \<Turnstile> (\<upsilon>' x)"
shows         "\<tau> \<Turnstile> (X->including(x)->includes(x))"
proof -
 have A : "bottom \<in> Set_0" by(simp add: Set_0_def UU_option_def)
 have B : "\<lfloor>bottom\<rfloor> \<in> Set_0" by(simp add: Set_0_def NULL_option_def UU_option_def)
 have C : "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> Set_0"
          apply(insert def_X[THEN definedD] val_x[THEN validD] Set_inv_lemma[OF def_X])
          apply(simp add: Set_0_def UU_option_def NULL_Set_0_def NULL_fun_def) 
          done
 show ?thesis
   apply(insert def_X[THEN definedD] val_x[THEN validD])
   apply(auto simp: OclValid_def UU_fun_def OclIncluding_def OclIncludes_def false_def true_def
                    defined'_def valid'_def bot_Set_0_def NULL_fun_def NULL_Set_0_def)
   apply(simp_all add: Abs_Set_0_inject Abs_Set_0_inverse A B C) 
 done
qed

lemma including_charn2:
assumes def_X:"\<tau> \<Turnstile> (\<delta>' X)"
and     val_x:"\<tau> \<Turnstile> (\<upsilon>' x)"
and     val_y:"\<tau> \<Turnstile> (\<upsilon>' y)"
and     neq  :"\<tau> \<Turnstile> not(x \<triangleq> y)" 
shows         "\<tau> \<Turnstile> (X->including(x)->includes(y)) \<triangleq> (X->includes(y))"
proof -
 have A : "bottom \<in> Set_0" by(simp add: Set_0_def UU_option_def)
 have B : "\<lfloor>bottom\<rfloor> \<in> Set_0" by(simp add: Set_0_def NULL_option_def UU_option_def)
 have C : "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> Set_0"
          apply(insert def_X[THEN definedD] val_x[THEN validD] Set_inv_lemma[OF def_X])
          apply(simp add: Set_0_def UU_option_def NULL_Set_0_def NULL_fun_def) 
          done
 have D : "y \<tau> \<noteq> x \<tau>" 
          apply(insert neq)
          by(auto simp: OclValid_def UU_fun_def OclIncluding_def OclIncludes_def 
                        false_def true_def defined'_def valid'_def bot_Set_0_def 
                        NULL_fun_def NULL_Set_0_def StrongEq_def not_def)
 show ?thesis
  apply(insert def_X[THEN definedD] val_x[THEN validD])
  apply(auto simp: OclValid_def UU_fun_def OclIncluding_def OclIncludes_def false_def true_def
                   defined'_def valid'_def bot_Set_0_def NULL_fun_def NULL_Set_0_def StrongEq_def)
  apply(simp_all add: Abs_Set_0_inject Abs_Set_0_inverse A B C D) 
 done
qed


syntax
  "_OclFinset" :: "args => ('\<AA>,'a::null) Set"    ("Set{(_)}")
translations
  "Set{x, xs}" == "CONST OclIncluding (Set{xs}) x"
  "Set{x}"     == "CONST OclIncluding (Set{}) x "

lemma syntax_test: "Set{\<two>,\<one>} = (Set{}->including(\<one>)->including(\<two>))"
by simp

lemma semantic_test: "\<tau> \<Turnstile> (Set{\<two>,null}->includes(null))"
oops

text{* Here is an example of a nested collection. Note that we have
to use the abstract NULL (since we did not (yet) define a concrete
constant @{term null} for the non-existing Sets) :*}
lemma semantic_test: "\<tau> \<Turnstile> (Set{Set{\<two>},NULL}->includes(NULL))"
oops

(* The next challenge:
lemma hurx : "Set{Set{\<two>},NULL} \<triangleq> Set{Set{\<two>},NULL}"
oops
*)

lemma semantic_test: "\<tau> \<Turnstile> (Set{null,\<two>}->includes(null))"
by(simp_all del: valid_is_valid' 
            add: valid_is_valid'[symmetric] including_charn1 including_valid_args_valid)

end
