theory OCL_lib2
imports OCL_core
begin


syntax
  "notequal"        :: "('\<AA>)Boolean \<Rightarrow> ('\<AA>)Boolean \<Rightarrow> ('\<AA>)Boolean"   (infix "<>" 40)
translations
  "a <> b" == "CONST not( a \<doteq> b)"

defs   StrictRefEq_int : "(x::('\<AA>,int)val) \<doteq> y \<equiv>
                             \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                                  then (x \<triangleq> y)\<tau>
                                  else invalid \<tau>"


defs   StrictRefEq_bool : "(x::('\<AA>,bool)val) \<doteq> y \<equiv>
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


lemma strictEqBool_vs_strongEq: 
"\<tau> \<Turnstile>(\<delta> x) \<Longrightarrow> \<tau> \<Turnstile>(\<delta> y) \<Longrightarrow> (\<tau> \<Turnstile> ((x::('\<AA>,bool)val) \<doteq> y)) = (\<tau> \<Turnstile> (x \<triangleq> y))"
by(simp add: StrictRefEq_bool OclValid_def)

lemma strictEqInt_vs_strongEq: 
"\<tau> \<Turnstile>(\<delta> x) \<Longrightarrow> \<tau> \<Turnstile>(\<delta> y) \<Longrightarrow> (\<tau> \<Turnstile> ((x::('\<AA>,int)val) \<doteq> y)) = (\<tau> \<Turnstile> (x \<triangleq> y))"
by(simp add: StrictRefEq_int OclValid_def)


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



lemmas cp_rules =
       cp_StrictRefEq_bool[THEN allI[THEN allI[THEN allI[THEN cpI2]], 
             of "StrictRefEq"]]
       cp_StrictRefEq_int[THEN allI[THEN allI[THEN allI[THEN cpI2]], 
             of "StrictRefEq"]]


lemma StrictRefEq_strict :
  assumes A: "\<delta> (x::('\<AA>,int)val) = true"
  and     B: "\<delta> y = true"
  shows   "\<delta> (x \<doteq> y) = true"
  apply(insert A B)
  apply(rule ext, simp add: StrongEq_def StrictRefEq_int true_def defined_def)
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

lemma [simp]:"\<delta> \<zero> = true" 
by(simp add:ocl_zero_def defined_def true_def)

lemma [simp]:"\<upsilon> \<zero> = true" 
by(simp add:ocl_zero_def valid_def true_def)

(* plus all the others ...*)


instance option   :: (plus) plus 
by intro_classes


instance "fun"    :: (type, plus) plus 
by intro_classes

(* Makarius: why does this not work ? It worked in 2005 !!! 
defs (overloaded) ocl_plus_def : 
            "op + \<equiv> (\<lambda> (X::('\<AA>)Integer) (Y::('\<AA>)Integer) \<tau>. 
                     if (\<delta> X) \<tau> = true \<tau> \<and> (\<delta> Y) \<tau> = true \<tau>
                     then \<lfloor>\<lfloor> \<lceil>\<lceil> (X \<tau>) \<rceil>\<rceil> + \<lceil>\<lceil> (Y \<tau>) \<rceil>\<rceil>  \<rfloor>\<rfloor> 
                     else invalid \<tau>)"
*)


definition ocl_less_int ::"('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer \<Rightarrow> ('\<AA>)Boolean" (infix "\<prec>" 40) 
where "x \<prec> y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> < \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                else invalid \<tau> "   

definition ocl_le_int ::"('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer \<Rightarrow> ('\<AA>)Boolean" (infix "\<preceq>" 40) 
where "x \<preceq> y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> \<le> \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                else invalid \<tau> "   



lemma zero_non_null[simp]: "\<zero> \<noteq> null"
apply(auto simp:ocl_zero_def  null_def ) 
apply(drule_tac x=x in fun_cong, simp)
done


section{*Collection Types*}

subsection {* Prerequisite: An Abstract Interface for OCL Types *}

text {* In order to have the possibility to nest collection types,
it is necessary to introduce a uniform interface for types having
the "invalid" (= bottom) element. In a second step, our base-types
will be shown to be instances of this class. *}

text{* This uniform interface consists in abstracting the null (which is defined
by @{text "\<lfloor> \<bottom> \<rfloor>"} on @{text "'a option option"} to a NULL - element, which may
have an abritrary semantic structure, and an undefinedness element @{text "\<bottom> "}
to an abstract undefinedness element @{text "UU"} (also written  
@{text "\<bottom> "} whenever no confusion arises). As a consequence, it is necessary  
to redefine the notions of invalid, defined, valuation etc.
on top of this interface. *}

text{* This interface consists in two abstract type classes @{text bottom} 
and @{text null} for the class of all types comprising a bottom and a 
distinct null element.  *}
class   bottom = 
   fixes  UU :: "'a"
   assumes nonEmpty : "\<exists> x. x \<noteq> UU"


begin
   notation (xsymbols)  UU ("\<bottom>")
end

class   null = bottom +
   fixes  NULL :: "'a"
   assumes null_is_valid : "NULL \<noteq> UU"

(* 
begin
   notation (xsymbols)  NULL ("\<null>")
end
*)


text{* In the following it is shown that the option-option type type is
in fact in the @{text null} class and that function spaces over these classes
again "live" in these classes. *}

instantiation   option  :: (type)bottom
begin 

   definition UU_option_def: "(UU::'a option) \<equiv> (None::'a option)"

   instance proof 
              show "\<exists>x\<Colon>'a option. x \<noteq> UU"  (* notation for \<bottom> which is too heavily
                                              overloaded here *)
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

lemma [simp]: "null = (NULL::('a)Integer)"
by(rule ext,simp add: UU_option_def NULL_option_def null_def NULL_fun_def)

lemma [simp]: "null = (NULL::('a)Boolean)"
by(rule ext,simp add: UU_option_def NULL_option_def null_def NULL_fun_def)

lemma [simp]: "\<zero>  \<noteq> NULL"
by(simp add: zero_non_null[simplified])


text{* Now, on this basis we generalize the concept of a valuation: we do no
longer care that the @{text "\<bottom>"} and @{text "NULL"} were actually constructed
by the type constructor option; rather, we require that the type is just from
the null-class:*}

type_synonym ('\<AA>,'\<alpha>) val' = "'\<AA> st \<Rightarrow> '\<alpha>::null"

text{* However, this has also the consequence that core concepts like definedned 
or validness have to be redefined on this type class:*}

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

lemmas cp_intro[simp,intro!] = 
       cp_defined'[THEN allI[THEN allI[THEN cpI1], of defined']]
       cp_valid'[THEN allI[THEN allI[THEN cpI1], of valid']]
       cp_intro

text{* In fact, it can be proven for the base types that both versions of undefined
and invalid are actually the same: *}

lemma defined_is_defined'[simp]: "\<delta> X = \<delta>' X"
by(rule ext,
   auto simp: defined'_def defined_def true_def false_def false_def true_def
              UU_fun_def UU_option_def NULL_option_def NULL_fun_def)

lemma valid_is_valid'[simp]: "\<upsilon>' X = \<upsilon>' X"
by(rule ext,
   auto simp: valid'_def valid_def true_def false_def false_def true_def
              UU_fun_def UU_option_def NULL_option_def NULL_fun_def)

subsection {* Example: The Set-Collection Type *}

text{* For the semantic construction of the collection types, we have two goals:
\begin{enumerate}
\item we want the types to be \emph{fully abstract}, i.e. the type should not
      contain junk-elements that are not representable by OCL expressions.
\item We want a possibility to nest collection types (so, we want the 
      potential to talking about @{text "Set(Set(Sequences(Pairs(X,Y))))"}), and
\end
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

text{* ... which means that we can have a type ('\<AA>,('\<AA>,('\<AA>) Integer) Set) Set
corresponding exactly to Set(Set(Integer)) in OCL notation. Note that the parameter
\<AA> still refers to the object universe; making the OCL semantics entirely parametric
in the object universe makes it possible to study (and prove) its properties 
independently from a concrete class diagram. *}


definition mtSet::"('\<AA>,'\<alpha>::null) Set"  ("Set{}")
where "Set{} \<equiv> (\<lambda> \<tau>.  Abs_Set_0 \<lfloor>\<lfloor>{}::'\<alpha> set\<rfloor>\<rfloor> )"

text{* Note that the collection types in OCL allow for NULL to be included;
  however, there is the NULL-collection into which inclusion yields invalid. *}

definition OclIncluding   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val'] \<Rightarrow> ('\<AA>,'\<alpha>) Set"
where     "OclIncluding x y = (\<lambda> \<tau>.  if (\<delta>' x) \<tau> = true \<tau> \<and> (\<upsilon>' y) \<tau> = true \<tau>
                                     then Abs_Set_0 \<lfloor>\<lfloor> \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>  \<union> {y \<tau>} \<rfloor>\<rfloor> 
                                     else UU )"

definition OclIncludes   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val'] \<Rightarrow> '\<AA> Boolean"
where     "OclIncludes x y = (\<lambda> \<tau>.  if (\<delta>' x) \<tau> = true \<tau> \<and> (\<upsilon>' y) \<tau> = true \<tau> 
                                    then UU
                                    else \<lfloor>\<lfloor>(y \<tau>) \<in> \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil> \<rfloor>\<rfloor> )"


consts (* abstract set collection operations *)
    OclSize        :: " ('\<AA>,'\<alpha>::null) Set \<Rightarrow> '\<AA> Integer"    
    OclCount       :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> '\<AA> Integer"    
 (* OclIncludes    :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val'] \<Rightarrow> '\<AA> Boolean"     *)
    OclExcludes    :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val'] \<Rightarrow> '\<AA> Boolean"    
 (* OclIncluding   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val'] \<Rightarrow> ('\<AA>,'\<alpha>) Set"    *)
    OclExcluding   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val'] \<Rightarrow> ('\<AA>,'\<alpha>) Set"
    OclSum         :: " ('\<AA>,'\<alpha>::null) Set \<Rightarrow> '\<AA> Integer"
    OclIncludesAll :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> '\<AA> Boolean"
    OclExcludesAll :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> '\<AA> Boolean"
    OclIsEmpty     :: " ('\<AA>,'\<alpha>::null) Set \<Rightarrow> '\<AA> Boolean"
    OclNotEmpty    :: " ('\<AA>,'\<alpha>::null) Set \<Rightarrow> '\<AA> Boolean"
    OclComplement  :: " ('\<AA>,'\<alpha>::null) Set \<Rightarrow> ('\<AA>,'\<alpha>) Set"
    OclUnion       :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> ('\<AA>,'\<alpha>) Set"
    OclIntersection:: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> ('\<AA>,'\<alpha>) Set"

  
notation  (* standard ascii syntax *)
    OclSize        ("_ ->size'(')" [66])
and
    OclCount       ("_ ->count'(_')" [66,65]65)
and
    OclIncludes    ("_ ->includes'(_')" [66,65]65)
and
    OclExcludes    ("_ ->excludes'(_')" [66,65]65)
and
    OclSum         ("_ ->sum'(')" [66])
and
    OclIncludesAll ("_ ->includesAll'(_')" [66,65]65)
and
    OclExcludesAll ("_ ->excludesAll'(_')" [66,65]65)
and
    OclIsEmpty     ("_ ->isEmpty'(')" [66])
and
    OclNotEmpty    ("_ ->notEmpty'(')" [66])
and
    OclIncluding   ("_ ->including'( _ ')")
and
    OclExcluding   ("_ ->excluding'( _ ')")
and
    OclComplement  ("_ ->complement'(')")
and
    OclUnion       ("_ ->union'( _ ')"          [66,65]65)
and
    OclIntersection("_ ->intersection'( _ ')"   [71,70]70)


lemma including_strict1[simp]:"(\<bottom>->including(x)) = \<bottom>"
by(simp add: OclIncluding_def UU_fun_def defined'_def valid'_def false_def true_def)

lemma including_strict2[simp]:"(X->including(\<bottom>)) = \<bottom>"
by(simp add: OclIncluding_def UU_fun_def defined'_def valid'_def false_def true_def)

lemma including_strict3[simp]:"(NULL->including(x)) = \<bottom>"
by(simp add: OclIncluding_def UU_fun_def defined'_def valid'_def false_def true_def)


syntax
  "_OclFinset" :: "args => ('\<AA>,'a::null) Set"    ("Set{(_)}")
translations
  "Set{x, xs}" == "CONST OclIncluding (Set{xs}) x"
  "Set{x}"     == "CONST OclIncluding (Set{}) x "

lemma syntax_test: "Set{\<two>,\<one>} = (Set{}->including(\<one>)->including(\<two>))"
by simp


end
