theory OCL_lib
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



section{*Collection Types*}


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

section {* Liftings of Type Constructors for Collections *}

text {* In order to have the possibility to nest collection types,
it is necessary to introduce a uniform interface for types having
the "invalid" (= bottom) element. In a second step, our base-types
will be shown to be instances of this class.

It is conceivable to construct a class of types that have both null AND
invalid; however, so far, we did not find a concrete need for this.*}

instantiation   option  :: (type)bottom
begin 

   definition bot_option_def: "(UU::'a option) \<equiv> (None::'a option)"

   instance proof 
              show "\<exists>x\<Colon>'a option. x \<noteq> \<bottom>"
              by(rule_tac x="Some x" in exI, simp add:bot_option_def)
            qed
end

instantiation "fun"  :: (type,bottom) bottom 
begin
   definition bot_fun_def: "UU \<equiv> (\<lambda> x. \<bottom>)"

   instance proof  show "\<exists>(x::'a \<Rightarrow> 'b). x \<noteq> \<bottom>"
                   apply(rule_tac x="\<lambda> _. (SOME y. y \<noteq> \<bottom>)" in exI, auto)
                   apply(drule_tac x=x in fun_cong,auto simp:bot_fun_def)
                   apply(erule contrapos_pp, simp)
                   apply(rule some_eq_ex[THEN iffD2])
                   apply(simp add: nonEmpty)
                   done
            qed
end

instantiation   option  :: (bottom)null
begin 
   definition NULL_def: "(NULL::'a\<Colon>bottom option) \<equiv>  \<lfloor> \<bottom> \<rfloor>"

   instance proof  show "(NULL::'a\<Colon>bottom option) \<noteq> \<bottom>"
                   by( simp add:NULL_def bot_option_def)
            qed
end

instantiation "fun"  :: (type,null) null 
begin
 definition null_fun_def: "(NULL::'a \<Rightarrow> 'b::null) \<equiv> (\<lambda> x. NULL)"

 instance proof 
              show "(NULL::'a \<Rightarrow> 'b::null) \<noteq> \<bottom>"
              apply(auto simp: null_fun_def bot_fun_def)
              apply(drule_tac x=x in fun_cong)
              apply(erule contrapos_pp, simp add: null_is_valid)
            done
          qed
end


lemma "\<zero> \<noteq> NULL"
apply(auto simp:ocl_zero_def null_fun_def NULL_def bot_option_def) 
apply(drule_tac x=x in fun_cong, simp)
done


text{* In order to have full abstract types (i.e. all elements of the 
"full" HOL-type correspond to elements in the OCL type; full abstractness
guarantees that an extensionality principle works as well), we need to exclude
elements in collections that are \<bottom> (null, however, is ok). The technical
machinery for this is a construction called "smashing" which maps essentially
all pre-collections with \<bottom> elements itself into \<bottom>. *}

typedef  '\<alpha> Set_0 = "{X::('\<alpha>\<Colon>null) set option option.
                         X = \<bottom> \<or> X = NULL \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> \<bottom>)}"
          
          by (rule_tac x="\<bottom>" in exI, simp)


instantiation   Set_0  :: (null)bottom
begin 

   definition bot_Set_0_def: "(UU::('a::null) Set_0) \<equiv> Abs_Set_0 None"

   instance proof show "\<exists>x\<Colon>'a Set_0. x \<noteq> \<bottom>"
                  apply(rule_tac x="Abs_Set_0 \<lfloor>None\<rfloor>" in exI)
                  apply(simp add:bot_Set_0_def)
                  apply(subst Abs_Set_0_inject) 
                  apply(simp_all add: Set_0_def bot_Set_0_def 
                                      NULL_def bot_option_def)
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
                                      NULL_def bot_option_def)
                  done
            qed
end


text{* Now, on this basis we redefine the concept of a valuation:*}

type_synonym ('\<AA>,'\<alpha>) val' = "'\<AA> st \<Rightarrow> '\<alpha>::null"

text{* ...  and lifting this type to the format of a valuation gives us:*}
type_synonym    ('\<AA>,'\<alpha>) Set  = "('\<AA>, '\<alpha> Set_0) val'"

text{* ... which means that we can have a type ('\<AA>,('\<AA>,('\<AA>) Integer) Set) Set
corresponding exactly to Set(Set(Integer)) in OCL notation. Note that the parameter
\<AA> still refers to the object universe; making the OCL semantics entirely parametric
in the object universe makes it possible to study (and prove) its properties 
independently from a concrete class diagram. *}

consts (* abstract set collection operations *)
    OclSize        :: " ('\<AA>,'\<alpha>::null) Set \<Rightarrow> '\<AA> Integer"    
    OclCount       :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> '\<AA> Integer"    
    OclIncludes    :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val'] \<Rightarrow> '\<AA> Boolean"    
    OclExcludes    :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val'] \<Rightarrow> '\<AA> Boolean"    
    OclIncluding   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val'] \<Rightarrow> ('\<AA>,'\<alpha>) Set"    
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


definition mtSet::"('\<AA>,'a::null) Set"  ("Set{}")
where "Set{} \<equiv> (\<lambda> \<tau>.  Abs_Set_0 \<lfloor>\<lfloor>{}::'a set\<rfloor>\<rfloor> )"

syntax
  "_OclFinset" :: "args => ('\<AA>,'a::null) Set"    ("Set{(_)}")
translations
  "Set{x, xs}" == "CONST OclIncluding (Set{xs}) x"
  "Set{x}" == "CONST OclIncluding (Set{}) x "

lemma syntax_test: "Set{\<two>,\<one>} = (Set{}->including(\<one>)->including(\<two>))"
by simp


(* And if we stick to the idea that there is just one notion of
   valuation ????? *)

end
