theory OCL_state
imports OCL_lib
begin

section{* Recall: The generic structure of States*}

text{* Next we will introduce the foundational concept of an object id (oid), 
which is just some infinite set.  *}

type_synonym oid = ind

text{* States are just a partial map from oid's to elements of an object universe @{text "'\<AA>"},
and state transitions pairs of states...  *}
type_synonym ('\<AA>)state = "oid \<rightharpoonup> '\<AA> "

type_synonym ('\<AA>)st = "'\<AA> state \<times> '\<AA> state"

text{* Now we refine our state-interface.
In certain contexts, we will require that the elements of the object universe have 
a particular structure; more precisely, we will require that there is a function that
reconstructs the oid of an object in the state (we will settle the question how to define
this function later). *}

class object =  fixes oid_of :: "'a \<Rightarrow> oid"

text{* Thus, if needed, we can constrain the object universe to objects by adding
the following type class constraint:*}
typ "'\<AA> :: object"


section{* Referential Object Equality in States*}

text{* Generic referential equality - to be used for instantiations
 with concrete object types ... *}
definition  gen_ref_eq :: "('\<AA>,'a::{object,null})val \<Rightarrow> ('\<AA>,'a)val \<Rightarrow> ('\<AA>)Boolean" 
where      "gen_ref_eq x y
            \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                    then if x \<tau> = null \<or> y \<tau> = null
                         then \<lfloor>\<lfloor>x \<tau> = null \<and> y \<tau> = null\<rfloor>\<rfloor>
                         else \<lfloor>\<lfloor>(oid_of (x \<tau>)) = (oid_of (y \<tau>)) \<rfloor>\<rfloor>
                    else invalid \<tau>"


lemma gen_ref_eq_object_strict1[simp] : 
"(gen_ref_eq x invalid) = invalid"
by(rule ext, simp add: gen_ref_eq_def true_def false_def)

lemma gen_ref_eq_object_strict2[simp] : 
"(gen_ref_eq invalid x) = invalid"
by(rule ext, simp add: gen_ref_eq_def true_def false_def)

lemma gen_ref_eq_object_strict3[simp] : 
"(gen_ref_eq x null) = invalid"
by(rule ext, simp add: gen_ref_eq_def true_def false_def)

lemma gen_ref_eq_object_strict4[simp] : 
"(gen_ref_eq null x) = invalid"
by(rule ext, simp add: gen_ref_eq_def true_def false_def)

lemma cp_gen_ref_eq_object: 
"(gen_ref_eq x y \<tau>) = (gen_ref_eq (\<lambda>_. x \<tau>) (\<lambda>_. y \<tau>)) \<tau>"
by(auto simp: gen_ref_eq_def StrongEq_def invalid_def  cp_defined[symmetric])

lemmas cp_intro[simp,intro!] = 
       OCL_core.cp_intro
       cp_gen_ref_eq_object[THEN allI[THEN allI[THEN allI[THEN cpI2]], 
             of "gen_ref_eq"]]

text{* Finally, we derive the usual laws on definedness for (generic) object equality:*}
lemma gen_ref_eq_defargs: 
"\<tau> \<Turnstile> (gen_ref_eq x (y::('\<AA>,'a::{null,object})val))\<Longrightarrow> (\<tau> \<Turnstile>(\<delta> x)) \<and> (\<tau> \<Turnstile>(\<delta> y))"
by(simp add: gen_ref_eq_def OclValid_def true_def invalid_def
             defined_def invalid_def bot_fun_def bot_option_def
        split: bool.split_asm HOL.split_if_asm)


section{* Further requirements on States*}
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
object type, the equality @{text "\<doteq>"} is defined by generic referential
equality. *}


(* wannabe *)theorem strictEqGen_vs_strongEq: 
"WFF \<tau> \<Longrightarrow> \<tau> \<Turnstile>(\<delta> x) \<Longrightarrow> \<tau> \<Turnstile>(\<delta> y) \<Longrightarrow> 
          (\<tau> \<Turnstile> (gen_ref_eq x y)) = (\<tau> \<Turnstile> (x \<triangleq> y))"
apply(auto simp: gen_ref_eq_def OclValid_def WFF_def StrongEq_def true_def)
sorry
text{* WFF and ref\_eq must be defined strong enough defined that this can be proven! *}


section{* Miscillaneous: Initial States (for Testing and Code Generation) *}

definition \<tau>\<^isub>0 :: "('\<AA>)st"
where     "\<tau>\<^isub>0 \<equiv> (Map.empty,Map.empty)"


section{* Generic Operations on States *}

text{* In order to denote OCL-types occuring in OCL expressions syntactically --- as, for example, 
as "argument" of allInstances --- we use the inverses of the injection functions into the object
universes; we show that this is sufficient "characterization". *}

definition allinstances :: "('\<AA> \<Rightarrow> '\<alpha>) \<Rightarrow> ('\<AA>::object,'\<alpha> option option) Set" 
                           ("_ ::oclAllInstances'(')")
where  "(H ::oclAllInstances()) \<tau> = Abs_Set_0 \<lfloor>\<lfloor>(Some o Some o H) ` (ran(snd \<tau>)) \<rfloor>\<rfloor> "

definition allinstancesATpre :: "('\<AA> \<Rightarrow> '\<alpha>) \<Rightarrow> ('\<AA>::object,'\<alpha> option option) Set" 
                           ("_ ::oclAllInstances@pre'(')")
where  "(H ::oclAllInstances@pre()) \<tau> = Abs_Set_0 \<lfloor>\<lfloor>(Some o Some o H) ` (ran(fst \<tau>)) \<rfloor>\<rfloor> "


consts oclisnew :: "('\<AA>::object,'\<alpha>)val \<Rightarrow> '\<AA> Boolean" ("_.oclIsNew'(')")

consts oclismodified ::"('\<AA>::object,'\<alpha>) Set \<Rightarrow> '\<AA> Boolean" ("_->oclIsModified'(')")



section{* Generic Operations on Objects *}

text{* The overloaded function of type casts in OCL. 
       We assume for each type-argument a set in HOL that contains
       exactly all object-representations of this types; this set is used
       to denote this type. *}
consts oclastype :: "('\<AA>::object,'\<alpha>)val \<Rightarrow> '\<beta> set \<Rightarrow> 
                     ('\<AA>::object,'\<beta>)val" ("_.oclAsType'(_')")

consts oclistype :: "('\<AA>::object,'\<alpha>)val \<Rightarrow> '\<beta> set \<Rightarrow>
                      '\<AA> Boolean" ("_.oclIsType'(_')")

consts ocliskind :: "('\<AA>::object,'\<alpha>)val \<Rightarrow> '\<beta> set \<Rightarrow>
                      '\<AA> Boolean" ("_.oclIsType'(_')")


end
