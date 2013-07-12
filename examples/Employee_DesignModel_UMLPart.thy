(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4 
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Employee_DesignModel_UMLPart.thy --- OCL Contracts and an Example.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2012-2013 Université Paris-Sud, France
 *               2013      IRT SystemX, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)
(* $Id:$ *)

header{* Part III: OCL Contracts and an Example *}

(* This example is not yet balanced. Some parts of should go to 
   Part III : State Operations and Objects *)

theory 
  Employee_DesignModel_UMLPart
imports
  "../src/OCL_main" (* Testing *)
begin



subsection{* Introduction *}
text{* For certain concepts like Classes and Class-types, only a generic definition for its resulting
semantics can be given. Generic means, there is a function outside HOL that "compiles" a concrete,
closed-world class diagram into a "theory" of this data model, consisting of a bunch of definitions
for classes, accessors, method, casts, and tests for actual types, as well as proofs for the 
fundamental properties of these operations in this concrete data model. *}

text{* Such generic function or "compiler" can be implemented in Isabelle on the ML level. 
This has been done, for a semantics following the open-world assumption, for UML 2.0 
in~\cite{brucker.ea:extensible:2008-b}. In this paper, we follow another approach for UML 2.4: we define the concepts
of the compilation informally, and present a concrete example which is verified in Isabelle/HOL. *}

subsection{* Outlining the Example *}

text{* We are presenting here a design-model of the (slightly modified) example Figure 7.3, 
page 20 of the \cite{Standard}. To be precise, this theory contains the formalization of 
the DATA-part covered by the UML diagram: ...
This means that the association (attached to the association class
\emph{EmployeeRanking}) with the association ends \verb+boss+ and \verb+employees+ is implemented
by the attribute  \verb+boss+ and the operation \verb+employees+ (to be discussed in the OCL part
captured by the subsequent theory).
*}

subsection{* Example Data-Universe and its Infrastructure *}
text{* Should be generated entirely from a class-diagram. *}

(* @{text "'\<AA>"} -- \mathfrak{A} *)
text{* Our data universe  consists in the concrete class diagram just of node's, 
and implicitly of the class object. Each class implies the existence of a class 
type defined for the corresponding object representations as follows: *}

datatype person =  mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n   oid          (* the oid to the person itself *)
                            "int option" (* the attribute "age" or null *) 
                            "oid option" (* the attribute "boss" or null *)

term "mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n   (0::nat)"

datatype oclany= mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid (* the oid to the oclany itself *)
                        "(int option \<times> oid option) option" 
                             (* the extensions to "person"; used to denote objects of actual type
                               "person" casted to "oclany"; in case of existence of several subclasses 
                                of oclany, sums of extensions have to be provided. *)

text{* Now, we construct a concrete "universe of oclany types" by injection into a 
sum type containing the class types. This type of oclanys will be used as instance
for all resp. type-variables ...*}

datatype \<AA> = in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person | in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oclany

text{* Recall that in order to denote OCL-types occuring in OCL expressions syntactically 
--- as, for example,  as "argument" of allInstances --- we use the inverses of the injection 
functions into the object universes; we show that this is sufficient "characterization". *}
definition Person :: "\<AA> \<Rightarrow> person"
where     "Person \<equiv> (the_inv in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n)"

definition OclAny :: "\<AA> \<Rightarrow> oclany"
where     "OclAny \<equiv> (the_inv in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y)"


text{* Having fixed the object universe, we can introduce type synonyms that exactly correspond
to OCL types. Again, we exploit that our representation of OCL is a "shallow embedding" with a
one-to-one correspondance of OCL-types to types of the meta-language HOL. *}
type_synonym Boolean     = "(\<AA>)Boolean"
type_synonym Integer     = "(\<AA>)Integer"
type_synonym Void        = "(\<AA>)Void"
type_synonym OclAny      = "(\<AA>,oclany option option) val"
type_synonym Person      = "(\<AA>, person option option)val"
type_synonym Set_Integer = "(\<AA>, int option option)Set"
type_synonym Set_Person  = "(\<AA>, person option option)Set"

text{* Just a little check: *}
typ "Boolean"

text{* In order to reuse key-elements of the library like referential equality, we have
to show that the object universe belongs to the type class "oclany", i.e. each class type
has to provide a function @{term oid_of} yielding the object id (oid) of the object. *}
instantiation person :: object
begin
   definition oid_of_person_def: "oid_of x = (case x of mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid _ _ \<Rightarrow> oid)"
   instance ..
end

instantiation oclany :: object
begin
   definition oid_of_oclany_def: "oid_of x = (case x of mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid _ \<Rightarrow> oid)"
   instance ..
end

instantiation \<AA> :: object
begin
   definition oid_of_\<AA>_def: "oid_of x = (case x of 
                                             in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person \<Rightarrow> oid_of person
                                           | in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y obj \<Rightarrow> oid_of obj)"
   instance ..
end

instantiation   option  :: (object)object
begin 
   definition oid_of_option_def: "oid_of x = oid_of (the x)"
   instance ..
end



section{* Instantiation of the generic strict equality. We instantiate the referential equality
on @{text "Person"} and @{text "OclAny"} *}

defs(overloaded)   StrictRefEq\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n   : "(x::Person) \<doteq> y  \<equiv> gen_ref_eq x y"
defs(overloaded)   StrictRefEq\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y   : "(x::OclAny) \<doteq> y  \<equiv> gen_ref_eq x y"

lemmas strict_eq_person =
    cp_gen_ref_eq_object[of "x::Person" "y::Person" "\<tau>", 
                         simplified StrictRefEq\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n[symmetric]]
    cp_intro(9)         [of "P::Person \<Rightarrow>Person""Q::Person \<Rightarrow>Person",
                         simplified StrictRefEq\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n[symmetric] ]
    gen_ref_eq_def      [of "x::Person" "y::Person", 
                         simplified StrictRefEq\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n[symmetric]]
    gen_ref_eq_defargs  [of _ "x::Person" "y::Person", 
                         simplified StrictRefEq\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n[symmetric]]
    gen_ref_eq_object_strict1 
                        [of "x::Person",
                         simplified StrictRefEq\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n[symmetric]]
    gen_ref_eq_object_strict2 
                        [of "x::Person",
                         simplified StrictRefEq\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n[symmetric]]

thm strict_eq_person
(* TODO: Analogue for object. *)


subsection{* AllInstances *}

(* IS THIS WHAT WE WANT ? THIS DEFINITION FILTERS OBJECTS THAT ARE BOOKED UNDER
THEIR APPARENT (STATIC) TYPE INTO THE CONTEXT, NOT BY THEIR ACTUAL (DYNAMIC) TYPE. *)
lemma "(Person .oclAllInstances()) = 
             (\<lambda>\<tau>.  Abs_Set_0 \<lfloor>\<lfloor>(Some \<circ> Some \<circ> (the_inv in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n))`(ran(heap(snd \<tau>))) \<rfloor>\<rfloor>) "
by(rule ext, simp add:allinstances_def Person_def)

lemma "(OclAny .oclAllInstances@pre()) = 
             (\<lambda>\<tau>.  Abs_Set_0 \<lfloor>\<lfloor>(Some \<circ> Some \<circ> (the_inv in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y))`(ran(heap(fst \<tau>))) \<rfloor>\<rfloor>) "
by(rule ext, simp add:allinstancesATpre_def OclAny_def)


text{* For each Class \emph{C}, we will have a casting operation \verb+.oclAsType(+\emph{C}\verb+)+,
   a test on the actual type \verb+.oclIsTypeOf(+\emph{C}\verb+)+ as well as its relaxed form
   \verb+.oclIsKindOf(+\emph{C}\verb+)+ (corresponding exactly to Java's \verb+instanceof+-operator. 
*}
text{* Thus, since we have two class-types in our concrete class hierarchy, we have
two operations to declare and to provide two overloading definitions for the two static types.
*}


section{* Selector Definition *}
text{* Should be generated entirely from a class-diagram. *}

typ "Person \<Rightarrow> Person"

definition "access fst_snd X f = (\<lambda> \<tau>. case X \<tau> of
               \<bottom> \<Rightarrow> invalid \<tau> (* exception propagation *)
          | \<lfloor>  \<bottom> \<rfloor> \<Rightarrow> invalid \<tau> (* dereferencing null pointer *)
          | \<lfloor>\<lfloor> mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid _ _ \<rfloor>\<rfloor> \<Rightarrow> 
                    case (heap (fst_snd \<tau>)) oid of (* We assume here that oid is indeed 'the' oid of the 
                                               Person, ie. we assume that  \<tau> is well-formed. *)
                       \<lfloor>in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n p\<rfloor> \<Rightarrow> f p \<tau>
                     | _ \<Rightarrow> invalid \<tau>)"

(*
definition "(access2 X f) =
               (\<lambda>(\<sigma>,\<sigma>'). (let Ob = (I\<lbrakk>X\<rbrakk>(\<sigma>,\<sigma>')) in
                            if (Ob=\<bottom>) \<or> (Ob=\<lfloor>\<bottom>\<rfloor>) \<or> (oid_of \<lceil>\<lceil>Ob\<rceil>\<rceil>) \<in> (dom \<sigma>') then invalid(\<sigma>,\<sigma>')
                            else undefined))"
*)

definition "access_to_boss fst_snd = (\<lambda> X \<tau>. case X of 
                     mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n _ _ \<bottom> \<Rightarrow> null \<tau> (* object contains null pointer *)
                   | mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n _ _ \<lfloor>boss\<rfloor> \<Rightarrow> case (heap (fst_snd \<tau>)) boss of
                       \<lfloor>in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n a b c) \<rfloor> \<Rightarrow> \<lfloor>\<lfloor> mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n a b c \<rfloor>\<rfloor>
                     | _ \<Rightarrow> invalid \<tau>)" (* illtyped state, not occuring in 
                                             well-formed, typed states *)

definition "access_to_age = (\<lambda> X _. case X of mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n _ i _ \<Rightarrow> \<lfloor>i\<rfloor>)"

definition "at_pre = fst"
definition "at_post = snd"

lemmas [simp] =
 at_pre_def at_post_def 
 access_def
 access_def[of at_pre] access_def[of at_post]
 access_to_boss_def
 access_to_age_def

fun dot_boss:: "Person \<Rightarrow> Person"  ("(1(_).boss)" 50)
  where "(X).boss = access at_post X (access_to_boss at_post)"

fun dot_age:: "Person \<Rightarrow> Integer"  ("(1(_).age)" 50)
  where "(X).age = access at_post X access_to_age"

fun dot_boss_at_pre:: "Person \<Rightarrow> Person"  ("(1(_).boss@pre)" 50)
  where "(X).boss@pre = access at_pre X (access_to_boss at_pre)"
  (* | \<lfloor>\<lfloor> mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid i \<bottom> \<rfloor>\<rfloor> \<Rightarrow> null \<tau>(* object contains null pointer. REALLY ? 
                                          And if this pointer was defined in the pre-state ?*) *)

fun dot_age_at_pre:: "Person \<Rightarrow> Integer"  ("(1(_).age@pre)" 50)
  where "(X).age@pre = access at_pre X access_to_age"

lemma cp_dot_boss: "((X).boss) \<tau> = ((\<lambda>_. X \<tau>).boss) \<tau>" by(simp)

lemma cp_dot_age: "((X).age) \<tau> = ((\<lambda>_. X \<tau>).age) \<tau>" by(simp)

lemma cp_dot_boss_at_pre: "((X).boss@pre) \<tau> = ((\<lambda>_. X \<tau>).boss@pre) \<tau>" by(simp)

lemma cp_dot_boss_pre: "((X).age@pre) \<tau> = ((\<lambda>_. X \<tau>).age@pre) \<tau>" by(simp)

lemmas cp_dot_bossI [simp, intro!]= 
       cp_dot_boss[THEN allI[THEN allI], of "\<lambda> X _. X" "\<lambda> _ \<tau>. \<tau>", THEN cpI1]

lemmas cp_dot_bossI_at_pre [simp, intro!]= 
       cp_dot_boss_at_pre[THEN allI[THEN allI],  
                          of "\<lambda> X _. X" "\<lambda> _ \<tau>. \<tau>", THEN cpI1]

lemma dot_boss_nullstrict [simp]: "(null).boss = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def)

lemma dot_boss_at_pre_nullstrict [simp] : "(null).boss@pre = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def)

lemma dot_boss_strict [simp] : "(invalid).boss = invalid" 
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def)

lemma dot_boss_at_pre_strict [simp] : "(invalid).boss@pre = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def)

subsection{* A little infra-structure on example states.*}

definition oid\<^isub>1::oid where "oid\<^isub>1 \<equiv> (0::nat)"
definition oid\<^isub>2::oid where "oid\<^isub>2 \<equiv> (1::nat)"
definition oid\<^isub>3::oid where "oid\<^isub>3 \<equiv> (2::nat)"
definition oid\<^isub>4::oid where "oid\<^isub>4 \<equiv> (3::nat)"
definition oid\<^isub>5::oid where "oid\<^isub>5 \<equiv> (4::nat)"
definition oid\<^isub>6::oid where "oid\<^isub>6 \<equiv> (5::nat)"
definition oid\<^isub>7::oid where "oid\<^isub>7 \<equiv> (6::nat)"

definition "person1 \<equiv> mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid\<^isub>1 \<lfloor>2\<rfloor> \<lfloor>oid\<^isub>2\<rfloor>"
definition "person2 \<equiv> mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid\<^isub>2 \<lfloor>5\<rfloor> \<lfloor>oid\<^isub>2\<rfloor>"
definition "person3 \<equiv> mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid\<^isub>3 None None"
definition "person4 \<equiv> mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid\<^isub>4 \<lfloor>8\<rfloor> None"
definition "person5 \<equiv> mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid\<^isub>5 \<lfloor>7\<rfloor> None"
definition "person6 \<equiv> mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid\<^isub>6 \<lfloor>11\<rfloor> \<lfloor>oid\<^isub>7\<rfloor>"

definition \<sigma>\<^isub>1 :: "\<AA> state"
where "\<sigma>\<^isub>1  \<equiv> \<lparr> heap = empty(oid\<^isub>1 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n(mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid\<^isub>1 \<lfloor>1\<rfloor> \<lfloor>oid\<^isub>2\<rfloor>))
                           (oid\<^isub>2 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n(mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid\<^isub>2 \<lfloor>3\<rfloor>  None))
                           (oid\<^isub>4 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n(mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid\<^isub>4 \<lfloor>6\<rfloor> \<lfloor>oid\<^isub>5\<rfloor>))
                           (oid\<^isub>5 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person5)
                           (oid\<^isub>6 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n(mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid\<^isub>6 \<lfloor>9\<rfloor> \<lfloor>oid\<^isub>4\<rfloor>)),
               assocs = empty\<rparr>"

definition \<sigma>\<^isub>1' :: "\<AA> state"
where "\<sigma>\<^isub>1' \<equiv> \<lparr> heap = empty(oid\<^isub>1 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person1)
                           (oid\<^isub>2 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person2)
                           (oid\<^isub>3 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person3)
                           (oid\<^isub>4 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person4)
                           (oid\<^isub>6 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person6)
                           (oid\<^isub>7 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n(mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid\<^isub>7 \<lfloor>10\<rfloor> \<lfloor>oid\<^isub>7\<rfloor>)),
               assocs = empty\<rparr>"
 
lemma basic_\<tau>_wff: "WFF(\<sigma>\<^isub>1,\<sigma>\<^isub>1')"
by(auto simp: WFF_def \<sigma>\<^isub>1_def \<sigma>\<^isub>1'_def
              oid\<^isub>1_def oid\<^isub>2_def oid\<^isub>3_def oid\<^isub>4_def oid\<^isub>5_def oid\<^isub>6_def oid\<^isub>7_def
              oid_of_\<AA>_def oid_of_person_def
              person1_def person2_def person3_def person4_def person5_def person6_def)

lemma [simp,code_unfold]: "dom (heap \<sigma>\<^isub>1) = {oid\<^isub>1,oid\<^isub>2,oid\<^isub>4,oid\<^isub>5,oid\<^isub>6}"
by(auto simp: \<sigma>\<^isub>1_def)

lemma [code_unfold]: "dom (heap \<sigma>\<^isub>1') = {oid\<^isub>1,oid\<^isub>2,oid\<^isub>3,oid\<^isub>4,oid\<^isub>6,oid\<^isub>7}"
by(auto simp: \<sigma>\<^isub>1'_def)

definition "X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 \<equiv> \<lambda> _ .\<lfloor>\<lfloor> person1 \<rfloor>\<rfloor>"
definition "X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 \<equiv> \<lambda> _ .\<lfloor>\<lfloor> person2 \<rfloor>\<rfloor>"
definition "X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n3 \<equiv> \<lambda> _ .\<lfloor>\<lfloor> person3 \<rfloor>\<rfloor>"
definition "X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n4 \<equiv> \<lambda> _ .\<lfloor>\<lfloor> person4 \<rfloor>\<rfloor>"
definition "X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n5 \<equiv> \<lambda> _ .\<lfloor>\<lfloor> person5 \<rfloor>\<rfloor>"
definition "X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6 \<equiv> \<lambda> _ .\<lfloor>\<lfloor> person6 \<rfloor>\<rfloor>"

lemma [code_unfold]: "((x::Person) \<doteq> y) = gen_ref_eq x y" by(simp only: StrictRefEq\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n)

value "\<not>((\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .age)    \<doteq> \<one> ))"
value "  (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .age)    \<doteq> \<two> )"
value "  (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .age@pre)     \<doteq> \<one>)" 
value "\<not>((\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .age@pre)     \<doteq> \<two> ))"
value "\<not>((\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .boss )  \<doteq> X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 ))"
value "  (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .boss .age)   \<doteq> \<five> )"
value "\<not>((\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .boss .boss)  \<doteq> X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 ))" 
value "  (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .boss@pre .age)  \<doteq> \<five> )"
value "  (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .boss@pre .age@pre)  \<doteq> \<three> )"
value "\<not>((\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .boss@pre .age@pre)  \<doteq> \<five> ))"
value "  (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .boss@pre .boss)  \<doteq> X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 )"
value "  (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .boss@pre .boss@pre)  \<doteq> null )"
value "  (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile> not(\<upsilon>(X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .boss@pre .boss@pre .boss@pre))"


value "  (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 .age)       \<doteq> \<five>)" 
value "  (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 .age@pre)   \<doteq> \<three>)" 
value "  (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 .boss)      \<doteq> X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2)"
value "  (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 .boss@pre)  \<doteq> null )"
value "\<not>((\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 .boss@pre)  \<doteq> X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2))" 
value "\<not>((\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 .boss@pre)  \<doteq> (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 .boss)))" 


value "  (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n3 .age)       \<doteq> null)"
value "  (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile> not(\<upsilon>(X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n3 .age@pre))"
value "\<not>((\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n3 .age@pre)   \<doteq> null))"

value "  (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n4 .boss@pre)   \<doteq> X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n5 )"
value "  (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile> not(\<upsilon>(X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n4 .boss@pre .age))" 
value "  (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n4 .boss@pre .age@pre)   \<doteq> \<seven> )"

value "  (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6 .boss .age)   \<doteq> \<one>\<zero> )"
value "  (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile> not(\<upsilon>(X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6 .boss .age@pre))" 
value "  (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6 .boss@pre .age)   \<doteq> \<eight> )"
value "  (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6 .boss@pre .age@pre)   \<doteq> \<six> )"

subsection{* Casts *}

consts oclastype\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y :: "'\<alpha> \<Rightarrow> OclAny" ("(_) .oclAsType'(OclAny')")
consts oclastype\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n :: "'\<alpha> \<Rightarrow> Person" ("(_) .oclAsType'(Person')")

defs (overloaded) oclastype\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny: 
        "(X::OclAny) .oclAsType(OclAny) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> null \<tau>   (* to avoid: null .oclAsType(OclAny) = null ? *)
                            | \<lfloor>\<lfloor>mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid a \<rfloor>\<rfloor> \<Rightarrow>  \<lfloor>\<lfloor>mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid a \<rfloor>\<rfloor>)"  (* identity *)

defs (overloaded) oclastype\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person:  
        "(X::Person) .oclAsType(OclAny) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> null \<tau>    (* OTHER POSSIBILITY : null ??? Really excluded 
                                                     by standard *)
                            | \<lfloor>\<lfloor>mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid a b \<rfloor>\<rfloor> \<Rightarrow>  \<lfloor>\<lfloor>  (mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid \<lfloor>(a,b)\<rfloor>) \<rfloor>\<rfloor>)"

defs (overloaded) oclastype\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny: 
        "(X::OclAny) .oclAsType(Person) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> null \<tau>   
                            | \<lfloor>\<lfloor>mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid \<bottom> \<rfloor>\<rfloor> \<Rightarrow>  invalid \<tau>   (* down-cast exception *)
                            | \<lfloor>\<lfloor>mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid \<lfloor>(a,b)\<rfloor> \<rfloor>\<rfloor> \<Rightarrow>  \<lfloor>\<lfloor>mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid a b \<rfloor>\<rfloor>)" 

defs (overloaded) oclastype\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person: 
        "(X::Person) .oclAsType(Person) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> null \<tau>   (* to avoid: null .oclAsType(OclAny) = null ? *)
                            | \<lfloor>\<lfloor>mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid a b \<rfloor>\<rfloor> \<Rightarrow>  \<lfloor>\<lfloor>mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid a b\<rfloor>\<rfloor>)"  (* identity *)


lemma cp_oclastype\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_Person: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::Person) :: Person) .oclAsType(OclAny))"
by(rule_tac f = "\<lambda>x. (x .oclAsType(OclAny))" in cpI1, simp_all add: oclastype\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person)
lemma cp_oclastype\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::OclAny) :: OclAny) .oclAsType(OclAny))"
by(rule_tac f = "\<lambda>x. (x .oclAsType(OclAny))" in cpI1, simp_all add: oclastype\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny)
lemma cp_oclastype\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Person: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::Person) :: Person) .oclAsType(Person))"
by(rule_tac f = "\<lambda>x. (x .oclAsType(Person))" in cpI1, simp_all add: oclastype\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person)
lemma cp_oclastype\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::OclAny) :: OclAny) .oclAsType(Person))"
by(rule_tac f = "\<lambda>x. (x .oclAsType(Person))" in cpI1, simp_all add: oclastype\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)

lemma cp_oclastype\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::Person) :: OclAny) .oclAsType(OclAny))"
by(rule_tac f = "\<lambda>x. (x .oclAsType(OclAny))" in cpI1, simp_all add: oclastype\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny)
lemma cp_oclastype\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_Person: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::OclAny) :: Person) .oclAsType(OclAny))"
by(rule_tac f = "\<lambda>x. (x .oclAsType(OclAny))" in cpI1, simp_all add: oclastype\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person)
lemma cp_oclastype\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::Person) :: OclAny) .oclAsType(Person))"
by(rule_tac f = "\<lambda>x. (x .oclAsType(Person))" in cpI1, simp_all add: oclastype\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)
lemma cp_oclastype\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Person: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::OclAny) :: Person) .oclAsType(Person))"
by(rule_tac f = "\<lambda>x. (x .oclAsType(Person))" in cpI1, simp_all add: oclastype\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person)

lemmas [simp] = 
 cp_oclastype\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_Person
 cp_oclastype\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_OclAny
 cp_oclastype\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Person
 cp_oclastype\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_OclAny

 cp_oclastype\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_OclAny
 cp_oclastype\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_Person
 cp_oclastype\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_OclAny
 cp_oclastype\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Person

lemma oclastype\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_strict[simp] : "(invalid::OclAny) .oclAsType(OclAny) = invalid" 
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclastype\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny)

lemma oclastype\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_nullstrict[simp] : "(null::OclAny) .oclAsType(OclAny) = null" 
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclastype\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny)

lemma oclastype\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_strict[simp] : "(invalid::Person) .oclAsType(OclAny) = invalid" 
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclastype\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person bot_Boolean_def)

lemma oclastype\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_nullstrict[simp] : "(null::Person) .oclAsType(OclAny) = null" 
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclastype\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person)

lemma oclastype\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_strict[simp] : "(invalid::OclAny) .oclAsType(Person) = invalid" 
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclastype\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)

lemma oclastype\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_nullstrict[simp] : "(null::OclAny) .oclAsType(Person) = null" 
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclastype\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)

lemma oclastype\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_strict[simp] : "(invalid::Person) .oclAsType(Person) = invalid" 
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclastype\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person bot_Boolean_def)

lemma oclastype\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_nullstrict[simp] : "(null::Person) .oclAsType(Person) = null" 
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclastype\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person)


section{* Tests for Actual Types *}

consts oclistypeof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_).oclIsTypeOf'(OclAny')")
consts oclistypeof\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n :: "'\<alpha> \<Rightarrow> Boolean" ("(_).oclIsTypeOf'(Person')")

defs (overloaded) oclistypeof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny: 
        "(X::OclAny) .oclIsTypeOf(OclAny) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> true \<tau>  (* invalid ?? *)
                            | \<lfloor>\<lfloor>mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid \<bottom> \<rfloor>\<rfloor> \<Rightarrow> true \<tau>
                            | \<lfloor>\<lfloor>mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid \<lfloor>_\<rfloor> \<rfloor>\<rfloor> \<Rightarrow> false \<tau>)" 

defs (overloaded) oclistypeof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person: 
        "(X::Person) .oclIsTypeOf(OclAny) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> true \<tau>    (* invalid ?? *)
                            | \<lfloor>\<lfloor> _ \<rfloor>\<rfloor> \<Rightarrow> false \<tau>)"  (* must have actual type Person otherwise  *)

defs (overloaded) oclistypeof\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny: 
        "(X::OclAny) .oclIsTypeOf(Person) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> true \<tau>  
                            | \<lfloor>\<lfloor>mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid \<bottom> \<rfloor>\<rfloor> \<Rightarrow> false \<tau>
                            | \<lfloor>\<lfloor>mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid \<lfloor>_\<rfloor> \<rfloor>\<rfloor> \<Rightarrow> true \<tau>)" 

defs (overloaded) oclistypeof\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person: 
        "(X::Person) .oclIsTypeOf(Person) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> true \<tau>  
                            | \<lfloor>\<lfloor> _ \<rfloor>\<rfloor> \<Rightarrow> true \<tau>)"  (* must have actual type Node otherwise  *)

lemma cp_oclistypeof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_Person: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::Person) :: Person) .oclIsTypeOf(OclAny))"
by(rule_tac f = "\<lambda>x. (x .oclIsTypeOf(OclAny))" in cpI1, simp_all add: oclistypeof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person)
lemma cp_oclistypeof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::OclAny) :: OclAny) .oclIsTypeOf(OclAny))"
by(rule_tac f = "\<lambda>x. (x .oclIsTypeOf(OclAny))" in cpI1, simp_all add: oclistypeof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny)
lemma cp_oclistypeof\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Person: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::Person) :: Person) .oclIsTypeOf(Person))"
by(rule_tac f = "\<lambda>x. (x .oclIsTypeOf(Person))" in cpI1, simp_all add: oclistypeof\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person)
lemma cp_oclistypeof\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::OclAny) :: OclAny) .oclIsTypeOf(Person))"
by(rule_tac f = "\<lambda>x. (x .oclIsTypeOf(Person))" in cpI1, simp_all add: oclistypeof\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)


lemma cp_oclistypeof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::Person) :: OclAny) .oclIsTypeOf(OclAny))"
by(rule_tac f = "\<lambda>x. (x .oclIsTypeOf(OclAny))" in cpI1, simp_all add: oclistypeof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny)
lemma cp_oclistypeof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_Person: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::OclAny) :: Person) .oclIsTypeOf(OclAny))"
by(rule_tac f = "\<lambda>x. (x .oclIsTypeOf(OclAny))" in cpI1, simp_all add: oclistypeof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person)
lemma cp_oclistypeof\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::Person) :: OclAny) .oclIsTypeOf(Person))"
by(rule_tac f = "\<lambda>x. (x .oclIsTypeOf(Person))" in cpI1, simp_all add: oclistypeof\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)
lemma cp_oclistypeof\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Person: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::OclAny) :: Person) .oclIsTypeOf(Person))"
by(rule_tac f = "\<lambda>x. (x .oclIsTypeOf(Person))" in cpI1, simp_all add: oclistypeof\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person)

lemmas [simp] = 
 cp_oclistypeof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_Person
 cp_oclistypeof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_OclAny
 cp_oclistypeof\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Person
 cp_oclistypeof\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_OclAny

 cp_oclistypeof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_OclAny
 cp_oclistypeof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_Person
 cp_oclistypeof\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_OclAny
 cp_oclistypeof\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Person

lemma oclistypeof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_strict1[simp]: 
     "(invalid::OclAny) .oclIsTypeOf(OclAny) = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclistypeof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny)
lemma oclistypeof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_strict2[simp]: 
     "(null::OclAny) .oclIsTypeOf(OclAny) = true"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclistypeof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny)
lemma oclistypeof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_strict1[simp]: 
     "(invalid::Person) .oclIsTypeOf(OclAny) = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclistypeof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person)
lemma oclistypeof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_strict2[simp]: 
     "(null::Person) .oclIsTypeOf(OclAny) = true"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclistypeof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person)
lemma oclistypeof\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_strict1[simp]: 
     "(invalid::OclAny) .oclIsTypeOf(Person) = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclistypeof\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)
lemma oclistypeof\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_strict2[simp]: 
     "(null::OclAny) .oclIsTypeOf(Person) = true"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclistypeof\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)
lemma oclistypeof\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_strict1[simp]: 
     "(invalid::Person) .oclIsTypeOf(Person) = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclistypeof\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person)
lemma oclistypeof\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_strict2[simp]: 
     "(null::Person) .oclIsTypeOf(Person) = true"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclistypeof\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person)



lemma actualType_larger_staticType:
assumes isdef: "\<tau> \<Turnstile> (\<delta> X)"
shows          "\<tau> \<Turnstile> (X::Person) .oclIsTypeOf(OclAny) \<triangleq> false"
using isdef
by(auto simp : bot_fun_def null_fun_def null_option_def bot_option_def null_def invalid_def
                  oclistypeof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person foundation22 foundation16
           split: option.split oclany.split person.split)

lemma down_cast: 
assumes isOclAny: "\<tau> \<Turnstile> (X::OclAny) .oclIsTypeOf(OclAny)"
and     non_null: "\<tau> \<Turnstile> (\<delta> X)"
shows             "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid" 
using isOclAny non_null
apply(auto simp : bot_fun_def null_fun_def null_option_def bot_option_def null_def invalid_def
                  oclastype\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person oclastype\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny foundation22 foundation16 
           split: option.split oclany.split person.split)
by(simp add: oclistypeof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny  OclValid_def false_def true_def)

lemma up_down_cast : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> X)"
shows "\<tau> \<Turnstile> ((X::Person) .oclAsType(OclAny) .oclAsType(Person) \<triangleq> X)" 
using isdef
by(auto simp : null_fun_def null_option_def bot_option_def null_def invalid_def
               oclastype\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person oclastype\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny foundation22 foundation16
        split: option.split person.split)


lemma up_down_cast2 [simp]: 
shows "((X::Person) .oclAsType(OclAny) .oclAsType(Person) = X)" 
 apply(rule ext, rename_tac \<tau>)
 apply(rule foundation22[THEN iffD1])
 apply(case_tac "\<tau> \<Turnstile> (\<delta> X)", simp add: up_down_cast)
 apply(simp add: def_split_local, elim disjE)
 apply(erule StrongEq_L_subst2_rev, simp, simp)+
done

(* MISSING:  Construction for  ocliskind *)

consts ocliskindof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_).oclIsKindOf'(OclAny')")
consts ocliskinfof\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n :: "'\<alpha> \<Rightarrow> Boolean" ("(_).oclIsKindOf'(Person')")

defs (overloaded) ocliskindof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny: 
        "(X::OclAny) .oclIsKindOf(OclAny) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> true \<tau>  
                            | \<lfloor>\<lfloor>mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid \<bottom> \<rfloor>\<rfloor> \<Rightarrow> true \<tau>
                            | \<lfloor>\<lfloor>mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid \<lfloor>_\<rfloor> \<rfloor>\<rfloor> \<Rightarrow> true \<tau>)" 

defs (overloaded) ocliskindof\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person: 
        "(X::Person) .oclIsKindOf(OclAny) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> true \<tau>  
                            | \<lfloor>\<lfloor>mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n e oid _ \<rfloor>\<rfloor> \<Rightarrow> true \<tau>)"  (* must have actual type Person otherwise  *)
(* Unchecked; or better directly on the OCL - level ??? *)

(* stricness, null-ness, cp, reduction-rules. *)


end
