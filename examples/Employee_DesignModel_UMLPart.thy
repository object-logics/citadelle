(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Employee_DesignModel_UMLPart.thy --- OCL Contracts and an Example.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2012-2013 Universite Paris-Sud, France
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

section{* Example Data-Universe and its Infrastructure *}
text{* Should be generated entirely from a class-diagram. *}

(* @{text "'\<AA>"} -- \mathfrak{A} *)
text{* Our data universe  consists in the concrete class diagram just of node's, 
and implicitly of the class object. Each class implies the existence of a class 
type defined for the corresponding object representations as follows: *}

datatype person =  mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n   oid          (* the oid to the person itself *)
                            "int option" (* the attribute "salary" or null *) 
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


(* The following definition gives ``isTypeOf semantics'' for allInstances; however, we want
   ``isTypeOf semantics'', thus we will need an internal object conversion ...
definition Person :: "\<AA> \<Rightarrow> person"
where     "Person \<equiv> (the_inv in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n)"

definition OclAny :: "\<AA> \<Rightarrow> oclany"
where     "OclAny \<equiv> (the_inv in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y)"
*)

fun    Person :: "\<AA> \<Rightarrow> person"
where "Person (in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y(mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid \<lfloor>(a,b)\<rfloor>)) = mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid a b"
    | "Person (in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n(mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid a b)) = mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid a b"

fun    OclAny :: "\<AA> \<Rightarrow> oclany"
where "OclAny (in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y X) = X"
     |"OclAny (in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid a b)) = mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid \<lfloor>(a,b)\<rfloor>"

definition    Person' :: "\<AA> \<Rightarrow> person option"
where "Person' = (\<lambda>x. case x of
      in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y (mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid \<lfloor>(a,b)\<rfloor>) \<Rightarrow> \<lfloor>mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid a b\<rfloor>
    | in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid a b) \<Rightarrow> \<lfloor>mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid a b\<rfloor>
    | _ \<Rightarrow> None)"

definition    OclAny' :: "\<AA> \<Rightarrow> oclany option"
where "OclAny' = (\<lambda>x. case x of
      in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y X \<Rightarrow> \<lfloor>X\<rfloor>
    | in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid a b) \<Rightarrow> \<lfloor>mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid \<lfloor>(a,b)\<rfloor>\<rfloor>)"

lemma oclany_none: "OclAny' x \<noteq> None"
 apply(simp add: OclAny'_def)
 apply(case_tac x, simp_all)
 apply(case_tac person, simp_all)
done

(* PROBLEM: THIS CONSTRUCTION IS NO LONGER injective, thus invertible ...
   Maybe this causes BIG PROBLEMS for our entire construction of allInstances ... bu *)


text{* Having fixed the object universe, we can introduce type synonyms that exactly correspond
to OCL types. Again, we exploit that our representation of OCL is a "shallow embedding" with a
one-to-one correspondance of OCL-types to types of the meta-language HOL. *}
type_synonym Boolean     = " \<AA> Boolean"
type_synonym Integer     = " \<AA> Integer"
type_synonym Void        = " \<AA> Void"
type_synonym OclAny      = "(\<AA>, oclany option option) val"
type_synonym Person      = "(\<AA>, person option option) val"
type_synonym Set_Integer = "(\<AA>, int option option) Set"
type_synonym Set_Person  = "(\<AA>, person option option) Set"

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

defs(overloaded)   StrictRefEq\<^isub>g\<^isub>e\<^isub>n_\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n   : "(x::Person) \<doteq> y  \<equiv> StrictRefEq\<^isub>g\<^isub>e\<^isub>n x y"
defs(overloaded)   StrictRefEq\<^isub>g\<^isub>e\<^isub>n_\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y   : "(x::OclAny) \<doteq> y  \<equiv> StrictRefEq\<^isub>g\<^isub>e\<^isub>n x y"

lemmas StrictRefEq\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n =
    cp_StrictRefEq\<^isub>g\<^isub>e\<^isub>n[of "x::Person" "y::Person" "\<tau>", 
                         simplified StrictRefEq\<^isub>g\<^isub>e\<^isub>n_\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n[symmetric]]
    cp_intro(9)         [of "P::Person \<Rightarrow>Person""Q::Person \<Rightarrow>Person",
                         simplified StrictRefEq\<^isub>g\<^isub>e\<^isub>n_\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n[symmetric] ]
    StrictRefEq\<^isub>g\<^isub>e\<^isub>n_def      [of "x::Person" "y::Person", 
                         simplified StrictRefEq\<^isub>g\<^isub>e\<^isub>n_\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n[symmetric]]
    StrictRefEq\<^isub>g\<^isub>e\<^isub>n_defargs  [of _ "x::Person" "y::Person", 
                         simplified StrictRefEq\<^isub>g\<^isub>e\<^isub>n_\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n[symmetric]]
    StrictRefEq\<^isub>g\<^isub>e\<^isub>n_strict1 
                        [of "x::Person",
                         simplified StrictRefEq\<^isub>g\<^isub>e\<^isub>n_\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n[symmetric]]
    StrictRefEq\<^isub>g\<^isub>e\<^isub>n_strict2 
                        [of "x::Person",
                         simplified StrictRefEq\<^isub>g\<^isub>e\<^isub>n_\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n[symmetric]]

thm StrictRefEq\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n
(* TODO: Analogue for object. *)

section{* OclAllInstances *}

(* IS THIS WHAT WE WANT ? THIS DEFINITION FILTERS OBJECTS THAT ARE BOOKED UNDER
THEIR APPARENT (STATIC) TYPE INTO THE CONTEXT, NOT BY THEIR ACTUAL (DYNAMIC) TYPE. *)
lemma "Person .allInstances() =
             (\<lambda>\<tau>.  Abs_Set_0 \<lfloor>\<lfloor>(Some \<circ> Some \<circ> Person_sumC)`(ran(heap(snd \<tau>))) \<rfloor>\<rfloor>) "
by(rule ext, simp add:OclAllInstances_def Person_def)

lemma "OclAllInstances' Person' =
             (\<lambda>\<tau>.  Abs_Set_0  \<lfloor>\<lfloor>Some ` (Person' ` ran (heap (snd \<tau>)) - {None})\<rfloor>\<rfloor>) "
by(rule ext, simp add:OclAllInstances'_def)

lemma "Person .allInstances@pre() = 
             (\<lambda>\<tau>.  Abs_Set_0 \<lfloor>\<lfloor>(Some \<circ> Some \<circ> Person_sumC)`(ran(heap(fst \<tau>))) \<rfloor>\<rfloor>) "
by(rule ext, simp add:OclAllInstances_at_pre_def Person_def)

lemma "OclAny .allInstances() =
             (\<lambda>\<tau>.  Abs_Set_0 \<lfloor>\<lfloor>(Some \<circ> Some \<circ> OclAny_sumC)`(ran(heap(snd \<tau>))) \<rfloor>\<rfloor>) "
by(rule ext, simp add:OclAllInstances_def OclAny_def)

lemma "OclAllInstances' OclAny' =
             (\<lambda>\<tau>.  Abs_Set_0  \<lfloor>\<lfloor> Some ` OclAny' ` ran (heap (snd \<tau>)) \<rfloor>\<rfloor>) "
 apply(rule ext, simp add: OclAllInstances'_def)
 apply(subgoal_tac " (OclAny' ` ran (heap (snd \<tau>)) - {None}) = (OclAny' ` ran (heap (snd \<tau>)))", simp)
 apply(simp add: image_def)
 apply(rule equalityI)
 apply(rule subsetI)
 apply (metis (lifting) Diff_iff)
 apply(rule subsetI)
 apply(simp)
 apply(drule bexE) prefer 2 apply assumption
 apply(case_tac x, metis oclany_none)
 apply(blast)
done

lemma "OclAny .allInstances@pre() = 
             (\<lambda>\<tau>.  Abs_Set_0 \<lfloor>\<lfloor>(Some \<circ> Some \<circ> OclAny_sumC)`(ran(heap(fst \<tau>))) \<rfloor>\<rfloor>) "
by(rule ext, simp add:OclAllInstances_at_pre_def OclAny_def)


text{* For each Class \emph{C}, we will have a casting operation \verb+.oclAsType(+\emph{C}\verb+)+,
   a test on the actual type \verb+.oclIsTypeOf(+\emph{C}\verb+)+ as well as its relaxed form
   \verb+.oclIsKindOf(+\emph{C}\verb+)+ (corresponding exactly to Java's \verb+instanceof+-operator. 
*}
text{* Thus, since we have two class-types in our concrete class hierarchy, we have
two operations to declare and to provide two overloading definitions for the two static types.
*}


section{* OclAsType *}
subsection{* Definition *}

consts OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y :: "'\<alpha> \<Rightarrow> OclAny" ("(_) .oclAsType'(OclAny')")
consts OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n :: "'\<alpha> \<Rightarrow> Person" ("(_) .oclAsType'(Person')")

defs (overloaded) OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny: 
        "(X::OclAny) .oclAsType(OclAny) \<equiv> X" 

defs (overloaded) OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person:  
        "(X::Person) .oclAsType(OclAny) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> null \<tau>    
                            | \<lfloor>\<lfloor>mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid a b \<rfloor>\<rfloor> \<Rightarrow>  \<lfloor>\<lfloor>  (mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid \<lfloor>(a,b)\<rfloor>) \<rfloor>\<rfloor>)"

defs (overloaded) OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny: 
        "(X::OclAny) .oclAsType(Person) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> null \<tau>   
                            | \<lfloor>\<lfloor>mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid \<bottom> \<rfloor>\<rfloor> \<Rightarrow>  invalid \<tau>   (* down-cast exception *)
                            | \<lfloor>\<lfloor>mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid \<lfloor>(a,b)\<rfloor> \<rfloor>\<rfloor> \<Rightarrow>  \<lfloor>\<lfloor>mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid a b \<rfloor>\<rfloor>)" 

defs (overloaded) OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person: 
        "(X::Person) .oclAsType(Person) \<equiv> X "  (* to avoid identity for null ? *)


lemmas [simp] =
 OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny
 OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person

subsection{* Context Passing *}

lemma cp_OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_Person: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::Person) :: Person) .oclAsType(OclAny))"
by(rule cpI1, simp_all add: OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person)
lemma cp_OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::OclAny) :: OclAny) .oclAsType(OclAny))"
by(rule cpI1, simp_all add: OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny)
lemma cp_OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Person: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::Person) :: Person) .oclAsType(Person))"
by(rule cpI1, simp_all add: OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person)
lemma cp_OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::OclAny) :: OclAny) .oclAsType(Person))"
by(rule cpI1, simp_all add: OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)

lemma cp_OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::Person) :: OclAny) .oclAsType(OclAny))"
by(rule cpI1, simp_all add: OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny)
lemma cp_OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_Person: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::OclAny) :: Person) .oclAsType(OclAny))"
by(rule cpI1, simp_all add: OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person)
lemma cp_OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::Person) :: OclAny) .oclAsType(Person))"
by(rule cpI1, simp_all add: OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)
lemma cp_OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Person: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::OclAny) :: Person) .oclAsType(Person))"
by(rule cpI1, simp_all add: OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person)

lemmas [simp] = 
 cp_OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_Person
 cp_OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_OclAny
 cp_OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Person
 cp_OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_OclAny

 cp_OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_OclAny
 cp_OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_Person
 cp_OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_OclAny
 cp_OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Person

subsection{* Execution with invalid or null as argument *}

lemma OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_strict : "(invalid::OclAny) .oclAsType(OclAny) = invalid" 
by(simp)

lemma OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_nullstrict : "(null::OclAny) .oclAsType(OclAny) = null" 
by(simp)

lemma OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_strict[simp] : "(invalid::Person) .oclAsType(OclAny) = invalid" 
by(rule ext, simp add: bot_option_def invalid_def
                       OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person)

lemma OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_nullstrict[simp] : "(null::Person) .oclAsType(OclAny) = null" 
by(rule ext, simp add: null_fun_def null_option_def bot_option_def
                       OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person)

lemma OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_strict[simp] : "(invalid::OclAny) .oclAsType(Person) = invalid" 
by(rule ext, simp add: bot_option_def invalid_def
                       OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)

lemma OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_nullstrict[simp] : "(null::OclAny) .oclAsType(Person) = null" 
by(rule ext, simp add: null_fun_def null_option_def bot_option_def
                       OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)

lemma OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_strict : "(invalid::Person) .oclAsType(Person) = invalid" 
by(simp)
lemma OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_nullstrict : "(null::Person) .oclAsType(Person) = null" 
by(simp)

section{* OclIsTypeOf *}
subsection{* Definition *}

consts OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_).oclIsTypeOf'(OclAny')")
consts OclIsTypeOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n :: "'\<alpha> \<Rightarrow> Boolean" ("(_).oclIsTypeOf'(Person')")

defs (overloaded) OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny: 
        "(X::OclAny) .oclIsTypeOf(OclAny) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> true \<tau>  (* invalid ?? *)
                            | \<lfloor>\<lfloor>mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid \<bottom> \<rfloor>\<rfloor> \<Rightarrow> true \<tau>
                            | \<lfloor>\<lfloor>mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid \<lfloor>_\<rfloor> \<rfloor>\<rfloor> \<Rightarrow> false \<tau>)" 


defs (overloaded) OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person: 
        "(X::Person) .oclIsTypeOf(OclAny) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> true \<tau>    (* invalid ?? *)
                            | \<lfloor>\<lfloor> _ \<rfloor>\<rfloor> \<Rightarrow> false \<tau>)"  (* must have actual type Person otherwise  *)

defs (overloaded) OclIsTypeOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny: 
        "(X::OclAny) .oclIsTypeOf(Person) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> true \<tau>  
                            | \<lfloor>\<lfloor>mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid \<bottom> \<rfloor>\<rfloor> \<Rightarrow> false \<tau>
                            | \<lfloor>\<lfloor>mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid \<lfloor>_\<rfloor> \<rfloor>\<rfloor> \<Rightarrow> true \<tau>)" 

defs (overloaded) OclIsTypeOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person: 
        "(X::Person) .oclIsTypeOf(Person) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom> \<Rightarrow> invalid \<tau>
                            | _ \<Rightarrow> true \<tau>)" (* for (* \<lfloor>\<lfloor> _ \<rfloor>\<rfloor> \<Rightarrow> true \<tau> *) : must have actual type Node otherwise  *)

subsection{* Context Passing *}

lemma cp_OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_Person: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::Person) :: Person) .oclIsTypeOf(OclAny))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person)
lemma cp_OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::OclAny) :: OclAny) .oclIsTypeOf(OclAny))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny)
lemma cp_OclIsTypeOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Person: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::Person) :: Person) .oclIsTypeOf(Person))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person)
lemma cp_OclIsTypeOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::OclAny) :: OclAny) .oclIsTypeOf(Person))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)


lemma cp_OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::Person) :: OclAny) .oclIsTypeOf(OclAny))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny)
lemma cp_OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_Person: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::OclAny) :: Person) .oclIsTypeOf(OclAny))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person)
lemma cp_OclIsTypeOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::Person) :: OclAny) .oclIsTypeOf(Person))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)
lemma cp_OclIsTypeOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Person: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::OclAny) :: Person) .oclIsTypeOf(Person))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person)

lemmas [simp] = 
 cp_OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_Person
 cp_OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_OclAny
 cp_OclIsTypeOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Person
 cp_OclIsTypeOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_OclAny

 cp_OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_OclAny
 cp_OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_Person
 cp_OclIsTypeOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_OclAny
 cp_OclIsTypeOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Person

subsection{* Execution with invalid or null as argument *}

lemma OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_strict1[simp]: 
     "(invalid::OclAny) .oclIsTypeOf(OclAny) = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny)
lemma OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_strict2[simp]: 
     "(null::OclAny) .oclIsTypeOf(OclAny) = true"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny)
lemma OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_strict1[simp]: 
     "(invalid::Person) .oclIsTypeOf(OclAny) = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person)
lemma OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_strict2[simp]: 
     "(null::Person) .oclIsTypeOf(OclAny) = true"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person)
lemma OclIsTypeOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_strict1[simp]: 
     "(invalid::OclAny) .oclIsTypeOf(Person) = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       OclIsTypeOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)
lemma OclIsTypeOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_strict2[simp]: 
     "(null::OclAny) .oclIsTypeOf(Person) = true"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       OclIsTypeOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)
lemma OclIsTypeOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_strict1[simp]: 
     "(invalid::Person) .oclIsTypeOf(Person) = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       OclIsTypeOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person)
lemma OclIsTypeOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_strict2[simp]: 
     "(null::Person) .oclIsTypeOf(Person) = true"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       OclIsTypeOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person)

subsection{* up down cast *}

lemma actualType_larger_staticType:
assumes isdef: "\<tau> \<Turnstile> (\<delta> X)"
shows          "\<tau> \<Turnstile> (X::Person) .oclIsTypeOf(OclAny) \<triangleq> false"
using isdef
by(auto simp : null_option_def bot_option_def
               OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person foundation22 foundation16)

lemma down_cast_type: 
assumes isOclAny: "\<tau> \<Turnstile> (X::OclAny) .oclIsTypeOf(OclAny)"
and     non_null: "\<tau> \<Turnstile> (\<delta> X)"
shows             "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid" 
using isOclAny non_null
apply(auto simp : bot_fun_def null_fun_def null_option_def bot_option_def null_def invalid_def
                  OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny foundation22 foundation16 
           split: option.split oclany.split person.split)
by(simp add: OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny  OclValid_def false_def true_def)

lemma up_down_cast : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> X)"
shows "\<tau> \<Turnstile> ((X::Person) .oclAsType(OclAny) .oclAsType(Person) \<triangleq> X)" 
using isdef
by(auto simp : null_fun_def null_option_def bot_option_def null_def invalid_def
               OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny foundation22 foundation16
        split: option.split person.split)


lemma up_down_cast_Person_OclAny_Person [simp]: 
shows "((X::Person) .oclAsType(OclAny) .oclAsType(Person) = X)" 
 apply(rule ext, rename_tac \<tau>)
 apply(rule foundation22[THEN iffD1])
 apply(case_tac "\<tau> \<Turnstile> (\<delta> X)", simp add: up_down_cast)
 apply(simp add: def_split_local, elim disjE)
 apply(erule StrongEq_L_subst2_rev, simp, simp)+
done

lemma up_down_cast_Person_OclAny_Person': assumes "\<tau> \<Turnstile> \<upsilon> X"
shows "\<tau> \<Turnstile> (((X :: Person) .oclAsType(OclAny) .oclAsType(Person)) \<doteq> X)"
 apply(simp only: up_down_cast_Person_OclAny_Person StrictRefEq\<^isub>g\<^isub>e\<^isub>n_\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n)
by(rule StrictRefEq\<^isub>g\<^isub>e\<^isub>n_sym, simp add: assms)


section{* OclIsKindOf *}
subsection{* Definition *}

consts OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_).oclIsKindOf'(OclAny')")
consts OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n :: "'\<alpha> \<Rightarrow> Boolean" ("(_).oclIsKindOf'(Person')")

defs (overloaded) OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny: 
        "(X::OclAny) .oclIsKindOf(OclAny) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom> \<Rightarrow> invalid \<tau>
                            | _ \<Rightarrow> true \<tau>)" 

defs (overloaded) OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person: 
        "(X::Person) .oclIsKindOf(OclAny) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom> \<Rightarrow> invalid \<tau>
                            | _\<Rightarrow> true \<tau>)"  
(* for (* \<lfloor>\<lfloor>mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n e oid _ \<rfloor>\<rfloor> \<Rightarrow> true \<tau> *) :  must have actual type Person otherwise  *)
(* Unchecked; or better directly on the OCL - level ??? *)

defs (overloaded) OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny: 
        "(X::OclAny) .oclIsKindOf(Person) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> true \<tau>  
                            | \<lfloor>\<lfloor>mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid \<bottom> \<rfloor>\<rfloor> \<Rightarrow> false \<tau>
                            | \<lfloor>\<lfloor>mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid \<lfloor>_\<rfloor> \<rfloor>\<rfloor> \<Rightarrow> true \<tau>)" 

defs (overloaded) OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person: 
        "(X::Person) .oclIsKindOf(Person) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom> \<Rightarrow> invalid \<tau>
                            | _ \<Rightarrow> true \<tau>)"

subsection{* Context Passing *}

lemma cp_OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_Person: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::Person) :: Person) .oclIsKindOf(OclAny))"
by(rule cpI1, simp_all add: OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person)
lemma cp_OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::OclAny) :: OclAny) .oclIsKindOf(OclAny))"
by(rule cpI1, simp_all add: OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny)
lemma cp_OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Person: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::Person) :: Person) .oclIsKindOf(Person))"
by(rule cpI1, simp_all add: OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person)
lemma cp_OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::OclAny) :: OclAny) .oclIsKindOf(Person))"
by(rule cpI1, simp_all add: OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)

lemma cp_OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::Person) :: OclAny) .oclIsKindOf(OclAny))"
by(rule cpI1, simp_all add: OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny)
lemma cp_OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_Person: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::OclAny) :: Person) .oclIsKindOf(OclAny))"
by(rule cpI1, simp_all add: OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person)
lemma cp_OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::Person) :: OclAny) .oclIsKindOf(Person))"
by(rule cpI1, simp_all add: OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)
lemma cp_OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Person: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::OclAny) :: Person) .oclIsKindOf(Person))"
by(rule cpI1, simp_all add: OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person)

lemmas [simp] = 
 cp_OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_Person
 cp_OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_OclAny
 cp_OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Person
 cp_OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_OclAny

 cp_OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_OclAny
 cp_OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_Person
 cp_OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_OclAny
 cp_OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Person

subsection{* Execution with invalid or null as argument *}

lemma OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_strict1[simp] : "(invalid::OclAny) .oclIsKindOf(OclAny) = invalid" 
by(rule ext, simp add: invalid_def bot_option_def
                       OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny)

lemma OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny_strict2[simp] : "(null::OclAny) .oclIsKindOf(OclAny) = true" 
by(rule ext, simp add: null_fun_def null_option_def
                       OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny)

lemma OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_strict1[simp] : "(invalid::Person) .oclIsKindOf(OclAny) = invalid" 
by(rule ext, simp add: bot_option_def invalid_def
                       OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person)

lemma OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person_strict2[simp] : "(null::Person) .oclIsKindOf(OclAny) = true" 
by(rule ext, simp add: null_fun_def null_option_def bot_option_def
                       OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person)

lemma OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_strict1[simp]: "(invalid::OclAny) .oclIsKindOf(Person) = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)

lemma OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_strict2[simp]: "(null::OclAny) .oclIsKindOf(Person) = true"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)

lemma OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_strict1[simp]: "(invalid::Person) .oclIsKindOf(Person) = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person)

lemma OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_strict2[simp]: "(null::Person) .oclIsKindOf(Person) = true"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person)

subsection{* up down cast *}

lemma actualKind_larger_staticKind:
assumes isdef: "\<tau> \<Turnstile> (\<delta> X)"
shows          "\<tau> \<Turnstile> (X::Person) .oclIsKindOf(OclAny) \<triangleq> true"
using isdef
by(auto simp : bot_option_def
               OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person foundation22 foundation16)

lemma down_cast_kind: 
assumes isOclAny: "\<not> \<tau> \<Turnstile> (X::OclAny) .oclIsKindOf(Person)"
and     non_null: "\<tau> \<Turnstile> (\<delta> X)"
shows             "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid" 
using isOclAny non_null
apply(auto simp : bot_fun_def null_fun_def null_option_def bot_option_def null_def invalid_def
                  OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny foundation22 foundation16 
           split: option.split oclany.split person.split)
by(simp add: OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny  OclValid_def false_def true_def)


section{* dot boss, dot salary *}
subsection{* Definition *}
text{* Should be generated entirely from a class-diagram. *}

definition "eval_extract X f = (\<lambda> \<tau>. case X \<tau> of
                                    \<bottom> \<Rightarrow> invalid \<tau>   (* exception propagation *)
                               | \<lfloor>  \<bottom> \<rfloor> \<Rightarrow> invalid \<tau> (* dereferencing null pointer *)
                               | \<lfloor>\<lfloor> obj \<rfloor>\<rfloor> \<Rightarrow> f (oid_of obj) \<tau>)"

(*
definition "OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_\<AA> u = (case u of in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n p \<Rightarrow>  p 
                                          | in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y (mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid \<lfloor>(a,b)\<rfloor>) \<Rightarrow> (mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid a b))" *)
(*
definition "deref\<^isub>o\<^isub>i\<^isub>d fst_snd f oid = (\<lambda>\<tau>. case (heap (fst_snd \<tau>)) oid of
                       \<lfloor> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n obj \<rfloor> \<Rightarrow> f obj \<tau>
                     | \<lfloor> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y obj \<rfloor> \<Rightarrow> f obj \<tau>
                     | _       \<Rightarrow> invalid \<tau>)" *)

definition "deref\<^isub>o\<^isub>i\<^isub>d_\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n fst_snd f oid = (\<lambda>\<tau>. case (heap (fst_snd \<tau>)) oid of
                       \<lfloor> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n obj \<rfloor> \<Rightarrow> f obj \<tau>
                     | _       \<Rightarrow> invalid \<tau>)"

definition "deref\<^isub>o\<^isub>i\<^isub>d_\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y fst_snd f oid = (\<lambda>\<tau>. case (heap (fst_snd \<tau>)) oid of
                       \<lfloor> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y obj \<rfloor> \<Rightarrow> f obj \<tau>
                     | _       \<Rightarrow> invalid \<tau>)"

text{* pointer undefined in state or not referencing a type conform object representation *}


definition "select\<^isub>a\<^isub>n\<^isub>y f = (\<lambda> X. case X of 
                     (mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y _ \<bottom>) \<Rightarrow> null
                   | (mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y _ \<lfloor>any\<rfloor>) \<Rightarrow> f (\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>) any)"


definition "select\<^isub>b\<^isub>o\<^isub>s\<^isub>s f = (\<lambda> X. case X of 
                     (mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n _ _ \<bottom>) \<Rightarrow> null  (* object contains null pointer *)
                   | (mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n _ _ \<lfloor>boss\<rfloor>) \<Rightarrow> f (\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>) boss)"


definition "select\<^isub>s\<^isub>a\<^isub>l\<^isub>a\<^isub>r\<^isub>y f = (\<lambda> X. case X of
                     (mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n _ \<bottom> _) \<Rightarrow> null
                   | (mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n _ \<lfloor>salary\<rfloor> _) \<Rightarrow> f (\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>) salary)" 


definition "in_pre_state = fst"
definition "in_post_state = snd"

definition "reconst_basetype = (\<lambda> convert x. convert x)"

fun dot\<^isub>a\<^isub>n\<^isub>y :: "OclAny \<Rightarrow> _"  ("(1(_).any)" 50)
  where "(X).any = eval_extract X 
                       (deref\<^isub>o\<^isub>i\<^isub>d_\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y in_post_state 
                          (select\<^isub>a\<^isub>n\<^isub>y 
                             reconst_basetype))"

fun dot\<^isub>b\<^isub>o\<^isub>s\<^isub>s :: "Person \<Rightarrow> Person"  ("(1(_).boss)" 50)
  where "(X).boss = eval_extract X 
                      (deref\<^isub>o\<^isub>i\<^isub>d_\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n in_post_state 
                         (select\<^isub>b\<^isub>o\<^isub>s\<^isub>s 
                            (deref\<^isub>o\<^isub>i\<^isub>d_\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n in_post_state)))"

fun dot\<^isub>s\<^isub>a\<^isub>l\<^isub>a\<^isub>r\<^isub>y :: "Person \<Rightarrow> Integer"  ("(1(_).salary)" 50)
  where "(X).salary = eval_extract X 
                       (deref\<^isub>o\<^isub>i\<^isub>d_\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n in_post_state 
                          (select\<^isub>s\<^isub>a\<^isub>l\<^isub>a\<^isub>r\<^isub>y 
                             reconst_basetype))"

fun dot\<^isub>a\<^isub>n\<^isub>y_at_pre :: "OclAny \<Rightarrow> _"  ("(1(_).any@pre)" 50)
  where "(X).any@pre = eval_extract X 
                       (deref\<^isub>o\<^isub>i\<^isub>d_\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y in_pre_state 
                          (select\<^isub>a\<^isub>n\<^isub>y 
                             reconst_basetype))"

fun dot\<^isub>b\<^isub>o\<^isub>s\<^isub>s_at_pre:: "Person \<Rightarrow> Person"  ("(1(_).boss@pre)" 50)
  where "(X).boss@pre = eval_extract X 
                         (deref\<^isub>o\<^isub>i\<^isub>d_\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n in_pre_state 
                            (select\<^isub>b\<^isub>o\<^isub>s\<^isub>s 
                               (deref\<^isub>o\<^isub>i\<^isub>d_\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n in_pre_state)))"
  (* | \<lfloor>\<lfloor> mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n _ _ \<bottom> \<rfloor>\<rfloor> \<Rightarrow> null (* object contains null pointer. REALLY ? 
                                     And if this pointer was defined in the pre-state ?*) *)

fun dot\<^isub>s\<^isub>a\<^isub>l\<^isub>a\<^isub>r\<^isub>y_at_pre:: "Person \<Rightarrow> Integer"  ("(1(_).salary@pre)" 50)
  where "(X).salary@pre = eval_extract X 
                            (deref\<^isub>o\<^isub>i\<^isub>d_\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n in_pre_state 
                               (select\<^isub>s\<^isub>a\<^isub>l\<^isub>a\<^isub>r\<^isub>y 
                                   reconst_basetype))"

subsection{* Context Passing *}

lemma cp_dot\<^isub>a\<^isub>n\<^isub>y: "((X).any) \<tau> = ((\<lambda>_. X \<tau>).any) \<tau>" by(simp add: eval_extract_def)
lemma cp_dot\<^isub>b\<^isub>o\<^isub>s\<^isub>s: "((X).boss) \<tau> = ((\<lambda>_. X \<tau>).boss) \<tau>" by(simp add: eval_extract_def)
lemma cp_dot\<^isub>s\<^isub>a\<^isub>l\<^isub>a\<^isub>r\<^isub>y: "((X).salary) \<tau> = ((\<lambda>_. X \<tau>).salary) \<tau>" by(simp add: eval_extract_def)

lemma cp_dot\<^isub>a\<^isub>n\<^isub>y_at_pre: "((X).any@pre) \<tau> = ((\<lambda>_. X \<tau>).any@pre) \<tau>" by(simp add: eval_extract_def)
lemma cp_dot\<^isub>b\<^isub>o\<^isub>s\<^isub>s_at_pre: "((X).boss@pre) \<tau> = ((\<lambda>_. X \<tau>).boss@pre) \<tau>" by(simp add: eval_extract_def)
lemma cp_dot\<^isub>s\<^isub>a\<^isub>l\<^isub>a\<^isub>r\<^isub>y_at_pre: "((X).salary@pre) \<tau> = ((\<lambda>_. X \<tau>).salary@pre) \<tau>" by(simp add: eval_extract_def)

lemmas cp_dot\<^isub>a\<^isub>n\<^isub>y_I [simp, intro!]= 
       cp_dot\<^isub>a\<^isub>n\<^isub>y[THEN allI[THEN allI], 
                          of "\<lambda> X _. X" "\<lambda> _ \<tau>. \<tau>", THEN cpI1]
lemmas cp_dot\<^isub>a\<^isub>n\<^isub>y_at_pre_I [simp, intro!]= 
       cp_dot\<^isub>a\<^isub>n\<^isub>y_at_pre[THEN allI[THEN allI],  
                          of "\<lambda> X _. X" "\<lambda> _ \<tau>. \<tau>", THEN cpI1]

lemmas cp_dot\<^isub>b\<^isub>o\<^isub>s\<^isub>s_I [simp, intro!]= 
       cp_dot\<^isub>b\<^isub>o\<^isub>s\<^isub>s[THEN allI[THEN allI], 
                          of "\<lambda> X _. X" "\<lambda> _ \<tau>. \<tau>", THEN cpI1]
lemmas cp_dot\<^isub>b\<^isub>o\<^isub>s\<^isub>s_at_pre_I [simp, intro!]= 
       cp_dot\<^isub>b\<^isub>o\<^isub>s\<^isub>s_at_pre[THEN allI[THEN allI],  
                          of "\<lambda> X _. X" "\<lambda> _ \<tau>. \<tau>", THEN cpI1]

lemmas cp_dot\<^isub>s\<^isub>a\<^isub>l\<^isub>a\<^isub>r\<^isub>y_I [simp, intro!]= 
       cp_dot\<^isub>s\<^isub>a\<^isub>l\<^isub>a\<^isub>r\<^isub>y[THEN allI[THEN allI], 
                          of "\<lambda> X _. X" "\<lambda> _ \<tau>. \<tau>", THEN cpI1]
lemmas cp_dot\<^isub>s\<^isub>a\<^isub>l\<^isub>a\<^isub>r\<^isub>y_at_pre_I [simp, intro!]= 
       cp_dot\<^isub>s\<^isub>a\<^isub>l\<^isub>a\<^isub>r\<^isub>y_at_pre[THEN allI[THEN allI],  
                          of "\<lambda> X _. X" "\<lambda> _ \<tau>. \<tau>", THEN cpI1]

subsection{* Execution with invalid or null as argument *}

lemma dot\<^isub>a\<^isub>n\<^isub>y_nullstrict [simp]: "(null).any = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def eval_extract_def)
lemma dot\<^isub>a\<^isub>n\<^isub>y_at_pre_nullstrict [simp] : "(null).any@pre = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def eval_extract_def)
lemma dot\<^isub>a\<^isub>n\<^isub>y_strict [simp] : "(invalid).any = invalid" 
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def eval_extract_def)
lemma dot\<^isub>a\<^isub>n\<^isub>y_at_pre_strict [simp] : "(invalid).any@pre = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def eval_extract_def)


lemma dot\<^isub>b\<^isub>o\<^isub>s\<^isub>s_nullstrict [simp]: "(null).boss = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def eval_extract_def)
lemma dot\<^isub>b\<^isub>o\<^isub>s\<^isub>s_at_pre_nullstrict [simp] : "(null).boss@pre = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def eval_extract_def)
lemma dot\<^isub>b\<^isub>o\<^isub>s\<^isub>s_strict [simp] : "(invalid).boss = invalid" 
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def eval_extract_def)
lemma dot\<^isub>b\<^isub>o\<^isub>s\<^isub>s_at_pre_strict [simp] : "(invalid).boss@pre = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def eval_extract_def)


lemma dot\<^isub>s\<^isub>a\<^isub>l\<^isub>a\<^isub>r\<^isub>y_nullstrict [simp]: "(null).salary = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def eval_extract_def)
lemma dot\<^isub>s\<^isub>a\<^isub>l\<^isub>a\<^isub>r\<^isub>y_at_pre_nullstrict [simp] : "(null).salary@pre = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def eval_extract_def)
lemma dot\<^isub>s\<^isub>a\<^isub>l\<^isub>a\<^isub>r\<^isub>y_strict [simp] : "(invalid).salary = invalid" 
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def eval_extract_def)
lemma dot\<^isub>s\<^isub>a\<^isub>l\<^isub>a\<^isub>r\<^isub>y_at_pre_strict [simp] : "(invalid).salary@pre = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def eval_extract_def)


section{* A little infra-structure on example states.*}

definition OclInt1000 ("\<one>\<zero>\<zero>\<zero>") where "OclInt1000 = (\<lambda> _ . \<lfloor>\<lfloor>1000\<rfloor>\<rfloor>)"
definition OclInt1200 ("\<one>\<two>\<zero>\<zero>") where "OclInt1200 = (\<lambda> _ . \<lfloor>\<lfloor>1200\<rfloor>\<rfloor>)"
definition OclInt1300 ("\<one>\<three>\<zero>\<zero>") where "OclInt1300 = (\<lambda> _ . \<lfloor>\<lfloor>1300\<rfloor>\<rfloor>)"
definition OclInt1800 ("\<one>\<eight>\<zero>\<zero>") where "OclInt1800 = (\<lambda> _ . \<lfloor>\<lfloor>1800\<rfloor>\<rfloor>)"
definition OclInt2600 ("\<two>\<six>\<zero>\<zero>") where "OclInt2600 = (\<lambda> _ . \<lfloor>\<lfloor>2600\<rfloor>\<rfloor>)"
definition OclInt2900 ("\<two>\<nine>\<zero>\<zero>") where "OclInt2900 = (\<lambda> _ . \<lfloor>\<lfloor>2900\<rfloor>\<rfloor>)"
definition OclInt3200 ("\<three>\<two>\<zero>\<zero>") where "OclInt3200 = (\<lambda> _ . \<lfloor>\<lfloor>3200\<rfloor>\<rfloor>)"
definition OclInt3500 ("\<three>\<five>\<zero>\<zero>") where "OclInt3500 = (\<lambda> _ . \<lfloor>\<lfloor>3500\<rfloor>\<rfloor>)"

definition "oid\<^isub>1 \<equiv> 0"
definition "oid\<^isub>2 \<equiv> 1"
definition "oid\<^isub>3 \<equiv> 2"
definition "oid\<^isub>4 \<equiv> 3"
definition "oid\<^isub>5 \<equiv> 4"
definition "oid\<^isub>6 \<equiv> 5"
definition "oid\<^isub>7 \<equiv> 6"
definition "oid\<^isub>8 \<equiv> 7"

definition "person1 \<equiv> mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid\<^isub>1 \<lfloor>1300\<rfloor> \<lfloor>oid\<^isub>2\<rfloor>"
definition "person2 \<equiv> mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid\<^isub>2 \<lfloor>1800\<rfloor> \<lfloor>oid\<^isub>2\<rfloor>"
definition "person3 \<equiv> mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid\<^isub>3 None None"
definition "person4 \<equiv> mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid\<^isub>4 \<lfloor>2900\<rfloor> None"
definition "person5 \<equiv> mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid\<^isub>5 \<lfloor>3500\<rfloor> None"
definition "person6 \<equiv> mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid\<^isub>6 \<lfloor>2500\<rfloor> \<lfloor>oid\<^isub>7\<rfloor>"
definition "person7 \<equiv> mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid\<^isub>7 \<lfloor>(\<lfloor>3200\<rfloor>, \<lfloor>oid\<^isub>7\<rfloor>)\<rfloor>"
definition "person8 \<equiv> mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y oid\<^isub>8 None"

definition 
      "\<sigma>\<^isub>1  \<equiv> \<lparr> heap = empty(oid\<^isub>1 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n(mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid\<^isub>1 \<lfloor>1000\<rfloor> \<lfloor>oid\<^isub>2\<rfloor>))
                           (oid\<^isub>2 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n(mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid\<^isub>2 \<lfloor>1200\<rfloor>  None))
                          (*oid\<^isub>3*)
                           (oid\<^isub>4 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n(mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid\<^isub>4 \<lfloor>2600\<rfloor> \<lfloor>oid\<^isub>5\<rfloor>))
                           (oid\<^isub>5 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person5)
                           (oid\<^isub>6 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n(mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid\<^isub>6 \<lfloor>2300\<rfloor> \<lfloor>oid\<^isub>4\<rfloor>))
                          (*oid\<^isub>7*)
                          (*oid\<^isub>8*),
               assocs = empty\<rparr>"

definition 
      "\<sigma>\<^isub>1' \<equiv> \<lparr> heap = empty(oid\<^isub>1 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person1)
                           (oid\<^isub>2 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person2)
                           (oid\<^isub>3 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person3)
                           (oid\<^isub>4 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person4)
                          (*oid\<^isub>5*)
                           (oid\<^isub>6 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person6)
                           (oid\<^isub>7 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person7)
                           (oid\<^isub>8 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8),
               assocs = empty\<rparr>"

lemma basic_\<tau>_wff: "WFF(\<sigma>\<^isub>1,\<sigma>\<^isub>1')"
by(auto simp: WFF_def \<sigma>\<^isub>1_def \<sigma>\<^isub>1'_def
              oid\<^isub>1_def oid\<^isub>2_def oid\<^isub>3_def oid\<^isub>4_def oid\<^isub>5_def oid\<^isub>6_def oid\<^isub>7_def oid\<^isub>8_def
              oid_of_\<AA>_def oid_of_person_def oid_of_oclany_def
              person1_def person2_def person3_def person4_def person5_def person6_def person7_def person8_def)

lemma [simp,code_unfold]: "dom (heap \<sigma>\<^isub>1) = {oid\<^isub>1,oid\<^isub>2,(*,oid\<^isub>3*)oid\<^isub>4,oid\<^isub>5,oid\<^isub>6(*,oid\<^isub>7,oid\<^isub>8*)}"
by(auto simp: \<sigma>\<^isub>1_def)

lemma [code_unfold]: "dom (heap \<sigma>\<^isub>1') = {oid\<^isub>1,oid\<^isub>2,oid\<^isub>3,oid\<^isub>4,(*,oid\<^isub>5*)oid\<^isub>6,oid\<^isub>7,oid\<^isub>8}"
by(auto simp: \<sigma>\<^isub>1'_def)

definition "X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 :: Person \<equiv> \<lambda> _ .\<lfloor>\<lfloor> person1 \<rfloor>\<rfloor>"
definition "X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 :: Person \<equiv> \<lambda> _ .\<lfloor>\<lfloor> person2 \<rfloor>\<rfloor>"
definition "X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n3 :: Person \<equiv> \<lambda> _ .\<lfloor>\<lfloor> person3 \<rfloor>\<rfloor>"
definition "X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n4 :: Person \<equiv> \<lambda> _ .\<lfloor>\<lfloor> person4 \<rfloor>\<rfloor>"
definition "X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n5 :: Person \<equiv> \<lambda> _ .\<lfloor>\<lfloor> person5 \<rfloor>\<rfloor>"
definition "X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6 :: Person \<equiv> \<lambda> _ .\<lfloor>\<lfloor> person6 \<rfloor>\<rfloor>"
definition "X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n7 :: OclAny \<equiv> \<lambda> _ .\<lfloor>\<lfloor> person7 \<rfloor>\<rfloor>"
definition "X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n8 :: OclAny \<equiv> \<lambda> _ .\<lfloor>\<lfloor> person8 \<rfloor>\<rfloor>"

lemma [code_unfold]: "((x::Person) \<doteq> y) = StrictRefEq\<^isub>g\<^isub>e\<^isub>n x y" by(simp only: StrictRefEq\<^isub>g\<^isub>e\<^isub>n_\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n)
lemma [code_unfold]: "((x::OclAny) \<doteq> y) = StrictRefEq\<^isub>g\<^isub>e\<^isub>n x y" by(simp only: StrictRefEq\<^isub>g\<^isub>e\<^isub>n_\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y)

lemmas [code_unfold, simp] =
 OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny
 OclAsType\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person
 OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny
 OclAsType\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person

 OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny
 OclIsTypeOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person
 OclIsTypeOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny
 OclIsTypeOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person

 OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_OclAny
 OclIsKindOf\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y_Person
 OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny
 OclIsKindOf\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person


value "\<And>\<sigma>\<^isub>1 . \<not>((\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .salary    \<doteq> \<one>\<zero>\<zero>\<zero> ))"
value "\<And>\<sigma>\<^isub>1 .   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .salary    \<doteq> \<one>\<three>\<zero>\<zero> )"
value "\<And>\<sigma>\<^isub>1'.   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .salary@pre     \<doteq> \<one>\<zero>\<zero>\<zero> )" 
value "\<And>\<sigma>\<^isub>1'. \<not>((\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .salary@pre     \<doteq> \<one>\<three>\<zero>\<zero> ))"
value "\<And>\<sigma>\<^isub>1 . \<not>((\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .boss   \<doteq> X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 ))"
value "\<And>\<sigma>\<^isub>1 .   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .boss .salary   \<doteq> \<one>\<eight>\<zero>\<zero> )"
value "\<And>\<sigma>\<^isub>1 . \<not>((\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .boss .boss  \<doteq> X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 ))" 
value "\<And>\<sigma>\<^isub>1 .   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .boss .boss  \<doteq> X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 )" 
value "        (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .boss@pre .salary  \<doteq> \<one>\<eight>\<zero>\<zero> )"
value "\<And>\<sigma>\<^isub>1'.   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .boss@pre .salary@pre  \<doteq> \<one>\<two>\<zero>\<zero> )"
value "\<And>\<sigma>\<^isub>1'. \<not>((\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .boss@pre .salary@pre  \<doteq> \<one>\<eight>\<zero>\<zero> ))"
value "\<And>\<sigma>\<^isub>1'.   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .boss@pre  \<doteq> X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 )"
value "        (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .boss@pre .boss  \<doteq> X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 )"
value "\<And>\<sigma>\<^isub>1'.   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .boss@pre .boss@pre  \<doteq> null )"
value "\<And>\<sigma>\<^isub>1'.   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile> not(\<upsilon>(X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .boss@pre .boss@pre .boss@pre))"
lemma "        (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .oclIsEverywhere())"
by(simp add: OclValid_def OclIsEverywhere_def 
             \<sigma>\<^isub>1_def \<sigma>\<^isub>1'_def
             X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1_def person1_def
             oid\<^isub>1_def oid\<^isub>2_def oid\<^isub>3_def oid\<^isub>4_def oid\<^isub>5_def oid\<^isub>6_def oid\<^isub>7_def
             oid_of_option_def oid_of_person_def)
lemma "\<And>\<sigma>\<^isub>1 \<sigma>\<^isub>1'. (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>    ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .oclAsType(OclAny) .oclAsType(Person)) \<doteq> X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1)"
by(rule up_down_cast_Person_OclAny_Person', simp add: X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1_def)
value "\<And>\<sigma>\<^isub>1 \<sigma>\<^isub>1'. (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .oclIsTypeOf(Person))"
value "\<And>\<sigma>\<^isub>1 \<sigma>\<^isub>1'. (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>  not(X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .oclIsTypeOf(OclAny))"
value "\<And>\<sigma>\<^isub>1 \<sigma>\<^isub>1'. (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .oclIsKindOf(Person))"
value "\<And>\<sigma>\<^isub>1 \<sigma>\<^isub>1'. (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .oclIsKindOf(OclAny))"
value "\<And>\<sigma>\<^isub>1 \<sigma>\<^isub>1'. (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>  not(X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .oclAsType(OclAny) .oclIsTypeOf(OclAny))"


value "\<And>\<sigma>\<^isub>1 .   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 .salary       \<doteq> \<one>\<eight>\<zero>\<zero> )" 
value "\<And>\<sigma>\<^isub>1'.   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 .salary@pre   \<doteq> \<one>\<two>\<zero>\<zero> )" 
value "\<And>\<sigma>\<^isub>1 .   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 .boss      \<doteq> X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2)"
value "\<And>\<sigma>\<^isub>1'.   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 .boss@pre  \<doteq> null )"
value "\<And>\<sigma>\<^isub>1'. \<not>((\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 .boss@pre  \<doteq> X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2))" 
value "      \<not>((\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 .boss@pre  \<doteq> (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 .boss)))" 
value "\<And>\<sigma>\<^isub>1'.   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile> not(\<upsilon>(X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 .boss@pre .boss))"
value "\<And>\<sigma>\<^isub>1'.   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile> not(\<upsilon>(X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 .boss@pre .salary@pre))"
lemma "        (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 .oclIsEverywhere())"
by(simp add: OclValid_def OclIsEverywhere_def 
             \<sigma>\<^isub>1_def \<sigma>\<^isub>1'_def
             X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2_def person2_def
             oid\<^isub>1_def oid\<^isub>2_def oid\<^isub>3_def oid\<^isub>4_def oid\<^isub>5_def oid\<^isub>6_def oid\<^isub>7_def
             oid_of_option_def oid_of_person_def)


value "\<And>\<sigma>\<^isub>1 .   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n3 .salary       \<doteq> null)"
value "\<And>\<sigma>\<^isub>1'.   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile> not(\<upsilon>(X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n3 .salary@pre))"
value "\<And>\<sigma>\<^isub>1'. \<not>((\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n3 .salary@pre   \<doteq> null))"
value "\<And>\<sigma>\<^isub>1 .   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n3 .boss       \<doteq> null)"
value "\<And>\<sigma>\<^isub>1 .   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile> not(\<upsilon>(X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n3 .boss .salary))"
value "\<And>\<sigma>\<^isub>1'.   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile> not(\<upsilon>(X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n3 .boss@pre))"
lemma "        (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n3 .oclIsNew())"
by(simp add: OclValid_def OclIsNew_def 
             \<sigma>\<^isub>1_def \<sigma>\<^isub>1'_def
             X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n3_def person3_def
             oid\<^isub>1_def oid\<^isub>2_def oid\<^isub>3_def oid\<^isub>4_def oid\<^isub>5_def oid\<^isub>6_def oid\<^isub>7_def
             oid_of_option_def oid_of_person_def)


value "\<And>\<sigma>\<^isub>1'.   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n4 .boss@pre   \<doteq> X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n5 )"
value "        (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile> not(\<upsilon>(X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n4 .boss@pre .salary))" 
value "\<And>\<sigma>\<^isub>1'.   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n4 .boss@pre .salary@pre   \<doteq> \<three>\<five>\<zero>\<zero> )"
lemma "        (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n4 .oclIsEverywhere())"
by(simp add: OclValid_def OclIsEverywhere_def 
             \<sigma>\<^isub>1_def \<sigma>\<^isub>1'_def
             X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n4_def person4_def
             oid\<^isub>1_def oid\<^isub>2_def oid\<^isub>3_def oid\<^isub>4_def oid\<^isub>5_def oid\<^isub>6_def oid\<^isub>7_def
             oid_of_option_def oid_of_person_def)


value "\<And>\<sigma>\<^isub>1 .   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile> not(\<upsilon>(X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n5 .salary))"
value "\<And>\<sigma>\<^isub>1'.   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n5 .salary@pre   \<doteq> \<three>\<five>\<zero>\<zero> )"
value "\<And>\<sigma>\<^isub>1 .   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile> not(\<upsilon>(X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n5 .boss))"
lemma "        (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n5 .oclIsOld())"
by(simp add: OclNot_def OclValid_def OclIsOld_def 
             \<sigma>\<^isub>1_def \<sigma>\<^isub>1'_def
             X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n5_def person5_def
             oid\<^isub>1_def oid\<^isub>2_def oid\<^isub>3_def oid\<^isub>4_def oid\<^isub>5_def oid\<^isub>6_def oid\<^isub>7_def oid\<^isub>8_def
             oid_of_option_def oid_of_person_def)


(* (* access to an oclany object not yet supported *) value "  (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6 .boss .salary)   \<doteq> \<three>\<two>\<zero>\<zero> )"*)
value "\<And>\<sigma>\<^isub>1 .   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile> not(\<upsilon>(X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6 .boss .salary@pre))" 
value "\<And>\<sigma>\<^isub>1'.   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6 .boss@pre   \<doteq> X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n4 )"
value "        (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6 .boss@pre .salary   \<doteq> \<two>\<nine>\<zero>\<zero> )"
value "\<And>\<sigma>\<^isub>1'.   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6 .boss@pre .salary@pre   \<doteq> \<two>\<six>\<zero>\<zero> )"
lemma "        (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6 .oclIsEverywhere())"
by(simp add: OclValid_def OclIsEverywhere_def 
             \<sigma>\<^isub>1_def \<sigma>\<^isub>1'_def
             X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6_def person6_def
             oid\<^isub>1_def oid\<^isub>2_def oid\<^isub>3_def oid\<^isub>4_def oid\<^isub>5_def oid\<^isub>6_def oid\<^isub>7_def
             oid_of_option_def oid_of_person_def)


(* (* access to an oclany object not yet supported *) value "  (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n7 .oclAsType(Person)   \<doteq>  (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6 .boss)))" *)
(* (* access to an oclany object not yet supported *) value "  (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n7 .oclAsType(Person) .boss)   \<doteq> (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n7 .oclAsType(Person)) )" *)
(* (* access to an oclany object not yet supported *) value "  (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n7 .oclAsType(Person) .boss .salary)   \<doteq> \<three>\<two>\<zero>\<zero> )" *)
value "\<And>\<sigma>\<^isub>1 \<sigma>\<^isub>1'. (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     \<upsilon>(X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n7 .oclAsType(Person))"
value "\<And>\<sigma>\<^isub>1'.    (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile> not(\<upsilon>(X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n7 .oclAsType(Person) .boss@pre))"
lemma "\<And>\<sigma>\<^isub>1 \<sigma>\<^isub>1'. (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>     ((X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n7 .oclAsType(Person) .oclAsType(OclAny) .oclAsType(Person))
                                 \<doteq> (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n7 .oclAsType(Person)) )"
by(rule up_down_cast_Person_OclAny_Person', simp add: X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n7_def OclValid_def valid_def person7_def)
lemma "        (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>       (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n7 .oclIsNew())"
by(simp add: OclValid_def OclIsNew_def 
             \<sigma>\<^isub>1_def \<sigma>\<^isub>1'_def
             X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n7_def person7_def
             oid\<^isub>1_def oid\<^isub>2_def oid\<^isub>3_def oid\<^isub>4_def oid\<^isub>5_def oid\<^isub>6_def oid\<^isub>7_def
             oid_of_option_def oid_of_oclany_def)


value "\<And>\<sigma>\<^isub>1 \<sigma>\<^isub>1'. \<not>((\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n8  \<doteq> X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n7 ))"
value "\<And>\<sigma>\<^isub>1 \<sigma>\<^isub>1'.   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile> not(\<upsilon>(X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n8 .oclAsType(Person)))"
value "\<And>\<sigma>\<^isub>1 \<sigma>\<^isub>1'.   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n8 .oclIsTypeOf(OclAny))"
value "\<And>\<sigma>\<^isub>1 \<sigma>\<^isub>1'.   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>   not(X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n8 .oclIsTypeOf(Person))"
value "\<And>\<sigma>\<^isub>1 \<sigma>\<^isub>1'.   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>   not(X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n8 .oclIsKindOf(Person))"
value "\<And>\<sigma>\<^isub>1 \<sigma>\<^isub>1'.   (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n8 .oclIsKindOf(OclAny))"


lemma "\<And>\<sigma>\<^isub>1.    (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (Person .allInstances() \<doteq> Set{ X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n3, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n4(*, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n5*), X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n7 .oclAsType(Person), \<lambda>_. \<lfloor>\<lfloor>Person (in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8)\<rfloor>\<rfloor> })"
proof -
 have p0 : "\<And>S oid\<^isub>8 oid\<^isub>7 person8 person7. oid\<^isub>8 \<noteq> oid\<^isub>7 \<Longrightarrow>
            S (oid\<^isub>8 \<mapsto> person8) (oid\<^isub>7 \<mapsto> person7) = S (oid\<^isub>7 \<mapsto> person7) (oid\<^isub>8 \<mapsto> person8)"
 by (metis fun_upd_twist)

 have perm : "\<sigma>\<^isub>1' = \<lparr> heap = empty
                           (oid\<^isub>8 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8)
                           (oid\<^isub>7 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person7)
                           (oid\<^isub>6 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person6)
                          (*oid\<^isub>5*)
                           (oid\<^isub>4 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person4)
                           (oid\<^isub>3 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person3)
                           (oid\<^isub>2 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person2)
                           (oid\<^isub>1 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person1)
                , assocs = empty \<rparr>"
  apply(simp add: \<sigma>\<^isub>1'_def
                  oid\<^isub>1_def oid\<^isub>2_def oid\<^isub>3_def oid\<^isub>4_def oid\<^isub>5_def oid\<^isub>6_def oid\<^isub>7_def oid\<^isub>8_def)
  apply(subst (1) p0, simp)
  apply(subst (2) p0, simp) apply(subst (1) p0, simp)
  apply(subst (3) p0, simp) apply(subst (2) p0, simp) apply(subst (1) p0, simp)
  apply(subst (4) p0, simp) apply(subst (3) p0, simp) apply(subst (2) p0, simp) apply(subst (1) p0, simp)
  apply(subst (5) p0, simp) apply(subst (4) p0, simp) apply(subst (3) p0, simp) apply(subst (2) p0, simp) apply(subst (1) p0, simp)
  apply(subst (6) p0, simp) apply(subst (5) p0, simp) apply(subst (4) p0, simp) apply(subst (3) p0, simp) apply(subst (2) p0, simp) apply(subst (1) p0, simp)
 by(simp)

 fix \<sigma>\<^isub>1
 have eq : "Person .allInstances() (\<sigma>\<^isub>1,\<sigma>\<^isub>1') =
       Set{X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n3, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n4(*, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n5*), X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n7 .oclAsType(Person), \<lambda>_. \<lfloor>\<lfloor>Person (in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8)\<rfloor>\<rfloor>} (\<sigma>\<^isub>1,\<sigma>\<^isub>1')"
  apply(simp only: perm)
  apply(simp add: oid\<^isub>1_def oid\<^isub>2_def oid\<^isub>3_def oid\<^isub>4_def oid\<^isub>5_def oid\<^isub>6_def oid\<^isub>7_def oid\<^isub>8_def
                  X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n3_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n4_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n5_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n7_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n8_def)
  apply(subst state_update_vs_allInstances_rec, simp)+
  apply(simp add: state_update_vs_allInstances_rec0)

  apply(subst including_cp_all
                                         ) prefer 4 apply(subst cp_OclIncluding[symmetric])
  apply(subst including_cp_all[of _ _ _ "(\<sigma>\<^isub>1, \<lparr>heap = [7 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8],
                    assocs = Map.empty\<rparr>)"]) prefer 4 apply(subst cp_OclIncluding[symmetric])
  apply(subst including_cp_all[of _ _ _ "(\<sigma>\<^isub>1, \<lparr>heap = [7 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8, 6 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person7],
                    assocs = Map.empty\<rparr>)"]) prefer 4 apply(subst cp_OclIncluding[symmetric])
  apply(subst including_cp_all[of _ _ _ "(\<sigma>\<^isub>1, \<lparr>heap = [7 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8, 6 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person7, 5 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person6],
                    assocs = Map.empty\<rparr>)"]) prefer 4 apply(subst cp_OclIncluding[symmetric])
  apply(subst including_cp_all[of _ _ _ "(\<sigma>\<^isub>1, \<lparr>heap = [7 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8, 6 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person7, 5 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person6, 3 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person4],
                    assocs = Map.empty\<rparr>)"]) prefer 4 apply(subst cp_OclIncluding[symmetric])
  apply(subst including_cp_all[of _ _ _ "(\<sigma>\<^isub>1, \<lparr>heap = [7 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8, 6 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person7, 5 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person6, 3 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person4, 2 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person3],
                    assocs = Map.empty\<rparr>)"]) prefer 4 apply(subst cp_OclIncluding[symmetric])
  apply(subst including_cp_all[of _ _ _ "(\<sigma>\<^isub>1, \<lparr>heap = [7 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8, 6 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person7, 5 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person6, 3 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person4, 2 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person3, Suc 0 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person2],
                    assocs = Map.empty\<rparr>)"]) prefer 4 apply(subst cp_OclIncluding[symmetric])
  apply(subst including_cp_all[of _ _ _ "(\<sigma>\<^isub>1, \<lparr>heap = [7 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8, 6 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person7, 5 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person6, 3 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person4, 2 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person3, Suc 0 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person2, 0 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person1],
                    assocs = Map.empty\<rparr>)"]) prefer 4 apply(subst cp_OclIncluding[symmetric])

  apply(simp add: person1_def person2_def person3_def person4_def person5_def person6_def person7_def person8_def)
  apply(simp_all add: is_int_def)
  apply((rule including_cp_all, simp_all add: is_int_def)+, simp add: mtSet_def)+
  apply(simp add: mtSet_def) apply(simp add: mtSet_def)
 by (metis (no_types) foundation1 foundation16 mtSet_defined)

 show "?thesis \<sigma>\<^isub>1"
  apply(simp only: StrictRefEq\<^isub>s\<^isub>e\<^isub>t StrongEq_def true_def OclValid_def)
  apply(subst cp_valid)
  apply(subst (1 2) eq)
  apply(subst cp_valid[symmetric])
  apply(simp add: X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n3_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n4_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n5_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n7_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n8_def
                  person1_def person2_def person3_def person4_def person5_def person6_def person7_def person8_def)
 done
qed

lemma "\<And>\<sigma>\<^isub>1.    (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (OclAllInstances' Person' \<doteq> Set{ X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n3, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n4(*, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n5*), X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n7 .oclAsType(Person) })"
proof -
 have p0 : "\<And>S oid\<^isub>8 oid\<^isub>7 person8 person7. oid\<^isub>8 \<noteq> oid\<^isub>7 \<Longrightarrow>
            S (oid\<^isub>8 \<mapsto> person8) (oid\<^isub>7 \<mapsto> person7) = S (oid\<^isub>7 \<mapsto> person7) (oid\<^isub>8 \<mapsto> person8)"
 by (metis fun_upd_twist)

 have perm : "\<sigma>\<^isub>1' = \<lparr> heap = empty
                           (oid\<^isub>8 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8)
                           (oid\<^isub>7 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person7)
                           (oid\<^isub>6 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person6)
                          (*oid\<^isub>5*)
                           (oid\<^isub>4 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person4)
                           (oid\<^isub>3 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person3)
                           (oid\<^isub>2 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person2)
                           (oid\<^isub>1 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person1)
                , assocs = empty \<rparr>"
  apply(simp add: \<sigma>\<^isub>1'_def
                  oid\<^isub>1_def oid\<^isub>2_def oid\<^isub>3_def oid\<^isub>4_def oid\<^isub>5_def oid\<^isub>6_def oid\<^isub>7_def oid\<^isub>8_def)
  apply(subst (1) p0, simp)
  apply(subst (2) p0, simp) apply(subst (1) p0, simp)
  apply(subst (3) p0, simp) apply(subst (2) p0, simp) apply(subst (1) p0, simp)
  apply(subst (4) p0, simp) apply(subst (3) p0, simp) apply(subst (2) p0, simp) apply(subst (1) p0, simp)
  apply(subst (5) p0, simp) apply(subst (4) p0, simp) apply(subst (3) p0, simp) apply(subst (2) p0, simp) apply(subst (1) p0, simp)
  apply(subst (6) p0, simp) apply(subst (5) p0, simp) apply(subst (4) p0, simp) apply(subst (3) p0, simp) apply(subst (2) p0, simp) apply(subst (1) p0, simp)
 by(simp)

 fix \<sigma>\<^isub>1
 have eq : "OclAllInstances' Person' (\<sigma>\<^isub>1,\<sigma>\<^isub>1') =
       Set{X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n3, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n4(*, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n5*), X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n7 .oclAsType(Person)} (\<sigma>\<^isub>1,\<sigma>\<^isub>1')"
  apply(simp only: perm)
  apply(simp add: oid\<^isub>1_def oid\<^isub>2_def oid\<^isub>3_def oid\<^isub>4_def oid\<^isub>5_def oid\<^isub>6_def oid\<^isub>7_def oid\<^isub>8_def
                  X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n3_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n4_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n5_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n7_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n8_def)
  apply(subst state_update_vs_allInstances'_rec, simp, simp add: Person'_def
   person1_def person2_def person3_def person4_def person5_def person6_def person7_def person8_def)
  apply(subst state_update_vs_allInstances'_rec, simp, simp add: Person'_def
   person1_def person2_def person3_def person4_def person5_def person6_def person7_def person8_def)
  apply(subst state_update_vs_allInstances'_rec, simp, simp add: Person'_def
   person1_def person2_def person3_def person4_def person5_def person6_def person7_def person8_def)
  apply(subst state_update_vs_allInstances'_rec, simp, simp add: Person'_def
   person1_def person2_def person3_def person4_def person5_def person6_def person7_def person8_def)
  apply(subst state_update_vs_allInstances'_rec, simp, simp add: Person'_def
   person1_def person2_def person3_def person4_def person5_def person6_def person7_def person8_def)
  apply(subst state_update_vs_allInstances'_rec, simp, simp add: Person'_def
   person1_def person2_def person3_def person4_def person5_def person6_def person7_def person8_def)
  apply(subst state_update_vs_allInstances'_recnone, simp, simp add: Person'_def
   person1_def person2_def person3_def person4_def person5_def person6_def person7_def person8_def)
  apply(subst state_update_vs_allInstances'_rec0)

  apply(subst including_cp_all
                                         ) prefer 4 apply(subst cp_OclIncluding[symmetric])
  apply(subst including_cp_all[of _ _ _ "(\<sigma>\<^isub>1, \<lparr>heap = [7 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8],
                    assocs = Map.empty\<rparr>)"]) prefer 4 apply(subst cp_OclIncluding[symmetric])
  apply(subst including_cp_all[of _ _ _ "(\<sigma>\<^isub>1, \<lparr>heap = [7 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8, 6 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person7],
                    assocs = Map.empty\<rparr>)"]) prefer 4 apply(subst cp_OclIncluding[symmetric])
  apply(subst including_cp_all[of _ _ _ "(\<sigma>\<^isub>1, \<lparr>heap = [7 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8, 6 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person7, 5 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person6],
                    assocs = Map.empty\<rparr>)"]) prefer 4 apply(subst cp_OclIncluding[symmetric])
  apply(subst including_cp_all[of _ _ _ "(\<sigma>\<^isub>1, \<lparr>heap = [7 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8, 6 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person7, 5 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person6, 3 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person4],
                    assocs = Map.empty\<rparr>)"]) prefer 4 apply(subst cp_OclIncluding[symmetric])
  apply(subst including_cp_all[of _ _ _ "(\<sigma>\<^isub>1, \<lparr>heap = [7 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8, 6 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person7, 5 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person6, 3 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person4, 2 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person3],
                    assocs = Map.empty\<rparr>)"]) prefer 4 apply(subst cp_OclIncluding[symmetric])
  apply(subst including_cp_all[of _ _ _ "(\<sigma>\<^isub>1, \<lparr>heap = [7 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8, 6 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person7, 5 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person6, 3 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person4, 2 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person3, Suc 0 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person2],
                    assocs = Map.empty\<rparr>)"]) prefer 4 apply(subst cp_OclIncluding[symmetric])
  apply(subst including_cp_all[of _ _ _ "(\<sigma>\<^isub>1, \<lparr>heap = [7 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8, 6 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person7, 5 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person6, 3 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person4, 2 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person3, Suc 0 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person2, 0 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person1],
                    assocs = Map.empty\<rparr>)"]) prefer 4 apply(subst cp_OclIncluding[symmetric])

  apply(simp add: Person'_def person1_def person2_def person3_def person4_def person5_def person6_def person7_def person8_def)
  apply(simp_all add: is_int_def)
  apply((rule including_cp_all, simp_all add: is_int_def)+, simp add: mtSet_def)+
  apply(simp add: mtSet_def) apply(simp add: mtSet_def) apply(simp add: mtSet_def)
 by (metis (no_types) foundation1 foundation16 mtSet_defined)

 show "?thesis \<sigma>\<^isub>1"
  apply(simp only: StrictRefEq\<^isub>s\<^isub>e\<^isub>t StrongEq_def true_def OclValid_def)
  apply(subst cp_valid)
  apply(subst (1 2) eq)
  apply(subst cp_valid[symmetric])
  apply(simp add: X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n3_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n4_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n5_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n7_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n8_def
                  person1_def person2_def person3_def person4_def person5_def person6_def person7_def person8_def)
 done
qed

lemma "\<And>\<sigma>\<^isub>1.    (\<sigma>\<^isub>1,\<sigma>\<^isub>1') \<Turnstile>      (OclAllInstances' OclAny' \<doteq> Set{ X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .oclAsType(OclAny), X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 .oclAsType(OclAny), X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n3 .oclAsType(OclAny), X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n4 .oclAsType(OclAny)(*, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n5*), X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6 .oclAsType(OclAny), X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n7, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n8 })"
proof -
 have p0 : "\<And>S oid\<^isub>8 oid\<^isub>7 person8 person7. oid\<^isub>8 \<noteq> oid\<^isub>7 \<Longrightarrow>
            S (oid\<^isub>8 \<mapsto> person8) (oid\<^isub>7 \<mapsto> person7) = S (oid\<^isub>7 \<mapsto> person7) (oid\<^isub>8 \<mapsto> person8)"
 by (metis fun_upd_twist)

 have perm : "\<sigma>\<^isub>1' = \<lparr> heap = empty
                           (oid\<^isub>8 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8)
                           (oid\<^isub>7 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person7)
                           (oid\<^isub>6 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person6)
                          (*oid\<^isub>5*)
                           (oid\<^isub>4 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person4)
                           (oid\<^isub>3 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person3)
                           (oid\<^isub>2 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person2)
                           (oid\<^isub>1 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person1)
                , assocs = empty \<rparr>"
  apply(simp add: \<sigma>\<^isub>1'_def
                  oid\<^isub>1_def oid\<^isub>2_def oid\<^isub>3_def oid\<^isub>4_def oid\<^isub>5_def oid\<^isub>6_def oid\<^isub>7_def oid\<^isub>8_def)
  apply(subst (1) p0, simp)
  apply(subst (2) p0, simp) apply(subst (1) p0, simp)
  apply(subst (3) p0, simp) apply(subst (2) p0, simp) apply(subst (1) p0, simp)
  apply(subst (4) p0, simp) apply(subst (3) p0, simp) apply(subst (2) p0, simp) apply(subst (1) p0, simp)
  apply(subst (5) p0, simp) apply(subst (4) p0, simp) apply(subst (3) p0, simp) apply(subst (2) p0, simp) apply(subst (1) p0, simp)
  apply(subst (6) p0, simp) apply(subst (5) p0, simp) apply(subst (4) p0, simp) apply(subst (3) p0, simp) apply(subst (2) p0, simp) apply(subst (1) p0, simp)
 by(simp)

 fix \<sigma>\<^isub>1
 have eq : "OclAllInstances' OclAny' (\<sigma>\<^isub>1,\<sigma>\<^isub>1') =
       Set{ X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 .oclAsType(OclAny), X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 .oclAsType(OclAny), X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n3 .oclAsType(OclAny), X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n4 .oclAsType(OclAny)(*, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n5*), X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6 .oclAsType(OclAny), X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n7, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n8 } (\<sigma>\<^isub>1,\<sigma>\<^isub>1')"
  apply(simp only: perm)
  apply(simp add: oid\<^isub>1_def oid\<^isub>2_def oid\<^isub>3_def oid\<^isub>4_def oid\<^isub>5_def oid\<^isub>6_def oid\<^isub>7_def oid\<^isub>8_def
                  X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n3_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n4_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n5_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n7_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n8_def)
  apply(subst state_update_vs_allInstances'_rec, simp, simp add: OclAny'_def
   person1_def person2_def person3_def person4_def person5_def person6_def person7_def person8_def)
  apply(subst state_update_vs_allInstances'_rec, simp, simp add: OclAny'_def
   person1_def person2_def person3_def person4_def person5_def person6_def person7_def person8_def)
  apply(subst state_update_vs_allInstances'_rec, simp, simp add: OclAny'_def
   person1_def person2_def person3_def person4_def person5_def person6_def person7_def person8_def)
  apply(subst state_update_vs_allInstances'_rec, simp, simp add: OclAny'_def
   person1_def person2_def person3_def person4_def person5_def person6_def person7_def person8_def)
  apply(subst state_update_vs_allInstances'_rec, simp, simp add: OclAny'_def
   person1_def person2_def person3_def person4_def person5_def person6_def person7_def person8_def)
  apply(subst state_update_vs_allInstances'_rec, simp, simp add: OclAny'_def
   person1_def person2_def person3_def person4_def person5_def person6_def person7_def person8_def)
  apply(subst state_update_vs_allInstances'_rec, simp, simp add: OclAny'_def
   person1_def person2_def person3_def person4_def person5_def person6_def person7_def person8_def)
  apply(subst state_update_vs_allInstances'_rec0)

  apply(subst including_cp_all
                                         ) prefer 4 apply(subst cp_OclIncluding[symmetric])
  apply(subst including_cp_all[of _ _ _ "(\<sigma>\<^isub>1, \<lparr>heap = [7 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8],
                    assocs = Map.empty\<rparr>)"]) prefer 4 apply(subst cp_OclIncluding[symmetric])
  apply(subst including_cp_all[of _ _ _ "(\<sigma>\<^isub>1, \<lparr>heap = [7 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8, 6 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person7],
                    assocs = Map.empty\<rparr>)"]) prefer 4 apply(subst cp_OclIncluding[symmetric])
  apply(subst including_cp_all[of _ _ _ "(\<sigma>\<^isub>1, \<lparr>heap = [7 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8, 6 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person7, 5 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person6],
                    assocs = Map.empty\<rparr>)"]) prefer 4 apply(subst cp_OclIncluding[symmetric])
  apply(subst including_cp_all[of _ _ _ "(\<sigma>\<^isub>1, \<lparr>heap = [7 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8, 6 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person7, 5 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person6, 3 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person4],
                    assocs = Map.empty\<rparr>)"]) prefer 4 apply(subst cp_OclIncluding[symmetric])
  apply(subst including_cp_all[of _ _ _ "(\<sigma>\<^isub>1, \<lparr>heap = [7 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8, 6 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person7, 5 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person6, 3 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person4, 2 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person3],
                    assocs = Map.empty\<rparr>)"]) prefer 4 apply(subst cp_OclIncluding[symmetric])
  apply(subst including_cp_all[of _ _ _ "(\<sigma>\<^isub>1, \<lparr>heap = [7 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8, 6 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person7, 5 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person6, 3 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person4, 2 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person3, Suc 0 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person2],
                    assocs = Map.empty\<rparr>)"]) prefer 4 apply(subst cp_OclIncluding[symmetric])
  apply(subst including_cp_all[of _ _ _ "(\<sigma>\<^isub>1, \<lparr>heap = [7 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person8, 6 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person7, 5 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person6, 3 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person4, 2 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person3, Suc 0 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person2, 0 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person1],
                    assocs = Map.empty\<rparr>)"]) prefer 4 apply(subst cp_OclIncluding[symmetric])

  apply(simp add: OclAny'_def person1_def person2_def person3_def person4_def person5_def person6_def person7_def person8_def)
  apply(simp_all add: is_int_def)
  apply((rule including_cp_all, simp_all add: is_int_def)+, simp add: mtSet_def)+
  apply(simp add: mtSet_def) apply(simp add: mtSet_def)
 by (metis (no_types) foundation1 foundation16 mtSet_defined)

 show "?thesis \<sigma>\<^isub>1"
  apply(simp only: StrictRefEq\<^isub>s\<^isub>e\<^isub>t StrongEq_def true_def OclValid_def)
  apply(subst cp_valid)
  apply(subst (1 2) eq)
  apply(subst cp_valid[symmetric])
  apply(simp add: X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n3_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n4_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n5_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n6_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n7_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n8_def
                  person1_def person2_def person3_def person4_def person5_def person6_def person7_def person8_def)
 done
qed




lemma
 fixes \<sigma>\<^isub>1 \<sigma>\<^isub>1'
       person0 person1 person2
       X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n0 X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2
 defines "person0 \<equiv> mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y 0 None"
 defines "person1 \<equiv> mk\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y 1 \<lfloor>(\<lfloor>20\<rfloor>, \<lfloor>2\<rfloor>)\<rfloor>"
 defines "person2 \<equiv> mk\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n 2 \<lfloor>30\<rfloor> \<lfloor>1\<rfloor>"
 defines "\<sigma>\<^isub>1' \<equiv> \<lparr> heap = empty(0 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person0)
                              (1 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person1)
                              (2 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person2)
                , assocs = empty \<rparr>"
 defines "X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n0 \<equiv> (\<lambda>_. \<lfloor>\<lfloor> person0 \<rfloor>\<rfloor>)"
 defines "X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1 \<equiv> (\<lambda>_. \<lfloor>\<lfloor> person1 \<rfloor>\<rfloor>)"
 defines "X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 :: Person \<equiv> (\<lambda>_. \<lfloor>\<lfloor> person2 \<rfloor>\<rfloor>)"
 shows "(OclAny .allInstances()) (\<sigma>\<^isub>1,\<sigma>\<^isub>1') = Set{X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n0, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1, X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2 .oclAsType(OclAny)} (\<sigma>\<^isub>1,\<sigma>\<^isub>1')"
proof -
 have perm : "\<sigma>\<^isub>1' = \<lparr> heap = empty(2 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person2)
                                 (1 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person1)
                                 (0 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person0)
                , assocs = empty \<rparr>"
  apply(simp add: \<sigma>\<^isub>1'_def)
  proof -
  have "Suc 0 = oid\<^isub>2" by (metis One_nat_def oid\<^isub>2_def)
  thus "[0 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person0, Suc 0 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person1, 2 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person2] = [2 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person2, Suc 0 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person1, 0 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person0]"
  by (metis One_nat_def Suc_1 Zero_not_Suc fun_upd_twist n_not_Suc_n zero_neq_numeral)
 qed

 show ?thesis
  apply(simp only: perm)
  apply(simp add: comp_def image_def \<sigma>\<^isub>1'_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n0_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n1_def X\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n2_def)
  apply(subst state_update_vs_allInstances_rec, simp)+
  apply(simp add: state_update_vs_allInstances_rec0)

  apply(subst including_cp_all
                                         ) prefer 4 apply(subst cp_OclIncluding[symmetric])
  apply(subst including_cp_all[of _ _ _ "(\<sigma>\<^isub>1, \<lparr>heap = [2 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person2],
                    assocs = Map.empty\<rparr>)"]) prefer 4 apply(subst cp_OclIncluding[symmetric])
  apply(subst including_cp_all[of _ _ _ "(\<sigma>\<^isub>1, \<lparr>heap = [2 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person2, Suc 0 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person1],
                    assocs = Map.empty\<rparr>)"]) prefer 4 apply(subst cp_OclIncluding[symmetric])
  apply(subst including_cp_all[of _ _ _ "(\<sigma>\<^isub>1, \<lparr>heap = [2 \<mapsto> in\<^isub>p\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n person2, Suc 0 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person1, 0 \<mapsto> in\<^isub>o\<^isub>c\<^isub>l\<^isub>a\<^isub>n\<^isub>y person0],
                    assocs = Map.empty\<rparr>)"]) prefer 4 apply(subst cp_OclIncluding[symmetric])

  apply(simp add: person2_def)
  apply(simp_all add: is_int_def)
  apply(rule including_cp_all)
  apply(simp_all add: is_int_def)
  apply(simp add: mtSet_def) apply(simp add: mtSet_def) apply(simp add: mtSet_def)
 by (metis (no_types) foundation1 foundation16 mtSet_defined)
qed

end
