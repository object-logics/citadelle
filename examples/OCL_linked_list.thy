(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4 
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_linked_list.thy --- OCL Contracts and an Example.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2012      Université Paris-Sud, France
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
   Part II : State and Objects. *)

theory 
  OCL_linked_list
imports
  "../OCL_main" (* Testing *)
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
of the compilation informally, an present a concrete example which is verified in Isabelle/HOL. *}

subsection{* Outlining the Example *}

subsection{* Example Data-Universe and its Infrastructure *}
text{* Should be generated entirely from a class-diagram. *}

(* @{text "'\<AA>"} -- \mathfrak{A} *)
text{* Our data universe  consists in the concrete class diagram just of node's, 
and implicitly of the class object. Each class implies the existence of a class 
type defined for the corresponding object representations as follows: *}

datatype node =  mk\<^isub>n\<^isub>o\<^isub>d\<^isub>e   oid          (* the oid to the node itself *)
                         "int option" (* the attribute "i" or null *) 
                         "oid option" (* the attribute "next" or null *)


datatype object= mk\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t oid (* the oid to the object itself *)
                           "(int option \<times> oid option) option" 
                           (* the extensions to "node"; used to denote objects of actual type
                             "node" casted to "object"; in case of existence of several subclasses 
                             of object,sums of extensions have to be provided. *)

text{* Now, we construct a concrete "universe of object types" by injection into a 
sum type containing the class types. This type of objects will be used as instance
for all resp. type-variables ...*}

datatype \<AA> = in\<^isub>n\<^isub>o\<^isub>d\<^isub>e node | in\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t object

text{* Recall that in order to denote OCL-types occuring in OCL expressions syntactically 
--- as, for example,  as "argument" of allInstances --- we use the inverses of the injection 
functions into the object universes; we show that this is sufficient "characterization". *}
definition Node :: "\<AA> \<Rightarrow> node"
where     "Node \<equiv> (the_inv in\<^isub>n\<^isub>o\<^isub>d\<^isub>e)"

definition Object :: "\<AA> \<Rightarrow> object"
where     "Object \<equiv> (the_inv in\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t)"


text{* Having fixed the object universe, we can introduce type synonyms that exactly correspond
to OCL types. Again, we exploit that our representation of OCL is a "shallow embedding" with a
one-to-one correspondance of OCL-types to types of the meta-language HOL. *}
type_synonym Boolean     = "(\<AA>)Boolean"
type_synonym Integer     = "(\<AA>)Integer"
type_synonym Void        = "(\<AA>)Void"
type_synonym Object      = "(\<AA>,object option option) val"
type_synonym Node        = "(\<AA>, node option option)val"
type_synonym Set_Integer = "(\<AA>, int option option)Set"
type_synonym Set_Node    = "(\<AA>, node option option)Set"

text{* Just a little check: *}
typ "Boolean"

text{* In order to reuse key-elements of the library like referential equality, we have
to show that the object universe belongs to the type class "object", i.e. each class type
has to provide a function @{term oid_of} yielding the object id (oid) of the object. *}
instantiation node :: object
begin
   definition oid_of_node_def: "oid_of x = (case x of mk\<^isub>n\<^isub>o\<^isub>d\<^isub>e oid _ _ \<Rightarrow> oid)"
   instance ..
end

instantiation object :: object
begin
   definition oid_of_object_def: "oid_of x = (case x of mk\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t oid _ \<Rightarrow> oid)"
   instance ..
end

instantiation \<AA> :: object
begin
   definition oid_of_\<AA>_def: "oid_of x = (case x of 
                                             in\<^isub>n\<^isub>o\<^isub>d\<^isub>e node \<Rightarrow> oid_of node
                                           | in\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t obj \<Rightarrow> oid_of obj)"
   instance ..
end

instantiation   option  :: (object)object
begin 
   definition oid_of_option_def: "oid_of x = oid_of (the x)"
   instance ..
end



section{* Instantiation of the generic strict equality. We instantiate the referential equality
on @{text "Node"} and @{text "Object"} *}

defs(overloaded)   StrictRefEq\<^isub>n\<^isub>o\<^isub>d\<^isub>e   :  "(x::Node) \<doteq> y    \<equiv> gen_ref_eq x y"
defs(overloaded)   StrictRefEq\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t  : "(x::Object) \<doteq> y  \<equiv> gen_ref_eq x y"

lemmas strict_eq_node =
    cp_gen_ref_eq_object[of "x::Node" "y::Node" "\<tau>", 
                         simplified StrictRefEq\<^isub>n\<^isub>o\<^isub>d\<^isub>e[symmetric]]
    cp_intro(9)         [of "P::Node \<Rightarrow>Node""Q::Node \<Rightarrow>Node",
                         simplified StrictRefEq\<^isub>n\<^isub>o\<^isub>d\<^isub>e[symmetric] ]
    gen_ref_eq_def      [of "x::Node" "y::Node", 
                         simplified StrictRefEq\<^isub>n\<^isub>o\<^isub>d\<^isub>e[symmetric]]
    gen_ref_eq_defargs  [of _ "x::Node" "y::Node", 
                         simplified StrictRefEq\<^isub>n\<^isub>o\<^isub>d\<^isub>e[symmetric]]
    gen_ref_eq_object_strict1 
                        [of "x::Node",
                         simplified StrictRefEq\<^isub>n\<^isub>o\<^isub>d\<^isub>e[symmetric]]
    gen_ref_eq_object_strict2 
                        [of "x::Node",
                         simplified StrictRefEq\<^isub>n\<^isub>o\<^isub>d\<^isub>e[symmetric]]
    gen_ref_eq_object_strict3 
                        [of "x::Node",
                         simplified StrictRefEq\<^isub>n\<^isub>o\<^isub>d\<^isub>e[symmetric]]
    gen_ref_eq_object_strict3 
                        [of "x::Node",
                         simplified StrictRefEq\<^isub>n\<^isub>o\<^isub>d\<^isub>e[symmetric]]
    gen_ref_eq_object_strict4 
                        [of "x::Node",
                         simplified StrictRefEq\<^isub>n\<^isub>o\<^isub>d\<^isub>e[symmetric]]

thm strict_eq_node
(* TODO: Analogue for object. *)

subsection{* AllInstances *}

(* IS THIS WHAT WE WANT ? THIS DEFINITION FILTERS OBJECTS THAT ARE BOOKED UNDER
THEIR APPARENT (STATIC) TYPE INTO THE CONTEXT, NOT BY THEIR ACTUAL (DYNAMIC) TYPE. *)
lemma "(Node .oclAllInstances()) = 
             (\<lambda>\<tau>.  Abs_Set_0 \<lfloor>\<lfloor>(Some \<circ> Some \<circ> (the_inv in\<^isub>n\<^isub>o\<^isub>d\<^isub>e))`(ran(snd \<tau>)) \<rfloor>\<rfloor>) "
by(rule ext, simp add:allinstances_def Node_def)

lemma "(Object .oclAllInstances@pre()) = 
             (\<lambda>\<tau>.  Abs_Set_0 \<lfloor>\<lfloor>(Some \<circ> Some \<circ> (the_inv in\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t))`(ran(fst \<tau>)) \<rfloor>\<rfloor>) "
by(rule ext, simp add:allinstancesATpre_def Object_def)


text{* For each Class \emph{C}, we will have an casting operation \verb+.oclAsType(+\emph{C}\verb+)+,
   a test on the actual type \verb+.oclIsTypeOf(+\emph{C}\verb+)+ as well as its relaxed form
   \verb+.oclIsKindOf(+\emph{C}\verb+)+ (corresponding exactly to Java's \verb+instanceof+-operator. 
*}
text{* Thus, since we have two class-types in our concrete class hierarchy, we have
two operations to declare and and to provide two overloading definitions for the two static types.
*}


section{* Selector Definition *}
text{* Should be generated entirely from a class-diagram. *}

typ "Node \<Rightarrow> Node"
fun dot_next:: "Node \<Rightarrow> Node"  ("(1(_).next)" 50)
  where "(X).next = (\<lambda> \<tau>. case X \<tau> of
               \<bottom> \<Rightarrow> invalid \<tau>           (* undefined pointer *)
          | \<lfloor>  \<bottom> \<rfloor> \<Rightarrow> invalid \<tau>         (* dereferencing null pointer *)
          | \<lfloor>\<lfloor> mk\<^isub>n\<^isub>o\<^isub>d\<^isub>e oid i \<bottom> \<rfloor>\<rfloor> \<Rightarrow> null \<tau>(* object contains null pointer *)
          | \<lfloor>\<lfloor> mk\<^isub>n\<^isub>o\<^isub>d\<^isub>e oid i \<lfloor>next\<rfloor> \<rfloor>\<rfloor> \<Rightarrow>   (* We assume here that oid is indeed 'the' oid of the Node,
                                           ie. we assume that  \<tau> is well-formed. *)
                    case (snd \<tau>) next of
                       \<bottom> \<Rightarrow> invalid \<tau> 
                    | \<lfloor>in\<^isub>n\<^isub>o\<^isub>d\<^isub>e (mk\<^isub>n\<^isub>o\<^isub>d\<^isub>e a b c)\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>mk\<^isub>n\<^isub>o\<^isub>d\<^isub>e a b c \<rfloor>\<rfloor>
                    | \<lfloor> _ \<rfloor>\<Rightarrow> invalid \<tau>)" (* illtyped state, not occuring in 
                                             well-formed, typed states *)

fun dot_i:: "Node \<Rightarrow> Integer"  ("(1(_).i)" 50)
  where "(X).i = (\<lambda> \<tau>. case X \<tau> of
               \<bottom> \<Rightarrow> invalid \<tau> 
          | \<lfloor>  \<bottom> \<rfloor> \<Rightarrow> invalid \<tau> 
          | \<lfloor>\<lfloor> mk\<^isub>n\<^isub>o\<^isub>d\<^isub>e oid \<bottom> _ \<rfloor>\<rfloor> \<Rightarrow>  null \<tau>
          | \<lfloor>\<lfloor> mk\<^isub>n\<^isub>o\<^isub>d\<^isub>e oid \<lfloor>i\<rfloor> _ \<rfloor>\<rfloor> \<Rightarrow>  \<lfloor>\<lfloor> i \<rfloor>\<rfloor>)"

fun dot_next_at_pre:: "Node \<Rightarrow> Node"  ("(1(_).next@pre)" 50)
  where "(X).next@pre = (\<lambda> \<tau>. case X \<tau> of
               \<bottom> \<Rightarrow> invalid \<tau>  
          | \<lfloor>  \<bottom> \<rfloor> \<Rightarrow> invalid \<tau> 
          | \<lfloor>\<lfloor> mk\<^isub>n\<^isub>o\<^isub>d\<^isub>e oid i \<bottom> \<rfloor>\<rfloor> \<Rightarrow> null \<tau>(* object contains null pointer. REALLY ? 
                                          And if this pointer was defined in the pre-state ?*)
          | \<lfloor>\<lfloor> mk\<^isub>n\<^isub>o\<^isub>d\<^isub>e oid i \<lfloor>next\<rfloor> \<rfloor>\<rfloor> \<Rightarrow> (* We assume here that oid is indeed 'the' oid of the Node,
                                        ie. we assume that  \<tau> is well-formed. *)
                 (case (fst \<tau>) next of
                        \<bottom> \<Rightarrow> invalid \<tau> 
                     | \<lfloor>in\<^isub>n\<^isub>o\<^isub>d\<^isub>e (mk\<^isub>n\<^isub>o\<^isub>d\<^isub>e a b c)\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>mk\<^isub>n\<^isub>o\<^isub>d\<^isub>e a b c \<rfloor>\<rfloor>
                     | \<lfloor> _ \<rfloor>\<Rightarrow> invalid \<tau>))"

fun dot_i_at_pre:: "Node \<Rightarrow> Integer"  ("(1(_).i@pre)" 50)
where "(X).i@pre = (\<lambda> \<tau>. case X \<tau> of
              \<bottom> \<Rightarrow> invalid \<tau>
          | \<lfloor>  \<bottom> \<rfloor> \<Rightarrow> invalid \<tau>
          | \<lfloor>\<lfloor> mk\<^isub>n\<^isub>o\<^isub>d\<^isub>e oid _ _ \<rfloor>\<rfloor> \<Rightarrow> 
                      if oid \<in> dom (fst \<tau>)
                      then (case (fst \<tau>) oid of
                                \<bottom> \<Rightarrow> invalid \<tau>
                            | \<lfloor>in\<^isub>n\<^isub>o\<^isub>d\<^isub>e (mk\<^isub>n\<^isub>o\<^isub>d\<^isub>e oid \<bottom> next) \<rfloor> \<Rightarrow> null \<tau>
                            | \<lfloor>in\<^isub>n\<^isub>o\<^isub>d\<^isub>e (mk\<^isub>n\<^isub>o\<^isub>d\<^isub>e oid \<lfloor>i\<rfloor>next) \<rfloor> \<Rightarrow> \<lfloor>\<lfloor> i \<rfloor>\<rfloor>
                            | \<lfloor> _ \<rfloor>\<Rightarrow> invalid \<tau>)
                      else invalid \<tau>)"

lemma cp_dot_next: "((X).next) \<tau> = ((\<lambda>_. X \<tau>).next) \<tau>" by(simp)

lemma cp_dot_i: "((X).i) \<tau> = ((\<lambda>_. X \<tau>).i) \<tau>" by(simp)

lemma cp_dot_next_at_pre: "((X).next@pre) \<tau> = ((\<lambda>_. X \<tau>).next@pre) \<tau>" by(simp)

lemma cp_dot_i_pre: "((X).i@pre) \<tau> = ((\<lambda>_. X \<tau>).i@pre) \<tau>" by(simp)

lemmas cp_dot_nextI [simp, intro!]= 
       cp_dot_next[THEN allI[THEN allI], of "\<lambda> X _. X" "\<lambda> _ \<tau>. \<tau>", THEN cpI1]

lemmas cp_dot_nextI_at_pre [simp, intro!]= 
       cp_dot_next_at_pre[THEN allI[THEN allI],  
                          of "\<lambda> X _. X" "\<lambda> _ \<tau>. \<tau>", THEN cpI1]

lemma dot_next_nullstrict [simp]: "(null).next = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def)

lemma dot_next_at_pre_nullstrict [simp] : "(null).next@pre = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def)

lemma dot_next_strict[simp] : "(invalid).next = invalid" 
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def)

lemma dot_next_strict'[simp] : "(null).next = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def)


lemma dot_nextATpre_strict[simp] : "(invalid).next@pre = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def)

lemma dot_nextATpre_strict'[simp] : "(null).next@pre = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def)


subsection{* Casts *}

consts oclastype\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t :: "'\<alpha> \<Rightarrow> Object" ("(_) .oclAsType'(Object')")
consts oclastype\<^isub>n\<^isub>o\<^isub>d\<^isub>e   :: "'\<alpha> \<Rightarrow> Node" ("(_) .oclAsType'(Node')")

defs (overloaded) oclastype\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_Object: 
        "(X::Object) .oclAsType(Object) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> invalid \<tau>   (* to avoid: null .oclAsType(Object) = null ? *)
                            | \<lfloor>\<lfloor>mk\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t oid a \<rfloor>\<rfloor> \<Rightarrow>  \<lfloor>\<lfloor>mk\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t oid a \<rfloor>\<rfloor>)"  (* identity *)

defs (overloaded) oclastype\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_Node:  
        "(X::Node) .oclAsType(Object) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> invalid \<tau>    (* OTHER POSSIBILITY : null ??? Really excluded 
                                                     by standard *)
                            | \<lfloor>\<lfloor>mk\<^isub>n\<^isub>o\<^isub>d\<^isub>e oid a b \<rfloor>\<rfloor> \<Rightarrow>  \<lfloor>\<lfloor>  (mk\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t oid \<lfloor>(a,b)\<rfloor>) \<rfloor>\<rfloor>)"

defs (overloaded) oclastype\<^isub>n\<^isub>o\<^isub>d\<^isub>e_Object: 
        "(X::Object) .oclAsType(Node) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> invalid \<tau>   
                            | \<lfloor>\<lfloor>mk\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t oid \<bottom> \<rfloor>\<rfloor> \<Rightarrow>  invalid \<tau>   (* down-cast exception *)
                            | \<lfloor>\<lfloor>mk\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t oid \<lfloor>(a,b)\<rfloor> \<rfloor>\<rfloor> \<Rightarrow>  \<lfloor>\<lfloor>mk\<^isub>n\<^isub>o\<^isub>d\<^isub>e oid a b \<rfloor>\<rfloor>)" 

defs (overloaded) oclastype\<^isub>n\<^isub>o\<^isub>d\<^isub>e_Node: 
        "(X::Node) .oclAsType(Node) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> invalid \<tau>   (* to avoid: null .oclAsType(Object) = null ? *)
                            | \<lfloor>\<lfloor>mk\<^isub>n\<^isub>o\<^isub>d\<^isub>e oid a b \<rfloor>\<rfloor> \<Rightarrow>  \<lfloor>\<lfloor>mk\<^isub>n\<^isub>o\<^isub>d\<^isub>e oid a b\<rfloor>\<rfloor>)"  (* identity *)

lemma oclastype\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_Object_strict[simp] : "(invalid::Object) .oclAsType(Object) = invalid" 
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclastype\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_Object)

lemma oclastype\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_Object_nullstrict[simp] : "(null::Object) .oclAsType(Object) = invalid" 
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclastype\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_Object)

lemma oclastype\<^isub>n\<^isub>o\<^isub>d\<^isub>e_Object_strict[simp] : "(invalid::Node) .oclAsType(Object) = invalid" 
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclastype\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_Node bot_Boolean_def)

lemma oclastype\<^isub>n\<^isub>o\<^isub>d\<^isub>e_Object_nullstrict[simp] : "(null::Node) .oclAsType(Object) = invalid" 
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclastype\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_Node)


section{* Tests for Actual Types *}

consts oclistypeof\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t :: "'\<alpha> \<Rightarrow> Boolean" ("(_).oclIsTypeOf'(Object')")
consts oclistypeof\<^isub>n\<^isub>o\<^isub>d\<^isub>e   :: "'\<alpha> \<Rightarrow> Boolean" ("(_).oclIsTypeOf'(Node')")

defs (overloaded) oclistypeof\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_Object: 
        "(X::Object) .oclIsTypeOf(Object) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> invalid \<tau>  
                            | \<lfloor>\<lfloor>mk\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t oid \<bottom> \<rfloor>\<rfloor> \<Rightarrow> true \<tau>
                            | \<lfloor>\<lfloor>mk\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t oid \<lfloor>_\<rfloor> \<rfloor>\<rfloor> \<Rightarrow> false \<tau>)" 

defs (overloaded) oclistypeof\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_Node: 
        "(X::Node) .oclIsTypeOf(Object) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> invalid \<tau>  
                            | \<lfloor>\<lfloor> _ \<rfloor>\<rfloor> \<Rightarrow> false \<tau>)"  (* must have actual type Node otherwise  *)

defs (overloaded) oclistypeof\<^isub>n\<^isub>o\<^isub>d\<^isub>e_Object: 
        "(X::Object) .oclIsTypeOf(Node) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> invalid \<tau>  
                            | \<lfloor>\<lfloor>mk\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t oid \<bottom> \<rfloor>\<rfloor> \<Rightarrow> false \<tau>
                            | \<lfloor>\<lfloor>mk\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t oid \<lfloor>_\<rfloor> \<rfloor>\<rfloor> \<Rightarrow> true \<tau>)" 

defs (overloaded) oclistypeof\<^isub>n\<^isub>o\<^isub>d\<^isub>e_Node: 
        "(X::Node) .oclIsTypeOf(Node) \<equiv> 
                   (\<lambda>\<tau>. case X \<tau> of 
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> invalid \<tau>  
                            | \<lfloor>\<lfloor> _ \<rfloor>\<rfloor> \<Rightarrow> true \<tau>)"  (* must have actual type Node otherwise  *)

(* TODO: Missing cp's.*)

   
lemma oclistypeof\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_Object_strict1[simp]: 
     "(invalid::Object) .oclIsTypeOf(Object) = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclistypeof\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_Object)
lemma oclistypeof\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_Object_strict2[simp]: 
     "(null::Object) .oclIsTypeOf(Object) = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclistypeof\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_Object)
lemma oclistypeof\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_Node_strict1[simp]: 
     "(invalid::Node) .oclIsTypeOf(Object) = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclistypeof\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_Node)
lemma oclistypeof\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_Node_strict2[simp]: 
     "(null::Node) .oclIsTypeOf(Object) = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclistypeof\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_Node)
lemma oclistypeof\<^isub>n\<^isub>o\<^isub>d\<^isub>e_Object_strict1[simp]: 
     "(invalid::Object) .oclIsTypeOf(Node) = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclistypeof\<^isub>n\<^isub>o\<^isub>d\<^isub>e_Object)
lemma oclistypeof\<^isub>n\<^isub>o\<^isub>d\<^isub>e_Object_strict2[simp]: 
     "(null::Object) .oclIsTypeOf(Node) = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclistypeof\<^isub>n\<^isub>o\<^isub>d\<^isub>e_Object)
lemma oclistypeof\<^isub>n\<^isub>o\<^isub>d\<^isub>e_Node_strict1[simp]: 
     "(invalid::Node) .oclIsTypeOf(Node) = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclistypeof\<^isub>n\<^isub>o\<^isub>d\<^isub>e_Node)
lemma oclistypeof\<^isub>n\<^isub>o\<^isub>d\<^isub>e_Node_strict2[simp]: 
     "(null::Node) .oclIsTypeOf(Node) = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       oclistypeof\<^isub>n\<^isub>o\<^isub>d\<^isub>e_Node)



lemma actualType_larger_staticType:
assumes isdef: "\<tau> \<Turnstile> (\<delta> X)"
shows          "\<tau> \<Turnstile> (X::Node) .oclIsTypeOf(Object) \<triangleq> false"
using isdef
by(auto simp : bot_fun_def null_fun_def null_option_def bot_option_def null_def invalid_def
                  oclistypeof\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_Node foundation22 foundation16
           split: option.split object.split node.split)

lemma down_cast: 
assumes isObject: "\<tau> \<Turnstile> (X::Object) .oclIsTypeOf(Object)"
shows             "\<tau> \<Turnstile> (X .oclAsType(Node)) \<triangleq> invalid" 
using isObject
apply(auto simp : bot_fun_def null_fun_def null_option_def bot_option_def null_def invalid_def
                  oclastype\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_Node oclastype\<^isub>n\<^isub>o\<^isub>d\<^isub>e_Object foundation22 foundation16
           split: option.split object.split node.split)
by(simp add: oclistypeof\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_Object  OclValid_def false_def true_def)

lemma up_down_cast : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> X)"
shows "\<tau> \<Turnstile> ((X::Node) .oclAsType(Object) .oclAsType(Node) \<triangleq> X)" 
using isdef
by(auto simp : null_fun_def null_option_def bot_option_def null_def invalid_def
               oclastype\<^isub>o\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_Node oclastype\<^isub>n\<^isub>o\<^isub>d\<^isub>e_Object foundation22 foundation16
        split: option.split node.split)

(* MISSING:  Construction for  ocliskind *)


section{* Standard State Infrastructure *}
text{* These definitions should be generated --- again --- from the class diagram. *}

section{* Invariant *}
text{* These recursive predicates can be defined conservatively 
by greatest fix-point constructions - automatically. See HOL-OCL Book
for details. For the purpose of this example, we state them as axioms
here.*}
axiomatization inv_Node :: "Node \<Rightarrow> Boolean"
where A : "(\<tau> \<Turnstile> (\<delta> self)) \<longrightarrow> 
               (\<tau> \<Turnstile> inv_Node(self)) =
                   ((\<tau> \<Turnstile> (self .next \<doteq> null)) \<or> 
                    ( \<tau> \<Turnstile> (self .next <> null) \<and> (\<tau> \<Turnstile> (self .next .i \<prec> self .i))  \<and> 
                     (\<tau> \<Turnstile> (inv_Node(self .next))))) "


axiomatization inv_Node_at_pre :: "Node \<Rightarrow> Boolean"
where B : "(\<tau> \<Turnstile> (\<delta> self)) \<longrightarrow> 
               (\<tau> \<Turnstile> inv_Node_at_pre(self)) =
                   ((\<tau> \<Turnstile> (self .next@pre \<doteq> null)) \<or> 
                    ( \<tau> \<Turnstile> (self .next@pre <> null) \<and> (\<tau> \<Turnstile> (self .next@pre .i@pre \<prec> self .i@pre))  \<and> 
                     (\<tau> \<Turnstile> (inv_Node_at_pre(self .next@pre))))) "

text{* A very first attempt to characterize the axiomatization by an inductive
definition - this can not be the last word since too weak (should be equality!) *}
coinductive inv :: "Node \<Rightarrow> (\<AA>)st \<Rightarrow> bool" where 
 "(\<tau> \<Turnstile> (\<delta> self)) \<Longrightarrow> ((\<tau> \<Turnstile> (self .next \<doteq> null)) \<or> 
                      (\<tau> \<Turnstile> (self .next <> null) \<and> (\<tau> \<Turnstile> (self .next .i \<prec> self .i))  \<and> 
                     ( (inv(self .next))\<tau> )))
                     \<Longrightarrow> ( inv self \<tau>)"


section{* The contract of a recursive query : *}
text{* The original specification of a recursive query :
\begin{verbatim}
context Node::contents():Set(Integer)
post:  result = if self.next = null 
                then Set{i}
                else self.next.contents()->including(i)
                endif
\end{verbatim} *}


consts dot_contents :: "Node \<Rightarrow> Set_Integer"  ("(1(_).contents'('))" 50)
 
axiomatization dot_contents_def where
"(\<tau> \<Turnstile> ((self).contents() \<triangleq> result)) =
 (if (\<delta> self) \<tau> = true \<tau> 
  then ((\<tau> \<Turnstile> true) \<and>  
        (\<tau> \<Turnstile> (result \<triangleq> if (self .next \<doteq> null) 
                        then (Set{self .i}) 
                        else (self .next .contents()->including(self .i))
                        endif)))
  else \<tau> \<Turnstile> result \<triangleq> invalid)"


consts dot_contents_AT_pre :: "Node \<Rightarrow> Set_Integer"  ("(1(_).contents@pre'('))" 50)
 
axiomatization where dot_contents_AT_pre_def:
"(\<tau> \<Turnstile> (self).contents@pre() \<triangleq> result) =
 (if (\<delta> self) \<tau> = true \<tau> 
  then \<tau> \<Turnstile> true \<and>                                (* pre *)
        \<tau> \<Turnstile> (result \<triangleq> if (self).next@pre \<doteq> null  (* post *)
                        then Set{(self).i@pre}
                        else (self).next@pre .contents@pre()->including(self .i@pre)
                        endif)
  else \<tau> \<Turnstile> result \<triangleq> invalid)"

text{* Note that these @pre variants on methods are only available on queries, i.e.
operations without side-effect. *}
(* TODO: Should be rephased by conservative means... *)

(* Missing: Properties on Casts, type-tests, and equality vs. projections. *)

section{* The contract of a method. *}
text{*
The specification in high-level OCL input syntax reads as follows:
\begin{verbatim}
context Node::insert(x:Integer) 
post: contents():Set(Integer)
contents() = contents@pre()->including(x)
\end{verbatim}
*}

consts dot_insert :: "Node \<Rightarrow> Integer \<Rightarrow> Void"  ("(1(_).insert'(_'))" 50)

axiomatization where dot_insert_def:
"(\<tau> \<Turnstile> ((self).insert(x) \<triangleq> result)) =
 (if (\<delta> self) \<tau> = true \<tau> \<and> (\<upsilon> x) \<tau> = true \<tau>  
  then \<tau> \<Turnstile> true \<and>  
       \<tau> \<Turnstile> ((self).contents() \<triangleq> (self).contents@pre()->including(x))
  else \<tau> \<Turnstile> ((self).insert(x) \<triangleq> invalid))"

(*
lemma H : "(\<tau> \<Turnstile> (self).insert(x) \<triangleq> result)"
 nitpick
thm dot_insert_def
oops
takes too long...
*) 
(* Old stuff by Matthias Diss - will not really work any longer in this context: 

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
*)

end
