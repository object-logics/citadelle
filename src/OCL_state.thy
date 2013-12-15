(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_state.thy --- State Operations and Objects.
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

header{* Formalization III:  State Operations and Objects *}

theory OCL_state
imports OCL_lib
begin

section{* Introduction: States over Typed Object Universes *}
text{* As mentioned earlier, 
the OCL is composed of
 \begin{enumerate}
 \item operators on built-in data structures such as Boolean, Integer or Set(\_),
 \item operators of the user-defined data model such as accessors,
   type casts and tests, and
 \item user-defined, side-effect-free methods.
 \end{enumerate}
*}

text{* In the following, we will refine the concepts of a user-defined
data-model (implied by a class-diagram) as well as 
the notion of $\state{}$ used in the
previous section to much more detail.  In contrast to wide-spread
opinions, UML class diagrams represent in a compact and visual manner
quite complex, object-oriented data-types with a surprisingly rich
theory. It is part of our endeavor here to make this theory explicit
and to point out corner cases.  A UML class diagram---underlying a
given OCL formula---produces a number of implicit operations which
become accessible via appropriate OCL syntax:
*}

text{*
\begin{enumerate}
\item Classes and class names (written as $C_1$, \ldots, $C_n$), which
  become types of data in OCL\@. Class names declare two projector
  functions to the set of all objects in a state:
  $C_i$\inlineocl{.allInstances()} and
  $C_i$\inlineocl{.allInstances}$\isasymOclATpre$\inlineocl{()},
\item an inheritance relation $\_ < \_$ on classes and a collection of
  attributes $A$ associated to classes,
\item two families of accessors; for each attribute $a$ in a
  class definition (denoted
  $\getAttrib{X}{\text{$a$}}               :: C_i \rightarrow A $ and
  $\getAttrib{X}{\text{$a$}\isasymOclATpre}:: C_i \rightarrow A $ for
  $A\in \{\V{}{\up{\ldots}}, C_1, \ldots, C_n\}$),
\item type casts that can change the static type of an object of a
      class ($\getAttrib{X}{\mocl{oclAsType(}\text{$C_i$}\mocl{)}}$ of type
      $C_j \rightarrow C_i$)
\item two dynamic type tests ($\getAttrib{X}{\mocl{oclIsTypeOf(}\text{$C_i$}\mocl{)}}$ and
      $\getAttrib{X}{\mocl{oclIsKindOf(}\text{$C_i$}\mocl{)}}$ ),
\item and last but not least, for each class name $C_i$ there is an
  instance of the overloaded referential equality (written $\_
  \isasymMathOclStrictEq \_$).
\end{enumerate}
*}

text{* Assuming a strong static type discipline in the sense of
Hindley-Milner types, Featherweight OCL has no ``syntactic subtyping''.
 This does not mean that subtyping can not be expressed
\emph{semantically} in Featherweight OCL; by giving a formal
semantics to type-casts, subtyping becomes an issue of the front-end
that can make implicit type-coersions explicit by introducing explicit
type-casts. Our perspective shifts the emphasis on the semantic
properties of casting, and the necessary universe of object 
representations (induced by a class model) that allows to esthablish them.
*}

subsection{* Onject Universes *}
text{*
It is natural to construct system states by a set of partial functions
$f$ that map object identifiers $\oid$ to some representations of
objects:
\begin{gather}
       \typedef \qquad \alpha~\state{} \defeq \{ \sigma :: 
        \oid \isasymrightharpoonup \alpha \ap|\ap \inv_\sigma(\sigma) \}
\end{gather}
where $\inv_\sigma$ is a to be discussed invariant on states. 
*}

text{*
The key
point is that we need a common type $\alpha$ for the set of all
possible \emph{object representations}.  Object representations model
``a piece of typed memory,'' \ie, a kind of record comprising
administration information and the information for all attributes of
an object; here, the primitive types as well as collections over them
are stored directly in the object representations, class types and
collections over them are represented by $\oid$'s (respectively lifted
collections over them).
*}

text{*
In a shallow embedding which must represent
UML types injectively by HOL types, there are two fundamentally
different ways to construct such a set of object representations,
which we call an \emph{object universe} $\mathfrak{A}$:
\begin{enumerate}
\item an object universe can be constructed for a given class model,
  leading to \emph{closed world semantics}, and
\item an object universe can be constructed for a given class model
  \emph{and all its extensions by new classes added into the leaves of
    the class hierarchy}, leading to an \emph{open world semantics}.
\end{enumerate}
For the sake of simplicity, we chose the first option for
Featherweight OCL, while \holocl~\cite{brucker.ea:extensible:2008-b}
used an involved construction allowing the latter.

*}

text{*
A na\"ive attempt to construct $\mathfrak{A}$ would look like this:
the class type $C_i$ induced by a class will be the type of such an
object representation: $C_i \defeq (\oid \times A_{i_1} \times \cdots
\times A_{i_k} )$ where the types $A_{i_1}$, \ldots, $A_{i_k}$ are the
attribute types (including inherited attributes) with class types
substituted by $\oid$. The function $\HolOclOidOf$ projects the first
component, the $\oid$, out of an object representation. Then the
object universe will be constructed by the type definition:
*}

text{*
$\mathfrak{A} := C_1 + \cdots +  C_n$.
*}

text{*
It is possible to define constructors, accessors, and the referential
equality on this object universe. However, the treatment of type casts
and type tests cannot be faithful with common object-oriented
semantics, be it in UML or Java: casting up along the class hierarchy
can only be implemented by loosing information, such that casting up
and casting down will \emph{not} give the required identity:
*}

text{*
\begin{gather}
        X.\mocl{oclIsTypeOf(}C_k\mocl{)} ~ ~  \mocl{implies} ~ ~ X\mocl{.oclAsType(}C_i\mocl{)}\mocl{.oclAsType(}C_k\mocl{)} \isasymMathOclStrictEq
   X \\
   \qquad \qquad  \qquad \qquad  \qquad \qquad \text{whenever $C_k  < C_i$ and $X$ is valid.}
\end{gather}
*}

text{*
To overcome this limitation, we introduce an auxiliary type
$C_{i\text{ext}}$ for \emph{class type extension}; together, they were
inductively defined for a given class diagram:
*}

text{*
Let $C_i$ be a class with a possibly empty set of subclasses
$\{C_{j_{1}}, \ldots, C_{j_{m}}\}$.
\begin{itemize}
\item Then the  \emph{class type extension} $C_{i\text{ext}}$
        associated to $C_i$ is
        $A_{i_{1}} \times \cdots \times A_{i_{n}} \times \up{(C_{j_{1}\text{ext}} + \cdots + C_{j_{m}\text{ext}})}$
        where $A_{i_{k}}$ ranges over the local
        attribute types of $C_i$ and $C_{j_{l}\text{ext}}$
        ranges over all class type extensions of the subclass $C_{j}$ of $C_i$.
\item Then the \emph{class type} for $C_i$ is
        $oid \times A_{i_{1}} \times \cdots \times A_{i_{n}} \times \up{(C_{j_{1}\text{ext}} + \cdots + C_{j_{m}\text{ext}})}$
        where $A_{i_{k}}$ ranges over the inherited \emph{and} local
        attribute types of $C_i$ and $C_{j_{l}\text{ext}}$
        ranges over all class type extensions of the subclass $C_{j}$ of $C_i$.
\end{itemize}
*}

text{*
This construction can \emph{not} be done in HOL itself since it
involves quantifications and iterations over the ``set of class-types'';
rather, it is a meta-level construction.  Technically, this means that
we need a compiler to be done in SML on the syntactic
``meta-model''-level of a class model.
*}

text{* With respect to our semantic construction here, 
which above all means is intended to be type-safe, this has the following consequences:
\begin{itemize}
\item there is a generic theory of states, which must be formulated independently
      from a concete object universe, 
\item there is a principle of translation (captured by the inductive scheme for
      class type extensions and class types above) that converts a given class model
      into an concrete object universe, 
\item there are fixed principles that allow to derive the semantic theory of any
      concrete object universe, called the \emph{object-oriented data type theory.}
\end{itemize}
We will work out concrete examples for the construction of the object-universes in
\autoref{PartIV} and \autoref{PartV} and the derivation of the
respective data type theories. While an automatization is clearly possible and
desirable for concrete applications of FeatherweightOCL, we consider this
out of the scope of this paper which has a focus on the semantic construction and its presentation.
*}


subsection{* Recall: The generic structure of States *}

text{* Next we will introduce the foundational concept of an object id (oid),
which is just some infinite set.

\begin{isar}
type_synonym oid = nat
\end{isar}

 States are pair of a partial map from oid's to elements of an object universe @{text "'\<AA>"}
--- the heap --- and a map to relations of objects. The relations were encoded as lists of
pairs in order to leave the possibility to have Bags, OrderedSets or Sequences as association
ends.  *}
text{* Recall:
\begin{isar}
record ('\<AA>)state =
             heap   :: "oid \<rightharpoonup> '\<AA> "
             assocs :: "oid  \<rightharpoonup> (oid \<times> oid) list"


type_synonym ('\<AA>)st = "'\<AA> state \<times> '\<AA> state"
\end{isar}

Now we refine our state-interface.
In certain contexts, we will require that the elements of the object universe have
a particular structure; more precisely, we will require that there is a function that
reconstructs the oid of an object in the state (we will settle the question how to define
this function later). *}

class object =  fixes oid_of :: "'a \<Rightarrow> oid"

text{* Thus, if needed, we can constrain the object universe to objects by adding
the following type class constraint:*}
typ "'\<AA> :: object"

instantiation   option  :: (object)object
begin
   definition oid_of_option_def: "oid_of x = oid_of (the x)"
   instance ..
end

section{* Fundamental Predicates on Object: Strict Equality *}
subsection{* Definition *}

text{* Generic referential equality - to be used for instantiations
 with concrete object types ... *}
definition  StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t :: "('\<AA>,'a::{object,null})val \<Rightarrow> ('\<AA>,'a)val \<Rightarrow> ('\<AA>)Boolean"
where      "StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y
            \<equiv> \<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                    then if x \<tau> = null \<or> y \<tau> = null
                         then \<lfloor>\<lfloor>x \<tau> = null \<and> y \<tau> = null\<rfloor>\<rfloor>
                         else \<lfloor>\<lfloor>(oid_of (x \<tau>)) = (oid_of (y \<tau>)) \<rfloor>\<rfloor>
                    else invalid \<tau>"

subsection{* Logic and Algebraic Layer on Object *}
subsubsection{* Validity and Definedness Properties *}

text{* We derive the usual laws on definedness for (generic) object equality:*}
lemma StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_defargs:
"\<tau> \<Turnstile> (StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x (y::('\<AA>,'a::{null,object})val))\<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<and> (\<tau> \<Turnstile>(\<upsilon> y))"
by(simp add: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def OclValid_def true_def invalid_def bot_option_def
        split: bool.split_asm HOL.split_if_asm)


subsubsection{* Symmetry *}

lemma StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym : assumes x_val : "\<tau> \<Turnstile> \<upsilon> x" shows "\<tau> \<Turnstile> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x x"
by(simp add: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def true_def OclValid_def x_val[simplified OclValid_def])

subsubsection{* Execution with invalid or null as argument *}

lemma StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_strict1[simp,code_unfold] :
"(StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x invalid) = invalid"
by(rule ext, simp add: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def true_def false_def)

lemma StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_strict2[simp,code_unfold] :
"(StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t invalid x) = invalid"
by(rule ext, simp add: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def true_def false_def)

subsubsection{* Context Passing *}

lemma cp_StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t:
"(StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y \<tau>) = (StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t (\<lambda>_. x \<tau>) (\<lambda>_. y \<tau>)) \<tau>"
by(auto simp: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def cp_valid[symmetric])

lemmas cp_intro''[intro!,simp,code_unfold] =
       cp_intro''
       cp_StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t[THEN allI[THEN allI[THEN allI[THEN cpI2]],
             of "StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t"]]

subsubsection{* Behavior vs StrongEq *}

text{*
It remains to clarify the role of the state invariant
$\inv_\sigma(\sigma)$ mentioned above that states the condition that
there is a ``one-to-one'' correspondence between object
representations and $\oid$'s: $\forall \mathit{oid} \in \dom\ap
\sigma\spot oid = \HolOclOidOf\ap \drop{\sigma(\mathit{oid})}$.  This
condition is also mentioned in~\cite[Annex A]{omg:ocl:2012} and goes
back to \citet{richters:precise:2002}; however, we state this
condition as an invariant on states rather than a global axiom. It
can, therefore, not be taken for granted that an $\oid$ makes sense
both in pre- and post-states of OCL expressions.
*}

text{* We capture this invariant in the predicate WFF :*}

definition WFF :: "('\<AA>::object)st \<Rightarrow> bool"
where "WFF \<tau> = ((\<forall> x \<in> ran(heap(fst \<tau>)). \<lceil>heap(fst \<tau>) (oid_of x)\<rceil> = x) \<and>
                (\<forall> x \<in> ran(heap(snd \<tau>)). \<lceil>heap(snd \<tau>) (oid_of x)\<rceil> = x))"

text{* It turns out that \verb+WFF+ is a key-concept for linking strict referential equality to
logical equality: in well-formed states (i.e. those states where the self (oid-of) field contains 
the pointer to which the object is associated to in the state), referential equality coincides 
with logical equality. *}

                
text{* We turn now to the generic definition of referential equality on objects:
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

theorem StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_vs_StrongEq:
assumes WFF: "WFF \<tau>"
and valid_x: "\<tau> \<Turnstile>(\<upsilon> x)"
and valid_y: "\<tau> \<Turnstile>(\<upsilon> y)"
and x_presented_pre: "x \<tau> \<in> ran (heap(fst \<tau>))"
and y_presented_pre: "y \<tau> \<in> ran (heap(fst \<tau>))"
and x_presented_post:"x \<tau> \<in> ran (heap(snd \<tau>))"
and y_presented_post:"y \<tau> \<in> ran (heap(snd \<tau>))"
 (* x and y must be object representations that exist in either the pre or post state *)
shows "(\<tau> \<Turnstile> (StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y)) = (\<tau> \<Turnstile> (x \<triangleq> y))"
apply(insert WFF valid_x valid_y x_presented_pre y_presented_pre x_presented_post y_presented_post)
apply(auto simp: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def OclValid_def WFF_def StrongEq_def true_def Ball_def)
apply(erule_tac x="x \<tau>" in allE', simp_all)
done

text{* So, if two object descriptions live in the same state (both pre or post), the referential
equality on objects implies in a WFF state the logical equality. Uffz. *}

section{* Operations on Object *}
subsection{* Initial States (for Testing and Code Generation) *}

definition \<tau>\<^sub>0 :: "('\<AA>)st"
where     "\<tau>\<^sub>0 \<equiv> (\<lparr>heap=Map.empty, assocs\<^sub>2= Map.empty, assocs\<^sub>3= Map.empty\<rparr>,
                 \<lparr>heap=Map.empty, assocs\<^sub>2= Map.empty, assocs\<^sub>3= Map.empty\<rparr>)"

subsection{* OclAllInstances *}

text{* In order to denote OCL-types occuring in OCL expressions syntactically --- as, for example,
as "argument" of allInstances --- we use the inverses of the injection functions into the object
universes; we show that this is sufficient "characterization". *}

definition OclAllInstances_generic :: "(('\<AA>::object) st \<Rightarrow> '\<AA> state) \<Rightarrow> ('\<AA>::object \<rightharpoonup> '\<alpha>) \<Rightarrow> 
                                       ('\<AA>, '\<alpha> option option) Set"
where [simp]: "OclAllInstances_generic fst_snd H =  
                    (\<lambda>\<tau>. Abs_Set_0 \<lfloor>\<lfloor> Some ` ((H ` ran (heap (fst_snd \<tau>))) - { None }) \<rfloor>\<rfloor>)"


definition OclAllInstances_at_post :: "('\<AA> :: object \<rightharpoonup> '\<alpha>) \<Rightarrow> ('\<AA>, '\<alpha> option option) Set"
                           ("_ .allInstances'(')")
where  "OclAllInstances_at_post H =  OclAllInstances_generic snd H "

definition OclAllInstances_at_pre :: "('\<AA> :: object \<rightharpoonup> '\<alpha>) \<Rightarrow> ('\<AA>, '\<alpha> option option) Set"
                           ("_ .allInstances@pre'(')")
where  "OclAllInstances_at_pre H = OclAllInstances_generic fst H "

lemma OclAllInstances_defined: "\<tau> \<Turnstile> \<delta> (X .allInstances())"
 apply(simp add: defined_def OclValid_def OclAllInstances_at_post_def bot_fun_def bot_Set_0_def null_fun_def null_Set_0_def false_def true_def)
 apply(rule conjI)
 apply(rule notI, subst (asm) Abs_Set_0_inject, simp)
 apply(rule disjI2)+
  apply (metis bot_option_def option.distinct(1))
 apply(simp add: bot_option_def)+

 apply(rule notI, subst (asm) Abs_Set_0_inject, simp)
 apply(rule disjI2)+
  apply (metis bot_option_def option.distinct(1))
 apply(simp add: bot_option_def null_option_def)+
done

lemma "\<tau>\<^sub>0 \<Turnstile> H .allInstances() \<triangleq> Set{}"
by(simp add: StrongEq_def OclAllInstances_at_post_def OclValid_def \<tau>\<^sub>0_def mtSet_def)


lemma "\<tau>\<^sub>0 \<Turnstile> H .allInstances@pre() \<triangleq> Set{}"
by(simp add: StrongEq_def OclAllInstances_at_pre_def OclValid_def \<tau>\<^sub>0_def mtSet_def)

lemma state_update_vs_allInstances_empty:
shows   "(Type .allInstances())
         (\<sigma>, \<lparr>heap=empty, assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)
         =
         Set{}
         (\<sigma>, \<lparr>heap=empty, assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)"
by(simp add: OclAllInstances_at_post_def mtSet_def)

lemma state_update_vs_allInstances_including':
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
    and "Type Object \<noteq> None"
  shows "(Type .allInstances())
         (\<sigma>, \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)
         =
         ((Type .allInstances())->including(\<lambda> _. \<lfloor>\<lfloor> drop (Type Object) \<rfloor>\<rfloor>))
         (\<sigma>, \<lparr>heap=\<sigma>',assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)"
proof -
 have allinst_def : "(\<sigma>, \<lparr>heap = \<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>) \<Turnstile> (\<delta> (Type .allInstances()))"
  apply(simp add: defined_def OclValid_def bot_fun_def null_fun_def bot_Set_0_def null_Set_0_def OclAllInstances_at_post_def)
  apply(subst (1 2) Abs_Set_0_inject)
 by(simp add: bot_option_def null_option_def)+

 have drop_none : "\<And>x. x \<noteq> None \<Longrightarrow> \<lfloor>\<lceil>x\<rceil>\<rfloor> = x"
 by(case_tac x, simp+)

 have insert_diff : "\<And>x S. insert \<lfloor>x\<rfloor> (S - {None}) = (insert \<lfloor>x\<rfloor> S) - {None}"
 by (metis insert_Diff_if option.distinct(1) singletonE)

 show ?thesis
  apply(simp add: OclIncluding_def allinst_def[simplified OclValid_def],
       simp add: OclAllInstances_at_post_def)
  apply(subst Abs_Set_0_inverse, simp add: bot_option_def, simp add: comp_def)
  apply(subst image_insert[symmetric])
  apply(subst drop_none, simp add: assms)
  apply(case_tac "Type Object", simp add: assms, simp only:)
  apply(subst insert_diff, drule sym, simp)
  apply(subgoal_tac "ran (\<sigma>'(oid \<mapsto> Object)) = insert Object (ran \<sigma>')", simp)
  apply(case_tac "\<not> (\<exists>x. \<sigma>' oid = Some x)")
  apply(rule ran_map_upd, simp)
  apply(simp, erule exE, frule assms, simp)
  apply(subgoal_tac "Object \<in> ran \<sigma>'") prefer 2
  apply(rule ranI, simp)
  apply(subst insert_absorb, simp)
 by (metis fun_upd_apply)
qed


lemma state_update_vs_allInstances_including:
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
    and "Type Object \<noteq> None"
shows   "(Type .allInstances())
         (\<sigma>, \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)
         =
         ((\<lambda>_. (Type .allInstances()) (\<sigma>, \<lparr>heap=\<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>))->including(\<lambda> _. \<lfloor>\<lfloor> drop (Type Object) \<rfloor>\<rfloor>))
         (\<sigma>, \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)"
proof -
 have allinst_def : "(\<sigma>, \<lparr>heap = \<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>) \<Turnstile> (\<delta> (Type .allInstances()))"
  apply(simp add: defined_def OclValid_def bot_fun_def null_fun_def bot_Set_0_def null_Set_0_def OclAllInstances_at_post_def)
  apply(subst (1 2) Abs_Set_0_inject)
 by(simp add: bot_option_def null_option_def)+

 show ?thesis

  apply(subst state_update_vs_allInstances_including', (simp add: assms)+)
  apply(subst cp_OclIncluding)
  apply(simp add: OclIncluding_def)
  apply(subst (1 3) cp_defined[symmetric], simp add: allinst_def[simplified OclValid_def])

  apply(simp add: defined_def OclValid_def bot_fun_def null_fun_def bot_Set_0_def null_Set_0_def OclAllInstances_at_post_def)
  apply(subst (1 3) Abs_Set_0_inject)
 by(simp add: bot_option_def null_option_def)+
qed



lemma state_update_vs_allInstances_noincluding':
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
    and "Type Object = None"
  shows "(Type .allInstances())
         (\<sigma>, \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)
         =
         (Type .allInstances())
         (\<sigma>, \<lparr>heap=\<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)"
proof -
 have allinst_def : "(\<sigma>, \<lparr>heap = \<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>) \<Turnstile> (\<delta> (Type .allInstances()))"
  apply(simp add: defined_def OclValid_def bot_fun_def null_fun_def bot_Set_0_def null_Set_0_def OclAllInstances_at_post_def)
  apply(subst (1 2) Abs_Set_0_inject)
 by(simp add: bot_option_def null_option_def)+

 have drop_none : "\<And>x. x \<noteq> None \<Longrightarrow> \<lfloor>\<lceil>x\<rceil>\<rfloor> = x"
 by(case_tac x, simp+)

 have insert_diff : "\<And>x S. insert \<lfloor>x\<rfloor> (S - {None}) = (insert \<lfloor>x\<rfloor> S) - {None}"
 by (metis insert_Diff_if option.distinct(1) singletonE)

 show ?thesis
  apply(simp add: OclIncluding_def allinst_def[simplified OclValid_def] OclAllInstances_at_post_def)
  apply(subgoal_tac "ran (\<sigma>'(oid \<mapsto> Object)) = insert Object (ran \<sigma>')", simp add: assms)
  apply(case_tac "\<not> (\<exists>x. \<sigma>' oid = Some x)")
  apply(rule ran_map_upd, simp)
  apply(simp, erule exE, frule assms, simp)
  apply(subgoal_tac "Object \<in> ran \<sigma>'") prefer 2
  apply(rule ranI, simp)
  apply(subst insert_absorb, simp)
 by (metis fun_upd_apply)
qed


lemma state_update_vs_allInstances_noincluding:
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
    and "Type Object = None"
shows   "(Type .allInstances())
         (\<sigma>, \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)
         =
         (\<lambda>_. (Type .allInstances()) (\<sigma>, \<lparr>heap=\<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>))
         (\<sigma>, \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)"
by(subst state_update_vs_allInstances_noincluding', (simp add: assms)+)

theorem state_update_vs_allInstances:
assumes "oid\<notin>dom \<sigma>'"
and     "cp P"
shows   "((\<sigma>, \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>) \<Turnstile> (P(Type .allInstances()))) =
         ((\<sigma>, \<lparr>heap=\<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>) \<Turnstile> (P((Type .allInstances())->including(\<lambda> _. \<lfloor>\<lfloor> drop (Type Object) \<rfloor>\<rfloor>)))) "
proof -
 have P_cp : "\<And>x \<tau>. P x \<tau> = P (\<lambda>_. x \<tau>) \<tau>"
 by (metis (full_types) assms(2) cp_def)
oops

theorem state_update_vs_allInstances_at_pre:
assumes "oid\<notin>dom \<sigma>"
and     "cp P"
shows   "((\<lparr>heap=\<sigma>(oid\<mapsto>Object), assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>') \<Turnstile> (P(Type .allInstances@pre()))) =
          ((\<lparr>heap=\<sigma>, assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>') \<Turnstile> (P((Type .allInstances@pre())->including(\<lambda> _. \<lfloor>\<lfloor>drop (Type Object)\<rfloor>\<rfloor>)))) "
oops

subsection{* OclIsNew *}

definition OclIsNew:: "('\<AA>, '\<alpha>::{null,object})val \<Rightarrow> ('\<AA>)Boolean"   ("(_).oclIsNew'(')")
where "X .oclIsNew() \<equiv> (\<lambda>\<tau> . if (\<delta> X) \<tau> = true \<tau>
                              then \<lfloor>\<lfloor>oid_of (X \<tau>) \<notin> dom(heap(fst \<tau>)) \<and>
                                     oid_of (X \<tau>) \<in> dom(heap(snd \<tau>))\<rfloor>\<rfloor>
                              else invalid \<tau>)"

text{* The following predicates --- which are not part of the OCL standard descriptions ---
complete the goal of oclIsNew() by describing where an object belongs.
*}

definition OclIsDeleted:: "('\<AA>, '\<alpha>::{null,object})val \<Rightarrow> ('\<AA>)Boolean"   ("(_).oclIsDeleted'(')")
where "X .oclIsDeleted() \<equiv> (\<lambda>\<tau> . if (\<delta> X) \<tau> = true \<tau>
                              then \<lfloor>\<lfloor>oid_of (X \<tau>) \<in> dom(heap(fst \<tau>)) \<and>
                                     oid_of (X \<tau>) \<notin> dom(heap(snd \<tau>))\<rfloor>\<rfloor>
                              else invalid \<tau>)"

definition OclIsMaintained:: "('\<AA>, '\<alpha>::{null,object})val \<Rightarrow> ('\<AA>)Boolean"   ("(_).oclIsMaintained'(')")
where "X .oclIsMaintained() \<equiv> (\<lambda>\<tau> . if (\<delta> X) \<tau> = true \<tau>
                              then \<lfloor>\<lfloor>oid_of (X \<tau>) \<in> dom(heap(fst \<tau>)) \<and>
                                     oid_of (X \<tau>) \<in> dom(heap(snd \<tau>))\<rfloor>\<rfloor>
                              else invalid \<tau>)"

definition OclIsAbsent:: "('\<AA>, '\<alpha>::{null,object})val \<Rightarrow> ('\<AA>)Boolean"   ("(_).oclIsAbsent'(')")
where "X .oclIsAbsent() \<equiv> (\<lambda>\<tau> . if (\<delta> X) \<tau> = true \<tau>
                              then \<lfloor>\<lfloor>oid_of (X \<tau>) \<notin> dom(heap(fst \<tau>)) \<and>
                                     oid_of (X \<tau>) \<notin> dom(heap(snd \<tau>))\<rfloor>\<rfloor>
                              else invalid \<tau>)"

lemma state_split : "\<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<tau> \<Turnstile> (X .oclIsNew()) \<or> \<tau> \<Turnstile> (X .oclIsDeleted()) \<or> \<tau> \<Turnstile> (X .oclIsMaintained()) \<or> \<tau> \<Turnstile> (X .oclIsAbsent())"
by(simp add: OclIsDeleted_def OclIsNew_def OclIsMaintained_def OclIsAbsent_def
             OclValid_def true_def, blast)

lemma notNew_vs_others : "\<tau> \<Turnstile> \<delta> X \<Longrightarrow> (\<not> \<tau> \<Turnstile> (X .oclIsNew())) = (\<tau> \<Turnstile> (X .oclIsDeleted()) \<or> \<tau> \<Turnstile> (X .oclIsMaintained()) \<or> \<tau> \<Turnstile> (X .oclIsAbsent()))"
by(simp add: OclIsDeleted_def OclIsNew_def OclIsMaintained_def OclIsAbsent_def
                OclNot_def OclValid_def true_def, blast)

subsection{* OclIsModifiedOnly *}

text{* The following predicate --- which is not part of the OCL standard descriptions ---
provides a simple, but powerful means to describe framing conditions. For any formal
approach, be it animation of OCL contracts, test-case generation or die-hard theorem
proving, the specification of the part of a system transistion that DOES NOT CHANGE
is of premordial importance. The following operator establishes the equality between
old and new objects in the state (provided that they exist in both states), with the
exception of those objects
*}

definition OclIsModifiedOnly ::"('\<AA>::object,'\<alpha>::{null,object})Set \<Rightarrow> '\<AA> Boolean"
                        ("_->oclIsModifiedOnly'(')")
where "X->oclIsModifiedOnly() \<equiv> (\<lambda>(\<sigma>,\<sigma>').  let  X' = (oid_of ` \<lceil>\<lceil>Rep_Set_0(X(\<sigma>,\<sigma>'))\<rceil>\<rceil>);
                                                 S = ((dom (heap \<sigma>) \<inter> dom (heap \<sigma>')) - X')
                                            in if (\<delta> X) (\<sigma>,\<sigma>') = true (\<sigma>,\<sigma>') \<and> (\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0(X(\<sigma>,\<sigma>'))\<rceil>\<rceil>. x \<noteq> null)
                                               then \<lfloor>\<lfloor>\<forall> x \<in> S. (heap \<sigma>) x = (heap \<sigma>') x\<rfloor>\<rfloor>
                                               else invalid (\<sigma>,\<sigma>'))"

lemma cp_OclIsModifiedOnly : "X->oclIsModifiedOnly() \<tau> = (\<lambda>_. X \<tau>)->oclIsModifiedOnly() \<tau>"
by(simp only: OclIsModifiedOnly_def, case_tac \<tau>, simp only:, subst cp_defined, simp)

definition [simp]: "OclSelf x H fst_snd = (\<lambda>\<tau> . if (\<delta> x) \<tau> = true \<tau>
                        then if oid_of (x \<tau>) \<in> dom(heap(fst \<tau>)) \<and> oid_of (x \<tau>) \<in> dom(heap (snd \<tau>))
                             then  H \<lceil>(heap(fst_snd \<tau>))(oid_of (x \<tau>))\<rceil>
                             else invalid \<tau>
                        else invalid \<tau>)"

definition OclSelf_at_pre :: "('\<AA>::object,'\<alpha>::{null,object})val \<Rightarrow>
                      ('\<AA> \<Rightarrow> '\<alpha>) \<Rightarrow>
                      ('\<AA>::object,'\<alpha>::{null,object})val" ("(_)@pre(_)")
where "x @pre H = OclSelf x H fst"

definition OclSelf_at_post :: "('\<AA>::object,'\<alpha>::{null,object})val \<Rightarrow>
                      ('\<AA> \<Rightarrow> '\<alpha>) \<Rightarrow>
                      ('\<AA>::object,'\<alpha>::{null,object})val" ("(_)@post(_)")
where "x @post H = OclSelf x H snd"

lemma all_oid_diff:
 assumes def_x : "\<tau> \<Turnstile> \<delta> x"
 assumes def_X : "\<tau> \<Turnstile> \<delta> X"
 assumes def_X' : "\<And>x. x \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> x \<noteq> null"

 defines "P \<equiv> (\<lambda>a. not (StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x a))"
 shows "(\<tau> \<Turnstile> X->forAll(a| P a)) = (oid_of (x \<tau>) \<notin> oid_of ` \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>)"
proof -
 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)
 have discr_eq_bot1_true : "\<And>\<tau>. (\<bottom> \<tau> = true \<tau>) = False" by (metis defined3 defined_def discr_eq_false_true)
 have discr_eq_bot2_true : "\<And>\<tau>. (\<bottom> = true \<tau>) = False" by (metis bot_fun_def discr_eq_bot1_true)
 have discr_eq_null_true : "\<And>\<tau>. (null \<tau> = true \<tau>) = False" by (metis OclValid_def foundation4)

 have P_null: "\<not> (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. P (\<lambda>(_:: 'a state \<times> 'a state). x) \<tau> = null \<tau>)"
  apply(simp, rule ballI)
  apply(simp add: P_def StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def)
  apply(subst cp_OclNot, simp)
  apply(subgoal_tac "x \<tau> \<noteq> null \<and> xa \<noteq> null", simp)
  apply(simp add: OclNot_def null_fun_def null_option_def bot_option_def invalid_def)
 by (metis def_X' def_x foundation17)

 have P_bot: "\<not> (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. P (\<lambda>(_:: 'a state \<times> 'a state). x) \<tau> = \<bottom> \<tau>)"
  apply(simp, rule ballI)
  apply(simp add: P_def StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def)
  apply(subst cp_OclNot, simp)
  apply(subgoal_tac "x \<tau> \<noteq> null \<and> xa \<noteq> null", simp)
  apply(simp add: OclNot_def null_fun_def null_option_def bot_option_def bot_fun_def invalid_def)
  apply (metis OCL_core.bot_fun_def OclValid_def Set_inv_lemma def_X def_x defined_def valid_def)
 by (metis def_X' def_x foundation17)

 have not_inj : "\<And>x y. ((not x) \<tau> = (not y) \<tau>) = (x \<tau> = y \<tau>)"
 by (metis foundation21 foundation22)

 have P_false : "\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = false \<tau> \<Longrightarrow> oid_of (x \<tau>) \<in> oid_of ` \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
  apply(erule bexE, rename_tac x')
  apply(simp add: P_def)
  apply(simp only: OclNot3[symmetric], simp only: not_inj)
  apply(simp add: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def split: split_if_asm)
  apply(subgoal_tac "x \<tau> \<noteq> null \<and> x' \<noteq> null", simp)
  apply (metis (mono_tags) OCL_core.drop.simps def_x foundation17 true_def)
 by(simp add: invalid_def bot_option_def true_def)+
 
 have P_true : "\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = true \<tau> \<Longrightarrow> oid_of (x \<tau>) \<notin> oid_of ` \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
  apply(subgoal_tac "\<forall>x'\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. oid_of x' \<noteq> oid_of (x \<tau>)")
  apply (metis imageE)
  apply(rule ballI, drule_tac x = "x'" in ballE) prefer 3 apply assumption
  apply(simp add: P_def)
  apply(simp only: OclNot4[symmetric], simp only: not_inj)
  apply(simp add: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def false_def split: split_if_asm)
  apply(subgoal_tac "x \<tau> \<noteq> null \<and> x' \<noteq> null", simp)
  apply (metis def_X' def_x foundation17)
 by(simp add: invalid_def bot_option_def false_def)+

 have bool_split : "\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> null \<tau> \<Longrightarrow>
                    \<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> \<bottom> \<tau> \<Longrightarrow>
                    \<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> false \<tau> \<Longrightarrow>
                    \<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = true \<tau>"
  apply(rule ballI)
  apply(drule_tac x = x in ballE) prefer 3 apply assumption
  apply(drule_tac x = x in ballE) prefer 3 apply assumption
  apply(drule_tac x = x in ballE) prefer 3 apply assumption
  apply (metis (full_types) OCL_core.bot_fun_def OclNot4 OclValid_def foundation16 foundation18' foundation9 not_inj null_fun_def)
 by(simp_all)

 show ?thesis
  apply(simp add: OclForall_def OclValid_def)
  apply(simp_all add: discr_eq_false_true discr_eq_bot1_true discr_eq_null_true discr_eq_bot2_true)+
  apply(simp add: P_null P_bot)
  apply((rule impI)+ | (rule conjI)+)+
  apply(rule P_false, simp)
  (* *)
  apply(rule impI, simp add: def_X[simplified OclValid_def])
  apply(rule P_true)
  apply(drule bool_split)
 by simp
qed

theorem framing:
      assumes modifiesclause:"\<tau> \<Turnstile> (X->excluding(x :: ('\<AA>::object,'\<alpha>::{null,object})val))->oclIsModifiedOnly()"
      and    represented_x: "\<tau> \<Turnstile> \<delta>(x @pre (H::('\<AA> \<Rightarrow> '\<alpha>)))"
      and oid_is_typerepr : "\<tau> \<Turnstile> X->forAll(a| not (StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x a))"
      shows "\<tau> \<Turnstile> (x @pre H  \<triangleq>  (x @post H))"
proof -
 have def_x : "\<tau> \<Turnstile> \<delta> x"
 by(insert represented_x, simp add: defined_def OclValid_def null_fun_def bot_fun_def false_def true_def OclSelf_at_pre_def invalid_def split: split_if_asm)
 have def_X : "\<tau> \<Turnstile> \<delta> X"
  apply(insert oid_is_typerepr, simp add: OclForall_def OclValid_def split: split_if_asm)
 by(simp add: bot_option_def true_def)
 have def_X' : "\<And>x. x \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> x \<noteq> null"
  apply(insert modifiesclause, simp add: OclIsModifiedOnly_def OclValid_def split: split_if_asm)
  apply(case_tac \<tau>, simp split: split_if_asm)
  apply(simp add: OclExcluding_def split: split_if_asm)
  apply(subst (asm) (2) Abs_Set_0_inverse)
  apply(simp, (rule disjI2)+)
  apply (metis (hide_lams, mono_tags) Diff_iff Set_inv_lemma def_X)
  apply(simp)
  apply(erule ballE[where P = "\<lambda>x. x \<noteq> null"]) apply(assumption)
  apply(simp)
  apply (metis (hide_lams, no_types) def_x foundation17)
  apply (metis (hide_lams, no_types) OclValid_def def_X def_x OclExcluding_valid_args_valid OclExcluding_valid_args_valid'' foundation20)
 by(simp add: invalid_def bot_option_def)
 have oid_is_typerepr : "oid_of (x \<tau>) \<notin> oid_of ` \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
 by(rule all_oid_diff[THEN iffD1, OF def_x def_X def_X' oid_is_typerepr])

 show ?thesis
  apply(simp add:StrongEq_def OclValid_def true_def OclSelf_at_pre_def OclSelf_at_post_def def_x[simplified OclValid_def])
  apply(rule conjI, rule impI)
  apply(rule_tac f = "\<lambda>x. H \<lceil>x\<rceil>" in arg_cong)
  apply(insert modifiesclause[simplified OclIsModifiedOnly_def OclValid_def])
  apply(case_tac \<tau>, rename_tac \<sigma> \<sigma>', simp split: split_if_asm)
  apply(subst (asm) (2) OclExcluding_def)
  apply(drule foundation5[simplified OclValid_def true_def], simp)
  apply(subst (asm) Abs_Set_0_inverse, simp)
  apply(rule disjI2)+
  apply (metis (hide_lams, no_types) DiffD1 OclValid_def Set_inv_lemma def_x foundation16 foundation18')
  apply(simp)
  apply(erule_tac x = "oid_of (x (\<sigma>, \<sigma>'))" in ballE) apply simp+
  apply (metis (hide_lams, no_types) DiffD1 image_iff image_insert insert_Diff_single insert_absorb oid_is_typerepr)
  apply(simp add: invalid_def bot_option_def)+
 by blast
qed

lemma pre_post_new: "\<tau> \<Turnstile> (x .oclIsNew()) \<Longrightarrow> \<not> (\<tau> \<Turnstile> \<upsilon>(x @pre H1)) \<and> \<not> (\<tau> \<Turnstile> \<upsilon>(x @post H2))"
by(simp add: OclIsNew_def OclSelf_at_pre_def OclSelf_at_post_def
             OclValid_def StrongEq_def true_def false_def
             bot_option_def invalid_def bot_fun_def valid_def
      split: split_if_asm)

lemma pre_post_old: "\<tau> \<Turnstile> (x .oclIsDeleted()) \<Longrightarrow> \<not> (\<tau> \<Turnstile> \<upsilon>(x @pre H1)) \<and> \<not> (\<tau> \<Turnstile> \<upsilon>(x @post H2))"
by(simp add: OclIsDeleted_def OclSelf_at_pre_def OclSelf_at_post_def
             OclValid_def StrongEq_def true_def false_def
             bot_option_def invalid_def bot_fun_def valid_def
      split: split_if_asm)

lemma pre_post_absent: "\<tau> \<Turnstile> (x .oclIsAbsent()) \<Longrightarrow> \<not> (\<tau> \<Turnstile> \<upsilon>(x @pre H1)) \<and> \<not> (\<tau> \<Turnstile> \<upsilon>(x @post H2))"
by(simp add: OclIsAbsent_def OclSelf_at_pre_def OclSelf_at_post_def
             OclValid_def StrongEq_def true_def false_def
             bot_option_def invalid_def bot_fun_def valid_def
      split: split_if_asm)

lemma pre_post_maintained: "(\<tau> \<Turnstile> \<upsilon>(x @pre H1) \<or> \<tau> \<Turnstile> \<upsilon>(x @post H2)) \<Longrightarrow> \<tau> \<Turnstile> (x .oclIsMaintained())"
by(simp add: OclIsMaintained_def OclSelf_at_pre_def OclSelf_at_post_def
             OclValid_def StrongEq_def true_def false_def
             bot_option_def invalid_def bot_fun_def valid_def
      split: split_if_asm)

lemma pre_post_maintained': 
"\<tau> \<Turnstile> (x .oclIsMaintained()) \<Longrightarrow> (\<tau> \<Turnstile> \<upsilon>(x @pre (Some o H1)) \<and> \<tau> \<Turnstile> \<upsilon>(x @post (Some o H2)))"
by(simp add: OclIsMaintained_def OclSelf_at_pre_def OclSelf_at_post_def
             OclValid_def StrongEq_def true_def false_def
             bot_option_def invalid_def bot_fun_def valid_def
      split: split_if_asm)

lemma framing_same_state: "(\<sigma>, \<sigma>) \<Turnstile> (x @pre H  \<triangleq>  (x @post H))"
by(simp add: OclSelf_at_pre_def OclSelf_at_post_def OclValid_def StrongEq_def)

end
