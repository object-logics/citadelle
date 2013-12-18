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

subsection{* Object Universes *}
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

text{* Example instances of this scheme --- outlining a compiler ---
can be found in \autoref{chap:eam1} and  \autoref{chap:edm1}.*}

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

subsection{* Accessors on Objects and Associations. *}

text{*
Our choice to use a shallow embedding of \OCL in \HOL and, thus having
an injective mapping from \OCL types to \HOL types, results in
type-safety of Featherweight \OCL. Arguments and results of accessors
are based on type-safe object representations and \emph{not} $\oid$'s.
This implies the following scheme for an accessor:
\begin{itemize}
\item The \emph{evaluation and extraction} phase. If the argument
  evaluation results in an object representation, the $\oid$ is
  extracted, if not, exceptional cases like \inlineocl{invalid} are
  reported.
\item The \emph{dereferentiation} phase. The $\oid$ is interpreted in
  the pre- or post-state, %(depending on the suffix of accessor),
  the resulting object is casted to the expected format.  The
  exceptional case of nonexistence in this state must be treated.
\item The \emph{selection} phase. The corresponding attribute is
  extracted from the object representation.
\item The \emph{re-construction} phase.  The resulting value has to be
  embedded in the adequate \HOL type.  If an attribute has the type of
  an object (not value), it is represented by an optional (set of)
  $\oid$, which must be converted via dereferentiation in one of the
  states in order to produce an object representation again. The
  exceptional case of nonexistence in this state must be treated.
\end{itemize}
*}

text{*
The first phase directly translates into the following formalization:
\begin{multline}
  \shoveleft{\definitionS}\quad\\
  \begin{array}{rllr}
 \operatorname{eval\_extract} X\ap f = (\lambda \tau\spot \HolCase
 X\ap
 \tau \HolOf & \bottom &\Rightarrow
 \mocl{invalid}\ap\tau&\text{exception}\\
 |& \lift{\bottom} &\Rightarrow
 \mocl{invalid}\ap\tau&\text{deref. null}\\
 |& \lift{\lift{\mathit{obj}}} &\Rightarrow f\ap (\operatorname{oid\_of} \ap \mathit{obj})\ap\tau)&
  \end{array}
\end{multline}
*}


text{*
For each class $C$, we introduce the dereferentiation phase of this
form:
\begin{multline}
  \definitionS \ap
  \operatorname{deref\_oid}_C \ap \mathit{fst\_snd}\ap f\ap \mathit{oid} =
                     (\lambda \tau\spot \HolCase\ap (\operatorname{heap}\ap
                     (\mathit{fst\_snd}\ap \tau))\ap \mathit{oid}\ap
                     \HolOf\\
  \begin{array}{ll}
           \phantom{|}\ap \lift{\operatorname{in}_C obj} &\Rightarrow f\ap
                     \mathit{obj} \ap \tau\\
                     |\ap \_ &\Rightarrow \mocl{invalid}\ap \tau)
      \end{array}
   \end{multline}
*}

text{*
The operation yields undefined if the $\oid$ is uninterpretable in the
state or referencing an object representation not conforming to the
expected type.
*}
text{*
We turn to the selection phase: for each class $C$ in the class model
with at least one attribute,
and each attribute $a$ in this class,
we introduce the selection phase of this form:
\begin{gather}
  \begin{array}{rlcll}
  \definitionS \ap
    \operatorname{select}_a \ap f = (\lambda &
                  \operatorname{mk}_C \ap oid & \cdots \bottom \cdots & C_{X\text{ext}} & \Rightarrow \mocl{null}\\
                  |& \operatorname{mk}_C \ap oid & \cdots \lift{a} \cdots & C_{X\text{ext}}
                    &\Rightarrow f\ap (\lambda \ap x \ap \_\spot
                   \lift{\lift{x}})\ap a)
  \end{array}
\end{gather}
*}

text{*

This works for definitions of basic values as well as for object
references in which the $a$ is of type $\oid$.  To increase
readability, we introduce the functions:
\begin{gather}
\begin{array}{llrlr}
\qquad\qquad&\definitionS\enspace&\operatorname{in\_pre\_state}    &= \operatorname{fst} & \qquad \text{first component}\\
\qquad\qquad&\definitionS\enspace&\operatorname{in\_post\_state}   &= \operatorname{snd} & \qquad \text{second component} \\
\qquad\qquad&\definitionS\enspace&\operatorname{reconst\_basetype} &= \operatorname{id} & \qquad \text{identity function}
\end{array}
\end{gather}
*}

text{*
Let \_\inlineocl{.getBase} be an accessor of class $C$ yielding a
value of base-type $A_{base}$. Then its definition is of the form:
\begin{gather}
  \begin{array}{lll}
\definitionS&\_\mocl{.getBase} &\ofType \ap C \Rightarrow A_{base}\\
\where\enspace&X\mocl{.getBase} &= \operatorname{eval\_extract}\ap X\ap
                       (\operatorname{deref\_oid}_C\ap \operatorname{in\_post\_state}\ap\\
              &          &\quad   (\operatorname{select}_\text{getBase}\ap \operatorname{reconst\_basetype}))
                           \end{array}
\end{gather}
*}
text{*
Let \_\inlineocl{.getObject} be an accessor of class $C$ yielding a
value of object-type $A_{object}$. Then its definition is of the form:
\begin{gather}
  \begin{array}{lll}
\definitionS&\_\mocl{.getObject} &\ofType \ap C \Rightarrow A_{object}\\
\where\enspace&X\mocl{.getObject} &= \operatorname{eval\_extract}\ap X\ap
                        (\operatorname{deref\_oid}_C\ap \operatorname{in\_post\_state}\ap\\
     &                    &\quad (\operatorname{select}_\text{getObject}\ap
                          (\operatorname{deref\_oid}_C\ap\operatorname{in\_post\_state})))
                           \end{array}
\end{gather}
The variant for an accessor yielding a collection is omitted here; its
construction follows by the application of the principles of the
former two.  The respective variants
$\getAttrib{\_}{\text{$a$}\isasymOclATpre}$ were produced when
\inlineisar+in_post_state+ is replaced by
$\operatorname{in\_pre\_state}$.

*}

text{* Examples for the construction of accessors via associations can be found in 
\autoref{sec:eam-accessors}, the construction of accessors via attributes in 
\autoref{sec:edm-accessors}. The construction of casts and type tests \verb+->oclIstypeOf()+ and 
\verb+->oclIsKindOf()+ is similarly.
*}


subsection{* Recall: The generic structure of States *}

text{* Recall the foundational concept of an object id (oid),
which is just some infinite set.*}

text{* \inlineisar+type_synonym oid = nat+ *}

text{*, Further, recall that states are pair of a partial map from oid's to elements of an 
object universe @{text "'\<AA>"} --- the heap --- and a map to relations of objects. 
The relations were encoded as lists of pairs in order to leave the possibility to have Bags, 
OrderedSets or Sequences as association ends.  *}
text{* This lead to the definitions:
\begin{isar}
record ('\<AA>)state =
             heap   :: "oid \<rightharpoonup> '\<AA> "
             assocs\<^sub>2 :: "oid  \<rightharpoonup> (oid \<times> oid) list"
             assocs\<^sub>3 :: "oid  \<rightharpoonup> (oid \<times> oid \<times> oid) list"

type_synonym ('\<AA>)st = "'\<AA> state \<times> '\<AA> state"
\end{isar}
*}

text{* Now we refine our state-interface.
In certain contexts, we will require that the elements of the object universe have
a particular structure; more precisely, we will require that there is a function that
reconstructs the oid of an object in the state (we will settle the question how to define
this function later). *}

class object =  fixes oid_of :: "'a \<Rightarrow> oid"

text{* Thus, if needed, we can constrain the object universe to objects by adding
the following type class constraint:*}
typ "'\<AA> :: object"

text{* The major instance needed are instances constructed over options: So, once an object,
options of objects are also objects... *}
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

lemma StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym : 
assumes x_val : "\<tau> \<Turnstile> \<upsilon> x" 
shows "\<tau> \<Turnstile> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x x"
by(simp add: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def true_def OclValid_def
             x_val[simplified OclValid_def])

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
and x_present_pre: "x \<tau> \<in> ran (heap(fst \<tau>))"
and y_present_pre: "y \<tau> \<in> ran (heap(fst \<tau>))"
and x_present_post:"x \<tau> \<in> ran (heap(snd \<tau>))"
and y_present_post:"y \<tau> \<in> ran (heap(snd \<tau>))"
 (* x and y must be object representations that exist in either the pre or post state *)
shows "(\<tau> \<Turnstile> (StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y)) = (\<tau> \<Turnstile> (x \<triangleq> y))"
apply(insert WFF valid_x valid_y x_present_pre y_present_pre x_present_post y_present_post)
apply(auto simp: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def OclValid_def WFF_def StrongEq_def true_def Ball_def)
apply(erule_tac x="x \<tau>" in allE', simp_all)
done

theorem StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_vs_StrongEq':
assumes WFF: "WFF \<tau>"
and valid_x: "\<tau> \<Turnstile>(\<upsilon> (x :: ('\<AA>::object,'\<alpha>::{null,object})val))"
and valid_y: "\<tau> \<Turnstile>(\<upsilon> y)"
and oid_preserve: "\<And>x. H x \<noteq> \<bottom> \<Longrightarrow> oid_of (H x) = oid_of x"
and xy_together: "x \<tau> \<in> H ` ran (heap(fst \<tau>)) \<and> y \<tau> \<in> H ` ran (heap(fst \<tau>)) \<or>
                  x \<tau> \<in> H ` ran (heap(snd \<tau>)) \<and> y \<tau> \<in> H ` ran (heap(snd \<tau>))"
 (* x and y must be object representations that exist in either the pre or post state *)
shows "(\<tau> \<Turnstile> (StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y)) = (\<tau> \<Turnstile> (x \<triangleq> y))"
 apply(insert WFF valid_x valid_y xy_together)
 apply(simp add: WFF_def)
 apply(auto simp: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def OclValid_def WFF_def StrongEq_def true_def Ball_def)
by (metis foundation18' oid_preserve valid_x valid_y)+

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

subsubsection{* OclAllInstances AT POST *}

definition OclAllInstances_at_post :: "('\<AA> :: object \<rightharpoonup> '\<alpha>) \<Rightarrow> ('\<AA>, '\<alpha> option option) Set"
                           ("_ .allInstances'(')")
where  "OclAllInstances_at_post =  OclAllInstances_generic snd"

lemma OclAllInstances_at_post_defined: "\<tau> \<Turnstile> \<delta> (H .allInstances())"
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


lemma represented_at_post_objects_nonnull: 
assumes A: "\<tau> \<Turnstile> (((H::('\<AA>::object \<rightharpoonup> '\<alpha>)).allInstances()) ->includes(x))"
shows      "\<tau> \<Turnstile> not(x \<triangleq> null)"
proof -
    have B: "\<tau> \<Turnstile> \<delta> (H .allInstances())" 
         by(insert  A[THEN OCL_core.foundation6, 
                      simplified OCL_lib.OclIncludes_defined_args_valid], auto)
    have C: "\<tau> \<Turnstile> \<upsilon> x"
         by(insert  A[THEN OCL_core.foundation6, 
                      simplified OCL_lib.OclIncludes_defined_args_valid], auto)
    show ?thesis
    apply(insert A)
    apply(simp add: StrongEq_def  OclValid_def 
                    OclNot_def null_def true_def OclIncludes_def B[simplified OclValid_def] 
                                                                 C[simplified OclValid_def])
    apply(simp add:OclAllInstances_at_post_def)
    apply(erule contrapos_pn)
    apply(subst OCL_lib.Set_0.Abs_Set_0_inverse, 
          auto simp: null_fun_def null_option_def bot_option_def)
    done
qed


lemma represented_at_post_objects_defined: 
assumes A: "\<tau> \<Turnstile> (((H::('\<AA>::object \<rightharpoonup> '\<alpha>)).allInstances()) ->includes(x))"
shows      "\<tau> \<Turnstile> \<delta> (H .allInstances()) \<and> \<tau> \<Turnstile> \<delta> x"
apply(insert  A[THEN OCL_core.foundation6, 
                simplified OCL_lib.OclIncludes_defined_args_valid]) 
apply(simp add: OCL_core.foundation16 OCL_core.foundation18 invalid_def, erule conjE)
apply(insert A[THEN represented_at_post_objects_nonnull])
by(simp add: foundation24 null_fun_def)


text{* One way to establish the actual presence of an object representation in a state is:*}

lemma 
assumes A: "\<tau> \<Turnstile> H .allInstances()->includes(x)"
shows      "x \<tau> \<in> (Some o H) ` ran (heap(snd \<tau>))"
proof -
   have B: "(\<delta> H .allInstances()) \<tau> = true \<tau>" 
           by(simp add: OCL_core.OclValid_def[symmetric] OclAllInstances_at_post_defined)
   have C: "(\<upsilon> x) \<tau> = true \<tau>"  
           by(insert  A[THEN OCL_core.foundation6, 
                           simplified OCL_lib.OclIncludes_defined_args_valid], 
                 auto simp: OclValid_def)
   have F: "Rep_Set_0 (Abs_Set_0 \<lfloor>\<lfloor>Some ` (H ` ran (heap (snd \<tau>)) - {None})\<rfloor>\<rfloor>) =
            \<lfloor>\<lfloor>Some ` (H ` ran (heap (snd \<tau>)) - {None})\<rfloor>\<rfloor>" 
           by(subst OCL_lib.Set_0.Abs_Set_0_inverse,simp_all add: bot_option_def) 
   show ?thesis
    apply(insert A)
    apply(simp add: OclIncludes_def OclValid_def ran_def B C image_def true_def)
    apply(simp add: OclAllInstances_at_post_def)
    apply(simp add: F)
    apply(simp add: ran_def)
   by(fastforce)
qed


lemma state_update_vs_allInstances_at_post_empty:
shows   "(\<sigma>, \<lparr>heap=empty, assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>) \<Turnstile> Type .allInstances() \<doteq> Set{}"
proof - 
 have state_update_vs_allInstances_empty: "(Type .allInstances()) (\<sigma>, \<lparr>heap=empty, assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>) =
                                           Set{} (\<sigma>, \<lparr>heap=empty, assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)"
 by(simp add: OclAllInstances_at_post_def mtSet_def)
 show ?thesis
  apply(simp only: OclValid_def, subst cp_StrictRefEq\<^sub>S\<^sub>e\<^sub>t, simp add: state_update_vs_allInstances_empty)
  apply(simp add: OclIf_def valid_def mtSet_def defined_def bot_fun_def bot_option_def null_fun_def null_option_def invalid_def bot_Set_0_def)
 by(subst Abs_Set_0_inject, (simp add: bot_option_def)+)
qed

text{* Here comes a couple of operational rules that allow to infer the value
of \inlineisar+allInstances+ from the context $\tau$. These rules are a special-case
in the sense that they are the only rules that relate statements with \emph{different}
$\tau$'s. For that reason, new concepts like "constant contexts P" are necessary
(for which we do not elaborate an own theory for reasons of space limitations;
 in examples, we will prove resulting constraints straight forward by hand.) *}

 
lemma state_update_vs_allInstances_at_post_including':
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


lemma state_update_vs_allInstances_at_post_including:
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

  apply(subst state_update_vs_allInstances_at_post_including', (simp add: assms)+)
  apply(subst cp_OclIncluding)
  apply(simp add: OclIncluding_def)
  apply(subst (1 3) cp_defined[symmetric], simp add: allinst_def[simplified OclValid_def])

  apply(simp add: defined_def OclValid_def bot_fun_def null_fun_def bot_Set_0_def null_Set_0_def OclAllInstances_at_post_def)
  apply(subst (1 3) Abs_Set_0_inject)
 by(simp add: bot_option_def null_option_def)+
qed



lemma state_update_vs_allInstances_at_post_noincluding':
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

theorem state_update_vs_allInstances_at_post_ntc:
assumes oid_def:   "oid\<notin>dom \<sigma>'"
and  non_type_conform: "Type Object = None "
and  cp_ctxt:      "cp P"
and  const_ctxt:   "\<forall> X. \<forall>\<tau> \<tau>'. X \<tau> = X \<tau>' \<longrightarrow> P X \<tau> =  P X \<tau>' "
shows   "((\<sigma>, \<lparr>heap=\<sigma>'(oid\<mapsto>Object),assocs\<^sub>2=A,assocs\<^sub>3=B\<rparr>) \<Turnstile> (P(Type .allInstances()))) =
         ((\<sigma>, \<lparr>heap=\<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)            \<Turnstile> (P(Type .allInstances())))"
         (is "(?\<tau> \<Turnstile> P ?\<phi>) = (?\<tau>' \<Turnstile> P ?\<phi>)") 
proof -
 have P_cp  : "\<And>x \<tau>. P x \<tau> = P (\<lambda>_. x \<tau>) \<tau>" 
             by (metis (full_types) cp_ctxt cp_def) 
 have includes_const_inv: "\<And>x S \<tau> \<tau>'. (\<lambda>_. S)->including(\<lambda>_. x) \<tau> = ((\<lambda>_. S)->including(\<lambda>_. x) \<tau>')"
             by(simp add: OclIncluding_def defined_def valid_def 
                          bot_fun_def null_fun_def true_def false_def)
 have       "(?\<tau> \<Turnstile> P ?\<phi>) = (?\<tau> \<Turnstile> \<lambda>_. P ?\<phi> ?\<tau>)"
             by(subst OCL_core.cp_validity, rule refl)
 also have  "... = (?\<tau> \<Turnstile> \<lambda>_. P (\<lambda>_. ?\<phi> ?\<tau>)  ?\<tau>)"
             by(subst P_cp, rule refl)
 also have  "... = (?\<tau>' \<Turnstile> \<lambda>_. P (\<lambda>_. ?\<phi> ?\<tau>)  ?\<tau>')"
             apply(simp add: OclValid_def)
             apply(subst const_ctxt[THEN spec,of"(\<lambda>_. ?\<phi> ?\<tau>)",THEN spec,of"?\<tau>",THEN spec,of"?\<tau>'"])
             by simp+
 finally have X: "(?\<tau> \<Turnstile> P ?\<phi>) = (?\<tau>' \<Turnstile> \<lambda>_. P (\<lambda>_. ?\<phi> ?\<tau>)  ?\<tau>')"
             by simp         
 show ?thesis
 apply(subst X) apply(subst OCL_core.cp_validity[symmetric])
 apply(rule StrongEq_L_subst3[OF cp_ctxt])
 apply(simp add: OclValid_def StrongEq_def )
 apply(rule state_update_vs_allInstances_at_post_noincluding')
 by(insert oid_def, auto simp: non_type_conform)
qed

theorem state_update_vs_allInstances_at_post_tc:
assumes oid_def:   "oid\<notin>dom \<sigma>'"
and  type_conform: "Type Object \<noteq> None "
and  cp_ctxt:      "cp P"
and  const_ctxt:   "\<forall> X. \<forall>\<tau> \<tau>'. X \<tau> = X \<tau>' \<longrightarrow> P X \<tau> =  P X \<tau>' "
shows   "((\<sigma>, \<lparr>heap=\<sigma>'(oid\<mapsto>Object),assocs\<^sub>2=A,assocs\<^sub>3=B\<rparr>) \<Turnstile> (P(Type .allInstances()))) =
         ((\<sigma>, \<lparr>heap=\<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)            \<Turnstile> (P((Type .allInstances())
                                                               ->including(\<lambda> _. \<lfloor>(Type Object)\<rfloor>))))"
         (is "(?\<tau> \<Turnstile> P ?\<phi>) = (?\<tau>' \<Turnstile> P ?\<phi>')") 
                                                           
proof -
 have P_cp  : "\<And>x \<tau>. P x \<tau> = P (\<lambda>_. x \<tau>) \<tau>" 
             by (metis (full_types) cp_ctxt cp_def) 
 have includes_const_inv: "\<And>x S \<tau> \<tau>'. (\<lambda>_. S)->including(\<lambda>_. x) \<tau> = ((\<lambda>_. S)->including(\<lambda>_. x) \<tau>')"
             by(simp add: OclIncluding_def defined_def valid_def 
                          bot_fun_def null_fun_def true_def false_def)
 have       "(?\<tau> \<Turnstile> P ?\<phi>) = (?\<tau> \<Turnstile> \<lambda>_. P ?\<phi> ?\<tau>)"
             by(subst OCL_core.cp_validity, rule refl)
 also have  "... = (?\<tau> \<Turnstile> \<lambda>_. P (\<lambda>_. ?\<phi> ?\<tau>)  ?\<tau>)"
             by(subst P_cp, rule refl)
 also have  "... = (?\<tau>' \<Turnstile> \<lambda>_. P (\<lambda>_. ?\<phi> ?\<tau>)  ?\<tau>')"
             apply(simp add: OclValid_def)
             apply(subst const_ctxt[THEN spec,of"(\<lambda>_. ?\<phi> ?\<tau>)",THEN spec,of"?\<tau>",THEN spec,of"?\<tau>'"])
             by simp+
 finally have X: "(?\<tau> \<Turnstile> P ?\<phi>) = (?\<tau>' \<Turnstile> \<lambda>_. P (\<lambda>_. ?\<phi> ?\<tau>)  ?\<tau>')"
             by simp
 have        "Type .allInstances() ?\<tau> = 
              \<lambda>_. Type .allInstances() ?\<tau>'->including(\<lambda>_.\<lfloor>\<lfloor>\<lceil>Type Object\<rceil>\<rfloor>\<rfloor>) ?\<tau>"
             apply(rule state_update_vs_allInstances_at_post_including)
             by(insert oid_def, auto simp: type_conform)
 also have   "... = ((\<lambda>_. Type .allInstances() ?\<tau>')->including(\<lambda>_. (\<lambda>_.\<lfloor>\<lfloor>\<lceil>Type Object\<rceil>\<rfloor>\<rfloor>) ?\<tau>') ?\<tau>')"
             by(rule includes_const_inv)
 also have   "... = ((Type .allInstances())->including(\<lambda> _. \<lfloor>(Type Object)\<rfloor>)?\<tau>')"
             apply(subst OCL_lib.cp_OclIncluding[symmetric])
             by(insert type_conform, auto)
 finally have Y : "Type .allInstances() ?\<tau> = 
                   ((Type .allInstances())->including(\<lambda> _. \<lfloor>(Type Object)\<rfloor>) ?\<tau>')"
             by auto
 show ?thesis
      apply(subst X) apply(subst OCL_core.cp_validity[symmetric])
      apply(rule StrongEq_L_subst3[OF cp_ctxt])
      apply(simp add: OclValid_def StrongEq_def Y)
 done
qed

subsubsection{* OclAllInstances AT PRE *}

definition OclAllInstances_at_pre :: "('\<AA> :: object \<rightharpoonup> '\<alpha>) \<Rightarrow> ('\<AA>, '\<alpha> option option) Set"
                           ("_ .allInstances@pre'(')")
where  "OclAllInstances_at_pre = OclAllInstances_generic fst"

lemma OclAllInstances_at_pre_defined: "\<tau> \<Turnstile> \<delta> (H .allInstances@pre())"
 apply(simp add: defined_def OclValid_def OclAllInstances_at_pre_def bot_fun_def bot_Set_0_def null_fun_def null_Set_0_def false_def true_def)
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

lemma "\<tau>\<^sub>0 \<Turnstile> H .allInstances@pre() \<triangleq> Set{}"
by(simp add: StrongEq_def OclAllInstances_at_pre_def OclValid_def \<tau>\<^sub>0_def mtSet_def)


lemma represented_at_pre_objects_nonnull: 
assumes A: "\<tau> \<Turnstile> (((H::('\<AA>::object \<rightharpoonup> '\<alpha>)).allInstances@pre()) ->includes(x))"
shows      "\<tau> \<Turnstile> not(x \<triangleq> null)"
proof -
    have B: "\<tau> \<Turnstile> \<delta> (H .allInstances@pre())" 
         by(insert  A[THEN OCL_core.foundation6, 
                      simplified OCL_lib.OclIncludes_defined_args_valid], auto)
    have C: "\<tau> \<Turnstile> \<upsilon> x"
         by(insert  A[THEN OCL_core.foundation6, 
                      simplified OCL_lib.OclIncludes_defined_args_valid], auto)
    show ?thesis
    apply(insert A)
    apply(simp add: StrongEq_def  OclValid_def 
                    OclNot_def null_def true_def OclIncludes_def B[simplified OclValid_def] 
                                                                 C[simplified OclValid_def])
    apply(simp add:OclAllInstances_at_pre_def)
    apply(erule contrapos_pn)
    apply(subst OCL_lib.Set_0.Abs_Set_0_inverse, 
          auto simp: null_fun_def null_option_def bot_option_def)
    done
qed

lemma represented_at_pre_objects_defined: 
assumes A: "\<tau> \<Turnstile> (((H::('\<AA>::object \<rightharpoonup> '\<alpha>)).allInstances@pre()) ->includes(x))"
shows      "\<tau> \<Turnstile> \<delta> (H .allInstances@pre()) \<and> \<tau> \<Turnstile> \<delta> x"
apply(insert  A[THEN OCL_core.foundation6, 
                simplified OCL_lib.OclIncludes_defined_args_valid]) 
apply(simp add: OCL_core.foundation16 OCL_core.foundation18 invalid_def, erule conjE)
apply(insert A[THEN represented_at_pre_objects_nonnull])
by(simp add: foundation24 null_fun_def)


text{* One way to establish the actual presence of an object representation in a state is:*}

lemma 
assumes A: "\<tau> \<Turnstile> H .allInstances@pre()->includes(x)"
shows      "x \<tau> \<in> (Some o H) ` ran (heap(fst \<tau>))"
proof -
   have B: "(\<delta> H .allInstances@pre()) \<tau> = true \<tau>" 
           by(simp add: OCL_core.OclValid_def[symmetric] OclAllInstances_at_pre_defined)
   have C: "(\<upsilon> x) \<tau> = true \<tau>"  
           by(insert  A[THEN OCL_core.foundation6, 
                           simplified OCL_lib.OclIncludes_defined_args_valid], 
                 auto simp: OclValid_def)
   have F: "Rep_Set_0 (Abs_Set_0 \<lfloor>\<lfloor>Some ` (H ` ran (heap (fst \<tau>)) - {None})\<rfloor>\<rfloor>) =
            \<lfloor>\<lfloor>Some ` (H ` ran (heap (fst \<tau>)) - {None})\<rfloor>\<rfloor>" 
           by(subst OCL_lib.Set_0.Abs_Set_0_inverse,simp_all add: bot_option_def) 
   show ?thesis
    apply(insert A)
    apply(simp add: OclIncludes_def OclValid_def ran_def B C image_def true_def)
    apply(simp add: OclAllInstances_at_pre_def)
    apply(simp add: F)
    apply(simp add: ran_def)
   by(fastforce)
qed


lemma state_update_vs_allInstances_at_pre_empty:
shows   "(\<lparr>heap=empty, assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>) \<Turnstile> Type .allInstances@pre() \<doteq> Set{}"
proof - 
 have state_update_vs_allInstances_empty: "(Type .allInstances@pre()) (\<lparr>heap=empty, assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>) =
                                           Set{} (\<lparr>heap=empty, assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>)"
 by(simp add: OclAllInstances_at_pre_def mtSet_def)
 show ?thesis
  apply(simp only: OclValid_def, subst cp_StrictRefEq\<^sub>S\<^sub>e\<^sub>t, simp add: state_update_vs_allInstances_empty)
  apply(simp add: OclIf_def valid_def mtSet_def defined_def bot_fun_def bot_option_def null_fun_def null_option_def invalid_def bot_Set_0_def)
 by(subst Abs_Set_0_inject, (simp add: bot_option_def)+)
qed

lemma state_update_vs_allInstances_at_pre_including':
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
    and "Type Object \<noteq> None"
  shows "(Type .allInstances@pre())
         (\<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>)
         =
         ((Type .allInstances@pre())->including(\<lambda> _. \<lfloor>\<lfloor> drop (Type Object) \<rfloor>\<rfloor>))
         (\<lparr>heap=\<sigma>',assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>)"
proof -
 have allinst_def : "(\<lparr>heap = \<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>) \<Turnstile> (\<delta> (Type .allInstances@pre()))"
  apply(simp add: defined_def OclValid_def bot_fun_def null_fun_def bot_Set_0_def null_Set_0_def OclAllInstances_at_pre_def)
  apply(subst (1 2) Abs_Set_0_inject)
 by(simp add: bot_option_def null_option_def)+

 have drop_none : "\<And>x. x \<noteq> None \<Longrightarrow> \<lfloor>\<lceil>x\<rceil>\<rfloor> = x"
 by(case_tac x, simp+)

 have insert_diff : "\<And>x S. insert \<lfloor>x\<rfloor> (S - {None}) = (insert \<lfloor>x\<rfloor> S) - {None}"
 by (metis insert_Diff_if option.distinct(1) singletonE)

 show ?thesis
  apply(simp add: OclIncluding_def allinst_def[simplified OclValid_def],
       simp add: OclAllInstances_at_pre_def)
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


lemma state_update_vs_allInstances_at_pre_including:
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
    and "Type Object \<noteq> None"
shows   "(Type .allInstances@pre())
         (\<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>)
         =
         ((\<lambda>_. (Type .allInstances@pre()) (\<lparr>heap=\<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>))->including(\<lambda> _. \<lfloor>\<lfloor> drop (Type Object) \<rfloor>\<rfloor>))
         (\<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>)"
proof -
 have allinst_def : "(\<lparr>heap = \<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>) \<Turnstile> (\<delta> (Type .allInstances@pre()))"
  apply(simp add: defined_def OclValid_def bot_fun_def null_fun_def bot_Set_0_def null_Set_0_def OclAllInstances_at_pre_def)
  apply(subst (1 2) Abs_Set_0_inject)
 by(simp add: bot_option_def null_option_def)+

 show ?thesis

  apply(subst state_update_vs_allInstances_at_pre_including', (simp add: assms)+)
  apply(subst cp_OclIncluding)
  apply(simp add: OclIncluding_def)
  apply(subst (1 3) cp_defined[symmetric], simp add: allinst_def[simplified OclValid_def])

  apply(simp add: defined_def OclValid_def bot_fun_def null_fun_def bot_Set_0_def null_Set_0_def OclAllInstances_at_pre_def)
  apply(subst (1 3) Abs_Set_0_inject)
 by(simp add: bot_option_def null_option_def)+
qed



lemma state_update_vs_allInstances_at_pre_noincluding':
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
    and "Type Object = None"
  shows "(Type .allInstances@pre())
         (\<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>)
         =
         (Type .allInstances@pre())
         (\<lparr>heap=\<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>)"
proof -
 have allinst_def : "(\<lparr>heap = \<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>) \<Turnstile> (\<delta> (Type .allInstances@pre()))"
  apply(simp add: defined_def OclValid_def bot_fun_def null_fun_def bot_Set_0_def null_Set_0_def OclAllInstances_at_pre_def)
  apply(subst (1 2) Abs_Set_0_inject)
 by(simp add: bot_option_def null_option_def)+

 have drop_none : "\<And>x. x \<noteq> None \<Longrightarrow> \<lfloor>\<lceil>x\<rceil>\<rfloor> = x"
 by(case_tac x, simp+)

 have insert_diff : "\<And>x S. insert \<lfloor>x\<rfloor> (S - {None}) = (insert \<lfloor>x\<rfloor> S) - {None}"
 by (metis insert_Diff_if option.distinct(1) singletonE)

 show ?thesis
  apply(simp add: OclIncluding_def allinst_def[simplified OclValid_def] OclAllInstances_at_pre_def)
  apply(subgoal_tac "ran (\<sigma>'(oid \<mapsto> Object)) = insert Object (ran \<sigma>')", simp add: assms)
  apply(case_tac "\<not> (\<exists>x. \<sigma>' oid = Some x)")
  apply(rule ran_map_upd, simp)
  apply(simp, erule exE, frule assms, simp)
  apply(subgoal_tac "Object \<in> ran \<sigma>'") prefer 2
  apply(rule ranI, simp)
  apply(subst insert_absorb, simp)
 by (metis fun_upd_apply)
qed

theorem state_update_vs_allInstances_at_pre_ntc:
assumes oid_def:   "oid\<notin>dom \<sigma>'"
and  non_type_conform: "Type Object = None "
and  cp_ctxt:      "cp P"
and  const_ctxt:   "\<forall> X. \<forall>\<tau> \<tau>'. X \<tau> = X \<tau>' \<longrightarrow> P X \<tau> =  P X \<tau>' "
shows   "((\<lparr>heap=\<sigma>'(oid\<mapsto>Object),assocs\<^sub>2=A,assocs\<^sub>3=B\<rparr>, \<sigma>) \<Turnstile> (P(Type .allInstances@pre()))) =
         ((\<lparr>heap=\<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>)            \<Turnstile> (P(Type .allInstances@pre())))"
         (is "(?\<tau> \<Turnstile> P ?\<phi>) = (?\<tau>' \<Turnstile> P ?\<phi>)") 
proof -
 have P_cp  : "\<And>x \<tau>. P x \<tau> = P (\<lambda>_. x \<tau>) \<tau>" 
             by (metis (full_types) cp_ctxt cp_def) 
 have includes_const_inv: "\<And>x S \<tau> \<tau>'. (\<lambda>_. S)->including(\<lambda>_. x) \<tau> = ((\<lambda>_. S)->including(\<lambda>_. x) \<tau>')"
             by(simp add: OclIncluding_def defined_def valid_def 
                          bot_fun_def null_fun_def true_def false_def)
 have       "(?\<tau> \<Turnstile> P ?\<phi>) = (?\<tau> \<Turnstile> \<lambda>_. P ?\<phi> ?\<tau>)"
             by(subst OCL_core.cp_validity, rule refl)
 also have  "... = (?\<tau> \<Turnstile> \<lambda>_. P (\<lambda>_. ?\<phi> ?\<tau>)  ?\<tau>)"
             by(subst P_cp, rule refl)
 also have  "... = (?\<tau>' \<Turnstile> \<lambda>_. P (\<lambda>_. ?\<phi> ?\<tau>)  ?\<tau>')"
             apply(simp add: OclValid_def)
             apply(subst const_ctxt[THEN spec,of"(\<lambda>_. ?\<phi> ?\<tau>)",THEN spec,of"?\<tau>",THEN spec,of"?\<tau>'"])
             by simp+
 finally have X: "(?\<tau> \<Turnstile> P ?\<phi>) = (?\<tau>' \<Turnstile> \<lambda>_. P (\<lambda>_. ?\<phi> ?\<tau>)  ?\<tau>')"
             by simp         
 show ?thesis
 apply(subst X) apply(subst OCL_core.cp_validity[symmetric])
 apply(rule StrongEq_L_subst3[OF cp_ctxt])
 apply(simp add: OclValid_def StrongEq_def )
 apply(rule state_update_vs_allInstances_at_pre_noincluding')
 by(insert oid_def, auto simp: non_type_conform)
qed

theorem state_update_vs_allInstances_at_pre_tc:
assumes oid_def:   "oid\<notin>dom \<sigma>'"
and  type_conform: "Type Object \<noteq> None "
and  cp_ctxt:      "cp P"
and  const_ctxt:   "\<forall> X. \<forall>\<tau> \<tau>'. X \<tau> = X \<tau>' \<longrightarrow> P X \<tau> =  P X \<tau>' "
shows   "((\<lparr>heap=\<sigma>'(oid\<mapsto>Object),assocs\<^sub>2=A,assocs\<^sub>3=B\<rparr>, \<sigma>) \<Turnstile> (P(Type .allInstances@pre()))) =
         ((\<lparr>heap=\<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>)            \<Turnstile> (P((Type .allInstances@pre())
                                                               ->including(\<lambda> _. \<lfloor>(Type Object)\<rfloor>))))"
         (is "(?\<tau> \<Turnstile> P ?\<phi>) = (?\<tau>' \<Turnstile> P ?\<phi>')") 
                                                           
proof -
 have P_cp  : "\<And>x \<tau>. P x \<tau> = P (\<lambda>_. x \<tau>) \<tau>" 
             by (metis (full_types) cp_ctxt cp_def) 
 have includes_const_inv: "\<And>x S \<tau> \<tau>'. (\<lambda>_. S)->including(\<lambda>_. x) \<tau> = ((\<lambda>_. S)->including(\<lambda>_. x) \<tau>')"
             by(simp add: OclIncluding_def defined_def valid_def 
                          bot_fun_def null_fun_def true_def false_def)
 have       "(?\<tau> \<Turnstile> P ?\<phi>) = (?\<tau> \<Turnstile> \<lambda>_. P ?\<phi> ?\<tau>)"
             by(subst OCL_core.cp_validity, rule refl)
 also have  "... = (?\<tau> \<Turnstile> \<lambda>_. P (\<lambda>_. ?\<phi> ?\<tau>)  ?\<tau>)"
             by(subst P_cp, rule refl)
 also have  "... = (?\<tau>' \<Turnstile> \<lambda>_. P (\<lambda>_. ?\<phi> ?\<tau>)  ?\<tau>')"
             apply(simp add: OclValid_def)
             apply(subst const_ctxt[THEN spec,of"(\<lambda>_. ?\<phi> ?\<tau>)",THEN spec,of"?\<tau>",THEN spec,of"?\<tau>'"])
             by simp+
 finally have X: "(?\<tau> \<Turnstile> P ?\<phi>) = (?\<tau>' \<Turnstile> \<lambda>_. P (\<lambda>_. ?\<phi> ?\<tau>)  ?\<tau>')"
             by simp
 have        "Type .allInstances@pre() ?\<tau> = 
              \<lambda>_. Type .allInstances@pre() ?\<tau>'->including(\<lambda>_.\<lfloor>\<lfloor>\<lceil>Type Object\<rceil>\<rfloor>\<rfloor>) ?\<tau>"
             apply(rule state_update_vs_allInstances_at_pre_including)
             by(insert oid_def, auto simp: type_conform)
 also have   "... = ((\<lambda>_. Type .allInstances@pre() ?\<tau>')->including(\<lambda>_. (\<lambda>_.\<lfloor>\<lfloor>\<lceil>Type Object\<rceil>\<rfloor>\<rfloor>) ?\<tau>') ?\<tau>')"
             by(rule includes_const_inv)
 also have   "... = ((Type .allInstances@pre())->including(\<lambda> _. \<lfloor>(Type Object)\<rfloor>)?\<tau>')"
             apply(subst OCL_lib.cp_OclIncluding[symmetric])
             by(insert type_conform, auto)
 finally have Y : "Type .allInstances@pre() ?\<tau> = 
                   ((Type .allInstances@pre())->including(\<lambda> _. \<lfloor>(Type Object)\<rfloor>) ?\<tau>')"
             by auto
 show ?thesis
      apply(subst X) apply(subst OCL_core.cp_validity[symmetric])
      apply(rule StrongEq_L_subst3[OF cp_ctxt])
      apply(simp add: OclValid_def StrongEq_def Y)
 done
qed

subsubsection{* AT POST or AT PRE *}

theorem StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_vs_StrongEq'':
assumes WFF: "WFF \<tau>"
and valid_x: "\<tau> \<Turnstile>(\<upsilon> (x :: ('\<AA>::object,'\<alpha>::object option option)val))"
and valid_y: "\<tau> \<Turnstile>(\<upsilon> y)"
and oid_preserve: "\<And>x. oid_of (H x) = oid_of x"
and xy_together: "\<tau> \<Turnstile> ((H .allInstances()->includes(x) and (H .allInstances()->includes(y))) or
                       (H .allInstances@pre()->includes(x) and (H .allInstances@pre()->includes(y))))"
 (* x and y must be object representations that exist in either the pre or post state *)
shows "(\<tau> \<Turnstile> (StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y)) = (\<tau> \<Turnstile> (x \<triangleq> y))"
proof -
   have at_post_def : "\<And>x. \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<delta> (H .allInstances()->includes(x))"
    apply(simp add: OclIncludes_def OclValid_def OclAllInstances_at_post_defined[simplified OclValid_def])
   by(subst cp_defined, simp)
   have at_pre_def : "\<And>x. \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<delta> (H .allInstances@pre()->includes(x))"
    apply(simp add: OclIncludes_def OclValid_def OclAllInstances_at_pre_defined[simplified OclValid_def])
   by(subst cp_defined, simp)
   have F: "Rep_Set_0 (Abs_Set_0 \<lfloor>\<lfloor>Some ` (H ` ran (heap (fst \<tau>)) - {None})\<rfloor>\<rfloor>) =
            \<lfloor>\<lfloor>Some ` (H ` ran (heap (fst \<tau>)) - {None})\<rfloor>\<rfloor>" 
           by(subst OCL_lib.Set_0.Abs_Set_0_inverse,simp_all add: bot_option_def) 
   have F': "Rep_Set_0 (Abs_Set_0 \<lfloor>\<lfloor>Some ` (H ` ran (heap (snd \<tau>)) - {None})\<rfloor>\<rfloor>) =
            \<lfloor>\<lfloor>Some ` (H ` ran (heap (snd \<tau>)) - {None})\<rfloor>\<rfloor>" 
           by(subst OCL_lib.Set_0.Abs_Set_0_inverse,simp_all add: bot_option_def) 
 show ?thesis
  apply(rule StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_vs_StrongEq'[OF WFF valid_x valid_y, where H = "Some o H"])
  apply(subst oid_preserve[symmetric], simp, simp add: oid_of_option_def)
  apply(insert xy_together)
  apply(subst (asm) foundation11)
  apply (metis at_post_def defined_and_I valid_x valid_y)
  apply (metis at_pre_def defined_and_I valid_x valid_y)
  apply(erule disjE)
  (* *)
  apply(drule foundation5, 
        simp add: OclAllInstances_at_post_def OclValid_def OclIncludes_def true_def F F'
                  valid_x[simplified OclValid_def] valid_y[simplified OclValid_def] bot_option_def
             split: split_if_asm)
  apply(simp add: comp_def image_def, fastforce)
  (* *)
  apply(drule foundation5, 
        simp add: OclAllInstances_at_pre_def OclValid_def OclIncludes_def true_def F F'
                  valid_x[simplified OclValid_def] valid_y[simplified OclValid_def] bot_option_def
             split: split_if_asm)
  apply(simp add: comp_def image_def, fastforce)
 done
qed

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

lemma state_split : "\<tau> \<Turnstile> \<delta> X \<Longrightarrow> 
                     \<tau> \<Turnstile> (X .oclIsNew()) \<or> \<tau> \<Turnstile> (X .oclIsDeleted()) \<or> 
                     \<tau> \<Turnstile> (X .oclIsMaintained()) \<or> \<tau> \<Turnstile> (X .oclIsAbsent())"
by(simp add: OclIsDeleted_def OclIsNew_def OclIsMaintained_def OclIsAbsent_def
             OclValid_def true_def, blast)

lemma notNew_vs_others : "\<tau> \<Turnstile> \<delta> X \<Longrightarrow> 
                         (\<not> \<tau> \<Turnstile> (X .oclIsNew())) = (\<tau> \<Turnstile> (X .oclIsDeleted()) \<or> 
                          \<tau> \<Turnstile> (X .oclIsMaintained()) \<or> \<tau> \<Turnstile> (X .oclIsAbsent()))"
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
  apply (metis (full_types) OCL_core.bot_fun_def OclNot4 OclValid_def foundation16 foundation18'
                            foundation9 not_inj null_fun_def)
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
 by(insert represented_x, simp add: defined_def OclValid_def null_fun_def bot_fun_def false_def
                                    true_def OclSelf_at_pre_def invalid_def split: split_if_asm)
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

section{* Miscellaneous : Propagation of "constant contexts P" *}

lemma true_cp_all : "true \<tau>1 = true \<tau>2"
by(simp add: true_def)

lemma false_cp_all : "false \<tau>1 = false \<tau>2"
by(simp add: false_def)

lemma null_cp_all : "null \<tau>1 = null \<tau>2"
by(simp add: null_fun_def)

lemma invalid_cp_all : "invalid \<tau>1 = invalid \<tau>2"
by(simp add: invalid_def)

lemma bot_cp_all : "\<bottom> \<tau>1 = \<bottom> \<tau>2"
by(simp add: bot_fun_def)

lemma defined_cp_all :
 assumes "X \<tau>1 = X \<tau>2"
 shows "(\<delta> X) \<tau>1 = (\<delta> X) \<tau>2"
by(simp add: defined_def false_def true_def bot_fun_def null_fun_def assms)

lemma valid_cp_all :
 assumes "X \<tau>1 = X \<tau>2"
 shows "(\<upsilon> X) \<tau>1 = (\<upsilon> X) \<tau>2"
by(simp add: valid_def false_def true_def bot_fun_def null_fun_def assms)

lemma OclAnd_cp_all :
  assumes "X \<tau>1 = X \<tau>2"
  assumes "X' \<tau>1 = X' \<tau>2"
  shows "(X and X') \<tau>1 = (X and X') \<tau>2"
by(subst (1 2) cp_OclAnd, simp add: assms OclAnd_def)

lemma OclIf_cp_all :
  assumes "B \<tau>1 = B \<tau>2"
  assumes "C1 \<tau>1 = C1 \<tau>2"
  assumes "C2 \<tau>1 = C2 \<tau>2"
  shows "(if B then C1 else C2 endif) \<tau>1 = (if B then C1 else C2 endif) \<tau>2"
 apply(subst (1 2) cp_OclIf, simp only: OclIf_def cp_defined[symmetric])
by(simp add: defined_cp_all[OF assms(1)] true_cp_all assms invalid_cp_all)

lemma OclIncluding_cp_all :
 assumes x_int : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> x"
     and x_incl : "x \<tau>1 = x \<tau>2"
     and S_def : "\<And>\<tau>. \<tau> \<Turnstile> \<delta> S"
     and S_incl : "S \<tau>1 = S \<tau>2"
   shows  "S->including(x) \<tau>1 = S->including(x) \<tau>2"
 apply(unfold OclIncluding_def)
 apply(simp add: S_def[simplified OclValid_def] x_int[simplified OclValid_def] S_incl)
 apply(simp add: x_incl)
done

lemma OclForall_cp_all :
  assumes "X \<tau>1 = X \<tau>2"
  assumes "\<And>x. x \<tau>1 = x \<tau>2 \<Longrightarrow> X' x \<tau>1 = X' x \<tau>2"
  shows "OclForall X X' \<tau>1 = OclForall X X' \<tau>2"
 apply(subst (1 2) cp_OclForall, simp only: OclForall_def cp_defined[symmetric])
by(simp only: defined_cp_all[OF assms(1)] true_cp_all[of \<tau>1 \<tau>2] false_cp_all[of \<tau>1 \<tau>2] null_cp_all[of \<tau>1 \<tau>2] bot_cp_all[of \<tau>1 \<tau>2] assms)

lemma OclIncludes_cp_all :
  assumes "X \<tau>1 = X \<tau>2"
  assumes "X' \<tau>1 = X' \<tau>2"
  shows "OclIncludes X X' \<tau>1 = OclIncludes X X' \<tau>2"
 apply(subst (1 2) cp_OclIncludes, simp only: OclIncludes_def cp_defined[symmetric] cp_valid[symmetric])
by(simp add: defined_cp_all[OF assms(1)] valid_cp_all[OF assms(2)] true_cp_all assms)

lemma OclNot_cp_all :
  assumes "X \<tau>1 = X \<tau>2"
  shows "not X \<tau>1 = not X \<tau>2"
by(simp add: OclNot_def assms)

lemma StrictEq_cp_all :
  assumes "(X :: (_,_::null) Set) \<tau>1 = X \<tau>2"
  assumes "X' \<tau>1 = X' \<tau>2"
  shows "(X \<doteq> X') \<tau>1 = (X \<doteq> X') \<tau>2"
 apply(simp add: StrictRefEq\<^sub>S\<^sub>e\<^sub>t)
 apply(rule OclIf_cp_all)
 apply(rule defined_cp_all, simp add: assms)
 apply(rule OclIf_cp_all)
 apply(rule defined_cp_all, simp add: assms)
 apply(rule OclAnd_cp_all)
 apply(rule OclForall_cp_all, simp add: assms)
 apply(rule OclIncludes_cp_all, simp add: assms, simp)
 apply(rule OclForall_cp_all, simp add: assms)
 apply(rule OclIncludes_cp_all, simp add: assms, simp)
 apply(rule OclIf_cp_all)
 apply(rule valid_cp_all, simp add: assms)
 apply(simp add: false_def, simp add: invalid_def)
 apply(rule OclIf_cp_all)
 apply(rule valid_cp_all, simp add: assms)
 apply(rule OclIf_cp_all)
 apply(rule valid_cp_all, simp add: assms)
 apply(rule OclNot_cp_all)
 apply(rule defined_cp_all, simp add: assms)
 apply(simp add: invalid_def)+
done

lemma mtSet_cp_all : "Set{} \<tau>1 = Set{} \<tau>2"
by(simp add: mtSet_def)

lemma StrictRefEq\<^sub>S\<^sub>e\<^sub>t_L_subst1 : "cp P \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> P x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> P y \<Longrightarrow> \<tau> \<Turnstile> (x::('\<AA>,'\<alpha>::null)Set) \<doteq> y \<Longrightarrow> \<tau> \<Turnstile> (P x ::('\<AA>,'\<alpha>::null)Set) \<doteq> P y"
 apply(simp only: StrictRefEq\<^sub>S\<^sub>e\<^sub>t OclValid_def)
 apply(split split_if_asm)
 apply(simp add: StrongEq_L_subst1[simplified OclValid_def])
by (simp add: invalid_def bot_option_def true_def)

lemma including_subst_set' :
shows "\<tau> \<Turnstile> \<delta> s \<Longrightarrow> \<tau> \<Turnstile> \<delta> t \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> ((s::('\<AA>,'a::null)Set) \<doteq> t) \<Longrightarrow> \<tau> \<Turnstile> (s->including(x) \<doteq> (t->including(x)))"
proof -
 have cp: "cp (\<lambda>s. (s->including(x)))"
  apply(simp add: cp_def, subst cp_OclIncluding)
 by (rule_tac x = "(\<lambda>xab ab. ((\<lambda>_. xab)->including(\<lambda>_. x ab)) ab)" in exI, simp)

 show "\<tau> \<Turnstile> \<delta> s \<Longrightarrow> \<tau> \<Turnstile> \<delta> t \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> (s \<doteq> t) \<Longrightarrow> ?thesis"
  apply(rule_tac P = "\<lambda>s. (s->including(x))" in StrictRefEq\<^sub>S\<^sub>e\<^sub>t_L_subst1)
  apply(rule cp)
  apply(simp add: foundation20) apply(simp add: foundation20)
  apply (simp add: foundation10 foundation6)+
 done
qed

end
