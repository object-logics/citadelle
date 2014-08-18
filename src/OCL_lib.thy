(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_lib.thy --- Library definitions.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2012-2014 Université Paris-Sud, France
 *               2013-2014 IRT SystemX, France
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


theory  OCL_lib
imports (* Basic Type Operations *)
        OCL_basic_type_Boolean
        OCL_basic_type_Void
        OCL_basic_type_Integer
        OCL_basic_type_Real
        OCL_basic_type_String
        
        (* Collection Type Operations *)
        OCL_collection_type_Pair
        OCL_collection_type_Set
        OCL_collection_type_Sequence
begin

section{* Miscellaneous Stuff*}

subsection{*  Properties on Collection Types: Strict Equality *}

text {* The structure of this chapter roughly follows the structure of Chapter
10 of the OCL standard~\cite{omg:ocl:2012}, which introduces the OCL
Library. *}

subsection{* MOVE TEXT : Collection Types *}

text{* For the semantic construction of the collection types, we have two goals:
\begin{enumerate}
\item we want the types to be \emph{fully abstract}, \ie, the type should not
      contain junk-elements that are not representable by OCL expressions, and
\item we want a possibility to nest collection types (so, we want the
      potential to talking about @{text "Set(Set(Sequences(Pairs(X,Y))))"}).
\end{enumerate}
The former principle rules out the option to define @{text "'\<alpha> Set"} just by
 @{text "('\<AA>, ('\<alpha> option option) set) val"}. This would allow sets to contain
junk elements such as @{text "{\<bottom>}"} which we need to identify with undefinedness
itself. Abandoning fully abstractness of rules would later on produce all sorts
of problems when quantifying over the elements of a type.
However, if we build an own type, then it must conform to our abstract interface
in order to have nested types: arguments of type-constructors must conform to our
abstract interface, and the result type too.
*}

lemmas cp_intro'' [intro!,simp,code_unfold] =
       cp_intro'
     (*  cp_intro''\<^sub>P\<^sub>a\<^sub>i\<^sub>r *)
       cp_intro''\<^sub>S\<^sub>e\<^sub>t
       cp_intro''\<^sub>S\<^sub>e\<^sub>q\<^sub>u\<^sub>e\<^sub>n\<^sub>c\<^sub>e

subsection{* MOVE TEXT: Test Statements *}

lemma syntax_test: "Set{\<two>,\<one>} = (Set{}->including(\<one>)->including(\<two>))"
by (rule refl)

text{* Here is an example of a nested collection. Note that we have
to use the abstract null (since we did not (yet) define a concrete
constant @{term null} for the non-existing Sets) :*}
lemma semantic_test2:
assumes H:"(Set{\<two>} \<doteq> null) = (false::('\<AA>)Boolean)"
shows   "(\<tau>::('\<AA>)st) \<Turnstile> (Set{Set{\<two>},null}->includes(null))"
by(simp add: OclIncludes_execute\<^sub>S\<^sub>e\<^sub>t H)



lemma short_cut'[simp,code_unfold]: "(\<eight> \<doteq> \<six>) = false"
 apply(rule ext)
 apply(simp add: StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r StrongEq_def OclInt8_def OclInt6_def
                 true_def false_def invalid_def bot_option_def)
done

lemma short_cut''[simp,code_unfold]: "(\<two> \<doteq> \<one>) = false"
 apply(rule ext)
 apply(simp add: StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r StrongEq_def OclInt2_def OclInt1_def
                 true_def false_def invalid_def bot_option_def)
done
lemma short_cut'''[simp,code_unfold]: "(\<one> \<doteq> \<two>) = false"
 apply(rule ext)
 apply(simp add: StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r StrongEq_def OclInt2_def OclInt1_def
                 true_def false_def invalid_def bot_option_def)
done

text{* Elementary computations on Sets.*}

declare OclSelect_body_def [simp]

Assert "\<not> (\<tau> \<Turnstile> \<upsilon>(invalid::('\<AA>,'\<alpha>::null) Set))"
Assert    "\<tau> \<Turnstile> \<upsilon>(null::('\<AA>,'\<alpha>::null) Set)"
Assert "\<not> (\<tau> \<Turnstile> \<delta>(null::('\<AA>,'\<alpha>::null) Set))"
Assert    "\<tau> \<Turnstile> \<upsilon>(Set{})"
Assert    "\<tau> \<Turnstile> \<upsilon>(Set{Set{\<two>},null})"
Assert    "\<tau> \<Turnstile> \<delta>(Set{Set{\<two>},null})"
Assert    "\<tau> \<Turnstile> (Set{\<two>,\<one>}->includes(\<one>))"
Assert "\<not> (\<tau> \<Turnstile> (Set{\<two>}->includes(\<one>)))"
Assert "\<not> (\<tau> \<Turnstile> (Set{\<two>,\<one>}->includes(null)))"
Assert    "\<tau> \<Turnstile> (Set{\<two>,null}->includes(null))"
Assert    "\<tau> \<Turnstile> (Set{null,\<two>}->includes(null))"

Assert    "\<tau> \<Turnstile> ((Set{})->forAll(z | \<zero> <\<^sub>i\<^sub>n\<^sub>t z))"

Assert    "\<tau> \<Turnstile> ((Set{\<two>,\<one>})->forAll(z | \<zero> <\<^sub>i\<^sub>n\<^sub>t z))"
Assert   "\<tau> \<Turnstile> (\<zero> <\<^sub>i\<^sub>n\<^sub>t \<two>) and (\<zero> <\<^sub>i\<^sub>n\<^sub>t \<one>) "
Assert "\<not> (\<tau> \<Turnstile> ((Set{\<two>,\<one>})->exists(z | z <\<^sub>i\<^sub>n\<^sub>t \<zero> )))"
Assert "\<not> (\<tau> \<Turnstile> (\<delta>(Set{\<two>,null})->forAll(z | \<zero> <\<^sub>i\<^sub>n\<^sub>t z)))"
Assert "\<not> (\<tau> \<Turnstile> ((Set{\<two>,null})->forAll(z | \<zero> <\<^sub>i\<^sub>n\<^sub>t z)))"
Assert    "\<tau> \<Turnstile> ((Set{\<two>,null})->exists(z | \<zero> <\<^sub>i\<^sub>n\<^sub>t z))"

Assert "\<not> (\<tau> \<Turnstile> (Set{null::'a Boolean} \<doteq> Set{}))"
Assert "\<not> (\<tau> \<Turnstile> (Set{null::'a Integer} \<doteq> Set{}))"

Assert "\<not> (\<tau> \<Turnstile> (Set{true} \<doteq> Set{false}))"
Assert "\<not> (\<tau> \<Turnstile> (Set{true,true} \<doteq> Set{false}))"
Assert "\<not> (\<tau> \<Turnstile> (Set{\<two>} \<doteq> Set{\<one>}))"
Assert    "\<tau> \<Turnstile> (Set{\<two>,null,\<two>} \<doteq> Set{null,\<two>})"
Assert    "\<tau> \<Turnstile> (Set{\<one>,null,\<two>} <> Set{null,\<two>})"
Assert    "\<tau> \<Turnstile> (Set{Set{\<two>,null}} \<doteq> Set{Set{null,\<two>}})"
Assert    "\<tau> \<Turnstile> (Set{Set{\<two>,null}} <> Set{Set{null,\<two>},null})"
Assert    "\<tau> \<Turnstile> (Set{null}->select(x | not x) \<doteq> Set{null})"
Assert    "\<tau> \<Turnstile> (Set{null}->reject(x | not x) \<doteq> Set{null})"

lemma     "const (Set{Set{\<two>,null}, invalid})" by(simp add: const_ss)



end
