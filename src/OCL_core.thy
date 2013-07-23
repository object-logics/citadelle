(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4 
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_core.thy --- Core definitions.
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

header{* Part I: Core Definitions *}

theory 
  OCL_core
imports
  Main (* Testing *)
begin
 
section{* Preliminaries *}
subsection{* Notations for the option type *}

text{*First of all, we will use a more compact notation for the library 
option type which occur all over in our definitions and which will make
the presentation more "textbook"-like:*}

notation Some ("\<lfloor>(_)\<rfloor>")
notation None ("\<bottom>")

text{* The following function (corresponding to @{term the} in the Isabelle/HOL library) 
is defined as the inverse of the injection @{term Some}. *}
fun    drop :: "'\<alpha> option \<Rightarrow> '\<alpha>" ("\<lceil>(_)\<rceil>")
where  drop_lift[simp]: "\<lceil>\<lfloor>v\<rfloor>\<rceil> = v"

subsection{* Minimal Notions of State and State Transitions *}
text{* Next we will introduce the foundational concept of an object id (oid), 
which is just some infinite set. *}

text{* In order to assure executability of as much as possible formulas, we fixed the
type of object id's to just natural numbers.*}
type_synonym oid = nat

text{* We refrained from the alternative: 
\begin{isar}
type_synonym oid = ind
\end{isar}
which is slightly more abstract but non-executable.
*}

text{* States are just a partial map from oid's to elements of an object universe @{text "'\<AA>"},
and state transitions pairs of states...  *}
record ('\<AA>)state = 
             heap   :: "oid \<rightharpoonup> '\<AA> "
             assocs :: "oid  \<rightharpoonup> (oid \<times> oid) list"
  
type_synonym ('\<AA>)st = "'\<AA> state \<times> '\<AA> state"

subsection{* Prerequisite: An Abstract Interface for OCL Types *}

text {* In order to have the possibility to nest collection types,
such that we can give semantics to expressions like @{text "Set{Set{\<two>},null}"},
it is necessary to introduce a uniform interface for types having
the @{text "invalid"} (= bottom) element. The reason is that we impose
a data-invariant on raw-collection \verb|types_code| which assures
that the @{text "invalid"} element is not allowed inside the collection;
all raw-collections of this form were identified with the @{text "invalid"} element
itself. The construction requires that the new collection type is
un-comparable with the raw-types (consisting of nested option type constructions),
such that the data-invariant must be expressed in terms of the interface.
In a second step, our base-types will be shown to be instances of this interface.
 *}

text{* This uniform interface consists in a type class requiring the existence
of a bot and a null element. The construction proceeds by
 abstracting the null (which is defined by @{text "\<lfloor> \<bottom> \<rfloor>"} on 
@{text "'a option option"} to a null - element, which may
have an abritrary semantic structure, and an undefinedness element @{text "\<bottom> "}
to an abstract undefinedness element @{text "bot"} (also written  
@{text "\<bottom> "} whenever no confusion arises). As a consequence, it is necessary  
to redefine the notions of invalid, defined, valuation etc.
on top of this interface. *}

text{* This interface consists in two abstract type classes @{text bot} 
and @{text null} for the class of all types comprising a bot and a 
distinct null element.  *}

instance option   :: (plus) plus  by intro_classes
instance "fun"    :: (type, plus) plus by intro_classes

class   bot = 
   fixes  bot :: "'a"
   assumes nonEmpty : "\<exists> x. x \<noteq> bot"


class      null = bot +
   fixes   null :: "'a"
   assumes null_is_valid : "null \<noteq> bot"


subsection{* Accomodation of Basic Types to the Abstract Interface *}

text{* In the following it is shown that the option-option type type is
in fact in the @{text null} class and that function spaces over these 
classes again "live" in these classes. This motivates the default construction
of the semantic domain for the basic types (Boolean, Integer, Reals, ...). *}

instantiation   option  :: (type)bot
begin 
   definition bot_option_def: "(bot::'a option) \<equiv> (None::'a option)"
   instance proof show "\<exists>x\<Colon>'a option. x \<noteq> bot"  
                  by(rule_tac x="Some x" in exI, simp add:bot_option_def)
            qed
end


instantiation   option  :: (bot)null
begin 
   definition null_option_def: "(null::'a\<Colon>bot option) \<equiv>  \<lfloor> bot \<rfloor>"
   instance proof  show "(null::'a\<Colon>bot option) \<noteq> bot"
                   by( simp add:null_option_def bot_option_def)
            qed
end


instantiation "fun"  :: (type,bot) bot 
begin
   definition bot_fun_def: "bot \<equiv> (\<lambda> x. bot)"

   instance proof  show "\<exists>(x::'a \<Rightarrow> 'b). x \<noteq> bot"
                   apply(rule_tac x="\<lambda> _. (SOME y. y \<noteq> bot)" in exI, auto)
                   apply(drule_tac x=x in fun_cong,auto simp:bot_fun_def)
                   apply(erule contrapos_pp, simp)
                   apply(rule some_eq_ex[THEN iffD2])
                   apply(simp add: nonEmpty)
                   done
            qed
end


instantiation "fun"  :: (type,null) null 
begin
 definition null_fun_def: "(null::'a \<Rightarrow> 'b::null) \<equiv> (\<lambda> x. null)"

 instance proof 
              show "(null::'a \<Rightarrow> 'b::null) \<noteq> bot"
              apply(auto simp: null_fun_def bot_fun_def)
              apply(drule_tac x=x in fun_cong)
              apply(erule contrapos_pp, simp add: null_is_valid)
            done
          qed
end

text{* A trivial consequence of this adaption of the interface is that
abstract and concrete versions of null are the same on base types
(as could be expected). *}

subsection{* The Semantic Space of OCL Types: Valuations. *}

text{* Valuations are now functions from a state pair (built upon 
data universe @{typ "'\<AA>"}) to an arbitrary null-type (i.e. containing
at least a destinguished @{text "null"} and @{text "invalid"} element. *}

type_synonym ('\<AA>,'\<alpha>) val = "'\<AA> st \<Rightarrow> '\<alpha>::null"

text{* The definitions for the constants and operations based on valuations 
will be geared towards a format that Isabelle can check to be a "conservative" 
(i.e. logically safe) axiomatic definition. By introducing an explicit 
interpretation function (which happens to be defined just as the identity
since we are using a shallow embedding of OCL into HOL), all these definions
can be rewritten into the conventional semantic "textbook" format  as follows: *}

definition Sem :: "'a \<Rightarrow> 'a" ("I\<lbrakk>_\<rbrakk>")
where "I\<lbrakk>x\<rbrakk> \<equiv> x"

text{* As a consequence of semantic domain definition, any OCL type will
have the two semantic constants @{text "invalid"} (for exceptional, aborted
computation) and @{text "null"}; the latter, however is either defined
 *}

definition invalid :: "('\<AA>,'\<alpha>::bot) val" 
where     "invalid \<equiv> \<lambda> \<tau>. bot"

text{* This conservative Isabelle definition of the polymorphic constant
@{const invalid} is equivalent with the textbook definition: *}

lemma invalid_def_textbook: "I\<lbrakk>invalid\<rbrakk>\<tau> = bot"
by(simp add: invalid_def Sem_def)


text {* Note that the definition : 
\begin{verbatim}
definition null    :: "('\<AA>,'\<alpha>::null) val" 
where     "null    \<equiv> \<lambda> \<tau>. null"
\end{verbatim}
is not  necessary since we defined the entire function space over null types
again as null-types; the crucial definition is @{thm "null_fun_def"}. 
Thus, the polymorphic constant @{const null} is simply the result of
a general type class construction. Nevertheless, we can derive the
semantic textbook definition for the OCL null constant based on the
abstract null: 
*}

lemma null_def_textbook: "I\<lbrakk>null::('\<AA>,'\<alpha>::null) val\<rbrakk> \<tau> = (null::'\<alpha>::null)"
by(simp add: null_fun_def Sem_def)


section{* Boolean Type and Logic *}

text{* The semantic domain of the (basic) boolean type is now defined as standard:
the space of valuation to @{typ "bool option option"}:*}

type_synonym ('\<AA>)Boolean = "('\<AA>,bool option option) val"

subsection{* Basic Constants *}

lemma bot_Boolean_def : "(bot::('\<AA>)Boolean) = (\<lambda> \<tau>. \<bottom>)"
by(simp add: bot_fun_def bot_option_def) 

lemma null_Boolean_def : "(null::('\<AA>)Boolean) = (\<lambda> \<tau>. \<lfloor>\<bottom>\<rfloor>)"
by(simp add: null_fun_def null_option_def bot_option_def) 

definition true :: "('\<AA>)Boolean"
where     "true \<equiv> \<lambda> \<tau>. \<lfloor>\<lfloor>True\<rfloor>\<rfloor>"


definition false :: "('\<AA>)Boolean"
where     "false \<equiv>  \<lambda> \<tau>. \<lfloor>\<lfloor>False\<rfloor>\<rfloor>"

lemma bool_split: "X \<tau> = invalid \<tau> \<or> X \<tau> = null \<tau> \<or> 
                   X \<tau> = true \<tau>    \<or> X \<tau> = false \<tau>"
apply(simp add: invalid_def null_def true_def false_def)
apply(case_tac "X \<tau>",simp_all add: null_fun_def null_option_def bot_option_def)
apply(case_tac "a",simp)
apply(case_tac "aa",simp)
apply auto
done



lemma [simp]: "false (a, b) = \<lfloor>\<lfloor>False\<rfloor>\<rfloor>"
by(simp add:false_def)

lemma [simp]: "true (a, b) = \<lfloor>\<lfloor>True\<rfloor>\<rfloor>"
by(simp add:true_def)

lemma true_def_textbook: "I\<lbrakk>true\<rbrakk> \<tau> = \<lfloor>\<lfloor>True\<rfloor>\<rfloor>"
by(simp add: Sem_def true_def)

lemma false_def_textbook: "I\<lbrakk>false\<rbrakk> \<tau> = \<lfloor>\<lfloor>False\<rfloor>\<rfloor>"
by(simp add: Sem_def false_def)

(* This following para contains a cool technique to generate documentation
   with formal content. We should use it everywhere for documentation. *)
text{* \textbf{Summary}:
\begin{table}[htbp]
   \centering
   \begin{tabular}{lp{10cm}} % Column formatting
      \toprule
      Name & Theorem \\
      \midrule
      @{thm [source] invalid_def_textbook}  & @{thm  invalid_def_textbook} \\
      @{thm [source] null_def_textbook}  & @{thm  null_def_textbook} \\
      @{thm [source] true_def_textbook}   & @{thm [display=true,margin=35] true_def_textbook} \\
      @{thm [source] false_def_textbook} & @{thm false_def_textbook} \\
      \bottomrule
   \end{tabular}
   \caption{Basic semantic constant definitions of the logic (except @{term null})}
   \label{tab:sem_basic_constants}
\end{table}
 % unfortunately, the margin indent construction does not work inside a table.
 % ask IsabelleUsers? Or Makarius ?

*}

subsection{* Fundamental Predicates I: Validity and Definedness *}

text{* However, this has also the consequence that core concepts like definedness, 
validness and even cp have to be redefined on this type class:*}

definition valid :: "('\<AA>,'a::null)val \<Rightarrow> ('\<AA>)Boolean" ("\<upsilon> _" [100]100)
where   "\<upsilon> X \<equiv>  \<lambda> \<tau> . if X \<tau> = bot \<tau> then false \<tau> else true \<tau>"

lemma valid1[simp]: "\<upsilon> invalid = false"
  by(rule ext,simp add: valid_def bot_fun_def bot_option_def 
                        invalid_def true_def false_def)

lemma valid2[simp]: "\<upsilon> null = true"
  by(rule ext,simp add: valid_def bot_fun_def bot_option_def null_is_valid
                        null_fun_def invalid_def true_def false_def)

lemma valid3[simp]: "\<upsilon> true = true"
  by(rule ext,simp add: valid_def bot_fun_def bot_option_def null_is_valid
                        null_fun_def invalid_def true_def false_def)

lemma valid4[simp]: "\<upsilon> false = true"
  by(rule ext,simp add: valid_def bot_fun_def bot_option_def null_is_valid
                        null_fun_def invalid_def true_def false_def)

 
lemma cp_valid: "(\<upsilon> X) \<tau> = (\<upsilon> (\<lambda> _. X \<tau>)) \<tau>"
by(simp add: valid_def)



definition defined :: "('\<AA>,'a::null)val \<Rightarrow> ('\<AA>)Boolean" ("\<delta> _" [100]100)
where   "\<delta> X \<equiv>  \<lambda> \<tau> . if X \<tau> = bot \<tau>  \<or> X \<tau> = null \<tau> then false \<tau> else true \<tau>"

text{* The generalized definitions of invalid and definedness have the same
properties as the old ones : *}
lemma defined1[simp]: "\<delta> invalid = false"
  by(rule ext,simp add: defined_def bot_fun_def bot_option_def 
                        null_def invalid_def true_def false_def)

lemma defined2[simp]: "\<delta> null = false"
  by(rule ext,simp add: defined_def bot_fun_def bot_option_def 
                        null_def null_option_def null_fun_def invalid_def true_def false_def)


lemma defined3[simp]: "\<delta> true = true"
  by(rule ext,simp add: defined_def bot_fun_def bot_option_def null_is_valid null_option_def
                        null_fun_def invalid_def true_def false_def)

lemma defined4[simp]: "\<delta> false = true"
  by(rule ext,simp add: defined_def bot_fun_def bot_option_def null_is_valid null_option_def
                        null_fun_def invalid_def true_def false_def)


lemma defined5[simp]: "\<delta> \<delta> X = true"
  by(rule ext,
     auto simp:           defined_def true_def false_def
                bot_fun_def bot_option_def null_option_def null_fun_def)

lemma defined6[simp]: "\<delta> \<upsilon> X = true"
  by(rule ext,
     auto simp: valid_def defined_def true_def false_def
                bot_fun_def bot_option_def null_option_def null_fun_def)

lemma valid5[simp]: "\<upsilon> \<upsilon> X = true"
  by(rule ext,
     auto simp: valid_def             true_def false_def
                bot_fun_def bot_option_def null_option_def null_fun_def)

lemma valid6[simp]: "\<upsilon> \<delta> X = true"
  by(rule ext,
     auto simp: valid_def defined_def true_def false_def
                bot_fun_def bot_option_def null_option_def null_fun_def)


lemma cp_defined:"(\<delta> X)\<tau> = (\<delta> (\<lambda> _. X \<tau>)) \<tau>"
by(simp add: defined_def)

text{* The definitions above for the constants @{const defined} and @{const valid}
can be rewritten into the conventional semantic "textbook" format  as follows: *}

lemma defined_def_textbook: "I\<lbrakk>\<delta>(X)\<rbrakk> \<tau> = (if I\<lbrakk>X\<rbrakk> \<tau> = I\<lbrakk>bot\<rbrakk> \<tau>  \<or> I\<lbrakk>X\<rbrakk> \<tau> = I\<lbrakk>null\<rbrakk> \<tau> 
                                     then I\<lbrakk>false\<rbrakk> \<tau> 
                                     else I\<lbrakk>true\<rbrakk> \<tau>)"
by(simp add: Sem_def defined_def)

lemma valid_def_textbook: "I\<lbrakk>\<upsilon>(X)\<rbrakk> \<tau> = (if I\<lbrakk>X\<rbrakk> \<tau> = I\<lbrakk>bot\<rbrakk> \<tau>  
                                   then I\<lbrakk>false\<rbrakk> \<tau> 
                                   else I\<lbrakk>true\<rbrakk> \<tau>)"
by(simp add: Sem_def valid_def)

text{* \textbf{Summary}:
\begin{table}[htbp]
   \centering
   \begin{tabular}{ll} % Column formatting
      \toprule
      Name & Theorem \\
      \midrule
      @{thm [source] defined_def_textbook}  & @{thm [show_question_marks=false,display=false,margin=35] defined_def_textbook} \\
      @{thm [source] valid_def_textbook}   & @{thm [show_question_marks=false,display=false,margin=35] valid_def_textbook} \\
      \bottomrule
   \end{tabular}
   \caption{Basic predicate definitions of the logic.)}
   \label{tab:sem_definedness}
\end{table}
 % unfortunately, the margin indent construction does not work inside a table.
 % ask IsabelleUsers? Or Makarius ?
These definitions lead quite directly to the algebraic laws on these predicates: 
\begin{table}[htbp]
   \centering
   \begin{tabular}{lp{10cm}} % Column formatting
      \toprule
      Name & Theorem \\
      \midrule
      @{thm [source] defined1}  & @{thm  defined1} \\
      @{thm [source] defined2}   & @{thm [display=false,margin=35] defined2} \\
      @{thm [source] defined3}   & @{thm [display=false,margin=35] defined3} \\
      @{thm [source] defined4}   & @{thm [display=false,margin=35] defined4} \\
      @{thm [source] defined5}   & @{thm [display=false,margin=35] defined5} \\
      @{thm [source] defined6}   & @{thm [display=false,margin=35] defined6} \\
      \bottomrule
   \end{tabular}
   \caption{Laws of the basic predicates of the logic.)}
   \label{tab:alglaws_definedness}
\end{table}
*}

subsection{*  Fundamental Predicates II: Logical (Strong) Equality *}
text{* Note that we define strong equality extremely generic, even for types that contain
an @{text "null"} or @{text "\<bottom>"} element:*}
definition StrongEq::"['\<AA> st \<Rightarrow> '\<alpha>,'\<AA> st \<Rightarrow> '\<alpha>] \<Rightarrow> ('\<AA>)Boolean"  (infixl "\<triangleq>" 30)
where     "X \<triangleq> Y \<equiv>  \<lambda> \<tau>. \<lfloor>\<lfloor>X \<tau> = Y \<tau> \<rfloor>\<rfloor>"


text{* Equality reasoning in OCL is not humpty dumpty. While strong equality
is clearly an equivalence: *}
lemma StrongEq_refl [simp]: "(X \<triangleq> X) = true"
by(rule ext, simp add: null_def invalid_def true_def false_def StrongEq_def)

lemma StrongEq_sym: "(X \<triangleq> Y) = (Y \<triangleq> X)"
by(rule ext, simp add: eq_sym_conv invalid_def true_def false_def StrongEq_def)

lemma StrongEq_trans_strong [simp]:
  assumes A: "(X \<triangleq> Y) = true"
  and     B: "(Y \<triangleq> Z) = true"
  shows   "(X \<triangleq> Z) = true"
  apply(insert A B) apply(rule ext)
  apply(simp add: null_def invalid_def true_def false_def StrongEq_def)
  apply(drule_tac x=x in fun_cong)+
  by auto

text{* ... it is only in a limited sense a congruence, at least from the point of view
of this semantic theory. The point is that it is only a congruence on OCL- expressions,
not arbitrary HOL expressions (with which we can mix Essential OCL expressions. A semantic
 --- not syntactic --- characterization of OCL-expressions is that they are \emph{context-passing}
or \emph{context-invariant}, i.e. the context of an entire OCL expression, i.e. the pre-and
poststate it referes to, is passed constantly and unmodified to the sub-expressions, i.e. all
sub-expressions inside an OCL expression refer to the same context. Expressed formally, this
boils down to: *}

lemma StrongEq_subst :
  assumes cp: "\<And>X. P(X)\<tau> = P(\<lambda> _. X \<tau>)\<tau>"
  and     eq: "(X \<triangleq> Y)\<tau> = true \<tau>"
  shows   "(P X \<triangleq> P Y)\<tau> = true \<tau>"
  apply(insert cp eq) 
  apply(simp add: null_def invalid_def true_def false_def StrongEq_def)
  apply(subst cp[of X])   
  apply(subst cp[of Y])
  by simp

subsection{*  Fundamental Predicates III *}


text{* And, last but not least, *}
lemma defined7[simp]: "\<delta> (X \<triangleq> Y) = true"
  by(rule ext,
     auto simp: defined_def           true_def false_def StrongEq_def
                bot_fun_def bot_option_def null_option_def null_fun_def)

lemma valid7[simp]: "\<upsilon> (X \<triangleq> Y) = true"
  by(rule ext,
     auto simp:             valid_def true_def false_def StrongEq_def
                bot_fun_def bot_option_def null_option_def null_fun_def)

lemma cp_StrongEq: "(X \<triangleq> Y) \<tau> = ((\<lambda> _. X \<tau>) \<triangleq> (\<lambda> _. Y \<tau>)) \<tau>"
by(simp add: StrongEq_def)

text{* The semantics of strict equality of OCL is constructed by overloading: 
for each base type, there is an equality.*}



subsection{* Logical Connectives and their Universal Properties *}
text{* It is a design goal to give OCL a semantics that is as closely as
possible to a "logical system" in a known sense; a specification logic
where the logical connectives can not be understood other that having
the truth-table aside when reading fails its purpose in our view. 

Practically, this means that we want to give a definition to the core
operations to be as close as possible to the lattice laws; this makes
also powerful symbolic normalizations of OCL specifications possible
as a pre-requisite for automated theorem provers. For example, it is 
still possible to compute without any definedness- and validity reasoning
the DNF of an OCL specification; be it for test-case generations or
for a smooth transition to a two-valued representation of the specification
amenable to fast standard SMT-solvers, for example. 

Thus, our representation of the OCL is merely a 4-valued Kleene-Logics with
@{term "invalid"} as least, @{term "null"} as middle and @{term "true"} resp.
@{term "false"} as unrelated top-elements.
*}


definition OclNot :: "('\<AA>)Boolean \<Rightarrow> ('\<AA>)Boolean" ("not")
where     "not X \<equiv>  \<lambda> \<tau> . case X \<tau> of
                               \<bottom>     \<Rightarrow> \<bottom>
                           | \<lfloor> \<bottom> \<rfloor>   \<Rightarrow> \<lfloor> \<bottom> \<rfloor>  
                           | \<lfloor>\<lfloor> x \<rfloor>\<rfloor>  \<Rightarrow> \<lfloor>\<lfloor> \<not> x \<rfloor>\<rfloor>"


lemma cp_OclNot: "(not X)\<tau> = (not (\<lambda> _. X \<tau>)) \<tau>"
by(simp add: OclNot_def)

lemma OclNot1[simp]: "not invalid = invalid"
  by(rule ext,simp add: OclNot_def null_def invalid_def true_def false_def bot_option_def)

lemma OclNot2[simp]: "not null = null"  
  by(rule ext,simp add: OclNot_def null_def invalid_def true_def false_def 
                        bot_option_def null_fun_def null_option_def )

lemma OclNot3[simp]: "not true = false"
  by(rule ext,simp add: OclNot_def null_def invalid_def true_def false_def)

lemma OclNot4[simp]: "not false = true"
  by(rule ext,simp add: OclNot_def null_def invalid_def true_def false_def)


lemma OclNot_not[simp]: "not (not X) = X"
  apply(rule ext,simp add: OclNot_def null_def invalid_def true_def false_def)
  apply(case_tac "X x", simp_all)
  apply(case_tac "a", simp_all)
  done

lemma OclNot_inject: "\<And> x y. not x = not y \<Longrightarrow> x = y" 
  by(subst OclNot_not[THEN sym], simp)

definition OclAnd :: "[('\<AA>)Boolean, ('\<AA>)Boolean] \<Rightarrow> ('\<AA>)Boolean" (infixl "and" 30)
where     "X and Y \<equiv>  (\<lambda> \<tau> . case X \<tau> of
                          \<lfloor>\<lfloor>False\<rfloor>\<rfloor> \<Rightarrow>               \<lfloor>\<lfloor>False\<rfloor>\<rfloor>
                        | \<bottom>        \<Rightarrow> (case Y \<tau> of
                                        \<lfloor>\<lfloor>False\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>False\<rfloor>\<rfloor>
                                      | _        \<Rightarrow> \<bottom>)
                        | \<lfloor>\<bottom>\<rfloor>      \<Rightarrow> (case Y \<tau> of
                                        \<lfloor>\<lfloor>False\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>False\<rfloor>\<rfloor>
                                      | \<bottom>        \<Rightarrow> \<bottom>
                                      | _        \<Rightarrow> \<lfloor>\<bottom>\<rfloor>)
                        | \<lfloor>\<lfloor>True\<rfloor>\<rfloor>  \<Rightarrow>               Y \<tau>)"


text{*Note that @{term "not"} is \emph{not} defined as a strict function; proximity to
lattice laws implies that we \emph{need} a definition of @{term "not"} that satisfies
@{text "not(not(x))=x"}. *}

text{* In textbook notation, the logical core constructs @{const "OclNot"} and
@{const "OclAnd"} were represented as follows: *}

lemma textbook_not: 
     "I\<lbrakk>not(X)\<rbrakk> \<tau> =  (case I\<lbrakk>X\<rbrakk> \<tau> of   \<bottom>   \<Rightarrow> \<bottom>
                                 |  \<lfloor> \<bottom> \<rfloor> \<Rightarrow> \<lfloor> \<bottom> \<rfloor>  
                                 | \<lfloor>\<lfloor> x \<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor> \<not> x \<rfloor>\<rfloor>)"
by(simp add: Sem_def OclNot_def)

lemma textbook_and: 
     "I\<lbrakk>X and Y\<rbrakk> \<tau> = (case I\<lbrakk>X\<rbrakk> \<tau> of
                            \<bottom>  \<Rightarrow> (case I\<lbrakk>Y\<rbrakk> \<tau> of
                                             \<bottom> \<Rightarrow>  \<bottom>
                                          | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> \<bottom>
                                          | \<lfloor>\<lfloor>True\<rfloor>\<rfloor> \<Rightarrow>  \<bottom>
                                          | \<lfloor>\<lfloor>False\<rfloor>\<rfloor> \<Rightarrow>  \<lfloor>\<lfloor>False\<rfloor>\<rfloor>)
                        | \<lfloor> \<bottom> \<rfloor> \<Rightarrow> (case I\<lbrakk>Y\<rbrakk> \<tau> of
                                             \<bottom> \<Rightarrow>  \<bottom>
                                          | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> \<lfloor>\<bottom>\<rfloor>
                                          | \<lfloor>\<lfloor>True\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<bottom>\<rfloor>
                                          | \<lfloor>\<lfloor>False\<rfloor>\<rfloor> \<Rightarrow>  \<lfloor>\<lfloor>False\<rfloor>\<rfloor>)
                        | \<lfloor>\<lfloor>True\<rfloor>\<rfloor> \<Rightarrow> (case I\<lbrakk>Y\<rbrakk> \<tau> of
                                             \<bottom> \<Rightarrow>  \<bottom>
                                          | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> \<lfloor>\<bottom>\<rfloor>
                                          | \<lfloor>\<lfloor>y\<rfloor>\<rfloor> \<Rightarrow>  \<lfloor>\<lfloor>y\<rfloor>\<rfloor>)
                        | \<lfloor>\<lfloor>False\<rfloor>\<rfloor> \<Rightarrow>  \<lfloor>\<lfloor> False \<rfloor>\<rfloor>)"
by(simp add: OclAnd_def Sem_def split: option.split bool.split)

definition OclOr :: "[('\<AA>)Boolean, ('\<AA>)Boolean] \<Rightarrow> ('\<AA>)Boolean"            (infixl "or" 25)
where    "X or Y \<equiv> not(not X and not Y)"

definition OclImplies :: "[('\<AA>)Boolean, ('\<AA>)Boolean] \<Rightarrow> ('\<AA>)Boolean"       (infixl "implies" 25)
where    "X implies Y \<equiv> not X or Y"

lemma cp_OclAnd:"(X and Y) \<tau> = ((\<lambda> _. X \<tau>) and (\<lambda> _. Y \<tau>)) \<tau>"
by(simp add: OclAnd_def)

lemma cp_OclOr:"((X::('\<AA>)Boolean) or Y) \<tau> = ((\<lambda> _. X \<tau>) or (\<lambda> _. Y \<tau>)) \<tau>"
apply(simp add: OclOr_def)
apply(subst cp_OclNot[of "not (\<lambda>_. X \<tau>) and not (\<lambda>_. Y \<tau>)"])
apply(subst cp_OclAnd[of "not (\<lambda>_. X \<tau>)" "not (\<lambda>_. Y \<tau>)"])
by(simp add: cp_OclNot[symmetric] cp_OclAnd[symmetric] )


lemma cp_OclImplies:"(X implies Y) \<tau> = ((\<lambda> _. X \<tau>) implies (\<lambda> _. Y \<tau>)) \<tau>"
apply(simp add: OclImplies_def)
apply(subst cp_OclOr[of "not (\<lambda>_. X \<tau>)" "(\<lambda>_. Y \<tau>)"])
by(simp add: cp_OclNot[symmetric] cp_OclOr[symmetric] )

lemma OclAnd1[simp]: "(invalid and true) = invalid"
  by(rule ext,simp add: OclAnd_def null_def invalid_def true_def false_def bot_option_def)
lemma OclAnd2[simp]: "(invalid and false) = false"
  by(rule ext,simp add: OclAnd_def null_def invalid_def true_def false_def bot_option_def)
lemma OclAnd3[simp]: "(invalid and null) = invalid"
  by(rule ext,simp add: OclAnd_def null_def invalid_def true_def false_def bot_option_def 
                        null_fun_def null_option_def)
lemma OclAnd4[simp]: "(invalid and invalid) = invalid"
  by(rule ext,simp add: OclAnd_def null_def invalid_def true_def false_def bot_option_def)

lemma OclAnd5[simp]: "(null and true) = null"
  by(rule ext,simp add: OclAnd_def null_def invalid_def true_def false_def bot_option_def
                        null_fun_def null_option_def)
lemma OclAnd6[simp]: "(null and false) = false"
  by(rule ext,simp add: OclAnd_def null_def invalid_def true_def false_def bot_option_def
                        null_fun_def null_option_def)
lemma OclAnd7[simp]: "(null and null) = null"
  by(rule ext,simp add: OclAnd_def null_def invalid_def true_def false_def bot_option_def
                        null_fun_def null_option_def)
lemma OclAnd8[simp]: "(null and invalid) = invalid"
  by(rule ext,simp add: OclAnd_def null_def invalid_def true_def false_def bot_option_def
                        null_fun_def null_option_def)

lemma OclAnd9[simp]: "(false and true) = false" 
  by(rule ext,simp add: OclAnd_def null_def invalid_def true_def false_def)
lemma OclAnd10[simp]: "(false and false) = false"
  by(rule ext,simp add: OclAnd_def null_def invalid_def true_def false_def)
lemma OclAnd11[simp]: "(false and null) = false"
  by(rule ext,simp add: OclAnd_def null_def invalid_def true_def false_def)
lemma OclAnd12[simp]: "(false and invalid) = false"
  by(rule ext,simp add: OclAnd_def null_def invalid_def true_def false_def)

lemma OclAnd13[simp]: "(true and true) = true"
  by(rule ext,simp add: OclAnd_def null_def invalid_def true_def false_def)
lemma OclAnd14[simp]: "(true and false) = false"
  by(rule ext,simp add: OclAnd_def null_def invalid_def true_def false_def)
lemma OclAnd15[simp]: "(true and null) = null"
  by(rule ext,simp add: OclAnd_def null_def invalid_def true_def false_def bot_option_def
                        null_fun_def null_option_def)
lemma OclAnd16[simp]: "(true and invalid) = invalid"
  by(rule ext,simp add: OclAnd_def null_def invalid_def true_def false_def bot_option_def
                        null_fun_def null_option_def)

lemma OclAnd_idem[simp]: "(X and X) = X"
  apply(rule ext,simp add: OclAnd_def null_def invalid_def true_def false_def)
  apply(case_tac "X x", simp_all)
  apply(case_tac "a", simp_all)
  apply(case_tac "aa", simp_all)
  done

lemma OclAnd_commute: "(X and Y) = (Y and X)"
  by(rule ext,auto simp:true_def false_def OclAnd_def invalid_def 
                   split: option.split option.split_asm
                          bool.split bool.split_asm)


lemma OclAnd_false1[simp]: "(false and X) = false"
  apply(rule ext, simp add: OclAnd_def)
  apply(auto simp:true_def false_def invalid_def 
             split: option.split option.split_asm)
  done

lemma OclAnd_false2[simp]: "(X and false) = false"
  by(simp add: OclAnd_commute) 


lemma OclAnd_true1[simp]: "(true and X) = X"
  apply(rule ext, simp add: OclAnd_def)
  apply(auto simp:true_def false_def invalid_def 
             split: option.split option.split_asm)
  done

lemma OclAnd_true2[simp]: "(X and true) = X"
  by(simp add: OclAnd_commute) 

lemma OclAnd_bot1[simp]: "\<And>\<tau>. X \<tau> \<noteq> false \<tau> \<Longrightarrow> (bot and X) \<tau> = bot \<tau>"
  apply(simp add: OclAnd_def)
  apply(auto simp:true_def false_def bot_fun_def bot_option_def 
             split: option.split option.split_asm)
done

lemma OclAnd_bot2[simp]: "\<And>\<tau>. X \<tau> \<noteq> false \<tau> \<Longrightarrow> (X and bot) \<tau> = bot \<tau>"
  by(simp add: OclAnd_commute) 

lemma OclAnd_null1[simp]: "\<And>\<tau>. X \<tau> \<noteq> false \<tau> \<Longrightarrow> X \<tau> \<noteq> bot \<tau> \<Longrightarrow> (null and X) \<tau> = null \<tau>"
  apply(simp add: OclAnd_def)
  apply(auto simp:true_def false_def bot_fun_def bot_option_def null_fun_def null_option_def 
             split: option.split option.split_asm)
done

lemma OclAnd_null2[simp]: "\<And>\<tau>. X \<tau> \<noteq> false \<tau> \<Longrightarrow> X \<tau> \<noteq> bot \<tau> \<Longrightarrow> (X and null) \<tau> = null \<tau>"
  by(simp add: OclAnd_commute) 

lemma OclAnd_assoc: "(X and (Y and Z)) = (X and Y and Z)"
  apply(rule ext, simp add: OclAnd_def) 
  apply(auto simp:true_def false_def null_def invalid_def 
             split: option.split option.split_asm
                    bool.split bool.split_asm)
done


lemma OclOr_idem[simp]: "(X or X) = X"
  by(simp add: OclOr_def)

lemma OclOr_commute: "(X or Y) = (Y or X)"
  by(simp add: OclOr_def OclAnd_commute)

lemma OclOr_false1[simp]: "(false or Y) = Y"
  by(simp add: OclOr_def)

lemma OclOr_false2[simp]: "(Y or false) = Y"
  by(simp add: OclOr_def)

lemma OclOr_true1[simp]: "(true or Y) = true"
  by(simp add: OclOr_def)

lemma OclOr_true2: "(Y or true) = true"
  by(simp add: OclOr_def)

lemma OclOr_assoc: "(X or (Y or Z)) = (X or Y or Z)"
  by(simp add: OclOr_def OclAnd_assoc)

lemma deMorgan1: "not(X and Y) = ((not X) or (not Y))"
  by(simp add: OclOr_def)

lemma deMorgan2: "not(X or Y) = ((not X) and (not Y))"
  by(simp add: OclOr_def)
 

section{* A Standard Logical Calculus for OCL *}
text{* Besides the need for algebraic laws for OCL in order to normalize *}
definition OclValid  :: "[('\<AA>)st, ('\<AA>)Boolean] \<Rightarrow> bool" ("(1(_)/ \<Turnstile> (_))" 50)
where     "\<tau> \<Turnstile> P \<equiv> ((P \<tau>) = true \<tau>)"

subsection{* Global vs. Local Judgements*}
lemma transform1: "P = true \<Longrightarrow> \<tau> \<Turnstile> P"
by(simp add: OclValid_def)


lemma transform1_rev: "\<forall> \<tau>. \<tau> \<Turnstile> P \<Longrightarrow> P = true"
by(rule ext, auto simp: OclValid_def true_def)

lemma transform2: "(P = Q) \<Longrightarrow> ((\<tau> \<Turnstile> P) = (\<tau> \<Turnstile> Q))"
by(auto simp: OclValid_def)

lemma transform2_rev: "\<forall> \<tau>. (\<tau> \<Turnstile> \<delta> P) \<and> (\<tau> \<Turnstile> \<delta> Q) \<and> (\<tau> \<Turnstile> P) = (\<tau> \<Turnstile> Q) \<Longrightarrow> P = Q"
apply(rule ext,auto simp: OclValid_def true_def defined_def)
apply(erule_tac x=a in allE)
apply(erule_tac x=b in allE)
apply(auto simp: false_def true_def defined_def bot_Boolean_def null_Boolean_def 
                 split: option.split_asm HOL.split_if_asm)
done
(* Something stronger is possible here (consider P null, Q invalid),
   but this thingi should do for our purpose *)

text{* However, certain properties (like transitivity) can not
       be \emph{transformed} from the global level to the local one, 
       they have to be re-proven on the local level. *}

lemma transform3: 
assumes H : "P = true \<Longrightarrow> Q = true"
shows "\<tau> \<Turnstile> P \<Longrightarrow> \<tau> \<Turnstile> Q"
apply(simp add: OclValid_def)
apply(rule H[THEN fun_cong])
apply(rule ext)
oops

subsection{* Local Validity and Meta-logic*}

lemma foundation1[simp]: "\<tau> \<Turnstile> true"
by(auto simp: OclValid_def)

lemma foundation2[simp]: "\<not>(\<tau> \<Turnstile> false)"
by(auto simp: OclValid_def true_def false_def)

lemma foundation3[simp]: "\<not>(\<tau> \<Turnstile> invalid)"
by(auto simp: OclValid_def true_def false_def invalid_def bot_option_def)

lemma foundation4[simp]: "\<not>(\<tau> \<Turnstile> null)"
by(auto simp: OclValid_def true_def false_def null_def null_fun_def null_option_def bot_option_def)

lemma bool_split_local[simp]: 
"(\<tau> \<Turnstile> (x \<triangleq> invalid)) \<or> (\<tau> \<Turnstile> (x \<triangleq> null)) \<or> (\<tau> \<Turnstile> (x \<triangleq> true)) \<or> (\<tau> \<Turnstile> (x \<triangleq> false))" 
apply(insert bool_split[of x \<tau>], auto)
apply(simp_all add: OclValid_def StrongEq_def true_def null_def invalid_def)
done

lemma def_split_local: 
"(\<tau> \<Turnstile> \<delta> x) = ((\<not>(\<tau> \<Turnstile> (x \<triangleq> invalid))) \<and> (\<not> (\<tau> \<Turnstile> (x \<triangleq> null))))"
by(simp add:defined_def true_def false_def invalid_def null_def 
               StrongEq_def OclValid_def bot_fun_def null_fun_def)

lemma foundation5: 
"\<tau> \<Turnstile> (P and Q) \<Longrightarrow> (\<tau> \<Turnstile> P) \<and> (\<tau> \<Turnstile> Q)"
by(simp add: OclAnd_def OclValid_def true_def false_def defined_def
             split: option.split option.split_asm bool.split bool.split_asm)

lemma foundation6: 
"\<tau> \<Turnstile> P \<Longrightarrow> \<tau> \<Turnstile> \<delta> P"
by(simp add: OclNot_def OclValid_def true_def false_def defined_def 
                null_option_def null_fun_def bot_option_def bot_fun_def
             split: option.split option.split_asm)


lemma foundation7[simp]: 
"(\<tau> \<Turnstile> not (\<delta> x)) = (\<not> (\<tau> \<Turnstile> \<delta> x))"
by(simp add: OclNot_def OclValid_def true_def false_def defined_def
             split: option.split option.split_asm)

lemma foundation7'[simp]: 
"(\<tau> \<Turnstile> not (\<upsilon> x)) = (\<not> (\<tau> \<Turnstile> \<upsilon> x))"
by(simp add: OclNot_def OclValid_def true_def false_def valid_def
             split: option.split option.split_asm)


text{* Key theorem for the Delta-closure: either an expression
is defined, or it can be replaced (substituted via \verb+StrongEq_L_subst2+; see
below) by invalid or null. Strictness-reduction rules will usually 
reduce these substituted terms drastically.  *}
lemma foundation8: 
"(\<tau> \<Turnstile> \<delta> x) \<or> (\<tau> \<Turnstile> (x \<triangleq> invalid)) \<or> (\<tau> \<Turnstile> (x \<triangleq> null))"
proof -
  have 1 : "(\<tau> \<Turnstile> \<delta> x) \<or> (\<not>(\<tau> \<Turnstile> \<delta> x))" by auto
  have 2 : "(\<not>(\<tau> \<Turnstile> \<delta> x)) = ((\<tau> \<Turnstile> (x \<triangleq> invalid)) \<or> (\<tau> \<Turnstile> (x \<triangleq> null)))"
           by(simp only: def_split_local, simp) 
  show ?thesis by(insert 1, simp add:2)
qed

lemma foundation9:
"\<tau> \<Turnstile> \<delta> x \<Longrightarrow> (\<tau> \<Turnstile> not x) = (\<not> (\<tau> \<Turnstile> x))"
apply(simp add: def_split_local )
by(auto simp: OclNot_def null_fun_def null_option_def bot_option_def 
                 OclValid_def invalid_def true_def null_def StrongEq_def)


lemma foundation10:
"\<tau> \<Turnstile> \<delta> x \<Longrightarrow> \<tau> \<Turnstile> \<delta> y \<Longrightarrow> (\<tau> \<Turnstile> (x and y)) = ( (\<tau> \<Turnstile> x) \<and> (\<tau> \<Turnstile> y))"
apply(simp add: def_split_local)
by(auto simp: OclAnd_def OclValid_def invalid_def 
              true_def null_def StrongEq_def null_fun_def null_option_def bot_option_def
        split:bool.split_asm)


lemma foundation11:
"\<tau> \<Turnstile> \<delta> x \<Longrightarrow>  \<tau> \<Turnstile> \<delta> y \<Longrightarrow> (\<tau> \<Turnstile> (x or y)) = ( (\<tau> \<Turnstile> x) \<or> (\<tau> \<Turnstile> y))"
apply(simp add: def_split_local)
by(auto simp: OclNot_def OclOr_def OclAnd_def OclValid_def invalid_def 
              true_def null_def StrongEq_def null_fun_def null_option_def bot_option_def
        split:bool.split_asm bool.split)



lemma foundation12:
"\<tau> \<Turnstile> \<delta> x \<Longrightarrow>  \<tau> \<Turnstile> \<delta> y \<Longrightarrow> (\<tau> \<Turnstile> (x implies y)) = ( (\<tau> \<Turnstile> x) \<longrightarrow> (\<tau> \<Turnstile> y))"
apply(simp add: def_split_local)
by(auto simp: OclNot_def OclOr_def OclAnd_def OclImplies_def bot_option_def
              OclValid_def invalid_def true_def null_def StrongEq_def null_fun_def null_option_def 
        split:bool.split_asm bool.split)

lemma foundation13:"(\<tau> \<Turnstile> A \<triangleq> true)    = (\<tau> \<Turnstile> A)" 
by(auto simp: OclNot_def  OclValid_def invalid_def true_def null_def StrongEq_def
           split:bool.split_asm bool.split)

lemma foundation14:"(\<tau> \<Turnstile> A \<triangleq> false)   = (\<tau> \<Turnstile> not A)" 
by(auto simp: OclNot_def  OclValid_def invalid_def false_def true_def null_def StrongEq_def 
        split:bool.split_asm bool.split option.split)

lemma foundation15:"(\<tau> \<Turnstile> A \<triangleq> invalid) = (\<tau> \<Turnstile> not(\<upsilon> A))" 
by(auto simp: OclNot_def  OclValid_def valid_def invalid_def false_def true_def null_def 
                 StrongEq_def bot_option_def null_fun_def null_option_def bot_option_def bot_fun_def
         split:bool.split_asm bool.split option.split)
 

(* ... and the usual rules on strictness, definedness propoagation, and cp ... *)
lemma foundation16: "\<tau> \<Turnstile> (\<delta> X) = (X \<tau> \<noteq> bot \<and> X \<tau> \<noteq> null)"
by(auto simp: OclValid_def defined_def false_def true_def  bot_fun_def null_fun_def
        split:split_if_asm)

lemmas foundation17 = foundation16[THEN iffD1,standard]

lemma foundation18: "\<tau> \<Turnstile> (\<upsilon> X) = (X \<tau> \<noteq> invalid \<tau>)"
by(auto simp: OclValid_def valid_def false_def true_def bot_fun_def invalid_def
        split:split_if_asm)

(*legacy*)
lemma foundation18': "\<tau> \<Turnstile> (\<upsilon> X) = (X \<tau> \<noteq> bot)"
by(auto simp: OclValid_def valid_def false_def true_def bot_fun_def
        split:split_if_asm)


lemmas foundation19 = foundation18[THEN iffD1,standard]

lemma foundation20 : "\<tau> \<Turnstile> (\<delta> X) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> X"
by(simp add: foundation18 foundation16 invalid_def) 

lemma foundation21: "(not A \<triangleq> not B) = (A \<triangleq> B)"
by(rule ext, auto simp: OclNot_def StrongEq_def
                     split: bool.split_asm HOL.split_if_asm option.split)

lemma foundation22: "(\<tau> \<Turnstile> (X \<triangleq> Y)) = (X \<tau> = Y \<tau>)"
by(auto simp: StrongEq_def OclValid_def true_def) 

lemma foundation23: "(\<tau> \<Turnstile> P) = (\<tau> \<Turnstile> (\<lambda> _ . P \<tau>))"
by(auto simp: OclValid_def true_def) 

lemmas cp_validity=foundation23

lemma defined_not_I : "\<tau> \<Turnstile> \<delta> (x) \<Longrightarrow> \<tau> \<Turnstile> \<delta> (not x)" 
  by(auto simp: OclNot_def null_def invalid_def defined_def valid_def OclValid_def
                  true_def false_def bot_option_def null_option_def null_fun_def bot_fun_def
             split: option.split_asm HOL.split_if_asm)

lemma valid_not_I : "\<tau> \<Turnstile> \<upsilon> (x) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> (not x)" 
  by(auto simp: OclNot_def null_def invalid_def defined_def valid_def OclValid_def
                  true_def false_def bot_option_def null_option_def null_fun_def bot_fun_def
          split: option.split_asm option.split HOL.split_if_asm)

lemma defined_and_I : "\<tau> \<Turnstile> \<delta> (x) \<Longrightarrow>  \<tau> \<Turnstile> \<delta> (y) \<Longrightarrow> \<tau> \<Turnstile> \<delta> (x and y)" 
  apply(simp add: OclAnd_def null_def invalid_def defined_def valid_def OclValid_def
                  true_def false_def bot_option_def null_option_def null_fun_def bot_fun_def
             split: option.split_asm HOL.split_if_asm)
  apply(auto simp: null_option_def split: bool.split)
  by(case_tac "ya",simp_all)

lemma valid_and_I :   "\<tau> \<Turnstile> \<upsilon> (x) \<Longrightarrow>  \<tau> \<Turnstile> \<upsilon> (y) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> (x and y)" 
  apply(simp add: OclAnd_def null_def invalid_def defined_def valid_def OclValid_def
                  true_def false_def bot_option_def null_option_def null_fun_def bot_fun_def
             split: option.split_asm HOL.split_if_asm)
  by(auto simp: null_option_def split: option.split bool.split)

subsection{* Local Judgements and Strong Equality *}

lemma StrongEq_L_refl: "\<tau> \<Turnstile> (x \<triangleq> x)"
by(simp add: OclValid_def StrongEq_def)


lemma StrongEq_L_sym: "\<tau> \<Turnstile> (x \<triangleq> y) \<Longrightarrow> \<tau> \<Turnstile> (y \<triangleq> x)"
by(simp add: StrongEq_sym)

lemma StrongEq_L_trans: "\<tau> \<Turnstile> (x \<triangleq> y) \<Longrightarrow> \<tau> \<Turnstile> (y \<triangleq> z) \<Longrightarrow> \<tau> \<Turnstile> (x \<triangleq> z)"
by(simp add: OclValid_def StrongEq_def true_def)

text{* In order to establish substitutivity (which does not
hold in general HOL-formulas we introduce the following 
predicate that allows for a calculus of the necessary side-conditions.*}
definition cp   :: "(('\<AA>,'\<alpha>) val \<Rightarrow> ('\<AA>,'\<beta>) val) \<Rightarrow> bool"
where     "cp P \<equiv> (\<exists> f. \<forall> X \<tau>. P X \<tau> = f (X \<tau>) \<tau>)"


text{* The rule of substitutivity in HOL-OCL holds only 
for context-passing expressions - i.e. those, that pass
the context @{text "\<tau>"} without changing it. Fortunately, all 
operators of the OCL language satisfy this property 
(but not all HOL operators).*}

lemma StrongEq_L_subst1: "\<And> \<tau>. cp P \<Longrightarrow> \<tau> \<Turnstile> (x \<triangleq> y) \<Longrightarrow> \<tau> \<Turnstile> (P x \<triangleq> P y)"
by(auto simp: OclValid_def StrongEq_def true_def cp_def)

lemma StrongEq_L_subst2: 
"\<And> \<tau>.  cp P \<Longrightarrow> \<tau> \<Turnstile> (x \<triangleq> y) \<Longrightarrow> \<tau> \<Turnstile> (P x) \<Longrightarrow> \<tau> \<Turnstile> (P y)"
by(auto simp: OclValid_def StrongEq_def true_def cp_def)

lemma StrongEq_L_subst2_rev: "\<tau> \<Turnstile> y \<triangleq> x \<Longrightarrow> cp P \<Longrightarrow> \<tau> \<Turnstile> P x \<Longrightarrow> \<tau> \<Turnstile> P y"
apply(erule StrongEq_L_subst2)
apply(erule StrongEq_L_sym)
by assumption
(* for an automated version of ocl_subst *)
ML{* (* just a fist sketch *)
fun ocl_subst_tac subst = 
          let val foundation22_THEN_iffD1 = @{thm foundation22} RS @{thm iffD1}
              val StrongEq_L_subst2_rev_ = @{thm StrongEq_L_subst2_rev}
              val the_context = @{context} (* Hack of bu : will not work in general *)
          in  EVERY[rtac foundation22_THEN_iffD1 1,
                    eres_inst_tac the_context [(("P",0),subst)] StrongEq_L_subst2_rev_ 1,
                    simp_tac (simpset_of the_context) 1,
                    simp_tac (simpset_of the_context) 1]
          end
                    
 *}

lemma cpI1:
"(\<forall> X \<tau>. f X \<tau> = f(\<lambda>_. X \<tau>) \<tau>) \<Longrightarrow> cp P \<Longrightarrow> cp(\<lambda>X. f (P X))"
apply(auto simp: true_def cp_def)
apply(rule exI, (rule allI)+)
by(erule_tac x="P X" in allE, auto)

lemma cpI2:
"(\<forall> X Y \<tau>. f X Y \<tau> = f(\<lambda>_. X \<tau>)(\<lambda>_. Y \<tau>) \<tau>) \<Longrightarrow> 
 cp P \<Longrightarrow> cp Q \<Longrightarrow> cp(\<lambda>X. f (P X) (Q X))"
apply(auto simp: true_def cp_def)
apply(rule exI, (rule allI)+)
by(erule_tac x="P X" in allE, auto)

lemma cpI3:
"(\<forall> X Y Z \<tau>. f X Y Z \<tau> = f(\<lambda>_. X \<tau>)(\<lambda>_. Y \<tau>)(\<lambda>_. Z \<tau>) \<tau>) \<Longrightarrow> 
 cp P \<Longrightarrow> cp Q \<Longrightarrow> cp R \<Longrightarrow> cp(\<lambda>X. f (P X) (Q X) (R X))"
apply(auto simp: true_def cp_def)
apply(rule exI, (rule allI)+)
by(erule_tac x="P X" in allE, auto)

lemma cpI4:
"(\<forall> W X Y Z \<tau>. f W X Y Z \<tau> = f(\<lambda>_. W \<tau>)(\<lambda>_. X \<tau>)(\<lambda>_. Y \<tau>)(\<lambda>_. Z \<tau>) \<tau>) \<Longrightarrow> 
 cp P \<Longrightarrow> cp Q \<Longrightarrow> cp R \<Longrightarrow> cp S \<Longrightarrow> cp(\<lambda>X. f (P X) (Q X) (R X) (S X))"
apply(auto simp: true_def cp_def)
apply(rule exI, (rule allI)+)
by(erule_tac x="P X" in allE, auto)

lemma cp_const : "cp(\<lambda>_. c)"
  by (simp add: cp_def, fast)

lemma cp_id :     "cp(\<lambda>X. X)"
  by (simp add: cp_def, fast)

lemmas cp_intro[simp,intro!] = 
       cp_const 
       cp_id
       cp_defined[THEN allI[THEN allI[THEN cpI1], of defined]]
       cp_valid[THEN allI[THEN allI[THEN cpI1], of valid]]
       cp_OclNot[THEN allI[THEN allI[THEN cpI1], of not]]
       cp_OclAnd[THEN allI[THEN allI[THEN allI[THEN cpI2]], of "op and"]]
       cp_OclOr[THEN allI[THEN allI[THEN allI[THEN cpI2]], of "op or"]]
       cp_OclImplies[THEN allI[THEN allI[THEN allI[THEN cpI2]], of "op implies"]]
       cp_StrongEq[THEN allI[THEN allI[THEN allI[THEN cpI2]], 
             of "StrongEq"]]

subsection{* Laws to Establish Definedness (Delta-Closure) *}

text{* For the logical connectives, we have --- beyond
@{thm foundation6} --- the following facts:  *}
lemma OclNot_defargs: 
"\<tau> \<Turnstile> (not P) \<Longrightarrow> \<tau> \<Turnstile> \<delta> P"
by(auto simp: OclNot_def OclValid_def true_def invalid_def defined_def false_def
                 bot_fun_def bot_option_def null_fun_def null_option_def
        split: bool.split_asm HOL.split_if_asm option.split option.split_asm)

text{* So far, we have only one strict Boolean predicate (-family): The strict equality. *}

section{*Miscellaneous: OCL's if then else endif *}

definition OclIf :: "[('\<AA>)Boolean , ('\<AA>,'\<alpha>::null) val, ('\<AA>,'\<alpha>) val] \<Rightarrow> ('\<AA>,'\<alpha>) val"
                     ("if (_) then (_) else (_) endif" [10,10,10]50)
where "(if C then B\<^isub>1 else B\<^isub>2 endif) = (\<lambda> \<tau>. if (\<delta> C) \<tau> = true \<tau> 
                                           then (if (C \<tau>) = true \<tau> 
                                                then B\<^isub>1 \<tau> 
                                                else B\<^isub>2 \<tau>)
                                           else invalid \<tau>)"


lemma cp_OclIf:"((if C then B\<^isub>1 else B\<^isub>2 endif) \<tau> = 
                  (if (\<lambda> _. C \<tau>) then (\<lambda> _. B\<^isub>1 \<tau>) else (\<lambda> _. B\<^isub>2 \<tau>) endif) \<tau>)"
by(simp only: OclIf_def, subst cp_defined, rule refl)

lemmas cp_intro'[simp,intro!] =
       cp_intro
       cp_OclIf[THEN allI[THEN allI[THEN allI[THEN allI[THEN cpI3]]], of "OclIf"]]

lemma OclIf_invalid [simp]: "(if invalid then B\<^isub>1 else B\<^isub>2 endif) = invalid"
by(rule ext, auto simp: OclIf_def)

lemma OclIf_null [simp]: "(if null then B\<^isub>1 else B\<^isub>2 endif) = invalid"
by(rule ext, auto simp: OclIf_def)

lemma OclIf_true [simp]: "(if true then B\<^isub>1 else B\<^isub>2 endif) = B\<^isub>1"
by(rule ext, auto simp: OclIf_def)

lemma OclIf_true' [simp]: "\<tau> \<Turnstile> P \<Longrightarrow> (if P then B\<^isub>1 else B\<^isub>2 endif)\<tau> = B\<^isub>1 \<tau>"
apply(subst cp_OclIf,auto simp: OclValid_def)
by(simp add:cp_OclIf[symmetric])

lemma OclIf_false [simp]: "(if false then B\<^isub>1 else B\<^isub>2 endif) = B\<^isub>2"
by(rule ext, auto simp: OclIf_def)

lemma OclIf_false' [simp]: "\<tau> \<Turnstile> not P \<Longrightarrow> (if P then B\<^isub>1 else B\<^isub>2 endif)\<tau> = B\<^isub>2 \<tau>"
apply(subst cp_OclIf)
apply(auto simp: foundation14[symmetric] foundation22)
by(auto simp: cp_OclIf[symmetric])


lemma OclIf_idem1[simp]:"(if \<delta> X then A else A endif) = A" 
by(rule ext, auto simp: OclIf_def)

lemma OclIf_idem2[simp]:"(if \<upsilon> X then A else A endif) = A" 
by(rule ext, auto simp: OclIf_def)


end
