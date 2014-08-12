(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_core.thy --- Core definitions.
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

header{* Formalization I: Core Definitions and OCL Types *}

theory    OCL_Types
imports   Main (* Testing *)
keywords "Assert" :: thy_decl
     and "Assert_local" :: thy_decl
begin

section{* Preliminaries *}
subsection{* Notations for the Option Type *}

text{*
  First of all, we will use a more compact notation for the library
  option type which occur all over in our definitions and which will make
  the presentation more like a textbook:
*}
notation Some ("\<lfloor>(_)\<rfloor>")
notation None ("\<bottom>")

text{*
  The following function (corresponding to @{term the} in the Isabelle/HOL library)
  is defined as the inverse of the injection @{term Some}.
*}
fun    drop :: "'\<alpha> option \<Rightarrow> '\<alpha>" ("\<lceil>(_)\<rceil>")
where  drop_lift[simp]: "\<lceil>\<lfloor>v\<rfloor>\<rceil> = v"

text{* The definitions for the constants and operations based on functions
will be geared towards a format that Isabelle can check to be a ``conservative''
(\ie, logically safe) axiomatic definition. By introducing an explicit
interpretation function (which happens to be defined just as the identity
since we are using a shallow embedding of OCL into HOL), all these definitions
can be rewritten into the conventional semantic textbook format.
To say it in other words: The interpretation function @{text Sem} as defined
below is just a textual marker for presentation purposes, i.e. intended for readers
used to conventional textbook notations on semantics. Since we use a ``shallow embedding'',
i.e. since we represent the syntax of OCL directly by HOL constants, the interpretation function
is semantically not only superfluous, but from an Isabelle perspective strictly in
the way for certain consistency checks performed by the definitional packages.
*}

definition Sem :: "'a \<Rightarrow> 'a" ("I\<lbrakk>_\<rbrakk>")
where "I\<lbrakk>x\<rbrakk> \<equiv> x"

subsection{* Minimal Notions of State and State Transitions *}
text{* In general, OCL operations are functions implicitly depending on a pair
of pre- and post-state. Since this will be reflected in our representation of
OCL Types within HOL, we need to introduce the foundational concept of an object id (oid),
which is just some infinite set, and some abstract notion of state. *}

text{* In order to assure executability of as much as possible formulas, we fixed the
type of object id's to just natural numbers.*}
type_synonym oid = nat

text{* We refrained from the alternative:
\begin{isar}[mathescape]
$\text{\textbf{type-synonym}}$ $\mathit{oid = ind}$
\end{isar}
which is slightly more abstract but non-executable.
*}

text{*
  States are just a partial map from oid's to elements of an object
  universe @{text "'\<AA>"}, and state transitions pairs of states
  \ldots
*}
record ('\<AA>)state =
             heap   :: "oid \<rightharpoonup> '\<AA> "
             assocs :: "oid \<rightharpoonup> (oid list list) list"


type_synonym ('\<AA>)st = "'\<AA> state \<times> '\<AA> state"

subsection{* Prerequisite: An Abstract Interface for OCL Types *}

text {* In order to have the possibility to nest collection types,
  such that we can give semantics to expressions like @{text "Set{Set{\<two>},null}"},
  it is necessary to introduce a uniform interface for types having
  the @{text "invalid"} (= bottom) element. The reason is that we impose
  a data-invariant on raw-collection \inlineisar|types_code| which assures
  that the @{text "invalid"} element is not allowed inside the collection;
  all raw-collections of this form were identified with the @{text "invalid"} element
  itself. The construction requires that the new collection type is
  not comparable with the raw-types (consisting of nested option type constructions),
  such that the data-invariant must be expressed in terms of the interface.
  In a second step, our base-types will be shown to be instances of this interface.
 *}

text{*
  This uniform interface consists in a type class requiring the existence
  of a bot and a null element. The construction proceeds by
  abstracting the null (defined by @{text "\<lfloor> \<bottom> \<rfloor>"} on
  @{text "'a option option"}) to a @{text null} element, which may
  have an arbitrary semantic structure, and an undefinedness element @{text "\<bottom> "}
  to an abstract undefinedness element @{text "bot"} (also written
  @{text "\<bottom> "} whenever no confusion arises). As a consequence, it is necessary
  to redefine the notions of invalid, defined, valuation etc.
  on top of this interface. *}

text{*
  This interface consists in two abstract type classes @{text bot}
  and @{text null} for the class of all types comprising a bot and a
  distinct null element.  *}
(*
instance option   :: (plus) plus  by intro_classes
instance "fun"    :: (type, plus) plus by intro_classes
*)
class   bot =
   fixes   bot :: "'a"
   assumes nonEmpty : "\<exists> x. x \<noteq> bot"


class      null = bot +
   fixes   null :: "'a"
   assumes null_is_valid : "null \<noteq> bot"


subsection{* Accommodation of Basic Types to the Abstract Interface *}

text{*
  In the following it is shown that the ``option-option'' type is
  in fact in the @{text null} class and that function spaces over these
  classes again ``live'' in these classes. This motivates the default construction
  of the semantic domain for the basic types (\inlineocl{Boolean},
  \inlineocl{Integer}, \inlineocl{Real}, \ldots).
*}

instantiation   option  :: (type)bot
begin
   definition bot_option_def: "(bot::'a option) \<equiv> (None::'a option)"
   instance proof show        "\<exists>x\<Colon>'a option. x \<noteq> bot"
                  by(rule_tac x="Some x" in exI, simp add:bot_option_def)
            qed
end


instantiation   option  :: (bot)null
begin
   definition null_option_def: "(null::'a\<Colon>bot option) \<equiv>  \<lfloor> bot \<rfloor>"
   instance proof  show        "(null::'a\<Colon>bot option) \<noteq> bot"
                   by( simp add : null_option_def bot_option_def)
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

subsection{* The Semantic Space of OCL Types: Valuations *}
text{* Since OCL operations in general depend on pre- and post-states, we will
represent OCL types as \emph{functions} from pre- and post-state to some
HOL raw-type that contains exactly the data in the OCL type --- see below. 
This gives rise to the idea that we represent OCL types by \emph{Valuations}.
*}
text{* Valuations are functions from a state pair (built upon
data universe @{typ "'\<AA>"}) to an arbitrary null-type (\ie, containing
at least a destinguished @{text "null"} and @{text "invalid"} element). *}

type_synonym ('\<AA>,'\<alpha>) val = "'\<AA> st \<Rightarrow> '\<alpha>::null"

text{* The definitions for the constants and operations based on valuations
will be geared towards a format that Isabelle can check to be a ``conservative''
(\ie, logically safe) axiomatic definition. By introducing an explicit
interpretation function (which happens to be defined just as the identity
since we are using a shallow embedding of OCL into HOL), all these definitions
can be rewritten into the conventional semantic textbook format  as follows: *}

subsection{* The fundamental constants 'invalid' and 'null'. *}

text{* As a consequence of semantic domain definition, any OCL type will
have the two semantic constants @{text "invalid"} (for exceptional, aborted
computation) and @{text "null"}:
 *}

definition invalid :: "('\<AA>,'\<alpha>::bot) val"
where     "invalid \<equiv> \<lambda> \<tau>. bot"

text{* This conservative Isabelle definition of the polymorphic constant
@{const invalid} is equivalent with the textbook definition: *}

lemma textbook_invalid: "I\<lbrakk>invalid\<rbrakk>\<tau> = bot"
by(simp add: invalid_def Sem_def)


text {* Note that the definition :
{\small
\begin{isar}[mathescape]
definition null    :: "('$\mathfrak{A}$,'\<alpha>::null) val"
where     "null    \<equiv> \<lambda> \<tau>. null"
\end{isar}
} is not  necessary since we defined the entire function space over null types
again as null-types; the crucial definition is @{thm "null_fun_def"}.
Thus, the polymorphic constant @{const null} is simply the result of
a general type class construction. Nevertheless, we can derive the
semantic textbook definition for the OCL null constant based on the
abstract null:
*}

lemma textbook_null_fun: "I\<lbrakk>null::('\<AA>,'\<alpha>::null) val\<rbrakk> \<tau> = (null::'\<alpha>::null)"
by(simp add: null_fun_def Sem_def)

section{* Basic OCL Types *}

text{* The semantic domain of the (basic) boolean type is now defined as the Standard:
the space of valuation to @{typ "bool option option"}, \ie{} the Boolean base type:*}

type_synonym Boolean\<^sub>b\<^sub>a\<^sub>s\<^sub>e  = "bool option option"
type_synonym ('\<AA>)Boolean = "('\<AA>,Boolean\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"

text{* Because of the previous class definitions, Isabelle type-inference establishes that
@{typ "('\<AA>)Boolean"} lives actually both in the type class @{term bot} and @{term null};
this type is sufficiently rich to contain at least these two elements.
Analogously we build: *}
type_synonym Integer\<^sub>b\<^sub>a\<^sub>s\<^sub>e  = "int option option"
type_synonym ('\<AA>)Integer = "('\<AA>,Integer\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"

type_synonym String\<^sub>b\<^sub>a\<^sub>s\<^sub>e  = "string option option"
type_synonym ('\<AA>)String = "('\<AA>,String\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"

text{* Slightly atypic are the definitions:*}
type_synonym Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e = "unit option"
type_synonym ('\<AA>)Void = "('\<AA>,Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"

(* type_synonym Real\<^sub>b\<^sub>a\<^sub>s\<^sub>e = "real option option" : 
   Only when Theory Real or Transcendent were imported *)
type_synonym Real\<^sub>b\<^sub>a\<^sub>s\<^sub>e  = "nat option option"
type_synonym ('\<AA>)Real = "('\<AA>,Real\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"

text{* Since @{term "Real"} is again a basic type, we define its semantic domain
as the valuations over @{text "real option option"} --- i.e. the mathematical type of real numbers.
The HOL-theory for @{text real} ``Real'' transcendental numbers such as $\pi$ and $e$ as well as
infrastructure to reason over infinite convergent Cauchy-sequences (it is thus possible, in principle,
to reason that the sum of two-s exponentials is actually 2.

If needed, a code-generator to compile @{text "Real"} to floating-point
numbers can be added; this allows for mapping reals to an efficient machine representation;
of course, this feature would be logically unsafe.*}

section{* Some OCL Collection Types *}
text{* The construction of collection types is sligtly more involved: We need to define an
concrete type, constrain it via a kind of data-invariant to ``legitimate elements'' (\ie{}
in our type will be ``no junk, no confusion''), and abstract it to a new type constructor.*}

subsection{* The Construction of the Pair Type (Tuples) *}

text{* The core of an own type construction is done via a type
  definition which provides the base-type @{text "('\<alpha>, '\<beta>) Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e"}. It
  is shown that this type ``fits'' indeed into the abstract type
  interface discussed in the previous section. *}

typedef ('\<alpha>, '\<beta>) Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e = "{X::('\<alpha>\<Colon>null \<times> '\<beta>\<Colon>null) option option.
                                       X = bot \<or> X = null \<or> (fst\<lceil>\<lceil>X\<rceil>\<rceil> \<noteq> bot \<and> snd\<lceil>\<lceil>X\<rceil>\<rceil> \<noteq> bot)}"
                          by (rule_tac x="bot" in exI, simp)

text{* We ``carve'' out from the concrete type @{typ "('\<alpha>\<Colon>null \<times> '\<beta>\<Colon>null) option option"} 
the new fully abstract type, which will not contain representations like @{term "\<lfloor>\<lfloor>(\<bottom>,a)\<rfloor>\<rfloor>"}
or @{term "\<lfloor>\<lfloor>(b,\<bottom>)\<rfloor>\<rfloor>"}. The type constuctor @{text "Pair{x,y}"} to be defined later will
identify these with @{term "invalid"}.
*}

instantiation   Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e  :: (null,null)bot
begin
   definition bot_Pair_0_def: "(bot_class.bot :: ('a\<Colon>null,'b\<Colon>null) Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<equiv> Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e None"

   instance proof show "\<exists>x\<Colon>('a,'b) Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e. x \<noteq> bot"
                  apply(rule_tac x="Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>" in exI)
                  apply(simp add:bot_Pair_0_def)
                  apply(subst Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject)
                  apply(simp_all add: bot_Pair_0_def
                                      null_option_def bot_option_def)
                  done
            qed
end

instantiation   Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e  :: (null,null)null
begin
   definition null_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def: "(null::('a::null,'b::null) Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<equiv> Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor> None \<rfloor>"

   instance proof show "(null::('a::null,'b::null) Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<noteq> bot"
                  apply(simp add:null_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Pair_0_def)
                  apply(subst Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject)
                  apply(simp_all add: bot_Pair_0_def null_option_def bot_option_def)
                  done
            qed
end


text{* ...  and lifting this type to the format of a valuation gives us:*}
type_synonym    ('\<AA>,'\<alpha>,'\<beta>) Pair  = "('\<AA>, ('\<alpha>,'\<beta>) Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"

subsection{* The Construction of the Set Type *}

text{* The core of an own type construction is done via a type
  definition which provides the raw-type @{text "'\<alpha> Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e"}. It
  is shown that this type ``fits'' indeed into the abstract type
  interface discussed in the previous section. Note that we make 
  no restriction whatsoever to \emph{finite} sets; the type
  constructor of FeatherWeight OCL is in fact infinite. *}

typedef '\<alpha> Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e ="{X::('\<alpha>\<Colon>null) set option option. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by (rule_tac x="bot" in exI, simp)

instantiation   Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e  :: (null)bot
begin

   definition bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def: "(bot::('a::null) Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<equiv> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e None"

   instance proof show "\<exists>x\<Colon>'a Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e. x \<noteq> bot"
                  apply(rule_tac x="Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>" in exI)
                  apply(simp add:bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
                  apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject)
                    apply(simp_all add: bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def
                                        null_option_def bot_option_def)
                  done
            qed
end

instantiation   Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e  :: (null)null
begin

   definition null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def: "(null::('a::null) Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<equiv> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor> None \<rfloor>"

   instance proof show "(null::('a::null) Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<noteq> bot"
                  apply(simp add:null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
                  apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject)
                    apply(simp_all add: bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_option_def bot_option_def)
                  done
            qed
end

text{* ...  and lifting this type to the format of a valuation gives us:*}
type_synonym    ('\<AA>,'\<alpha>) Set  = "('\<AA>, '\<alpha> Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"


(*<*)
section{* Miscelleaneous: ML assertions *}
text{* \fixme{Can we suppress this form the text ???} *}
text{* We introduce here a new command \emph{Assert} similar as \emph{value} for proving
 that the given term in argument is a true proposition. The difference with \emph{value} is that
\emph{Assert} fails if the normal form of the term evaluated is not equal to @{term True}. 
Moreover, in case \emph{value} could not normalize the given term, as another strategy of reduction
 we try to prove it with a single ``simp'' tactic. *}

ML{*
fun disp_msg title msg status = title ^ ": '" ^ msg ^ "' " ^ status

fun lemma msg specification_theorem concl in_local thy =
  SOME
    (in_local (fn lthy =>
           specification_theorem Thm.lemmaK NONE (K I) (@{binding ""}, []) [] [] 
             (Element.Shows [((@{binding ""}, []),[(concl lthy, [])])])
             false lthy
        |> Proof.global_terminal_proof
             ((Method.Then [Method.Basic (fn ctxt => SIMPLE_METHOD (asm_full_simp_tac ctxt 1))],
               (Position.none, Position.none)), NONE))
              thy)
  handle ERROR s =>
    (warning s; writeln (disp_msg "KO" msg "failed to normalize"); NONE)

fun outer_syntax_command command_spec theory in_local =
  Outer_Syntax.command command_spec "assert that the given specification is true"
    (Parse.term >> (fn elems_concl => theory (fn thy =>
      case
        lemma "code_unfold" Specification.theorem
          (fn lthy => 
            let val expr = Value.value lthy (Syntax.read_term lthy elems_concl)
                val thy = Proof_Context.theory_of lthy
                open HOLogic in
            if Sign.typ_equiv thy (fastype_of expr, @{typ "prop"}) then
              expr
            else mk_Trueprop (mk_eq (@{term "True"}, expr))
            end)
          in_local
          thy
      of  NONE => 
            let val attr_simp = "simp" in
            case lemma attr_simp Specification.theorem_cmd (K elems_concl) in_local thy of
               NONE => raise (ERROR "Assertion failed")
             | SOME thy => 
                (writeln (disp_msg "OK" "simp" "finished the normalization");
(* TO BE DONE
   why does this not work ? ? ?
   une regle importante est dans simp, mais pas dans code_unfold ... *)
                 thy)
            end
        | SOME thy => thy)))

fun in_local decl thy =
  thy
  |> Named_Target.init I ""
  |> decl
  |> Local_Theory.exit_global

val () = outer_syntax_command @{command_spec "Assert"} Toplevel.theory in_local 
val () = outer_syntax_command @{command_spec "Assert_local"} (Toplevel.local_theory NONE) I
(* TO BE DONE
   merge the two commands together *)
*}
(*>*)


end

