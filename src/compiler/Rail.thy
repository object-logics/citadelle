(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Rail.thy ---
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013-2015 Université Paris-Saclay, Univ Paris Sud, France
 *               2013-2015 IRT SystemX, France
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

header\<open>Part ...\<close>

(*<*)
theory Rail
imports "../UML_Types"
        Aux_text
        Generator_dynamic
begin
ML_file "~~/src/Doc/antiquote_setup.ML"
(*>*)

section\<open>The Meta Compiler\<close>
text \<open>
\begin{matharray}{rcl}
  @{command_def generation_syntax} & : & @{text "theory \<rightarrow> theory"}
\end{matharray}

@{rail \<open>
  @@{command generation_syntax}
    ( '[' (@{syntax syntax} * ',') ']'
    | @{syntax syntax}
    | @'deep' @'flush_all')
  ;
  @{syntax_def syntax}:
                 @'deep' @{syntax semantics} @{syntax deep_embedding}
               | @'shallow' @{syntax semantics} @{syntax long_or_dirty}
               | @'syntax_print' number?
  ;
  @{syntax_def semantics}:
               ('(' @'generation_semantics' \<newline>
                 ('[' (@'design' | @'analysis') (',' @'oid_start' nat)? ']') ')')?
  ;
  @{syntax_def deep_embedding}:
               (@'skip_export')? \<newline>
               ('(' @'THEORY' name ')' \<newline>
                '(' @'IMPORTS' '[' (name * ',') ']' name ')')? \<newline>
               (@'SECTION')? \<newline>
               @{syntax long_or_dirty} \<newline>
               ('[' (@{syntax export_code} + ',') ']') \<newline>
               ('(' @'output_directory' name ')')?
  ;
  @{syntax_def export_code}:
               @'in' (  'Haskell'
                      | ((  'OCaml'
                          | 'Scala'
                          | 'SML') @'module_name' name)) ( '(' args ')' ) ?
  ;
  @{syntax_def long_or_dirty}:
               (@'SORRY' | @'no_dirty')?
  ;
\<close>}
\<close>

section\<open>UML/OCL: Extended USE Grammar\<close>
subsection\<open>.......................................................................................................................................\<close>
text \<open>
\begin{matharray}{rcl}
  @{command_def Class} & : & @{text "theory \<rightarrow> theory"} \\
  @{command_def Abstract_class} & : & @{text "theory \<rightarrow> theory"} \\
\end{matharray}

@{rail \<open>
  (  @@{command Class}
   | @@{command Abstract_class})
                   (  binding '=' @{syntax type_base}
                    | @{syntax type_object}
                      @{syntax class})
  ;
  @{syntax_def class}:
               @'Attributes'? ((binding ':' @{syntax uml_type}) * (';'?)) \<newline>
               @{syntax context}
  ;
  @{syntax_def context}:
            (( ((() | @'Operations' | '::')
                binding @{syntax uml_type} \<newline>
                ('=' term | term)? (((@'Pre' | @'Post') @{syntax use_prop}
                                    | @{syntax invariant}) * ())
               )
             | @{syntax invariant}) * ())
  ;
  @{syntax_def invariant}:
               @'Constraints'? @'Existential'? @'Inv' @{syntax use_prop}
  ;
\<close>}
\<close>
subsection\<open>.......................................................................................................................................\<close>
text \<open>
\begin{matharray}{rcl}
  @{command_def Aggregation} & : & @{text "theory \<rightarrow> theory"} \\
  @{command_def Association} & : & @{text "theory \<rightarrow> theory"} \\
  @{command_def Composition} & : & @{text "theory \<rightarrow> theory"}
\end{matharray}

@{rail \<open>
  (  @@{command Aggregation}
   | @@{command Association}
   | @@{command Composition}) binding? @{syntax association}
  ;
  @{syntax_def association}:
               @'Between'? (@{syntax association_end} (@{syntax association_end}+))?
  ;
  @{syntax_def association_end}:
               @{syntax type_object}
               @{syntax category}
               ';'?
  ;
\<close>}
\<close>
subsection\<open>.......................................................................................................................................\<close>
text \<open>
\begin{matharray}{rcl}
  @{command_def Associationclass} & : & @{text "theory \<rightarrow> theory"} \\
  @{command_def Abstract_associationclass} & : & @{text "theory \<rightarrow> theory"}
\end{matharray}

@{rail \<open>
  (  @@{command Associationclass}
   | @@{command Abstract_associationclass}) @{syntax type_object} \<newline>
                                            @{syntax association} @{syntax class} (() | 'aggregation' | 'composition')
  ;
\<close>}
\<close>
subsection\<open>.......................................................................................................................................\<close>
text \<open>
\begin{matharray}{rcl}
  @{command_def Context} & : & @{text "theory \<rightarrow> theory"}
\end{matharray}

@{rail \<open>
  @@{command Context} ('[' @'shallow' ']')? @{syntax type_object} @{syntax context}
  ;
\<close>}
\<close>

subsection\<open>.......................................................................................................................................\<close>
text \<open>
\begin{matharray}{rcl}
  @{command_def Instance} & : & @{text "theory \<rightarrow> theory"}
\end{matharray}

@{rail \<open>
  @@{command Instance} ((binding ('::' @{syntax type_object})? '=' \<newline>
                         (@{syntax term_object} | @{syntax object_cast})) * ('and'?))
  ;
  @{syntax_def term_object}:
                 ('[' ((('(' binding ',' binding ')' '|=')? \<newline>
                        binding '=' @{syntax uml_term}) * ',') ']')
  ;
  @{syntax_def object_cast}:
               '(' @{syntax term_object} '::' @{syntax type_object} ')' \<newline>
               (('\<rightarrow>' 'oclAsType' '(' @{syntax type_object} ')') * ())
  ;
\<close>}
\<close>
subsection\<open>.......................................................................................................................................\<close>
text \<open>
\begin{matharray}{rcl}
  @{command_def State} & : & @{text "theory \<rightarrow> theory"}
\end{matharray}

@{rail \<open>
  @@{command State} ('[' @'shallow' ']')? binding ('=' @{syntax state})?
  ;
  @{syntax_def state}:
               '[' ((binding | @{syntax object_cast}) * ',') ']'
  ;
\<close>}
\<close>
subsection\<open>.......................................................................................................................................\<close>
text \<open>
\begin{matharray}{rcl}
  @{command_def PrePost} & : & @{text "theory \<rightarrow> theory"}
\end{matharray}

@{rail \<open>
  @@{command PrePost} ('[' @'shallow' ']')? (binding '=')? \<newline>
    @{syntax pre_post}
    @{syntax pre_post}?
  ;
  @{syntax_def pre_post}:
               binding | @{syntax state}
  ;
\<close>}
\<close>
(*
subsection\<open>.......................................................................................................................................\<close>
text \<open>
\begin{matharray}{rcl}
  @{command_def Enum} & : & @{text "theory \<rightarrow> theory"}
\end{matharray}

@{rail \<open>
  @@{command Enum} binding '[' (binding * ',') ']'
  ;
\<close>}
\<close>
*)
section\<open>UML/OCL: Type System\<close>
subsection\<open>.......................................................................................................................................\<close>
text \<open>
@{rail \<open>
  @{syntax_def unlimited_natural}:
               ('*'| '\<infinity>') | number
  ;
  @{syntax_def term_base}:
                 ('true' | 'false')
               | @{syntax unlimited_natural}
               | number
               | float_number
               | string
  ;
  @{syntax_def multiplicity}:
               '[' ((@{syntax unlimited_natural} ('\<bullet>\<bullet>' @{syntax unlimited_natural})?) * ',') ']'
  ;
  @{syntax_def uml_term}:
                 @{syntax term_base}
               | @{syntax multiplicity}

               | binding

               | @'self' nat?
               | '[' (@{syntax uml_term} * ',') ']'
               | '(' (@{syntax uml_term} * ',') ')'

               | '\<langle>' term '\<rangle>'
  ;
  @{syntax_def name_object}:
               ((binding + ',') ':')? binding
  ;
  @{syntax_def type_base}:
                 'Void'
               | 'Boolean'
               | 'UnlimitedNatural'
               | 'Integer'
               | 'Real'
               | 'String'
  ;
  @{syntax_def type_object}:
               @{syntax name_object} (('<' (@{syntax name_object} + ',')) * ())
  ;
  @{syntax_def category}:
               @{syntax multiplicity} \<newline>
               (@'Role' binding)? 
               (( @'Derived' '=' term
                | @'Nonunique'
                | @'Ordered'
                | @'Qualifier' @{syntax uml_type}
                | @'Redefines' binding
                | @'Sequence_'
                | @'Subsets' binding
                | @'Union') * ())
  ;
  @{syntax_def uml_type}:
                 @{syntax type_base}
               | @{syntax type_object}

               | ('Sequence' | 'Set' | @{syntax category}) @{syntax uml_type}
               | 'Pair' ( @{syntax uml_type} @{syntax uml_type}
                        | '(' @{syntax uml_type} ',' @{syntax uml_type} ')')
               | '(' ((binding ':' ('(' @{syntax uml_type} ')' | uml_type_weak)) * ',') ')' \<newline>
                 (':' @{syntax uml_type})?
               | '(' @{syntax uml_type} ')'

               | '\<langle>' type '\<rangle>'
  ;
  @{syntax_def use_prop}:
              (  @{syntax type_object}
               | @{syntax association}
               | (binding? ':')? prop) (';'?)
  ;
\<close>}
\<close>
text\<open>uml\_type\_weak is like uml\_type except that type\_object can not contain quantified names.\<close>

section\<open>UML/OCL: Miscellaneous\<close>
subsection\<open>.......................................................................................................................................\<close>
text \<open>
\begin{matharray}{rcl}
  @{command_def End} & : & @{text "theory \<rightarrow> theory"}
\end{matharray}

@{rail \<open>
  @@{command End} ('[' 'forced' ']' | '!')?
\<close>}
\<close>
subsection\<open>.......................................................................................................................................\<close>
text \<open>
\begin{matharray}{rcl}
  @{command_def BaseType} & : & @{text "theory \<rightarrow> theory"}
\end{matharray}

@{rail \<open>
  @@{command BaseType} '[' (@{syntax term_base} * ',') ']'
  ;
\<close>}
\<close>

section\<open>Featherweight OCL: Library\<close>
text \<open>
\begin{matharray}{rcl}
  @{command_def Assert} & : & @{text "theory \<rightarrow> theory"} \\
  @{command_def Assert_local} & : & @{text "local_theory \<rightarrow> local_theory"}
\end{matharray}

@{rail \<open>
  @@{command Assert} term
  ;
  @@{command Assert_local} term
  ;
\<close>}
\<close>

section\<open>Featherweight OCL: Auxiliary\<close>
text \<open>
\begin{matharray}{rcl}
  @{command_def lazy_text} & : & @{text "local_theory \<rightarrow> local_theory"} \\
  @{command_def apply_text} & : & @{text "local_theory \<rightarrow> local_theory"} \\
  @{command_def reset_text} & : & @{text "local_theory \<rightarrow> local_theory"}
\end{matharray}

@{rail \<open>
  @@{command lazy_text} target? text
  ;
  @@{command apply_text} '(' ')'
  ;
  @@{command reset_text} '(' ')'
  ;
\<close>}
\<close>

section\<open>Featherweight OCL: Compiler\<close>
subsection\<open>.......................................................................................................................................\<close>
(* WARNING syntax errors during the extraction to LaTeX for the symbol "acute":
           fun\<acute>, definition\<acute> or code_reflect\<acute> *)
text \<open>
\begin{matharray}{rcl}
  @{command_def "fun'"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
  @{command_def "definition'"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
  @{command_def "code_reflect'"} & : & @{text "theory \<rightarrow> theory"}
\end{matharray}

@{rail \<open>
  @@{command "fun'"} target? functionopts? fixes \<newline>
                     @'where' equations
  ;
  @@{command "definition'"} target? \<newline>
                            (decl @'where')? thmdecl prop
  ;
  @@{command "code_reflect'"} @'open'? string \<newline>
    ( @'datatypes' ( string '=' ( '_' | ( string + '|' ) + @'and' ) ) ) ? \<newline>
    ( @'functions' ( string + ) ) ? ( @'file' string ) ?
  ;
\<close>}
\<close>

subsection\<open>.......................................................................................................................................\<close>
text \<open>
\begin{matharray}{rcl}
  @{command_def lazy_code_printing} & : & @{text "theory \<rightarrow> theory"} \\
  @{command_def apply_code_printing} & : & @{text "theory \<rightarrow> theory"} \\
  @{command_def apply_code_printing_reflect} & : & @{text "local_theory \<rightarrow> local_theory"}
\end{matharray}

@{rail \<open>
  @@{command lazy_code_printing}
      ( ( printing_const | printing_typeconstructor
      | printing_class | printing_class_relation | printing_class_instance
      | printing_module ) + '|' )
  ;
  @@{command apply_code_printing} '(' ')'
  ;
  @@{command apply_code_printing_reflect} text
  ;
\<close>}
\<close>

(*<*)
end
(*>*)
