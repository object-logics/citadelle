(******************************************************************************
 * Generation of Language.C Grammar with ML Interface Binding
 *
 * Copyright (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
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

chapter \<open>Appendices\<close>

(*<*)
theory C_Appendices
  imports C_examples.C1
          C_Conclusion
          "~~/src/Doc/Isar_Ref/Base"
begin

ML \<comment> \<open>\<^file>\<open>~~/src/Doc/antiquote_setup.ML\<close>\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      Doc/antiquote_setup.ML
    Author:     Makarius

Auxiliary antiquotations for the Isabelle manuals.
*)
\<open>
structure C_Antiquote_Setup =
struct

(* misc utils *)

fun translate f = Symbol.explode #> map f #> implode;

val clean_string = translate
  (fn "_" => "\\_"
    | "#" => "\\#"
    | "$" => "\\$"
    | "%" => "\\%"
    | "<" => "$<$"
    | ">" => "$>$"
    | "{" => "\\{"
    | "|" => "$\\mid$"
    | "}" => "\\}"
    | "\<hyphen>" => "-"
    | c => c);

fun clean_name "\<dots>" = "dots"
  | clean_name ".." = "ddot"
  | clean_name "." = "dot"
  | clean_name "_" = "underscore"
  | clean_name "{" = "braceleft"
  | clean_name "}" = "braceright"
  | clean_name s = s |> translate (fn "_" => "-" | "\<hyphen>" => "-" | "\<approx>" => "symbol-lower-approx" | "\<Down>" => "symbol-upper-down" | c => c);


(* Isabelle/Isar entities (with index) *)

local

val arg = enclose "{" "}" o clean_string;

fun entity check markup binding index =
  Thy_Output.antiquotation_raw
    (binding |> Binding.map_name (fn name => name ^
      (case index of NONE => "" | SOME true => "_def" | SOME false => "_ref")))
    (Scan.lift (Scan.optional (Args.parens Args.name) "" -- Parse.position Args.name))
    (fn ctxt => fn (logic, (name, pos)) =>
      let
        val kind = translate (fn "_" => " " | c => c) (Binding.name_of binding);
        val hyper_name =
          "{" ^ Long_Name.append kind (Long_Name.append logic (clean_name name)) ^ "}";
        val hyper =
          enclose ("\\hyperlink" ^ hyper_name ^ "{") "}" #>
          index = SOME true ? enclose ("\\hypertarget" ^ hyper_name ^ "{") "}";
        val idx =
          (case index of
            NONE => ""
          | SOME is_def =>
              "\\index" ^ (if is_def then "def" else "ref") ^ arg logic ^ arg kind ^ arg name);
        val _ =
          if Context_Position.is_reported ctxt pos then ignore (check ctxt (name, pos)) else ();
        val latex =
          idx ^
          (Output.output name
            |> (if markup = "" then I else enclose ("\\" ^ markup ^ "{") "}")
            |> hyper o enclose "\\mbox{\\isa{" "}}");
      in Latex.string latex end);

fun entity_antiqs check markup kind =
  entity check markup kind NONE #>
  entity check markup kind (SOME true) #>
  entity check markup kind (SOME false);

in

val _ =
  Theory.setup
   (entity_antiqs C_Annotation.check_command "isacommand" @{binding annotation});

end;

end;

\<close>
(*>*)

section \<open>Architecture of Isabelle/C\<close>

text \<open>
\<^dir>\<open>copied_from_git\<close> represents the location of
external libraries needed by the C parser at run-time. At the time of
writing, it only contains
\<^dir>\<open>copied_from_git/mlton\<close>, and more specifically
\<^dir>\<open>copied_from_git/mlton/lib/mlyacc-lib\<close>. All
files in this last folder are solely used by
\<^theory>\<open>C.C_Parser_Language\<close>. The rest has been copied
from the original repository of MLton
\<^footnote>\<open>\<^url>\<open>https://github.com/MLton/mlton\<close>
and \<^url>\<open>https://gitlri.lri.fr/ftuong/mlton\<close>\<close>.
\<close>

text \<open>
The purpose of \<^dir>\<open>generated\<close> is to host generated
files, which are necessary for a first boot of the front-end. A major
subset of these files can actually be seen as superfluous, i.e., in
theory a simpler loading of a ``root un-generated file'' (generating
these files) would suffice, using for instance
\<^theory_text>\<open>code_reflect\<close>. However certain generators
are not written in a pure ML form (or are not yet automatically seen
as being translated to ML), so some manual steps of decomposition and
static generation was undertaken. In more detail:

  \<^item> \<^file>\<open>generated/c_ast.ML\<close> contains the
  Abstract Syntax Tree of C, which is loaded by
  \<^theory>\<open>C.C_Ast\<close>.
  
  \<^item> \<^file>\<open>generated/c_grammar_fun.grm\<close> is a
  generated file not used by the project, except for further
  generating \<^file>\<open>generated/c_grammar_fun.grm.sig\<close>
  and \<^file>\<open>generated/c_grammar_fun.grm.sml\<close>, or
  informative documentation purposes. It represents the basis point of
  our SML grammar file, generated by an initial Haskell grammar file
  (namely
  \<^url>\<open>https://github.com/visq/language-c/blob/master/src/Language/C/Parser/Parser.y\<close>).

  In short, it has to be compiled with a modified version of ML-Yacc,
  included in MLton itself
  (\<^url>\<open>https://gitlri.lri.fr/ftuong/mlton\<close>).

  \<^item> \<^file>\<open>generated/c_grammar_fun.grm.sig\<close>
  and \<^file>\<open>generated/c_grammar_fun.grm.sml\<close> are
  generated using the process described above.

\<close>

section \<open>Case Study: Mapping on the Parsed AST\<close>

text \<open> In this section, we give a concrete example of a situation where one is interested to
do some automated transformations on the parsed AST, such as changing the type of every encountered
variables from \<^C>\<open>int _;\<close> to \<^C>\<open>int _ [];\<close>. The main theory of
interest here is \<^theory>\<open>C.C_Parser_Language\<close>, where the C grammar is loaded, in
contrast to \<^theory>\<open>C.C_Lexer\<close> which is only dedicated to build a list of C
tokens. As another example, \<^theory>\<open>C.C_Parser_Language\<close> also contains the portion
of the code implementing the report to the user of various characteristics of encountered variables
during parsing: if a variable is bound or free, or if the declaration of a variable is made in the
global topmost space or locally declared in a function. \<close>

subsection \<open>Prerequisites\<close>

text \<open> Even if \<^file>\<open>generated/c_grammar_fun.grm.sig\<close> and
\<^file>\<open>generated/c_grammar_fun.grm.sml\<close> are files written in ML syntax, we have
actually modified \<^dir>\<open>copied_from_git/mlton/lib/mlyacc-lib\<close> in such a way that
at run time, the overall loading and execution of \<^theory>\<open>C.C_Parser_Language\<close> will
mimic all necessary features of the Haskell parser generator Happy
\<^footnote>\<open>\<^url>\<open>https://www.haskell.org/happy/doc/html/index.html\<close>\<close>,
including any monadic interactions between the lexing (\<^theory>\<open>C.C_Lexer\<close>) and
parsing part (\<^theory>\<open>C.C_Parser_Language\<close>).

This is why in the remaining part, we will at least assume a mandatory familiarity with Happy (e.g.,
the reading of ML-Yacc's manual can happen later if wished
\<^footnote>\<open>\<^url>\<open>https://www.cs.princeton.edu/~appel/modern/ml/ml-yacc/manual.html\<close>\<close>). In
particular, we will use the term \<^emph>\<open>rule code\<close> to designate \<^emph>\<open>a
Haskell expression enclosed in braces\<close>
\<^footnote>\<open>\<^url>\<open>https://www.haskell.org/happy/doc/html/sec-grammar.html\<close>\<close>.
\<close>

subsection \<open>Structure of \<^theory>\<open>C.C_Parser_Language\<close>\<close>

text \<open> In more detail, \<^theory>\<open>C.C_Parser_Language\<close> can be seen as being
principally divided into two parts:
  \<^item> a first part containing the implementation of
  \<^ML_structure>\<open>C_Grammar_Rule_Lib\<close>, which provides the ML implementation library
  used by any rule code written in the C grammar
  \<^url>\<open>https://github.com/visq/language-c/blob/master/src/Language/C/Parser/Parser.y\<close>
  (\<^file>\<open>generated/c_grammar_fun.grm.sml\<close>).
  \<^item> a second part implementing \<^ML_structure>\<open>C_Grammar_Rule_Wrap\<close>, providing
  one wrapping function for each rule code, for potentially complementing the rule code with an
  additional action to be executed after its call. The use of wrapping functions is very optional:
  by default, they are all assigned as identity functions.

The difference between \<^ML_structure>\<open>C_Grammar_Rule_Lib\<close> and
\<^ML_structure>\<open>C_Grammar_Rule_Wrap\<close> relies in how often functions in the two
structures are called: while building subtree pieces of the final AST, grammar rules are free to
call any functions in \<^ML_structure>\<open>C_Grammar_Rule_Lib\<close> for completing their
respective tasks, but also free to not use \<^ML_structure>\<open>C_Grammar_Rule_Lib\<close> at
all. On the other hand, irrespective of the actions done by a rule code, the function associated to
the rule code in \<^ML_structure>\<open>C_Grammar_Rule_Wrap\<close> is retrieved and always executed
(but a visible side-effect will likely mostly happen whenever one has provided an implementation far
different from \<^ML>\<open>I\<close>). \<close>

text \<open> Because the grammar
\<^url>\<open>https://github.com/visq/language-c/blob/master/src/Language/C/Parser/Parser.y\<close>
(\<^file>\<open>generated/c_grammar_fun.grm.sml\<close>) has been defined in such a way that
computation of variable scopes are completely handled by functions in
\<^ML_structure>\<open>C_Grammar_Rule_Lib\<close> and not in rule code (which are just calling
functions in \<^ML_structure>\<open>C_Grammar_Rule_Lib\<close>), it is enough to overload functions
in \<^ML_structure>\<open>C_Grammar_Rule_Lib\<close> whenever it is wished to perform new actions
depending on variable scopes, for example to do a specific PIDE report at the first time when a C
variable is being declared. In particular, functions in
\<^ML_structure>\<open>C_Grammar_Rule_Lib\<close> are implemented in monadic style, making a
subsequent modification on the parsing environment \<^theory>\<open>C.C_Environment\<close> possible
(whenever appropriate) as this last is carried in the monadic state.

Fundamentally, this is feasible because the monadic environment fulfills the property of being
always properly enriched with declared variable information at any time, because we assume
  \<^item> working with a language where a used variable must be at most declared or redeclared
  somewhere before its actual used,
  \<^item> and using a parser scanning tokens uniquely, from left to right, in the same order than
  the execution of rule code actions. \<close>

subsubsection \<open>Example\<close>

text \<open> As illustration, \<^ML>\<open>C_Grammar_Rule_Lib.markup_var true\<close> is
(implicitly) called by a rule code while a variable being declared is encountered. Later, a call to
\<^ML>\<open>C_Grammar_Rule_Lib.markup_var false\<close> in
\<^ML_structure>\<open>C_Grammar_Rule_Wrap\<close> (actually, in
\<^ML_structure>\<open>C_Grammar_Rule_Wrap_Overloading\<close>) is made after the execution of
another rule code to signal the position of a variable in use, together with the information
retrieved from the environment of the position of where it is declared. \<close>

text \<open> In more detail, the second argument of
\<^ML>\<open>C_Grammar_Rule_Lib.markup_var\<close> is among other of the form:
\<^ML_type>\<open>Position.T * {global: bool}\<close>, where particularly the field
\<^ML>\<open>#global : C_Env.markup_ident -> bool\<close> of the record is informing
\<^ML>\<open>C_Grammar_Rule_Lib.markup_var\<close> if the variable being reported (at either first
declaration time, or first use time) is global or local (inside a function for instance). Because
once declared, the property \<^ML>\<open>#global : C_Env.markup_ident -> bool\<close> of a variable
does not change afterwards, it is enough to store that information in the monadic environment:
\<^item> \<^bold>\<open>Storing the information at declaration time\<close> The part deciding if a
variable being declared is global or not is implemented in
\<^ML>\<open>C_Grammar_Rule_Lib.doDeclIdent\<close> and
\<^ML>\<open>C_Grammar_Rule_Lib.doFuncParamDeclIdent\<close>. The two functions come from
\<^url>\<open>https://github.com/visq/language-c/blob/master/src/Language/C/Parser/Parser.y\<close>
(so do any functions in \<^ML_structure>\<open>C_Grammar_Rule_Lib\<close>). Ultimately, they are
both calling \<^ML>\<open>C_Grammar_Rule_Lib.markup_var true\<close> at some point.
\<^item> \<^bold>\<open>Retrieving the information at use time\<close>
\<^ML>\<open>C_Grammar_Rule_Lib.markup_var false\<close> is only called by
\<^ML>\<open>C_Grammar_Rule_Wrap.primary_expression1\<close>, while treating a variable being
already declared. In particular the second argument of
\<^ML>\<open>C_Grammar_Rule_Lib.markup_var\<close> is just provided by what has been computed by the
above point when the variable was declared (e.g., the globality versus locality
information). \<close>

subsection \<open>Rewriting of AST node\<close>

text \<open> For the case of rewriting a specific AST node, from subtree \<open>T1\<close> to
subtree \<open>T2\<close>, it is useful to zoom on the different parsing evaluation stages, as well
as make precise when the evaluation of semantic back-ends are starting.

\<^enum> Whereas annotations in Isabelle/C code have the potential of carrying arbitrary ML code (as
in \<^theory>\<open>C_examples.C1\<close>), the moment when they are effectively evaluated will not be
discussed here, because to closely follow the semantics of the language in embedding (so C), we
suppose comments --- comprising annotations --- may not affect any parsed tokens living outside
comments. So no matter when annotations are scheduled to be future evaluated in Isabelle/C, it will
be not possible to write a code changing \<open>T1\<close> to \<open>T2\<close> inside annotations.

\<^enum> To our knowledge, the sole category of code having the capacity to affect incoming stream
of tokens are directives, which are processed and evaluated before the ``major'' parsing step
occurs. Since in Isabelle/C, directives are relying on ML code, changing an AST node from
\<open>T1\<close> to \<open>T2\<close> can then be perfectly implemented in directives.

\<^enum> After the directive (pre)processing step, the main parsing happens. But since what are
driving the parsing engine are principally rule code, this step means to execute
\<^ML_structure>\<open>C_Grammar_Rule_Lib\<close> and
\<^ML_structure>\<open>C_Grammar_Rule_Wrap\<close>, i.e., rules in
\<^file>\<open>generated/c_grammar_fun.grm.sml\<close>.

\<^enum> Once the parsing finishes, we have a final AST value, which topmost root type entry-point
constitutes the last node built before the grammar parser
\<^url>\<open>https://github.com/visq/language-c/blob/master/src/Language/C/Parser/Parser.y\<close>
ever entered in a stop state. For the case of a stop acceptance state, that moment happens when we
reach the first rule code building the type \<^ML_type>\<open>C_Ast.CTranslUnit\<close>, since there
is only one possible node making the parsing stop, according to what is currently written in the C
grammar. (For the case of a state stopped due to an error, it is the last successfully built value
that is returned, but to simplify the discussion, we will assume in the rest of the document the
parser is taking in input a fully well-parsed C code.)

\<^enum> By \<^emph>\<open>semantic back-ends\<close>, we denote any kind of ``relatively
efficient'' compiled code generating Isabelle/HOL theorems, proofs, definitions, and so with the
potential of generally generating Isabelle packages. In our case, the input of semantic back-ends
will be the type \<^ML_type>\<open>C_Ast.CTranslUnit\<close> (actually, whatever value provided by
the above parser). But since our parser is written in monadic style, it is as well possible to give
slightly more information to semantic back-ends, such as the last monadic computed state, so
including the last state of the parsing environment. \<close>

text \<open> Generally, semantic back-ends can be written in full ML starting from
\<^ML_type>\<open>C_Ast.CTranslUnit\<close>, but to additionally support formalizing tasks requiring
to start from an AST defined in Isabelle/HOL, we provide an equivalent AST in HOL in the project,
such as the one obtained after loading
\<^file>\<open>../Featherweight-OCL/doc/Meta_C_generated.thy\<close> \<^footnote>\<open>from the
Citadelle project \<^url>\<open>gitlri.lri.fr/ftuong/citadelle-devel\<close>\<close> (In fact, the
ML AST is just generated from the HOL one.) \<close>



text \<open>
Based on the above information, there are now several \<^emph>\<open>equivalent\<close> ways to
proceed for the purpose of having an AST node be mapped from \<open>T1\<close> to
\<open>T2\<close>. The next bullets providing several possible solutions to follow are particularly
sorted in increasing action time.

\<^item> \<^emph>\<open>Before even starting the Isabelle system.\<close> A first approach would be
to modify the C code in input, by adding a directive \<^C>\<open>#define _ _\<close> performing the
necessary rewrite.

\<^item> \<^emph>\<open>Before even starting the Isabelle system.\<close> As an alternative of changing the C
code, one can modify
\<^url>\<open>https://github.com/visq/language-c/blob/master/src/Language/C/Parser/Parser.y\<close>
by hand, by explicitly writing \<open>T2\<close> at the specific position of the rule code
generating \<open>T1\<close>. However, this solution implies to re-generate
\<^file>\<open>generated/c_grammar_fun.grm.sml\<close>.

\<^item> \<^emph>\<open>At grammar loading time, while the source of Isabelle/C is still being
processed.\<close> Instead of modifying the grammar, it should be possible to first locate which
rule code is building \<open>T1\<close>. Then it would remain to retrieve and modify the respective
function of \<^ML_structure>\<open>C_Grammar_Rule_Wrap\<close> executed after that rule code, by
providing a replacement function to be put in
\<^ML_structure>\<open>C_Grammar_Rule_Wrap_Overloading\<close>. However, as a design decision,
wrapping functions generated in \<^file>\<open>generated/c_grammar_fun.grm.sml\<close> have only
been generated to affect monadic states, not AST values. This is to prevent an erroneous replacement
of an end-user while parsing C code. (It is currently left open about whether this feature will be
implemented in future versions of the parser...)

\<^item> \<^emph>\<open>At directive setup time, before executing any
\<^theory_text>\<open>C\<close> command of interest.\<close> Since the behavior of directives can be
dynamically modified, this solution amounts to change the semantics of any wished directive,
appearing enough earlier in the code. (But for the overall code be in the end mostly compatible with
any other C preprocessors, the implementation change has to be somehow at least consistent with how
a preprocessor is already expected to treat an initial C un(pre)processed code.) For example, the
current semantics of \<^C>\<open>#undef _\<close> depends on what has been registered in
\<^ML>\<open>C_Context.directive_update\<close> (see \<^theory>\<open>C.C_Command\<close>).

\<^item> \<^emph>\<open>After parsing and obtaining a constructive value.\<close> Another solution
consists in directly writing a mapping function acting on the full AST, so writing a ML function of
type \<^ML_type>\<open>C_Ast.CTranslUnit -> C_Ast.CTranslUnit\<close> (or a respective HOL function)
which has to act on every constructor of the AST (so in the worst case about hundred of constructors
for the considered AST, i.e., whenever a node has to be not identically returned). However, as we
have already implemented a conversion function from \<^ML_type>\<open>C_Ast.CTranslUnit\<close>
(subset of C11) to a subset AST of C99, it might be useful to save some effort by starting from this
conversion function, locate where \<open>T1\<close> is pattern-matched by the conversion function,
and generate \<open>T2\<close> instead.

As example, the conversion function \<^ML>\<open>C_Ast.main\<close> is particularly used to connect
the C11 front-end to the entry-point of AutoCorres in
\<^verbatim>\<open>l4v/src/tools/c-parser/StrictCParser.ML\<close>.

\<^item> \<^emph>\<open>At semantic back-ends execution time.\<close> The above points were dealing
with the cases where modification actions were all occurring before getting a final
\<^ML_type>\<open>C_Ast.CTranslUnit\<close> value. But this does not mean it is forbidden to make
some slight adjustments once that resulting \<^ML_type>\<open>C_Ast.CTranslUnit\<close> value
obtained. In particular, it is the tasks of semantic back-ends to precisely work with
\<^ML_type>\<open>C_Ast.CTranslUnit\<close> as starting point, and possibly translate it to another
different type. So letting a semantic back-end implement the mapping from \<open>T1\<close> to
\<open>T2\<close> would mean here to first understand the back-end of interest's architecture, to
see where the necessary minimal modifications must be made.

By taking l4v as a back-end example, its integration with Isabelle/C first starts with translating
\<^ML_type>\<open>C_Ast.CTranslUnit\<close> to l4v's default C99 AST. Then various analyses on the
obtained AST are performed in
\<^url>\<open>https://github.com/seL4/l4v/tree/master/tools/c-parser\<close> (the reader interested
in the details can start by further exploring the ML files loaded by
\<^url>\<open>https://github.com/seL4/l4v/blob/master/tools/c-parser/CTranslation.thy\<close>). In
short, to implement the mapping from \<open>T1\<close> to \<open>T2\<close> in the back-end part,
one can either:
  \<^item> modify the translation from \<^ML_type>\<open>C_Ast.CTranslUnit\<close> to C99,
  \<^item> or modify the necessary ML files of interests in the l4v project.
\<close>

text \<open> More generally, to better inspect the list of rule code really executed when a C code
is parsed, it might be helpful to proceed as in \<^theory>\<open>C_examples.C1\<close>, by activating
\<^theory_text>\<open>declare[[C_parser_trace]]\<close>. Then, the output window will display the
sequence of Shift Reduce actions associated to the \<^theory_text>\<open>C\<close> command of
interest.
\<close> 


section \<open>Syntax Commands for Isabelle/C\<close>

subsection \<open>Outer Syntax Commands\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "C_file"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "C"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "C_export_boot"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "C_prf"} & : & \<open>proof \<rightarrow> proof\<close> \\
    @{command_def "C_val"} & : & \<open>any \<rightarrow>\<close> \\
    @{command_def "C_export_file"} & : & \<open>any \<rightarrow>\<close> \\
  \end{matharray}
  \begin{tabular}{rcll}
    @{attribute_def C_lexer_trace} & : & \<open>attribute\<close> & default \<open>false\<close> \\
    @{attribute_def C_parser_trace} & : & \<open>attribute\<close> & default \<open>false\<close> \\
    @{attribute_def C_ML_verbose} & : & \<open>attribute\<close> & default \<open>true\<close> \\
    @{attribute_def C_propagate_env} & : & \<open>attribute\<close> & default \<open>false\<close> \\
  \end{tabular}

  @{rail \<open>
    @@{command C_file} @{syntax name} ';'?
    ;
    (@@{command C} | @@{command C_export_boot} | @@{command C_prf} |
      @@{command C_val} | @@{command C_export_file}) @{syntax text}
    ;
  \<close>}

  \<^descr> \<^theory_text>\<open>C_file name\<close> resembles to
  \<^theory_text>\<open>ML_file name\<close>: it reads the given C
  file, and let any attached semantic back-ends to proceed for further
  subsequent evaluation. Top-level C bindings are stored within the
  (global or local) theory context; the initial environment is set by
  default to be an empty one, or the one returned by a previous
  \<^theory_text>\<open>C_file\<close> (depending on @{attribute_def
    C_propagate_env}). Multiple \<^theory_text>\<open>C_file\<close>
  commands may be used to build larger C projects if they are all
  written in a single theory file (existing parent theories are
  ignored, and not affecting the current working theory).

  \<^descr> \<^theory_text>\<open>C\<close> is similar to
  \<^theory_text>\<open>C_file\<close>, but evaluates directly the
  given \<open>text\<close>. Top-level resulting bindings are stored
  within the (global or local) theory context.

  \<^descr> \<^theory_text>\<open>C_export_boot\<close> is similar to
  \<^theory_text>\<open>ML_export\<close>, except that the code in
  input is understood as being processed by
  \<^theory_text>\<open>C\<close> instead of \<^theory_text>\<open>ML\<close>.

  \<^descr> \<^theory_text>\<open>C_prf\<close> is similar to
  \<^theory_text>\<open>ML_prf\<close>, except that the code in input
  is understood as being processed by
  \<^theory_text>\<open>C\<close> instead of \<^theory_text>\<open>ML\<close>.

  \<^descr> \<^theory_text>\<open>C_val\<close> is similar to
  \<^theory_text>\<open>ML_val\<close>, except that the code in input
  is understood as being processed by
  \<^theory_text>\<open>C\<close> instead of \<^theory_text>\<open>ML\<close>.

  \<^descr> \<^theory_text>\<open>C_export_file\<close> dumps all
  existing previous C code to \<open>T.c\<close>, where
  \<open>T.thy\<close> is the name of the current working theory. The
  dump is actually restricted to \<open>T\<close> (parent theories are
  ignored).
\<close>

text \<open>

  \<^descr> @{attribute C_lexer_trace} indicates whether the list of C
  tokens associated to the source text should be output (that list is
  computed during the lexing phase).

  \<^descr> @{attribute C_parser_trace} indicates whether the stack
  forest of Shift-Reduce node should be output (it is the final stack
  which is printed, i.e., the one taken as soon as the parsing
  terminates).

  \<^descr> @{attribute C_ML_verbose} indicates whether nested
  \<^theory_text>\<open>ML\<close> commands are acting similarly as
  their default verbose configuration in top-level.

  \<^descr> @{attribute_def C_propagate_env} makes the start of a C
  command (e.g., \<^theory_text>\<open>C_file\<close>,
  \<^theory_text>\<open>C\<close>) initialized with the environment of
  the previous C command if existing.
\<close>

subsection \<open>Inner Syntax Commands\<close>

text \<open>
  @{rail \<open>
    (@@{annotation ML_file} | @@{annotation "ML_file\<Down>"} |
      @@{annotation C_file} | @@{annotation "C_file\<Down>"}) @{syntax name} ';'?
    ;
    (@@{annotation ML} | @@{annotation "ML\<Down>"} |
      @@{annotation setup} | @@{annotation "setup\<Down>"} |
      @@{annotation "\<approx>setup"} | @@{annotation "\<approx>setup\<Down>"} |
      @@{annotation C} | @@{annotation "C\<Down>"} |
      @@{annotation C_export_boot} | @@{annotation "C_export_boot\<Down>"} |
      @@{annotation C_export_file} | @@{annotation "C_export_file\<Down>"}) @{syntax text}
    ;
  \<close>}

  \<^descr> \<^C_theory_text>\<open>ML_file\<close>, \<^C_theory_text>\<open>C_file\<close>,
  \<^C_theory_text>\<open>ML\<close>, \<^C_theory_text>\<open>setup\<close>,
  \<^C_theory_text>\<open>C\<close>, \<^C_theory_text>\<open>C_export_boot\<close>, and
  \<^C_theory_text>\<open>C_export_file\<close> behave similarly as the respective outer commands
  \<^theory_text>\<open>ML_file\<close>, \<^theory_text>\<open>C_file\<close>,
  \<^theory_text>\<open>ML\<close>, \<^theory_text>\<open>setup\<close>,
  \<^theory_text>\<open>C\<close>, \<^theory_text>\<open>C_export_boot\<close>,
  \<^theory_text>\<open>C_export_file\<close>.

  \<^descr> \<^C_theory_text>\<open>\<approx>setup \<open>f'\<close>\<close> has the same semantics
  as \<^C_theory_text>\<open>setup \<open>f\<close>\<close> whenever \<^term>\<open>\<And> stack top
  env. f' stack top env = f\<close>. In particular, depending on where the annotation
  \<^C_theory_text>\<open>\<approx>setup \<open>f'\<close>\<close> is located in the C code, the
  additional values \<open>stack\<close>, \<open>top\<close> and \<open>env\<close> can drastically
  vary, and then can be possibly used in the body of \<open>f'\<close> for implementing new
  interactive features (e.g., in contrast to \<open>f\<close>, which by default does not have the
  possibility to directly use the information provided by \<open>stack\<close>, \<open>top\<close>
  and \<open>env\<close>).

  \<^descr> \<^C_theory_text>\<open>ML_file\<Down>\<close>,
  \<^C_theory_text>\<open>C_file\<Down>\<close>, \<^C_theory_text>\<open>ML\<Down>\<close>,
  \<^C_theory_text>\<open>setup\<Down>\<close>,
  \<^C_theory_text>\<open>\<approx>setup\<Down>\<close>, \<^C_theory_text>\<open>C\<Down>\<close>,
  \<^C_theory_text>\<open>C_export_boot\<Down>\<close>, and
  \<^C_theory_text>\<open>C_export_file\<Down>\<close>
  behave similarly as the respective (above inner) commands
  \<^C_theory_text>\<open>ML_file\<close>, \<^C_theory_text>\<open>C_file\<close>,
  \<^C_theory_text>\<open>ML\<close>, \<^C_theory_text>\<open>setup\<close>,
  \<^C_theory_text>\<open>\<approx>setup\<close>, \<^C_theory_text>\<open>C\<close>,
  \<^C_theory_text>\<open>C_export_boot\<close>, and \<^C_theory_text>\<open>C_export_file\<close>
  except that their evaluations happen later.
\<close>

section \<open>A Guide to Implement Semantic Back-Ends for Isabelle/C\<close>

subsection \<open>General Principles\<close>

subsection \<open>Example: CLEAN\<close>

subsection \<open>Example: AutoCorres\<close>

(*<*)
end
(*>*)
