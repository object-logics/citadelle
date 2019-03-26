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

theory C1
  imports "../semantic-backends/AutoCorres/AC_Command"
begin

declare[[C_lexer_trace]]

section \<open>Regular C Code\<close>

C \<comment> \<open>Nesting of comments \<^url>\<open>https://gcc.gnu.org/onlinedocs/cpp/Initial-processing.html\<close>\<close> \<open>
/* inside /* inside */ int a = "outside";
// inside // inside until end of line
int a = "outside";
/* inside
  // inside
inside
*/ int a = "outside";
// inside /* inside until end of line
int a = "outside";
\<close>

C \<comment> \<open>Backslash newline\<close> \<open>
i\    
n\                
t a = "/* //  /\ 
*\
fff */\
";
\<close>

C \<comment> \<open>Backslash newline, Directive \<^url>\<open>https://gcc.gnu.org/onlinedocs/cpp/Initial-processing.html\<close>\<close> \<open>
/\
*
*/ # /*
*/ defi\
ne FO\
O 10\
20\<close>

C \<comment> \<open>Directive: conditional\<close> \<open>
#ifdef a
#elif
#else
#if
#endif
#endif
\<close>
(*
C \<comment> \<open>Directive: pragma\<close> \<open># f # "/**/"
/**/
#     /**/ //  #

_Pragma /\
**/("a")
\<close>
*)
C \<comment> \<open>Directive: macro\<close> \<open>
#define a zz
#define a(x1,x2) z erz(( zz
#define a (x1,x2) z erz(( zz
#undef z
#if
#define a zz
#define a(x1,x2) z erz(( zz
#define a (x1,x2) z erz(( zz
#endif
\<close>

section \<open>C Annotations\<close>

subsection \<open>Actions on the Parsing Stack\<close>

C \<comment> \<open>Nesting ML code in C comments\<close> \<open>
int a = (((0))); /*@ ML \<open>@{print_stack}\<close> */
                 /*@ ML \<open>@{print_top}\<close> */
\<close>

text \<open>In terms of execution order, nested ML code are not pre-filtered out of the C code, but
executed when the C parser is in an intermediate parsing state of having already read all previous
tokens, constructed for each read token a respective temporary parsed subtree
(to be included in the final value), and about to read the ML code.

Moreover, the ML code can get access to the current parsing state (represented as a stack of parsed
values). Because values in the state are changing depending on where the ML code is situated,
we can conveniently use ML antiquotations for printing and reporting actions.\<close>

C \<comment> \<open>Positional navigation: referring to any previous parsed sub-tree in the stack\<close> \<open>
int a = (((0
      + 5)))  /*@@ ML \<open>fn _ => fn (_, (value, pos1, pos2)) => fn _ => fn context =>
                          let
                            val () = writeln (@{make_string} value)
                            val () = Position.reports_text [((Position.range (pos1, pos2) 
                                                            |> Position.range_position, Markup.intensify), "")]
                          in context end\<close>
               */
      * 4; 
float b = 7 / 3;
\<close>

text \<open>The special \<open>@\<close> symbol makes the command be executed whenever the first element \<open>E\<close>
 in the stack is about to be irremediably replaced by a more structured parent element (having \<open>E\<close>
as one of its direct children). It is the parent element which is provided to the ML code.

Instead of always referring to the first element of the stack, 
\<open>N\<close> consecutive occurrences of \<open>@\<close> will make the ML code getting as argument the direct parent
of the \<open>N\<close>-th element.\<close>

C \<comment> \<open>Positional navigation: referring to any previous parsed sub-tree in the stack\<close> \<open>
int a = (((0 + 5)))  /*@@ ML \<open>@{print_top}\<close> */
      * 4;

int a = (((0 + 5)))  /*@& ML \<open>@{print_top}\<close> */
      * 4;

int a = (((0 + 5)))  /*@@@@@ ML \<open>@{print_top}\<close> */
      * 4;

int a = (((0 + 5)))  /*@&&&& ML \<open>@{print_top}\<close> */
      * 4;
\<close>

text \<open>\<open>&\<close> behaves as \<open>@\<close>, but instead of always giving the designated direct parent to the ML code,
it finds the first parent ancestor making non-trivial changes in the respective grammar rule
(a non-trivial change can be for example the registration of the position of the current AST node
being built).\<close>

C \<comment> \<open>Positional navigation: moving the comment after a number of C token\<close> \<open>
int b = 7 / (3) * 50;
/*@+++@@ ML \<open>@{print_top}\<close>*/
long long f (int a) {
  while (0) { return 0; }
}
int b = 7 / (3) * 50;
\<close>

text \<open>\<open>N\<close> consecutive occurrences of \<open>+\<close> will delay the interpretation of the comment,
which is ignored at the place it is written. The comment is only really considered after the
C parser has treated \<open>N\<close> more tokens.\<close>

C \<comment> \<open>Closing C comments \<open>*/\<close> must close anything, even when editing ML code\<close> \<open>
int a = (((0 //@ (* inline *) ML \<open>fn _ => fn _ => fn _ => fn context => let in (* */ *) context end\<close>
             /*@ ML \<open>(K o K o K) I\<close> (*   * /   *) */
         )));
\<close>

C \<comment> \<open>Inline comments with antiquotations\<close> \<open>
 /*@ ML\<open>(K o K o K) (fn x => K x @{con\
text (**)})\<close> */ // break of line activated everywhere (also in antiquotations)
int a = 0; //\
@ ML\<open>(K o K o K) (fn x => K x @{term \<open>a \
          + b (* (**) *\      
\     
)\<close>})\<close>
\<close>

C \<comment> \<open>Permissive Types of Antiquotations\<close> \<open>
int a = 0;
  /*@ ML (* Errors: Explicit warning + Explicit markup reporting *)
   */
  /** ML (* Errors: Turned into tracing report information *)
   */

  /** ML \<open>fn _ => fn _ => fn _ => I\<close> (* An example of correct syntax accepted as usual *)
   */
\<close>

subsection \<open>Mixing Together Any Types of Antiquotations\<close>

C \<comment> \<open>Permissive Types of Antiquotations\<close> \<open>
int a = 0;
  /*@ ML \<open>fn _ => fn _ => fn _ => I\<close>
      ML (* Parsing error of a single command does not propagate to other commands *)
      ML \<open>fn _ => fn _ => fn _ => I\<close>
      context
   */
  /** ML \<open>fn _ => fn _ => fn _ => I\<close>
      ML (* Parsing error of a single command does not propagate to other commands *)
      ML \<open>fn _ => fn _ => fn _ => I\<close>
      context
   */
  
  /*@ ML (* Errors in all commands are all rendered *)
      ML (* Errors in all commands are all rendered *)
      ML (* Errors in all commands are all rendered *)
   */
  /** ML (* Errors in all commands makes the whole comment considered as an usual comment *)
      ML (* Errors in all commands makes the whole comment considered as an usual comment *)
      ML (* Errors in all commands makes the whole comment considered as an usual comment *)
   */
\<close>

ML\<open>
structure Example_Data = Generic_Data (type T = string list
                                      val empty = [] val extend = I val merge = #2)
fun add_ex s1 s2 =
  Example_Data.map (cons s2)
  #> (fn context => let val () = warning (s1 ^ s2)
                        val () = app (fn s => writeln ("  Data content: " ^ s)) (Example_Data.get context)
                    in context end)
\<close>

setup \<open>Context.theory_map (Example_Data.put [])\<close>

declare[[ML_source_trace]]
declare[[C_parser_trace]]

C \<comment> \<open>Arbitrary interleaving of effects\<close> \<open>
int x /** OWNED_BY foo */, hh /*@
  MODIFIES: [*] x
  ML \<open>@{print_stack "evaluation of 2_print_stack"}\<close>
  +++++@@ ML \<open>fn s => fn x => fn env => @{print_top} s x env #> add_ex "evaluation of " "2_print_top"\<close>
  OWNED_BY bar
  @ML \<open>fn s => fn x => fn env => @{print_top} s x env #> add_ex "evaluation of " "1_print_top"\<close>
  ML \<open>@{print_stack "evaluation of 1_print_stack"}\<close>
*/, z;

int b = 0;
\<close>

C \<comment> \<open>Arbitrary interleaving of effects: \<open>ML\<close> vs \<open>ML_reverse\<close>\<close> \<open>
int b,c,d/*@@ ML \<open>fn s => fn x => fn env => @{print_top} s x env #> add_ex "evaluation of " "3_print_top"\<close> */,e = 0; /*@@ ML \<open>fn s => fn x => fn env => @{print_top} s x env #> add_ex "evaluation of " "4_print_top"\<close> */
int b,c,d/*@@ ML_reverse \<open>fn s => fn x => fn env => @{print_top} s x env #> add_ex "evaluation of " "6_print_top"\<close> */,e = 0; /*@@ ML_reverse \<open>fn s => fn x => fn env => @{print_top} s x env #> add_ex "evaluation of " "5_print_top"\<close> */
\<close>

subsection \<open>Reporting of Positions and Contextual Update of Environment\<close>

subsubsection \<open>1\<close>

declare [[ML_source_trace = false]]
declare [[C_lexer_trace = false]]

C \<comment> \<open>Reporting of Positions\<close> \<open>
typedef int i, j;
  /*@@ ML \<open>@{print_top'}\<close> */ //@ +++++@ ML \<open>@{print_top'}\<close>
int j = 0;
typedef int i, j;
j jj1 = 0;
j jj = jj1;
j j = jj1 + jj;
typedef i j;
typedef i j;
typedef i j;
i jj = jj;
j j = jj;
\<close>

subsubsection \<open>2\<close>

declare [[C_parser_trace = false]]

ML\<open>
fun show_env0 make_string f msg context =
  warning ("(" ^ msg ^ ") "
           ^ make_string (f (the (Symtab.lookup (#tab (C11_core.Data.get context))
                                                (Context.theory_name (Context.theory_of context))))))

val show_env = tap o show_env0 @{make_string} length

fun C src = tap (fn _ => C_Outer_Syntax.C src)
val C' = C_Outer_Syntax.C' (fn _ => fn _ => fn pos =>
                             tap (fn _ => warning ("Parser: No matching grammar rule " ^ Position.here pos)))
\<close>

C \<comment> \<open>Nesting C code without propagating the C environment\<close> \<open>
int a = 0;
int b = 7 / (3) * 50
  /*@@@@@ ML \<open>fn _ => fn _ => fn _ =>
               C      \<open>int b = a + a + a + a + a + a + a
                       ;\<close> \<close> */;
\<close>

C \<comment> \<open>Nesting C code and propagating the C environment\<close> \<open>
int a = 0;
int b = 7 / (3) * 50
  /*@@@@@ ML \<open>fn _ => fn _ => fn env =>
               C' env \<open>int b = a + a + a + a + a + a + a
                       ;\<close> \<close> */;
\<close>

subsubsection \<open>3\<close>

ML\<open>
local
fun command dir f_cmd name =
  C_Annotation.command' name ""
    (fn (stack1, (to_delay, stack2)) =>
      C_Parse.range C_Parse.ML_source >>
        (fn (src, range) =>
          (fn f => Once ((stack1, stack2), (range, dir, to_delay, f)))
            (fn _ => fn context => f_cmd (Stack_Data_Lang.get context |> #2) src context)))
in
val _ = Theory.setup (   command Bottom_up (K C) ("C", \<^here>)
                      #> command Top_down (K C) ("C_reverse", \<^here>)
                      #> command Bottom_up C' ("C'", \<^here>)
                      #> command Top_down C' ("C'_reverse", \<^here>))
end
\<close>

C \<comment> \<open>Nesting C code without propagating the C environment\<close> \<open>
int f (int a) {
  int b = 7 / (3) * 50 /*@ C  \<open>int b = a + a + a + a + a + a + a;\<close> */;
  int c = b + a + a + a + a + a + a;
} \<close>

C \<comment> \<open>Nesting C code and propagating the C environment\<close> \<open>
int f (int a) {
  int b = 7 / (3) * 50 /*@ C' \<open>int b = a + a + a + a + a + a + a;\<close> */;
  int c = b + b + b + b + a + a + a + a + a + a;
} \<close>

C \<comment> \<open>Miscellaneous\<close> \<open>
int f (int a) {
  int b = 7 / (3) * 50 /*@ C  \<open>int b = a + a + a + a + a; //@ C' \<open>int c = b + b + b + b + a;\<close> \<close> */;
  int b = 7 / (3) * 50 /*@ C' \<open>int b = a + a + a + a + a; //@ C' \<open>int c = b + b + b + b + a;\<close> \<close> */;
  int c = b + b + b + b + a + a + a + a + a + a;
} \<close>

subsubsection \<open>4\<close>

C \<comment> \<open>Propagation of Updates\<close> \<open>
typedef int i, j;
int j = 0;
typedef int i, j;
j jj1 = 0;
j jj = jj1; /*@@ ML \<open>fn _ => fn _ => fn _ => show_env "POSITION 0"\<close> @ML \<open>@{print_top'}\<close> */
typedef int k; /*@@ ML \<open>fn _ => fn _ => fn env =>
                          C' env \<open>k jj = jj; //@@ ML \<open>@{print_top'}\<close>
                                  k jj = jj + jj1;
                                  typedef k l; //@@ ML \<open>@{print_top'}\<close>\<close>
                          #> show_env "POSITION 1"\<close> */
j j = jj1 + jj; //@@ ML \<open>@{print_top'}\<close>
typedef i j; /*@@ ML \<open>fn _ => fn _ => fn _ => show_env "POSITION 2"\<close> */
typedef i j;
typedef i j;
i jj = jj;
j j = jj;
\<close>

ML\<open>show_env "POSITION 3" (Context.Theory @{theory})\<close>

C \<comment> \<open>Propagation of Updates\<close> \<open>
int a = 0;
int b = a * a + 0;
int jjj = b;
int main (void main(int *x,int *y),int *jjj) {
  return a + jjj + main(); }
int main2 () {
  int main3 () { main2() + main(); }
  int main () { main2() + main(); }
  return a + jjj + main3() + main(); }
\<close>

section \<open>Miscellaneous\<close>

C \<comment> \<open>Antiquotations acting on a parsed-subtree\<close> \<open>
# /**/ include  <a\b\\c> // backslash rendered unescaped
f(){0 +  0;} /**/  // val _ : theory => 'a => theory
# /* context */ if if elif
#include <stdio.h>
if then else ;
# /* zzz */  elif /**/
#else\
            
#define FOO  00 0 "" ((
FOO(FOO(a,b,c))
#endif\<close>

end
