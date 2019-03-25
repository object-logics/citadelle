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
  imports "../C_Main"
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

subsection \<open>User Defined Commands in the Semantic Verification Space\<close>

ML\<open>
local
type text_range = Symbol_Pos.text * Position.T

datatype antiq_hol = Invariant of string (* term *)
                   | Fnspec of text_range (* ident *) * string (* term *)
                   | Relspec of string (* term *)
                   | Modifies of (bool (* true: [*] *) * text_range) list
                   | Dont_translate
                   | Auxupd of string (* term *)
                   | Ghostupd of string (* term *)
                   | Spec of string (* term *)
                   | End_spec of string (* term *)
                   | Calls of text_range list
                   | Owned_by of text_range

val scan_ident = Scan.one C_Token.is_ident >> (fn tok => (C_Token.content_of tok, C_Token.pos_of tok))
val scan_sym_ident_not_stack = Scan.one (fn c => C_Token.is_sym_ident c andalso
                                                 not (C_Token.is_stack1 c) andalso
                                                 not (C_Token.is_stack2 c))
                               >> (fn tok => (C_Token.content_of tok, C_Token.pos_of tok))
fun command cmd scan f =
  C_Annotation.command' cmd "" (K (Scan.option (Scan.one C_Token.is_colon) -- (scan >> f)
                                      >> K Never))
in
val _ = Theory.setup ((* 1 '@' *)
                         command ("INVARIANT", \<^here>) C_Parse.term Invariant
                      #> command ("INV", \<^here>) C_Parse.term Invariant

                      (* '+' until being at the position of the first ident
                        then 2 '@' *)
                      #> command ("FNSPEC", \<^here>) (scan_ident --| Scan.option (Scan.one C_Token.is_colon) -- C_Parse.term) Fnspec
                      #> command ("RELSPEC", \<^here>) C_Parse.term Relspec
                      #> command ("MODIFIES", \<^here>) (Scan.repeat (   scan_sym_ident_not_stack >> pair true
                                                                || scan_ident >> pair false))
                                                  Modifies
                      #> command ("DONT_TRANSLATE", \<^here>) (Scan.succeed ()) (K Dont_translate)

                      (**)
                      #> command ("AUXUPD", \<^here>) C_Parse.term Auxupd
                      #> command ("GHOSTUPD", \<^here>) C_Parse.term Ghostupd
                      #> command ("SPEC", \<^here>) C_Parse.term Spec
                      #> command ("END-SPEC", \<^here>) C_Parse.term End_spec

                      (**)
                      #> command ("CALLS", \<^here>) (Scan.repeat scan_ident) Calls
                      #> command ("OWNED_BY", \<^here>) scan_ident Owned_by);
end
\<close>

C \<comment> \<open>Copyright\<close> \<open>
/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */
\<close>

C \<comment> \<open>\<open>INVARIANT\<close> Inserting an invariant after the \<open>while\<close> loop \<^url>\<open>https://github.com/seL4/l4v/blob/master/tools/c-parser/testfiles/breakcontinue.c\<close>\<close> \<open>
int h(int e)
{
  while (e < 10)
    /** INV: "\<lbrace> True \<rbrace>" */
  {
    if (e < -10) { continue; }
    if (e < 0) { break; }
    e = e - 1;
  }
  return e;
}
\<close>

C \<comment> \<open>\<open>FNSPEC\<close> Providing a specification before a function \<^url>\<open>https://github.com/seL4/l4v/blob/master/tools/c-parser/testfiles/list_reverse.c\<close>\<close> \<open>
typedef unsigned long word_t;

/** FNSPEC reverse_spec:
  "\<Gamma> \<turnstile>
    \<lbrace> (list zs \<acute>i)\<^bsup>sep\<^esup> \<rbrace>
      \<acute>ret__long :== PROC reverse(\<acute>i)
    \<lbrace> (list (rev zs) (Ptr (scast \<acute>ret__long)))\<^bsup>sep\<^esup> \<rbrace>"
*/

long reverse(word_t *i)
{
  word_t j = 0;

  while (i)
    /** INV: "\<lbrace> \<exists>xs ys. (list xs \<acute>i \<and>\<^sup>* list ys (Ptr \<acute>j))\<^bsup>sep\<^esup> \<and> rev zs = (rev xs)@ys \<rbrace>" */
  {
    word_t *k = (word_t*)*i;

    *i = j;
    j = (word_t)i;
    i = k;
  }

  return j;
}
\<close>

C \<comment> \<open>\<open>AUXUPD\<close> \<^url>\<open>https://github.com/seL4/l4v/blob/master/tools/c-parser/testfiles/parse_auxupd.c\<close>\<close> \<open>
int f(int x)
{
  for (int i = 0; i < 10; i++ /** AUXUPD: foo */) {
    x = x + i;
  }
  return x;
}
\<close>

C \<comment> \<open>\<open>GHOSTUPD\<close> \<^url>\<open>https://github.com/seL4/l4v/blob/master/tools/c-parser/testfiles/ghoststate2.c\<close>\<close> \<open>
int f(int x)
{
  /** GHOSTUPD:
        "(True, (%n. n + 1))" */
  return x + 3;
}
\<close>

C \<comment> \<open>\<open>SPEC\<close> \<open>END-SPEC\<close> \<^url>\<open>https://github.com/seL4/l4v/blob/master/tools/c-parser/testfiles/parse_spec.c\<close>\<close> \<open>
int f(int m, int n)
{
  int i;
  i = m;
  /** SPEC: "\<tau> . \<lbrace> \<tau>. \<acute>i = \<^bsup>\<sigma> \<^esup>m \<rbrace>" */
  m = n;
  n = i;
  /** END-SPEC: "\<lbrace> \<acute>m = \<^bsup>\<tau>\<^esup>n \<and> \<acute>n = \<^bsup>\<tau>\<^esup>i \<rbrace>" */
  return m + n;
}
\<close>


C \<comment> \<open>\<open>CALLS\<close> \<^url>\<open>https://github.com/seL4/l4v/blob/master/tools/c-parser/testfiles/fnptr.c\<close>\<close> \<open>
int intcaller(int (*ipfn)(void) /** CALLS intcallable2 */)
{
  return ipfn();
}
\<close>

C \<comment> \<open>\<open>OWNED_BY\<close> \<^url>\<open>https://github.com/seL4/l4v/blob/master/tools/c-parser/testfiles/jiraver313.c\<close>\<close> \<open>
int x /** OWNED_BY foo */, y /** OWNED_BY bar */, z;

/* reads/writes x, writes z */
int f(int i)
{
  x += i;
  z++;
  return x;
}

/* reads x & z, writes y */
int g(int i)
{
  y++;
  return x + i + z;
}
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
