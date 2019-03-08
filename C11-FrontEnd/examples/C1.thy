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
  imports "../C11-Interface"
begin

declare[[C_source_trace]]

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

section \<open>Antiquotations\<close>

subsection \<open>Classic ML\<close>

C \<comment> \<open>Inline comments with antiquotations\<close> \<open>
 /*@con\
text (**) */ // break of line activated everywhere (also in antiquotations)
int a = 0; //\
@ \<open>term \<open>a \
          + b (* (**) *\      
\     
)\<close>\<close>
\<close>

subsection \<open>Actions on the Parsing Stack\<close>

C \<comment> \<open>Closing C comments \<open>*/\<close> must close anything, even when editing ML code\<close> \<open>
int a = (((0 //@ setup \<open>fn _ => fn thy => let in (* */ *) thy end\<close>
             /*@ setup \<open>K I\<close> (*   * /   *) */
         )));
\<close>

C \<comment> \<open>\<^theory_text>\<open>setup\<close> is executed during SHIFT actions\<close> \<open>
int a = (((0))); /*@ setup \<open>@{setup}\<close> */
\<close>

C \<comment> \<open>\<^theory_text>\<open>hook\<close> is executed during REDUCE actions\<close> \<open>
int a = (((0
      + 5)))  /*@ hook \<open>fn (_, (value, pos1, pos2)) => fn thy =>
                          let
                            val () = writeln (@{make_string} value)
                            val () = Position.reports_text [((Position.range (pos1, pos2) |> Position.range_position, Markup.intensify), "")]
                          in thy end\<close>
               */
      * 4; 
float b = 7 / 3;
\<close>

C \<comment> \<open>Positional navigation: pointing to deeper sub-trees in the stack\<close> \<open>
int b = 7 / (3) * 50 /*@@@@ hook \<open>@{hook}\<close>
                      */;
\<close>

C \<comment> \<open>Nesting C code in ML\<close> \<open>
int b = 7 / (3) * 50
  /*@@@@ hook \<open>(hook @{make_string} o tap)
                 (fn _ => C_Outer_Syntax.C
                            \<open>int b = 7 / 5 * 2 + 3 * 50 //@ hook \<open>@{hook}\<close>
                             ;\<close>)\<close>
   */;
\<close>

C \<comment> \<open>Positional navigation: pointing to sub-trees situated after any part of the code\<close> \<open>
int b = 7 / (3) * 50;
/*@+++@ hook \<open>@{hook}\<close>*/
long long f (int a) {
  while (0) { return 0; }
}
int b = 7 / (3) * 50;
\<close>

subsection \<open>User Defined Commands in the Semantic Verification Space\<close>

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

subsection \<open>Mixing It All Together\<close>

ML\<open>
structure Example_Data = Theory_Data (type T = string list
                                      val empty = [] val extend = I val merge = #2)
fun add_ex s1 s2 =
  Example_Data.map (cons s2)
  #> (fn thy => let val () = warning (s1 ^ s2)
                    val () = app (fn s => writeln ("  Data content: " ^ s)) (Example_Data.get thy)
                in thy end)
\<close>

setup \<open>Example_Data.put []\<close>

declare[[ML_source_trace]]

C \<comment> \<open>Arbitrary interleaving of effects\<close> \<open>
int x /** OWNED_BY foo */, hh /*@
  MODIFIES: [*] x
  setup \<open>@{setup "evaluation of 2_setup"}\<close>
  +++++@ hook \<open>fn x => @{hook} x #> add_ex "evaluation of " "2_hook"\<close>
  OWNED_BY bar
  theory
  context
  hook \<open>fn x => @{hook} x #> add_ex "evaluation of " "1_hook"\<close>
  setup \<open>@{setup "evaluation of 1_setup"}\<close>
  \<open>term "a + b"\<close>
*/, z;

int b = 0;
\<close>

section \<open>Miscellaneous\<close>

C \<comment> \<open>Antiquotations acting on a parsed-subtree\<close> \<open>
# /**/ include  <a\b\\c> // backslash rendered unescaped
f(){0 +  0;} /**/  // val _ : theory => 'a => theory
# /*@ context */ if if elif
#include
if then else ;
# /* zzz */  elif /**/
#else\
            
#define FOO  00 0 "" ((
FOO(FOO(a,b,c))
#endif\<close>

end