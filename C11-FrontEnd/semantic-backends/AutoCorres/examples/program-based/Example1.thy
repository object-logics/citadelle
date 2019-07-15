(******************************************************************************
 * Isabelle/C
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

theory Example1
  imports "../../src/compiler/Init"
begin

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

end
