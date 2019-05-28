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

chapter \<open>Example\<close>

theory C2
  imports C.C_Main
begin

ML\<open>
structure Data_Out = Generic_Data
  (type T = (C_Ast.CTranslUnit * C_Antiquote.antiq C_Env.stream) list
   val empty = []
   val extend = K empty
   val merge = K empty)

fun get_module thy =
  let val context = Context.Theory thy
  in (Data_Out.get context, C_Module.Data_In_Env.get context) end
\<close>

setup \<open>Context.theory_map (C_Module.Data_Accept.put (fn ast => fn env_lang => Data_Out.map (cons (ast, #stream_ignored env_lang |> rev))))\<close>

C\<open>

#include <stdio.h>
#include /*sdfsdf */ <stdlib.h>
#define a B
#define b(C) 
#pragma
\<close>
ML\<open> 
val ((C_Ast.CTranslUnit0 (t,u), v)::R, env) = get_module @{theory};
val u = C_Grammar_Rule_Lib.decode u; 
C_Ast.CTypeSpec0;
\<close>


C\<open>
/* @ ensures \result >= x && \result >= y;
  @*/

int max(int x, int y) {
  if (x > y) return x; else return y;
}
\<close>

ML\<open> 
val ((C_Ast.CTranslUnit0 (t,u), v)::R, env) = get_module @{theory};
val u = C_Grammar_Rule_Lib.decode u
\<close>


C\<open>
int sqrt(int a) {
  int i = 0;
  int tm = 1;
  int sum = 1;

  /* @ loop invariant 1 <= sum <= a+tm;
    @ loop invariant (i+1)*(i+1) == sum;
    @ loop invariant tm+(i*i) == sum;
    @ loop invariant 1<=tm<=sum;
    @ loop assigns i, tm, sum;
    @ loop variant a-sum;
    @*/
  while (sum <= a) {      
    i++;
    tm = tm + 2;
    sum = sum + tm;
  }
  
  return i;
}
\<close>

C\<open>
/* @ requires n >= 0;
  @ requires \valid(t+(0..n-1));
  @ ensures \exists integer i; (0<=i<n && t[i] != 0) <==> \result == 0;
  @ ensures (\forall integer i; 0<=i<n ==> t[i] == 0) <==> \result == 1;
  @ assigns \nothing;
  @*/

int allzeros(int t[], int n) {
  int k = 0;

  /* @ loop invariant 0 <= k <= n;
    @ loop invariant \forall integer i; 0<=i<k ==> t[i] == 0;
    @ loop assigns k;
    @ loop variant n-k;
    @*/
  while(k < n) {
    if (t[k]) return 0;
    k = k + 1;
  }
  return 1;
}

\<close>

C\<open>

/* @ requires n >= 0;
  @ requires \valid(t+(0..n-1));
  @ ensures (\forall integer i; 0<=i<n ==> t[i] != v) <==> \result == -1;
  @ ensures (\exists integer i; 0<=i<n && t[i] == v) <==> \result == v;
  @ assigns \nothing;
  @*/

int binarysearch(int t[], int n, int v) {
  int l = 0;
  int u = n-1;

  /* @ loop invariant \false;
    @*/
  while (l <= u) {
    int m = (l + u) / 2;
    if (t[m] < v) {
      l = m + 1;
    } else if (t[m] > v) {
      u = m - 1;
    }
    else return m; 
  }
  return -1;
}
\<close>


C\<open>
/* @ requires n >= 0;
  @ requires \valid(t+(0..n-1));
  @ requires (\forall integer i,j; 0<=i<=j<n ==> t[i] <= t[j]);
  @ ensures \exists integer i; (0<=i<n && t[i] == x) <==> \result == 1;
  @ ensures (\forall integer i; 0<=i<n ==> t[i] != x) <==> \result == 0;
  @ assigns \nothing;
 */

int linearsearch(int x, int t[], int n) {
  int i = 0;

  /* @ loop invariant 0<=i<=n;  
    @ loop invariant \forall integer j; 0<=j<i ==> (t[j] != x);
    @ loop assigns i;
    @ loop variant n-i;
   */
  while (i < n) {
    if (t[i] < x) {
      i++;
    } else {
      return (t[i] == x);
    }
  }

  return 0;
}
\<close>

ML\<open>
val p  = @{here};
open Position;
ML_Syntax.print_position p;
writeln it;
\<close>

section\<open>Some realistic Selection sort with Input and Output\<close>
C\<open>
#include <stdio.h>
 
int main()
{
  int array[100], n, c, d, position, swap;
 
  printf("Enter number of elements\n");
  scanf("%d", &n);
 
  printf("Enter %d integers\n", n);
 
  for (c = 0; c < n; c++) scanf("%d", &array[c]);
 
  for (c = 0; c < (n - 1); c++)
  {
    position = c;
   
    for (d = c + 1; d < n; d++)
    {
      if (array[position] > array[d])
        position = d;
    }
    if (position != c)
    {
      swap = array[c];
      array[c] = array[position];
      array[position] = swap;
    }
  }

printf("Sorted list in ascending order:\n");
 
  for (c = 0; c < n; c++)
    printf("%d\n", array[c]);
 
  return 0;
}
\<close>

text\<open>A better one:\<close>

C\<open>
#include <stdio.h>
#include <stdlib.h>
 
#define SIZE 10
 
void swap(int *x,int *y);
void selection_sort(int* a, const int n);
void display(int a[],int size);
 
void main()
{
 
    int a[SIZE] = {8,5,2,3,1,6,9,4,0,7};
 
    int i;
    printf("The array before sorting:\n");
    display(a,SIZE);
 
    selection_sort(a,SIZE);
 
    printf("The array after sorting:\n");
    display(a,SIZE);
}
 
/*
    swap two integers
*/
void swap(int *x,int *y)
{
    int temp;
 
    temp = *x;
    *x = *y;
    *y = temp;
}
/*
    perform selection sort
*/
void selection_sort(int* a,const int size)
{
    int i, j, min;
 
    for (i = 0; i < size - 1; i++)
    {
        min = i;
        for (j = i + 1; j < size; j++)
        {
            if (a[j] < a[min])
            {
                min = j;
            }
        }
        swap(&a[i], &a[min]);
    }
}
/*
    display array content
*/
void display(int a[],const int size)
{
    int i;
    for(i=0; i<size; i++)
        printf("%d ",a[i]);
    printf("\n");
}
\<close>

ML\<open>
local open C_Ast in
val _ = CTranslUnit0
val ((CTranslUnit0 (t,u), v)::_, _) = get_module @{theory};
val u = C_Grammar_Rule_Lib.decode u
val _ = case  u of Left (p1,p2) => writeln (Position.here p1 ^ " " ^ Position.here p2)
val CDeclExt0(x1)::_ = t;
val _ = CDecl0
end
\<close>


end