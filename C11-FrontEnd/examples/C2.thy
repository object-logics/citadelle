theory C2
  imports "../C11-Interface"
begin


C\<open>
/* @ ensures \result >= x && \result >= y;
  @*/

int max(int x, int y) {
  if (x > y) return x; else return y;
}
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


section\<open>Some realistic Selection sort with Input and Output\<close>
C\<open>
#include <stdio.h>
 
int main()
{
  int array[100], n, c, d, position, swap;
 
  printf("Enter number of elements\n");
  scanf("%d", &n);
 
  printf("Enter %d integers\n", n);
 
  for (c = 0; c < n; c++)
    scanf("%d", &array[c]);
 
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
ML\<open> C11_core.dest_list @{theory}; \<close>