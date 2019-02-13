theory C1
  imports "../C11-Interface"
begin

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
C \<comment> \<open>Inline comments with antiquotations\<close> \<open>
 /*@con\
text (**) */ // break of line activated everywhere (also in antiquotations)
int a = 0; //\
@ term \<open>a \
          + b (* (**) *\      
\     
)\<close>
\<close>

C \<comment> \<open>Embedding ML in antiquotations\<close> \<comment> \<open>Closing C comments \<open>*/\<close> must close anything, even when editing ML code\<close> \<open>
int a = (((0 //@ setup \<open>fn _ => fn thy => let in (* */ *) thy end\<close>
             /*@ setup (*   * /   *) */
         )));
\<close>

C \<comment> \<open>Embedding ML in antiquotations\<close> \<comment> \<open>\<^theory_text>\<open>setup\<close> is executed during SHIFT actions\<close> \<open>
int a = (((0))); /*@ setup \<open>fn stack => fn thy =>
                            let
                              val () = warning ("SHIFT  " ^ @{make_string} (length stack - 1) ^ "    +1 ")
                              val () = stack
                                    |> split_list
                                    |> #2
                                    |> map_index I
                                    |> app (fn (i, (value, pos1, pos2)) => writeln ("   " ^ @{make_string} (length stack - i) ^ " " ^ @{make_string} value ^ " " ^ Position.here pos1 ^ " " ^ Position.here pos2))
                            in thy end\<close> */
\<close>

C \<comment> \<open>Embedding ML in antiquotations\<close> \<comment> \<open>\<^theory_text>\<open>hook\<close> is executed during REDUCE actions\<close> \<open>
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

C \<comment> \<open>Embedding ML in antiquotations\<close> \<comment> \<open>\<^theory_text>\<open>hook\<close>: selecting deeper sub-trees\<close> \<open>
int b = 7 / (3) * 50 /*@@@@ hook \<open>@{hook}\<close>
                      */;
\<close>

C \<comment> \<open>Embedding ML in antiquotations\<close> \<comment> \<open>\<^theory_text>\<open>hook\<close>: nesting parsed C code\<close> \<open>
int b = 7 / (3) * 50
  /*@@@@ hook \<open>(hook @{make_string} o tap)
                 (fn _ => C_Outer_Syntax.C
                            \<open>int b = 7 / 5 * 2 + 3 * 50 //@ hook \<open>@{hook}\<close>
                             ;\<close>)\<close>
   */;
\<close>

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