theory Constracts
imports OCL_state OCL_lib
begin

text{* Modeling of an operation contract for an operation  with 2 arguments,
       (so depending on three parameters if one takes "self" into account). *}
       
locale contract2 =
   fixes f   :: "('\<AA>,'\<alpha>0::null)val \<Rightarrow>            
                  ('\<AA>,'\<alpha>1::null)val \<Rightarrow> ('\<AA>,'\<alpha>2::null)val \<Rightarrow>
                  ('\<AA>,'res::null)val"
   fixes PRE ::  "('\<AA>,'\<alpha>0::null)val \<Rightarrow> 
                  ('\<AA>,'\<alpha>1::null)val \<Rightarrow> ('\<AA>,'\<alpha>2::null)val \<Rightarrow> 
                  ('\<AA>, Boolean\<^sub>b\<^sub>a\<^sub>s\<^sub>e)val"
   fixes POST :: "('\<AA>,'\<alpha>0::null)val \<Rightarrow>            
                  ('\<AA>,'\<alpha>1::null)val \<Rightarrow> ('\<AA>,'\<alpha>2::null)val \<Rightarrow>
                  ('\<AA>,'res::null)val \<Rightarrow>
                  ('\<AA>, Boolean\<^sub>b\<^sub>a\<^sub>s\<^sub>e)val"
   assumes def_scheme: "f self a1 a2 \<equiv> 
                               (\<lambda> \<tau>. if (\<tau> \<Turnstile> (\<delta> self)) \<and>  (\<tau> \<Turnstile> \<upsilon> a1) \<and>  (\<tau> \<Turnstile> \<upsilon> a2)
                                     then SOME res. (\<tau> \<Turnstile> PRE self a1 a2) \<and>
                                                    (\<tau> \<Turnstile> POST self a1 a2 (\<lambda> _. res))
                                     else invalid \<tau>) "
   assumes "\<forall> \<sigma> \<sigma>' \<sigma>''.  ((\<sigma>,\<sigma>') \<Turnstile> PRE self a1 a2) = ((\<sigma>,\<sigma>'') \<Turnstile> PRE self a1 a2)"
           (* PRE is really a pre-condition semantically,
              i.e. it does not depend on the post-state. ... *)
   assumes "PRE (self) (a1) (a2) \<tau> = PRE (\<lambda> _. self \<tau>) (\<lambda> _. a1 \<tau>) (\<lambda> _. a2 \<tau>) \<tau> "
           (* this interface is preferable than :
              assumes "cp self' \<Longrightarrow> cp a1' \<Longrightarrow> cp a2' \<Longrightarrow> cp (\<lambda>X. PRE (self' X) (a1' X) (a2' X) )"
              which is too polymorphic. *)
   assumes "POST (self) (a1) (a2) (res) \<tau> = POST (\<lambda> _. self \<tau>)(\<lambda> _. a1 \<tau>)(\<lambda> _. a2 \<tau>) (\<lambda> _. res \<tau>) \<tau>"
   (*
   assumes "cp self' \<Longrightarrow> cp a1' \<Longrightarrow> cp a2' \<Longrightarrow> cp res'
                \<Longrightarrow> cp (\<lambda>X. POST (self' X) (a1' X) (a2' X) (res' X))" *)
begin  
   lemma strict0 [simp]: "f invalid X Y = invalid"
   by(rule ext, rename_tac "\<tau>", simp add: def_scheme)

   lemma nullstrict1[simp]: "f null X Y = invalid"
   by(rule ext, rename_tac "\<tau>", simp add: def_scheme)

   lemma strict1[simp]: "f self invalid Y = invalid"
   by(rule ext, rename_tac "\<tau>", simp add: def_scheme)

   lemma strict2[simp]: "f self X invalid = invalid"
   by(rule ext, rename_tac "\<tau>", simp add: def_scheme)
   
   lemma cp_pre: "cp self' \<Longrightarrow> cp a1' \<Longrightarrow> cp a2' \<Longrightarrow> cp (\<lambda>X. PRE (self' X) (a1' X) (a2' X) )"
   sorry
   
   lemma cp_post: "cp self' \<Longrightarrow> cp a1' \<Longrightarrow> cp a2' \<Longrightarrow> cp res'
                   \<Longrightarrow> cp (\<lambda>X. POST (self' X) (a1' X) (a2' X) (res' X))"
   sorry
   
   lemma cp0 [simp]:  "cp self' \<Longrightarrow> cp a1' \<Longrightarrow> cp a2' \<Longrightarrow> cp res'
                       \<Longrightarrow> cp (\<lambda>X. f (self' X) (a1' X) (a2' X))"
   sorry                 
   
   lemma unfold : "f self a1 a2 = undefined "
   sorry
end



                 term "THE x. P x" 
                  
