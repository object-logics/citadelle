(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * UML_Contracts.thy ---
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013-2014 Universite Paris-Sud, France
 *               2013-2014 IRT SystemX, France
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

theory UML_Contracts
imports UML_State UML_Library
begin

text{* Modeling of an operation contract for an operation  with 2 arguments,
       (so depending on three parameters if one takes "self" into account). *}
 
locale contract0 =
   fixes f   :: "('\<AA>,'\<alpha>0::null)val \<Rightarrow>            
                  ('\<AA>,'res::null)val"
   fixes PRE ::  "('\<AA>,'\<alpha>0::null)val \<Rightarrow> 
                  ('\<AA>, Boolean\<^sub>b\<^sub>a\<^sub>s\<^sub>e)val"
   fixes POST :: "('\<AA>,'\<alpha>0::null)val \<Rightarrow>            
                  ('\<AA>,'res::null)val \<Rightarrow>
                  ('\<AA>, Boolean\<^sub>b\<^sub>a\<^sub>s\<^sub>e)val"
   assumes def_scheme: "f self \<equiv>  (\<lambda> \<tau>. if (\<tau> \<Turnstile> (\<delta> self))
                                         then SOME res. (\<tau> \<Turnstile> PRE self) \<and>
                                                        (\<tau> \<Turnstile> POST self (\<lambda> _. res))
                                         else invalid \<tau>)"
   assumes "\<forall> \<sigma> \<sigma>' \<sigma>''. ((\<sigma>,\<sigma>') \<Turnstile> PRE self) = ((\<sigma>,\<sigma>'') \<Turnstile> PRE self)"
           (* PRE is really a pre-condition semantically,
              i.e. it does not depend on the post-state. ... *)
   assumes cp\<^sub>P\<^sub>R\<^sub>E: "PRE (self)  \<tau> = PRE (\<lambda> _. self \<tau>) \<tau> "
           (* this interface is preferable than :
              assumes "cp self' \<Longrightarrow> cp a1' \<Longrightarrow> cp a2' \<Longrightarrow> cp (\<lambda>X. PRE (self' X) (a1' X) (a2' X) )"
              which is too polymorphic. *)
   assumes cp\<^sub>P\<^sub>O\<^sub>S\<^sub>T:"POST (self) (res) \<tau> = POST (\<lambda> _. self \<tau>) (\<lambda> _. res \<tau>) \<tau>"

begin  
   lemma strict0 [simp]: "f invalid  = invalid"
   by(rule ext, rename_tac "\<tau>", simp add: def_scheme)

   lemma nullstrict0[simp]: "f null = invalid"
   by(rule ext, rename_tac "\<tau>", simp add: def_scheme)

   lemma cp_pre: "cp self' \<Longrightarrow>  cp (\<lambda>X. PRE (self' X)  )"
   by(rule_tac f=PRE in cpI1, auto intro: cp\<^sub>P\<^sub>R\<^sub>E)
  
   
   lemma cp_post: "cp self' \<Longrightarrow> cp res'  \<Longrightarrow> cp (\<lambda>X. POST (self' X) (res' X))"
   by(rule_tac f=POST in cpI2, auto intro: cp\<^sub>P\<^sub>O\<^sub>S\<^sub>T)  
    
   lemma cp0 : "f self \<tau> = f (\<lambda> _. self \<tau>) \<tau>"
   proof -
      have A: "(\<tau> \<Turnstile> \<delta> (\<lambda>_. self \<tau>)) = (\<tau> \<Turnstile> \<delta> self)" by(simp add: OclValid_def cp_defined[symmetric])
      have D: "(\<tau> \<Turnstile> PRE (\<lambda>_. self \<tau>)) = ( \<tau> \<Turnstile> PRE self)" by(simp add: OclValid_def cp\<^sub>P\<^sub>R\<^sub>E[symmetric])
      show ?thesis
        apply(auto simp: def_scheme A  D)
        apply(simp add: OclValid_def)
        by(subst cp\<^sub>P\<^sub>O\<^sub>S\<^sub>T, simp)
      qed
      
   lemma cp [simp]:  "cp self' \<Longrightarrow>  cp res' \<Longrightarrow> cp (\<lambda>X. f (self' X) )"
      by(rule_tac f=f in cpI1, auto intro:cp0)  
   
   theorem unfold : 
      assumes context_ok:    "cp E"
      and args_def_or_valid: "(\<tau> \<Turnstile> \<delta> self)"
      and pre_satisfied:     "\<tau> \<Turnstile> PRE self"
      and post_satisfiable:  " \<exists>res. (\<tau> \<Turnstile> POST self (\<lambda> _. res))"
      and sat_for_sols_post: "(\<And>res. \<tau> \<Turnstile> POST self (\<lambda> _. res)  \<Longrightarrow> \<tau> \<Turnstile> E (\<lambda> _. res))"
      shows                  "\<tau> \<Turnstile> E(f self)"
   proof -  
      have cp0: "\<And> X \<tau>. E X \<tau> = E (\<lambda>_. X \<tau>) \<tau>" by(insert context_ok[simplified cp_def], auto)
      show ?thesis
         apply(simp add: OclValid_def, subst cp0, fold OclValid_def)
         apply(simp add:def_scheme args_def_or_valid pre_satisfied)
         apply(insert post_satisfiable, elim exE)
         apply(rule Hilbert_Choice.someI2, assumption)
         by(rule sat_for_sols_post, simp)
   qed
   
   lemma unfold2 :
      assumes context_ok:      "cp E"
      and args_def_or_valid:   "(\<tau> \<Turnstile> \<delta> self)"
      and pre_satisfied:       "\<tau> \<Turnstile> PRE self"
      and postsplit_satisfied: "\<tau> \<Turnstile> POST' self" (* split constraint holds on post-state *)
      and post_decomposable  : "\<And> res. (POST self res) = 
                                       ((POST' self)  and (res \<triangleq> (BODY self)))"
      shows "(\<tau> \<Turnstile> E(f self)) = (\<tau> \<Turnstile> E(BODY self))"
   proof -
      have cp0: "\<And> X \<tau>. E X \<tau> = E (\<lambda>_. X \<tau>) \<tau>" by(insert context_ok[simplified cp_def], auto)
      show ?thesis
         apply(simp add: OclValid_def, subst cp0, fold OclValid_def)      
         apply(simp add:def_scheme args_def_or_valid pre_satisfied 
                        post_decomposable postsplit_satisfied foundation27)
         apply(subst some_equality)
         apply(simp add: OclValid_def StrongEq_def true_def)+
         by(subst (2) cp0, rule refl)
   qed
end


locale contract1 =
   fixes f   :: "('\<AA>,'\<alpha>0::null)val \<Rightarrow>            
                  ('\<AA>,'\<alpha>1::null)val \<Rightarrow> 
                  ('\<AA>,'res::null)val"
   fixes PRE ::  "('\<AA>,'\<alpha>0::null)val \<Rightarrow> 
                  ('\<AA>,'\<alpha>1::null)val \<Rightarrow> 
                  ('\<AA>, Boolean\<^sub>b\<^sub>a\<^sub>s\<^sub>e)val"
   fixes POST :: "('\<AA>,'\<alpha>0::null)val \<Rightarrow>            
                  ('\<AA>,'\<alpha>1::null)val \<Rightarrow> 
                  ('\<AA>,'res::null)val \<Rightarrow>
                  ('\<AA>, Boolean\<^sub>b\<^sub>a\<^sub>s\<^sub>e)val"
   assumes def_scheme: "f self a1 \<equiv> 
                               (\<lambda> \<tau>. if (\<tau> \<Turnstile> (\<delta> self)) \<and>  (\<tau> \<Turnstile> \<upsilon> a1)
                                     then SOME res. (\<tau> \<Turnstile> PRE self a1) \<and>
                                                    (\<tau> \<Turnstile> POST self a1 (\<lambda> _. res))
                                     else invalid \<tau>) "
   assumes "\<forall> \<sigma> \<sigma>' \<sigma>''.  ((\<sigma>,\<sigma>') \<Turnstile> PRE self a1) = ((\<sigma>,\<sigma>'') \<Turnstile> PRE self a1)"
           (* PRE is really a pre-condition semantically,
              i.e. it does not depend on the post-state. ... *)
   assumes cp\<^sub>P\<^sub>R\<^sub>E: "PRE (self) (a1)  \<tau> = PRE (\<lambda> _. self \<tau>) (\<lambda> _. a1 \<tau>) \<tau> "
           (* this interface is preferable than :
              assumes "cp self' \<Longrightarrow> cp a1' \<Longrightarrow> cp a2' \<Longrightarrow> cp (\<lambda>X. PRE (self' X) (a1' X) (a2' X) )"
              which is too polymorphic. *)
   assumes cp\<^sub>P\<^sub>O\<^sub>S\<^sub>T:"POST (self) (a1) (res) \<tau> = POST (\<lambda> _. self \<tau>)(\<lambda> _. a1 \<tau>) (\<lambda> _. res \<tau>) \<tau>"

begin  
   lemma strict0 [simp]: "f invalid X = invalid"
   by(rule ext, rename_tac "\<tau>", simp add: def_scheme)

   lemma nullstrict0[simp]: "f null X = invalid"
   by(rule ext, rename_tac "\<tau>", simp add: def_scheme)

   lemma strict1[simp]: "f self invalid = invalid"
   by(rule ext, rename_tac "\<tau>", simp add: def_scheme)
   
   lemma cp_pre: "cp self' \<Longrightarrow> cp a1' \<Longrightarrow>  cp (\<lambda>X. PRE (self' X) (a1' X)  )"
   by(rule_tac f=PRE in cpI2, auto intro: cp\<^sub>P\<^sub>R\<^sub>E)
  
   
   lemma cp_post: "cp self' \<Longrightarrow> cp a1' \<Longrightarrow> cp res'
                   \<Longrightarrow> cp (\<lambda>X. POST (self' X) (a1' X) (res' X))"
   by(rule_tac f=POST in cpI3, auto intro: cp\<^sub>P\<^sub>O\<^sub>S\<^sub>T)  
    
   lemma cp0 : "f self a1 \<tau> = f (\<lambda> _. self \<tau>) (\<lambda> _. a1 \<tau>) \<tau>"
   proof -
      have A: "(\<tau> \<Turnstile> \<delta> (\<lambda>_. self \<tau>)) = (\<tau> \<Turnstile> \<delta> self)" by(simp add: OclValid_def cp_defined[symmetric])
      have B: "(\<tau> \<Turnstile> \<upsilon> (\<lambda>_. a1 \<tau>)) = (\<tau> \<Turnstile> \<upsilon> a1)" by(simp add: OclValid_def cp_valid[symmetric])
      have D: "(\<tau> \<Turnstile> PRE (\<lambda>_. self \<tau>) (\<lambda>_. a1 \<tau>)) = ( \<tau> \<Turnstile> PRE self a1 )"
                                                 by(simp add: OclValid_def cp\<^sub>P\<^sub>R\<^sub>E[symmetric])
      show ?thesis
        apply(auto simp: def_scheme A B D)
        apply(simp add: OclValid_def)
        by(subst cp\<^sub>P\<^sub>O\<^sub>S\<^sub>T, simp)
      qed
      
   lemma cp [simp]:  "cp self' \<Longrightarrow> cp a1' \<Longrightarrow>  cp res' \<Longrightarrow> cp (\<lambda>X. f (self' X) (a1' X))"
      by(rule_tac f=f in cpI2, auto intro:cp0)  
      
   theorem unfold : 
      assumes context_ok:    "cp E"
      and args_def_or_valid: "(\<tau> \<Turnstile> \<delta> self) \<and> (\<tau> \<Turnstile> \<upsilon> a1)"
      and pre_satisfied:     "\<tau> \<Turnstile> PRE self a1"
      and post_satisfiable:  " \<exists>res. (\<tau> \<Turnstile> POST self a1 (\<lambda> _. res))"
      and sat_for_sols_post: "(\<And>res. \<tau> \<Turnstile> POST self a1 (\<lambda> _. res)  \<Longrightarrow> \<tau> \<Turnstile> E (\<lambda> _. res))"
      shows                  "\<tau> \<Turnstile> E(f self a1)"
   proof -  
      have cp0: "\<And> X \<tau>. E X \<tau> = E (\<lambda>_. X \<tau>) \<tau>" by(insert context_ok[simplified cp_def], auto)
      show ?thesis
         apply(simp add: OclValid_def, subst cp0, fold OclValid_def)
         apply(simp add:def_scheme args_def_or_valid pre_satisfied)
         apply(insert post_satisfiable, elim exE)
         apply(rule Hilbert_Choice.someI2, assumption)
         by(rule sat_for_sols_post, simp)
   qed
   
   lemma unfold2 :
      assumes context_ok:      "cp E"
      and args_def_or_valid:   "(\<tau> \<Turnstile> \<delta> self) \<and> (\<tau> \<Turnstile> \<upsilon> a1)"
      and pre_satisfied:       "\<tau> \<Turnstile> PRE self a1"
      and postsplit_satisfied: "\<tau> \<Turnstile> POST' self a1" (* split constraint holds on post-state *)
      and post_decomposable  : "\<And> res. (POST self a1 res) = 
                                       ((POST' self a1)  and (res \<triangleq> (BODY self a1)))"
      shows "(\<tau> \<Turnstile> E(f self a1)) = (\<tau> \<Turnstile> E(BODY self a1))"
   proof -
      have cp0: "\<And> X \<tau>. E X \<tau> = E (\<lambda>_. X \<tau>) \<tau>" by(insert context_ok[simplified cp_def], auto)
      show ?thesis
         apply(simp add: OclValid_def, subst cp0, fold OclValid_def)      
         apply(simp add:def_scheme args_def_or_valid pre_satisfied 
                        post_decomposable postsplit_satisfied foundation27)
         apply(subst some_equality)
         apply(simp add: OclValid_def StrongEq_def true_def)+
         by(subst (2) cp0, rule refl)
   qed
end


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
   assumes cp\<^sub>P\<^sub>R\<^sub>E: "PRE (self) (a1) (a2) \<tau> = PRE (\<lambda> _. self \<tau>) (\<lambda> _. a1 \<tau>) (\<lambda> _. a2 \<tau>) \<tau> "
           (* this interface is preferable than :
              assumes "cp self' \<Longrightarrow> cp a1' \<Longrightarrow> cp a2' \<Longrightarrow> cp (\<lambda>X. PRE (self' X) (a1' X) (a2' X) )"
              which is too polymorphic. *)
   assumes cp\<^sub>P\<^sub>O\<^sub>S\<^sub>T:"\<And>res. POST (self) (a1) (a2) (res) \<tau> = 
                         POST (\<lambda> _. self \<tau>)(\<lambda> _. a1 \<tau>)(\<lambda> _. a2 \<tau>) (\<lambda> _. res \<tau>) \<tau>"

begin  
   lemma strict0 [simp]: "f invalid X Y = invalid"
   by(rule ext, rename_tac "\<tau>", simp add: def_scheme)

   lemma nullstrict0[simp]: "f null X Y = invalid"
   by(rule ext, rename_tac "\<tau>", simp add: def_scheme)

   lemma strict1[simp]: "f self invalid Y = invalid"
   by(rule ext, rename_tac "\<tau>", simp add: def_scheme)

   lemma strict2[simp]: "f self X invalid = invalid"
   by(rule ext, rename_tac "\<tau>", simp add: def_scheme)
   
   lemma cp_pre: "cp self' \<Longrightarrow> cp a1' \<Longrightarrow> cp a2' \<Longrightarrow> cp (\<lambda>X. PRE (self' X) (a1' X) (a2' X) )"
   by(rule_tac f=PRE in cpI3, auto intro: cp\<^sub>P\<^sub>R\<^sub>E)
  
   
   lemma cp_post: "cp self' \<Longrightarrow> cp a1' \<Longrightarrow> cp a2' \<Longrightarrow> cp res'
                   \<Longrightarrow> cp (\<lambda>X. POST (self' X) (a1' X) (a2' X) (res' X))"
   by(rule_tac f=POST in cpI4, auto intro: cp\<^sub>P\<^sub>O\<^sub>S\<^sub>T)  
   
   lemma cp0 : "f self a1 a2 \<tau> = f (\<lambda> _. self \<tau>) (\<lambda> _. a1 \<tau>) (\<lambda> _. a2 \<tau>) \<tau>"
   proof -
      have A: "(\<tau> \<Turnstile> \<delta> (\<lambda>_. self \<tau>)) = (\<tau> \<Turnstile> \<delta> self)" by(simp add: OclValid_def cp_defined[symmetric])
      have B: "(\<tau> \<Turnstile> \<upsilon> (\<lambda>_. a1 \<tau>)) = (\<tau> \<Turnstile> \<upsilon> a1)" by(simp add: OclValid_def cp_valid[symmetric])
      have C: "(\<tau> \<Turnstile> \<upsilon> (\<lambda>_. a2 \<tau>)) = (\<tau> \<Turnstile> \<upsilon> a2)" by(simp add: OclValid_def cp_valid[symmetric])
      have D: "(\<tau> \<Turnstile> PRE (\<lambda>_. self \<tau>) (\<lambda>_. a1 \<tau>) (\<lambda>_. a2 \<tau>)) = ( \<tau> \<Turnstile> PRE self a1 a2 )"
                                                 by(simp add: OclValid_def cp\<^sub>P\<^sub>R\<^sub>E[symmetric])
      show ?thesis
        apply(auto simp: def_scheme A B C D)
        apply(simp add: OclValid_def)
        by(subst cp\<^sub>P\<^sub>O\<^sub>S\<^sub>T, simp)
      qed
      
   lemma cp [simp]:  "cp self' \<Longrightarrow> cp a1' \<Longrightarrow> cp a2' \<Longrightarrow> cp res'
                       \<Longrightarrow> cp (\<lambda>X. f (self' X) (a1' X) (a2' X))"
      by(rule_tac f=f in cpI3, auto intro:cp0)  
   
   theorem unfold : 
      assumes context_ok:    "cp E"
      and args_def_or_valid: "(\<tau> \<Turnstile> \<delta> self) \<and> (\<tau> \<Turnstile> \<upsilon> a1) \<and>  (\<tau> \<Turnstile> \<upsilon> a2)"
      and pre_satisfied:     "\<tau> \<Turnstile> PRE self a1 a2"
      and post_satisfiable:  " \<exists>res. (\<tau> \<Turnstile> POST self a1 a2 (\<lambda> _. res))"
      and sat_for_sols_post: "(\<And>res. \<tau> \<Turnstile> POST self a1 a2 (\<lambda> _. res)  \<Longrightarrow> \<tau> \<Turnstile> E (\<lambda> _. res))"
      shows                  "\<tau> \<Turnstile> E(f self a1 a2)"
   proof -  
      have cp0: "\<And> X \<tau>. E X \<tau> = E (\<lambda>_. X \<tau>) \<tau>" by(insert context_ok[simplified cp_def], auto)
      show ?thesis
         apply(simp add: OclValid_def, subst cp0, fold OclValid_def)
         apply(simp add:def_scheme args_def_or_valid pre_satisfied)
         apply(insert post_satisfiable, elim exE)
         apply(rule Hilbert_Choice.someI2, assumption)
         by(rule sat_for_sols_post, simp)
   qed
   
   lemma unfold2 :
      assumes context_ok:      "cp E"
      and args_def_or_valid:   "(\<tau> \<Turnstile> \<delta> self) \<and> (\<tau> \<Turnstile> \<upsilon> a1) \<and>  (\<tau> \<Turnstile> \<upsilon> a2)"
      and pre_satisfied:       "\<tau> \<Turnstile> PRE self a1 a2"
      and postsplit_satisfied: "\<tau> \<Turnstile> POST' self a1 a2" (* split constraint holds on post-state *)
      and post_decomposable  : "\<And> res. (POST self a1 a2 res) = 
                                       ((POST' self a1 a2)  and (res \<triangleq> (BODY self a1 a2)))"
      shows "(\<tau> \<Turnstile> E(f self a1 a2)) = (\<tau> \<Turnstile> E(BODY self a1 a2))"
   proof -
      have cp0: "\<And> X \<tau>. E X \<tau> = E (\<lambda>_. X \<tau>) \<tau>" by(insert context_ok[simplified cp_def], auto)
      show ?thesis
         apply(simp add: OclValid_def, subst cp0, fold OclValid_def)      
         apply(simp add:def_scheme args_def_or_valid pre_satisfied 
                        post_decomposable postsplit_satisfied foundation27)
         apply(subst some_equality)
         apply(simp add: OclValid_def StrongEq_def true_def)+
         by(subst (2) cp0, rule refl)
   qed
end


end
