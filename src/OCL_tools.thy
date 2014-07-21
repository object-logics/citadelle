(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4 
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_tools.thy ---
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2012      Université Paris-Sud, France
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

theory OCL_tools
imports OCL_core
begin


lemmas substs1 = OCL_core.StrongEq_L_subst2_rev
                 OCL_core.foundation15[THEN iffD2, THEN OCL_core.StrongEq_L_subst2_rev]
                 OCL_core.foundation7'[THEN iffD2, THEN OCL_core.foundation15[THEN iffD2, 
                                       THEN OCL_core.StrongEq_L_subst2_rev]]                
                 OCL_core.foundation14[THEN iffD2, THEN OCL_core.StrongEq_L_subst2_rev]
                 OCL_core.foundation13[THEN iffD2, THEN OCL_core.StrongEq_L_subst2_rev]
                
lemmas substs2 = OCL_core.StrongEq_L_subst3_rev
                 OCL_core.foundation15[THEN iffD2, THEN OCL_core.StrongEq_L_subst3_rev]
                 OCL_core.foundation7'[THEN iffD2, THEN OCL_core.foundation15[THEN iffD2, 
                                       THEN OCL_core.StrongEq_L_subst3_rev]]                
                 OCL_core.foundation14[THEN iffD2, THEN OCL_core.StrongEq_L_subst3_rev]
                 OCL_core.foundation13[THEN iffD2, THEN OCL_core.StrongEq_L_subst3_rev]
                 
lemmas substs4 = OCL_core.StrongEq_L_subst4_rev
                 OCL_core.foundation15[THEN iffD2, THEN OCL_core.StrongEq_L_subst4_rev]
                 OCL_core.foundation7'[THEN iffD2, THEN OCL_core.foundation15[THEN iffD2, 
                                       THEN OCL_core.StrongEq_L_subst4_rev]]                
                 OCL_core.foundation14[THEN iffD2, THEN OCL_core.StrongEq_L_subst4_rev]
                 OCL_core.foundation13[THEN iffD2, THEN OCL_core.StrongEq_L_subst4_rev]

                 
lemmas substs = substs1 substs2 substs4 [THEN iffD2] substs4
thm substs
ML{*
fun ocl_subst_asm_tac ctxt  = FIRST'(map (fn C => (etac C) THEN' (simp_tac ctxt)) 
                                         @{thms "substs"})

val ocl_subst_asm = fn ctxt => SIMPLE_METHOD (ocl_subst_asm_tac ctxt 1); 

val _ = Theory.setup 
             (Method.setup (Binding.name "ocl_subst_asm") 
             (Scan.succeed (ocl_subst_asm)) 
             "ocl substition step") 
 
*}

lemma test1 : "\<tau> \<Turnstile> A \<Longrightarrow> \<tau> \<Turnstile> (A and B \<triangleq> B)"
apply(tactic "ocl_subst_asm_tac @{context} 1")
apply(simp)
done

lemma test2 : "\<tau> \<Turnstile> A \<Longrightarrow> \<tau> \<Turnstile> (A and B \<triangleq> B)"
by(ocl_subst_asm, simp)

lemma test3 : "\<tau> \<Turnstile> A \<Longrightarrow> \<tau> \<Turnstile> (A and A)"
by(ocl_subst_asm, simp)

lemma test4 : "\<tau> \<Turnstile> not A \<Longrightarrow> \<tau> \<Turnstile> (A and B \<triangleq> false)"
by(ocl_subst_asm, simp)

lemma test5 : "\<tau> \<Turnstile> (A \<triangleq> null) \<Longrightarrow> \<tau> \<Turnstile> (B \<triangleq> null) \<Longrightarrow> \<not> (\<tau> \<Turnstile> (A and B))"
by(ocl_subst_asm,ocl_subst_asm,simp)

lemma test6 : "\<tau> \<Turnstile> not A \<Longrightarrow> \<not> (\<tau> \<Turnstile> (A and B))"
by(ocl_subst_asm, simp)

lemma test7 : "\<not> (\<tau> \<Turnstile> (\<upsilon> A)) \<Longrightarrow> \<tau> \<Turnstile> (not B) \<Longrightarrow> \<not> (\<tau> \<Turnstile> (A and B))"
by(ocl_subst_asm,ocl_subst_asm,simp)

lemma X: "\<not> (\<tau> \<Turnstile> (invalid and B))"
oops

lemma Y: "\<not> (\<tau> \<Turnstile> (null and B))"
oops

lemma Z: "\<not> (\<tau> \<Turnstile> (false and B))"
oops

lemma Z: "(\<tau> \<Turnstile> (true and B)) = (\<tau> \<Turnstile> B)"
oops

 (* TODO : establish tactic support for ocl_subst thm1 ... thmn
    (argument line version)
 *)
 
 (* TODO : Implement delta-closure procedure *)
 
 (* TODO : Implement ocl_smt *)

 
end
