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


lemmas substs = OCL_core.foundation13[THEN iffD2, THEN OCL_core.StrongEq_L_subst2_rev]
                OCL_core.foundation14[THEN iffD2, THEN OCL_core.StrongEq_L_subst2_rev]
                OCL_core.foundation15[THEN iffD2, THEN OCL_core.StrongEq_L_subst2_rev]
                OCL_core.foundation7'[THEN iffD2, THEN OCL_core.foundation15[THEN iffD2, 
                                      THEN OCL_core.StrongEq_L_subst2_rev]]
                OCL_core.StrongEq_L_subst2_rev

                
ML{*
local val [c1,c2,c3,c4,c5] = @{thms "substs"}
in

fun ocl_subst_asm_tac ctxt x = FIRST[(etac c5 x) THEN (simp_tac ctxt x), 
                                     (etac c4 x) THEN (simp_tac ctxt x), 
                                     (etac c3 x) THEN (simp_tac ctxt x), 
                                     (etac c2 x) THEN (simp_tac ctxt x),
                                     (etac c1 x) THEN (simp_tac ctxt x)]
end;

val ocl_subst_asm = fn ctxt => SIMPLE_METHOD (ocl_subst_asm_tac ctxt 1); 

val _ = Theory.setup 
             (Method.setup (Binding.name "ocl_subst_asm") 
             (Scan.succeed (ocl_subst_asm)) 
             "ocl substition step") 
 
*}

lemma test1' : "\<tau> \<Turnstile> A \<Longrightarrow> \<tau> \<Turnstile> (A and B \<triangleq> B)"
apply(tactic "ocl_subst_asm_tac @{context} 1")
apply(simp)
done

lemma test1 : "\<tau> \<Turnstile> A \<Longrightarrow> \<tau> \<Turnstile> (A and B \<triangleq> B)"
by(ocl_subst_asm, simp)

lemma test2 : "\<tau> \<Turnstile> not A \<Longrightarrow> \<tau> \<Turnstile> (A and B \<triangleq> false)"
by(ocl_subst_asm, simp)

lemma test3 : "\<tau> \<Turnstile> (A \<triangleq> null) \<Longrightarrow> \<tau> \<Turnstile> (B \<triangleq> null) \<Longrightarrow> \<tau> \<Turnstile> not(A and B)"
apply(ocl_subst_asm,ocl_subst_asm,simp)
oops

 (* TODO : establish support for goals of the form 
   -  \<not> \<tau> \<Turnstile> A  
   -  (\<tau> \<Turnstile> A)  = (\<tau> \<Turnstile> A')  
   -  \<not>(\<tau> \<Turnstile> A)  = \<not>(\<tau> \<Turnstile> A')  
   
   Use :  OCL_core.StrongEq_L_subst3 etc...
 *)

 (* TODO : establish tactic support for ocl_subst thm1 ... thmn
    (argument line version)
 *)
 
 (* TODO : Implement delta-closure procedure *)
 
 (* TODO : Implement ocl_smt *)

 
end
