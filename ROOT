(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013-2014 Université Paris-Sud, France
 *               2013-2014 IRT SystemX, France
 *               2013-2014 Achim D. Brucker, Germany
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

session "OCL-dirty" in "src" = HOL +
  description {* Featherweight OCL (Quick and Dirty) *}
  options [quick_and_dirty,document=pdf,document_output=document_generated,
           document_variants="annex-a=annexa,-afp,-proof,-ML:document=afp,-annexa:outline=-annexa,afp,/proof,/ML",
           show_question_marks = false]
  theories
    "../src/UML_Main"
    "../examples/Employee_Model/Analysis/Analysis_OCL"
    "../examples/Employee_Model/Design/Design_OCL"
  files
    "document/root.tex"
    "document/root.bib"
    "document/formalization.tex"
    "document/introduction.tex"


session "OCL" in "src" = HOL +
  description {* Featherweigt OCL *}
  options [document=pdf,document_output=document_generated,
           document_variants="annex-a=annexa,-afp,-proof,-ML:document=afp,-annexa:outline=-annexa,afp,/proof,/ML",
           show_question_marks = false]
  theories
    "../src/UML_Main"
    "../examples/Employee_Model/Analysis/Analysis_OCL"
    "../examples/Employee_Model/Design/Design_OCL"
  files
    "document/root.tex"
    "document/root.bib"
    "document/formalization.tex"
    "document/introduction.tex"


session "OCL-all" in src = HOL +
  description {* HOL-TestGen *}
  options [quick_and_dirty,document=pdf,document_output=document_generated,
           document_variants="document:outline=/proof,/ML"]
  theories
    "../src/UML_Main"
    "../examples/Employee_Model/Analysis/Analysis_OCL"
    "../examples/Employee_Model/Design/Design_OCL"
(*    "../src/OCL_compiler_aux_proof"*)
(*    "../src/OCL_compiler_aux_text"*)
(*    "../src/OCL_compiler_generator_static"*)
(*    "../src/OCL_compiler_generator_dynamic"*)
(*    "../doc/Employee_AnalysisModel_UMLPart_generated"*)
(*    "../doc/Employee_DesignModel_UMLPart_generated"*)
(*    "../examples/OCL_basic_type_UnlimitedNatural"*)
(*    "../examples/OCL_lib_Gogolla_challenge_integer"*)
  files
    "document/root.tex"
    "document/root.bib"
    "document/conclusion.tex"
    "document/formalization.tex"
    "document/introduction.tex"
