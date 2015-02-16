(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013-2015 Université Paris-Sud, France
 *               2013-2015 IRT SystemX, France
 *               2013-2015 Achim D. Brucker, Germany
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
           document_variants="annex-a=annexa,-theory,-afp,-proof,-ML:document=afp,-annexa:outline=-annexa,afp,/proof,/ML",
           show_question_marks = false]
  theories
    "../src/UML_Main"
    "../examples/Employee_Model/Analysis/Analysis_OCL"
    "../examples/Employee_Model/Design/Design_OCL"
  files
    "document/root.tex"
    "document/root.bib"


session "OCL" in "src" = HOL +
  description {* Featherweight OCL *}
  options [document=pdf,document_output=document_generated,
           document_variants="annex-a=annexa,-theory,-afp,-proof,-ML:document=afp,-annexa:outline=-annexa,afp,/proof,/ML",
           show_question_marks = false]
  theories
    "../examples/Employee_Model/Design/Design_OCL"
  theories
    "../src/UML_Main"
    "../examples/Employee_Model/Analysis/Analysis_OCL"
  files
    "document/root.tex"
    "document/root.bib"


(******************************************************)

session "OCL-all-dirty" in "src" = HOL +
  description {* Featherweight OCL (Long and Dirty) *}
  options [quick_and_dirty,document=pdf,document_output=document_generated,
           document_variants="document=afp,-annexa",
           show_question_marks = false]
  theories
    "../src/UML_Main"
    "../src/basic_types/UML_UnlimitedNatural"

    "../examples/empirical_evaluation/Class_model"

    "../examples/Employee_Model/Analysis/Analysis_OCL"
    "../examples/Employee_Model/Design/Design_OCL"
    "../doc/Employee_AnalysisModel_UMLPart_generated"
    "../doc/Employee_DesignModel_UMLPart_generated"

    "../examples/Bank_Model"
    (*"../examples/Employee_Model/Analysis_deep"*)
    "../examples/Employee_Model/Analysis_shallow"
    (*"../examples/Employee_Model/Design_deep"*)
    "../examples/Employee_Model/Design_shallow"
    "../examples/Flight_Model"
    "../examples/LinkedList"
    "../examples/archive/Simple_Model"

    "../src/compiler/OCL_compiler_aux_proof"
    "../src/compiler/OCL_compiler_aux_tactic"
    "../src/compiler/OCL_compiler_aux_text"
    "../src/compiler/OCL_compiler_rail"

    "../examples/archive/OCL_lib_Gogolla_challenge_integer"
  files
    "document/root.tex"
    "document/root.bib"


(******************************************************)

session "FOCL" in "src" = HOL +
  description {* Featherweight OCL (Compiler) *}
  options [document=pdf,document_output=document_generated,
           document_variants="document=afp,-annexa",
           show_question_marks = false]
  theories
    UML_OCL
  files
    "document/root.tex"
    "document/root.bib"

session "FOCL-dirty" in "src" = HOL +
  description {* Featherweight OCL (Compiler) *}
  options [quick_and_dirty,document=pdf,document_output=document_generated,
           document_variants="document=afp,-annexa",
           show_question_marks = false]
  theories
    UML_OCL
  files
    "document/root.tex"
    "document/root.bib"
