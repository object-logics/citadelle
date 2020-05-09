(******************************************************************************
 * http://www.brucker.ch/projects/hol-testgen/
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2011-2018 Université Paris-Saclay, Univ. Paris-Sud, France
 *               2013-2017 IRT SystemX, France
 *               2011-2015 Achim D. Brucker, Germany
 *               2016-2018 The University of Sheffield, UK
 *               2016-2017 Nanyang Technological University, Singapore
 *               2017-2018 Virginia Tech, USA
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

session OCL in "src/uml_main" = HOL +
  description \<open>Featherweight OCL\<close>
  options [document=pdf,document_output=document_generated,
           document_variants="annex-a=annexa,-theory,-afp,-noexample,-proof,-ML:document=afp,-annexa,-noexample:outline=-annexa,-noexample,afp,/proof,/ML",
           show_question_marks = false]
  theories
    UML_Main
    "../../examples/Employee_Model/Analysis/Analysis_OCL"
    "../../examples/Employee_Model/Design/Design_OCL"
  document_files
    "conclusion.tex"
    "figures/AbstractSimpleChair.pdf"
    "figures/jedit.png"
    (*"figures/logo_focl.pdf"*)
    "figures/pdf.png"
    "figures/person.png"
    "figures/pre-post.pdf"
    "fixme.sty"
    "hol-ocl-isar.sty"
    "introduction.tex"
    "lstisar.sty"
    "omg.sty"
    "prooftree.sty"
    "root.bib"
    "root.tex"
    "FOCL_Syntax.tex"

session FOCL in "src/uml_ocl" = "HOL-Library" +
  description \<open>Citadelle (Sequential)\<close>
  options [document=pdf,document_output=document_generated,
           document_variants="document=noexample,-afp,-annexa",
           show_question_marks = false]
  sessions
    OCL
    Isabelle_Meta_Model
  theories
    UML_OCL
  document_files
    "conclusion.tex"
    "figures/AbstractSimpleChair.pdf"
    "figures/jedit.png"
    (*"figures/logo_focl.pdf"*)
    "figures/pdf.png"
    "figures/person.png"
    "figures/pre-post.pdf"
    "fixme.sty"
    "hol-ocl-isar.sty"
    "introduction.tex"
    "lstisar.sty"
    "omg.sty"
    "prooftree.sty"
    "root.bib"
    "root.tex"
    "FOCL_Syntax.tex"

session Citadelle in "src/compiler_citadelle" = FOCL +
  description \<open>Citadelle (Concurrent)\<close>
  theories
    Generator_dynamic_concurrent
    Generator_dynamic_export_testing

session Citadelle_C_init in "src/compiler_citadelle_c/init" = Citadelle +
  theories
    C_Model_init

session "Citadelle_C_deep-dirty" in "src/compiler_citadelle_c/doc" = Citadelle_C_init +
  options [quick_and_dirty]
  theories
    Meta_C_generated

session "Citadelle_C_shallow-dirty" in "src/compiler_citadelle_c/core" = Citadelle_C_init +
  options [quick_and_dirty]
  theories
    C_Model_core

session "Citadelle_C_model-dirty" in "src/compiler_citadelle_c/ml" = "Citadelle_C_shallow-dirty" +
  options [quick_and_dirty]
  theories
    C_Model_ml

(******************************************************)

session "Max-dirty" = "HOL-Library" (* Note: replacing with FOCL will fail! *) +
  options [quick_and_dirty]
  sessions
    OCL
    FOCL
  theories
    "src/basic_types_extra/UML_UnlimitedNatural"

    "examples/empirical_evaluation/Class_model"

    "src/compiler_misc/Generator_static"
    "src/compiler_misc/meta/Printer_init"

    "doc/Employee_AnalysisModel_UMLPart_generated"
    "doc/Employee_DesignModel_UMLPart_generated"

    "examples/uml_ocl/Bank_Model"
    "examples/uml_ocl/Bank_Test_Model"
    "examples/uml_ocl/Clocks_Lib_Model"
    (*"examples/Employee_Model/Analysis_generation/Analysis_deep"*)
    "examples/Employee_Model/Analysis_generation/Analysis_shallow"
    (*"examples/Employee_Model/Design_generation/Design_deep"*)
    "examples/Employee_Model/Design_generation/Design_shallow"
    "examples/uml_ocl/Flight_Model"
    "examples/uml_ocl/AbstractList"
    "examples/uml_ocl/LinkedList"
    (*"examples/uml_ocl/ListRefinement"*)
    "examples/archive/uml_ocl/Flight_Model_compact"
    "examples/archive/uml_ocl/Simple_Model"
    "examples/archive/uml_ocl/Toy_deep"
    "examples/archive/uml_ocl/Toy_shallow"

    "src/compiler_misc/Aux_proof"
    "src/compiler_misc/Aux_tactic"
    "src/compiler_misc/Aux_text"
    "src/compiler_misc/Rail"

    "examples/archive/uml_ocl/OCL_core_experiments"
    "examples/archive/uml_ocl/OCL_lib_Gogolla_challenge_naive"
    "examples/archive/uml_ocl/OCL_lib_Gogolla_challenge_integer"
