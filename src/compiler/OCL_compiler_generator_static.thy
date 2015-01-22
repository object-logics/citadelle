(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_generator_static.thy ---
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013-2015 Université Paris-Sud, France
 *               2013-2015 IRT SystemX, France
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

header{* Part ... *}

theory  OCL_compiler_generator_static
imports OCL_compiler_printer
begin

subsection{* General Compiling Process: Test Scenario: Deep (without reflection) *}

definition "Employee_DesignModel_UMLPart =
  [ ocl_class_raw.make \<langle>''Galaxy''\<rangle> [(\<langle>''sound''\<rangle>, OclTy_raw \<langle>''unit''\<rangle>), (\<langle>''moving''\<rangle>, OclTy_raw \<langle>''bool''\<rangle>)] [] [] None
  , ocl_class_raw.make \<langle>''Planet''\<rangle> [(\<langle>''weight''\<rangle>, OclTy_raw \<langle>''nat''\<rangle>)] [] [] (Some \<langle>''Galaxy''\<rangle>)
  , ocl_class_raw.make \<langle>''Person''\<rangle> [(\<langle>''salary''\<rangle>, OclTy_raw \<langle>''int''\<rangle>)] [] [] (Some \<langle>''Planet''\<rangle>) ]"

definition "main = write_file
 (ocl_compiler_config.extend
   (ocl_compiler_config_empty True None (oidInit (Oid 0)) Gen_only_design False
      \<lparr> D_disable_thy_output := False
      , D_file_out_path_dep := Some (\<langle>''Employee_DesignModel_UMLPart_generated''\<rangle>
                                    ,[\<langle>''../src/OCL_main''\<rangle>]
                                    ,\<langle>''../src/compiler/OCL_compiler_generator_dynamic''\<rangle>) \<rparr>)
   ( List_map (OclAstClassRaw Floor1) Employee_DesignModel_UMLPart
     @@ [ OclAstAssociation (ocl_association.make OclAssTy_association
            [ (\<langle>''Person''\<rangle>, OclMult [(Mult_star, None)] Set, None)
            , (\<langle>''Person''\<rangle>, OclMult [(Mult_nat 0, Some (Mult_nat 1))] Set, Some \<langle>''boss''\<rangle>)])
        , OclAstFlushAll OclFlushAll]
   , None))"
(*
apply_code_printing ()
export_code main
  in OCaml module_name M
  (no_signatures)
*)
end
