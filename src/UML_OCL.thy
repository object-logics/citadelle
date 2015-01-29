theory   UML_OCL
imports  "../src/UML_Main"
         "../src/compiler/OCL_compiler_static"
         "../src/compiler/OCL_compiler_generator_dynamic"
begin

generation_syntax [ (*deep
                      (*(generation_semantics [ analysis (*, oid_start 10*) ])*)
                      (THEORY Bank_Model_generated)
                      (IMPORTS ["../src/UML_Main", "../src/compiler/OCL_compiler_static"]
                               "../src/compiler/OCL_compiler_generator_dynamic")
                      SECTION
                      (*SORRY*)
                      [ in SML module_name M (no_signatures) ]
                      (output_directory "../doc")
                  ,*) shallow (*SORRY*) ]
end