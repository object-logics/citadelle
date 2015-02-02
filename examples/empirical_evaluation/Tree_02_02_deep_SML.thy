theory Tree_02_02_deep_SML imports  "../../src/compiler/OCL_compiler_generator_dynamic" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_02_02_generated_SML)
                      (IMPORTS ["../../../src/UML_Main", "../../../src/compiler/OCL_compiler_static"]
                               "../../../src/compiler/OCL_compiler_generator_dynamic")
                      SECTION
                      [ in SML module_name M ]
                      (output_directory "./doc") ]

Class Aazz End
Class Bbyy End
Class Ccxx < Aazz End
Class Ddww < Aazz End
Class Eevv < Bbyy End
Class Ffuu < Bbyy End

(* 6 *)

generation_syntax deep flush_all


end
