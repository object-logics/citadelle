theory Tree_02_03_deep_SML imports  "../../src/compiler/OCL_compiler_generator_dynamic" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_02_03_generated_SML)
                      (IMPORTS ["../../../src/UML_Main", "../../../src/compiler/OCL_compiler_static"]
                               "../../../src/compiler/OCL_compiler_generator_dynamic")
                      SECTION
                      [ in SML module_name M ]
                      (output_directory "./doc") ]

Class Aazz End
Class Bbyy End
Class Ccxx < Aazz End
Class Ddww < Aazz End
Class Eevv < Ccxx End
Class Ffuu < Ccxx End
Class Ggtt < Ddww End
Class Hhss < Ddww End
Class Iirr < Bbyy End
Class Jjqq < Bbyy End
Class Kkpp < Iirr End
Class Lloo < Iirr End
Class Mmnn < Jjqq End
Class Nnmm < Jjqq End

(* 14 *)

generation_syntax deep flush_all


end
