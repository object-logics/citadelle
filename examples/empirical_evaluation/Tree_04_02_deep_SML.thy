theory Tree_04_02_deep_SML imports  "../../src/compiler/OCL_compiler_generator_dynamic" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_04_02_generated_SML)
                      (IMPORTS ["../../../src/UML_Main", "../../../src/compiler/OCL_compiler_static"]
                               "../../../src/compiler/OCL_compiler_generator_dynamic")
                      SECTION
                      [ in SML module_name M ]
                      (output_directory "./doc") ]

Class Aazz End
Class Bbyy End
Class Ccxx End
Class Ddww End
Class Eevv < Aazz End
Class Ffuu < Aazz End
Class Ggtt < Aazz End
Class Hhss < Aazz End
Class Iirr < Bbyy End
Class Jjqq < Bbyy End
Class Kkpp < Bbyy End
Class Lloo < Bbyy End
Class Mmnn < Ccxx End
Class Nnmm < Ccxx End
Class Ooll < Ccxx End
Class Ppkk < Ccxx End
Class Qqjj < Ddww End
Class Rrii < Ddww End
Class Sshh < Ddww End
Class Ttgg < Ddww End

(* 20 *)

generation_syntax deep flush_all


end
