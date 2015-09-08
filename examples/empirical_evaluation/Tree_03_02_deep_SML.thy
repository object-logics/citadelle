theory Tree_03_02_deep_SML imports  "../../src/compiler/Generator_dynamic" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_03_02_generated_SML)
                      (IMPORTS ["../../../src/UML_Main", "../../../src/compiler/Static"]
                               "../../../src/compiler/Generator_dynamic")
                      SECTION
                      [ in SML module_name M ]
                      (output_directory "./doc") ]

Class Aazz End
Class Bbyy End
Class Ccxx End
Class Ddww < Aazz End
Class Eevv < Aazz End
Class Ffuu < Aazz End
Class Ggtt < Bbyy End
Class Hhss < Bbyy End
Class Iirr < Bbyy End
Class Jjqq < Ccxx End
Class Kkpp < Ccxx End
Class Lloo < Ccxx End

(* 12 *)

generation_syntax deep flush_all


end
