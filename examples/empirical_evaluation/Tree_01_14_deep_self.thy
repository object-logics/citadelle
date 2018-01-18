theory Tree_01_14_deep_self imports  "../../src/compiler/Generator_dynamic_sequential" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_01_14_generated_self)
                      (IMPORTS ["../../../src/UML_Main", "../../../src/compiler/Static"]
                               "../../../src/compiler/Generator_dynamic_sequential")
                      SECTION
                      [ in self  ]
                      (output_directory "./doc") ]

Class Aazz End
Class Bbyy < Aazz End
Class Ccxx < Bbyy End
Class Ddww < Ccxx End
Class Eevv < Ddww End
Class Ffuu < Eevv End
Class Ggtt < Ffuu End
Class Hhss < Ggtt End
Class Iirr < Hhss End
Class Jjqq < Iirr End
Class Kkpp < Jjqq End
Class Lloo < Kkpp End
Class Mmnn < Lloo End
Class Nnmm < Mmnn End

(* 14 *)

generation_syntax deep flush_all


end
