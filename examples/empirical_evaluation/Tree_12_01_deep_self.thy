theory Tree_12_01_deep_self imports  "../../src/compiler/Generator_dynamic" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_12_01_generated_self)
                      (IMPORTS ["../../../src/UML_Main", "../../../src/compiler/Static"]
                               "../../../src/compiler/Generator_dynamic")
                      SECTION
                      [ in self  ]
                      (output_directory "./doc") ]

Class Aazz End
Class Bbyy End
Class Ccxx End
Class Ddww End
Class Eevv End
Class Ffuu End
Class Ggtt End
Class Hhss End
Class Iirr End
Class Jjqq End
Class Kkpp End
Class Lloo End

(* 12 *)

generation_syntax deep flush_all


end
