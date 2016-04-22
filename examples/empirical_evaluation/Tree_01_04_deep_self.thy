theory Tree_01_04_deep_self imports  "../../src/compiler/Generator_dynamic" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_01_04_generated_self)
                      (IMPORTS ["../../../src/UML_Main", "../../../src/compiler/Static"]
                               "../../../src/compiler/Generator_dynamic")
                      SECTION
                      [ in self  ]
                      (output_directory "./doc") ]

Class Aazz End
Class Bbyy < Aazz End
Class Ccxx < Bbyy End
Class Ddww < Ccxx End

(* 4 *)

generation_syntax deep flush_all


end
