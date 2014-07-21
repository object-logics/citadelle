theory Tree_02_03_deep imports  "../../src/OCL_class_diagram_generator" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_02_03_generated)
                      (IMPORTS ["../../../src/OCL_main", "../../../src/OCL_class_diagram_static"]
                               "../../../src/OCL_class_diagram_generator")
                      SECTION
                      [ in SML module_name M (no_signatures) ]
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
