theory Tree_05_02_deep imports  "../../src/OCL_class_diagram_generator" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_05_02_generated)
                      (IMPORTS ["../../../src/OCL_main", "../../../src/OCL_class_diagram_static"])
                      SECTION
                      [ in SML module_name M (no_signatures) ]
                      (output_directory "./doc") ]

Class Aa End
Class Bb End
Class Cc End
Class Dd End
Class Ee End

(* 5 *)

generation_syntax deep flush_all

end
