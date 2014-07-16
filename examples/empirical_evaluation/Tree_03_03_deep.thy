theory Tree_03_03_deep imports  "../../src/OCL_class_diagram_generator" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_03_03_generated)
                      (IMPORTS ["../../../src/OCL_main", "../../../src/OCL_class_diagram_static"]
                               "../../../src/OCL_class_diagram_generator")
                      SECTION
                      [ in SML module_name M (no_signatures) ]
                      (output_directory "./doc") ]

Class Aa End
Class Bb End
Class Cc End
Class Dd < Aa End
Class Ee < Aa End
Class Ff < Aa End
Class Gg < Bb End
Class Hh < Bb End
Class Ii < Bb End
Class Jj < Cc End
Class Kk < Cc End
Class Ll < Cc End

(* 12 *)

generation_syntax deep flush_all

end
