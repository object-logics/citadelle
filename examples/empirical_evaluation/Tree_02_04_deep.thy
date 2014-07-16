theory Tree_02_04_deep imports  "../../src/OCL_class_diagram_generator" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_02_04_generated)
                      (IMPORTS ["../../../src/OCL_main", "../../../src/OCL_class_diagram_static"]
                               "../../../src/OCL_class_diagram_generator")
                      SECTION
                      [ in SML module_name M (no_signatures) ]
                      (output_directory "./doc") ]

Class Aa End
Class Bb End
Class Cc < Aa End
Class Dd < Aa End
Class Ee < Cc End
Class Ff < Cc End
Class Gg < Dd End
Class Hh < Dd End
Class Ii < Bb End
Class Jj < Bb End
Class Kk < Ii End
Class Ll < Ii End
Class Mm < Jj End
Class Nn < Jj End

(* 14 *)

generation_syntax deep flush_all

end
