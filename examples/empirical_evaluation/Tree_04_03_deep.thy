theory Tree_04_03_deep imports  "../../src/OCL_class_diagram_generator" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_04_03_generated)
                      (IMPORTS ["../../../src/OCL_main", "../../../src/OCL_class_diagram_static"]
                               "../../../src/OCL_class_diagram_generator")
                      SECTION
                      [ in SML module_name M (no_signatures) ]
                      (output_directory "./doc") ]

Class Aa End
Class Bb End
Class Cc End
Class Dd End
Class Ee < Aa End
Class Ff < Aa End
Class Gg < Aa End
Class Hh < Aa End
Class Ii < Bb End
Class Jj < Bb End
Class Kk < Bb End
Class Ll < Bb End
Class Mm < Cc End
Class Nn < Cc End
Class Oo < Cc End
Class Pp < Cc End
Class Qq < Dd End
Class Rr < Dd End
Class Ss < Dd End
Class Tt < Dd End

(* 20 *)

generation_syntax deep flush_all

end
