theory Tree_01_21_deep imports  "../../src/OCL_class_diagram_generator" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_01_21_generated)
                      (IMPORTS ["../../../src/OCL_main", "../../../src/OCL_class_diagram_static"]
                               "../../../src/OCL_class_diagram_generator")
                      SECTION
                      [ in SML module_name M (no_signatures) ]
                      (output_directory "./doc") ]

Class Aa End
Class Bb < Aa End
Class Cc < Bb End
Class Dd < Cc End
Class Ee < Dd End
Class Ff < Ee End
Class Gg < Ff End
Class Hh < Gg End
Class Ii < Hh End
Class Jj < Ii End
Class Kk < Jj End
Class Ll < Kk End
Class Mm < Ll End
Class Nn < Mm End
Class Oo < Nn End
Class Pp < Oo End
Class Qq < Pp End
Class Rr < Qq End
Class Ss < Rr End
Class Tt < Ss End

(* 20 *)

generation_syntax deep flush_all

end
