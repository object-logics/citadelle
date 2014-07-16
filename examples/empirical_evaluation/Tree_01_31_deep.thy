theory Tree_01_31_deep imports  "../../src/OCL_class_diagram_generator" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_01_31_generated)
                      (IMPORTS ["../../../src/OCL_main", "../../../src/OCL_class_diagram_static"])
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
Class Uu < Tt End
Class Vv < Uu End
Class Ww < Vv End
Class Xx < Ww End
Class Yy < Xx End
Class Zz < Yy End
Class Baba < Zz End
Class Bbbb < Baba End
Class Bcbc < Bbbb End
Class Bdbd < Bcbc End

(* 30 *)

generation_syntax deep flush_all

end
