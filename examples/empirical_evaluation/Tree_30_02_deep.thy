theory Tree_30_02_deep imports  "../../src/OCL_class_diagram_generator" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_30_02_generated)
                      (IMPORTS ["../../../src/OCL_main", "../../../src/OCL_class_diagram_static"])
                      SECTION
                      [ in SML module_name M (no_signatures) ]
                      (output_directory "./doc") ]

Class Aa End
Class Bb End
Class Cc End
Class Dd End
Class Ee End
Class Ff End
Class Gg End
Class Hh End
Class Ii End
Class Jj End
Class Kk End
Class Ll End
Class Mm End
Class Nn End
Class Oo End
Class Pp End
Class Qq End
Class Rr End
Class Ss End
Class Tt End
Class Uu End
Class Vv End
Class Ww End
Class Xx End
Class Yy End
Class Zz End
Class Baba End
Class Bbbb End
Class Bcbc End
Class Bdbd End

(* 30 *)

generation_syntax deep flush_all

end
