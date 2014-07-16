theory Tree_05_03_deep imports  "../../src/OCL_class_diagram_generator" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_05_03_generated)
                      (IMPORTS ["../../../src/OCL_main", "../../../src/OCL_class_diagram_static"])
                      SECTION
                      [ in SML module_name M (no_signatures) ]
                      (output_directory "./doc") ]

Class Aa End
Class Bb End
Class Cc End
Class Dd End
Class Ee End
Class Ff < Aa End
Class Gg < Aa End
Class Hh < Aa End
Class Ii < Aa End
Class Jj < Aa End
Class Kk < Bb End
Class Ll < Bb End
Class Mm < Bb End
Class Nn < Bb End
Class Oo < Bb End
Class Pp < Cc End
Class Qq < Cc End
Class Rr < Cc End
Class Ss < Cc End
Class Tt < Cc End
Class Uu < Dd End
Class Vv < Dd End
Class Ww < Dd End
Class Xx < Dd End
Class Yy < Dd End
Class Zz < Ee End
Class Baba < Ee End
Class Bbbb < Ee End
Class Bcbc < Ee End
Class Bdbd < Ee End

(* 30 *)

generation_syntax deep flush_all

end
