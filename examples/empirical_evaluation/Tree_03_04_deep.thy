theory Tree_03_04_deep imports  "../../src/OCL_class_diagram_generator" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_03_04_generated)
                      (IMPORTS ["../../../src/OCL_main", "../../../src/OCL_class_diagram_static"])
                      SECTION
                      [ in SML module_name M (no_signatures) ]
                      (output_directory "./doc") ]

Class Aa End
Class Bb End
Class Cc End
Class Dd < Aa End
Class Ee < Aa End
Class Ff < Aa End
Class Gg < Dd End
Class Hh < Dd End
Class Ii < Dd End
Class Jj < Ee End
Class Kk < Ee End
Class Ll < Ee End
Class Mm < Ff End
Class Nn < Ff End
Class Oo < Ff End
Class Pp < Bb End
Class Qq < Bb End
Class Rr < Bb End
Class Ss < Pp End
Class Tt < Pp End
Class Uu < Pp End
Class Vv < Qq End
Class Ww < Qq End
Class Xx < Qq End
Class Yy < Rr End
Class Zz < Rr End
Class Baba < Rr End
Class Bbbb < Cc End
Class Bcbc < Cc End
Class Bdbd < Cc End
Class Bebe < Bbbb End
Class Bfbf < Bbbb End
Class Bgbg < Bbbb End
Class Bhbh < Bcbc End
Class Bibi < Bcbc End
Class Bjbj < Bcbc End
Class Bkbk < Bdbd End
Class Blbl < Bdbd End
Class Bmbm < Bdbd End

(* 39 *)

generation_syntax deep flush_all

end
