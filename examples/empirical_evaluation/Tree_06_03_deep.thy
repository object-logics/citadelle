theory Tree_06_03_deep imports  "../../src/OCL_class_diagram_generator" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_06_03_generated)
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
Class Gg < Aa End
Class Hh < Aa End
Class Ii < Aa End
Class Jj < Aa End
Class Kk < Aa End
Class Ll < Aa End
Class Mm < Bb End
Class Nn < Bb End
Class Oo < Bb End
Class Pp < Bb End
Class Qq < Bb End
Class Rr < Bb End
Class Ss < Cc End
Class Tt < Cc End
Class Uu < Cc End
Class Vv < Cc End
Class Ww < Cc End
Class Xx < Cc End
Class Yy < Dd End
Class Zz < Dd End
Class Baba < Dd End
Class Bbbb < Dd End
Class Bcbc < Dd End
Class Bdbd < Dd End
Class Bebe < Ee End
Class Bfbf < Ee End
Class Bgbg < Ee End
Class Bhbh < Ee End
Class Bibi < Ee End
Class Bjbj < Ee End
Class Bkbk < Ff End
Class Blbl < Ff End
Class Bmbm < Ff End
Class Bnbn < Ff End
Class Bobo < Ff End
Class Bpbp < Ff End

(* 42 *)

generation_syntax deep flush_all

end
