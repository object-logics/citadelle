theory Tree_07_03_deep imports  "../../src/OCL_class_diagram_generator" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_07_03_generated)
                      (IMPORTS ["../../../src/OCL_main", "../../../src/OCL_class_diagram_static"]
                               "../../../src/OCL_class_diagram_generator")
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
Class Hh < Aa End
Class Ii < Aa End
Class Jj < Aa End
Class Kk < Aa End
Class Ll < Aa End
Class Mm < Aa End
Class Nn < Aa End
Class Oo < Bb End
Class Pp < Bb End
Class Qq < Bb End
Class Rr < Bb End
Class Ss < Bb End
Class Tt < Bb End
Class Uu < Bb End
Class Vv < Cc End
Class Ww < Cc End
Class Xx < Cc End
Class Yy < Cc End
Class Zz < Cc End
Class Baba < Cc End
Class Bbbb < Cc End
Class Bcbc < Dd End
Class Bdbd < Dd End
Class Bebe < Dd End
Class Bfbf < Dd End
Class Bgbg < Dd End
Class Bhbh < Dd End
Class Bibi < Dd End
Class Bjbj < Ee End
Class Bkbk < Ee End
Class Blbl < Ee End
Class Bmbm < Ee End
Class Bnbn < Ee End
Class Bobo < Ee End
Class Bpbp < Ee End
Class Bqbq < Ff End
Class Brbr < Ff End
Class Bsbs < Ff End
Class Btbt < Ff End
Class Bubu < Ff End
Class Bvbv < Ff End
Class Bwbw < Ff End
Class Bxbx < Gg End
Class Byby < Gg End
Class Bzbz < Gg End
Class Caca < Gg End
Class Cbcb < Gg End
Class Cccc < Gg End
Class Cdcd < Gg End

(* 56 *)

generation_syntax deep flush_all

end
