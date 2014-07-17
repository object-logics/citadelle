theory Tree_01_40_deep imports  "../../src/OCL_class_diagram_generator" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_01_40_generated)
                      (IMPORTS ["../../../src/OCL_main", "../../../src/OCL_class_diagram_static"]
                               "../../../src/OCL_class_diagram_generator")
                      SECTION
                      [ in SML module_name M (no_signatures) ]
                      (output_directory "./doc") ]

Class Aazz End
Class Bbyy < Aazz End
Class Ccxx < Bbyy End
Class Ddww < Ccxx End
Class Eevv < Ddww End
Class Ffuu < Eevv End
Class Ggtt < Ffuu End
Class Hhss < Ggtt End
Class Iirr < Hhss End
Class Jjqq < Iirr End
Class Kkpp < Jjqq End
Class Lloo < Kkpp End
Class Mmnn < Lloo End
Class Nnmm < Mmnn End
Class Ooll < Nnmm End
Class Ppkk < Ooll End
Class Qqjj < Ppkk End
Class Rrii < Qqjj End
Class Sshh < Rrii End
Class Ttgg < Sshh End
Class Uuff < Ttgg End
Class Vvee < Uuff End
Class Wwdd < Vvee End
Class Xxcc < Wwdd End
Class Yybb < Xxcc End
Class Zzaa < Yybb End
Class Baba < Zzaa End
Class Bbbb < Baba End
Class Bcbc < Bbbb End
Class Bdbd < Bcbc End
Class Bebe < Bdbd End
Class Bfbf < Bebe End
Class Bgbg < Bfbf End
Class Bhbh < Bgbg End
Class Bibi < Bhbh End
Class Bjbj < Bibi End
Class Bkbk < Bjbj End
Class Blbl < Bkbk End
Class Bmbm < Blbl End

(* 39 *)

generation_syntax deep flush_all

end
