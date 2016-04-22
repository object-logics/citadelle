theory Tree_02_04_deep_self imports  "../../src/compiler/Generator_dynamic" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_02_04_generated_self)
                      (IMPORTS ["../../../src/UML_Main", "../../../src/compiler/Static"]
                               "../../../src/compiler/Generator_dynamic")
                      SECTION
                      [ in self  ]
                      (output_directory "./doc") ]

Class Aazz End
Class Bbyy End
Class Ccxx < Aazz End
Class Ddww < Aazz End
Class Eevv < Ccxx End
Class Ffuu < Ccxx End
Class Ggtt < Eevv End
Class Hhss < Eevv End
Class Iirr < Ffuu End
Class Jjqq < Ffuu End
Class Kkpp < Ddww End
Class Lloo < Ddww End
Class Mmnn < Kkpp End
Class Nnmm < Kkpp End
Class Ooll < Lloo End
Class Ppkk < Lloo End
Class Qqjj < Bbyy End
Class Rrii < Bbyy End
Class Sshh < Qqjj End
Class Ttgg < Qqjj End
Class Uuff < Sshh End
Class Vvee < Sshh End
Class Wwdd < Ttgg End
Class Xxcc < Ttgg End
Class Yybb < Rrii End
Class Zzaa < Rrii End
Class Baba < Yybb End
Class Bbbb < Yybb End
Class Bcbc < Zzaa End
Class Bdbd < Zzaa End

(* 30 *)

generation_syntax deep flush_all


end
