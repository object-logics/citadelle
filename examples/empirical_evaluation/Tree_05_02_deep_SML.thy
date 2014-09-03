theory Tree_05_02_deep_SML imports  "../../src/compiler/OCL_compiler_generator_dynamic" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_05_02_generated_SML)
                      (IMPORTS ["../../../src/UML_Main", "../../../src/compiler/OCL_compiler_static"]
                               "../../../src/compiler/OCL_compiler_generator_dynamic")
                      SECTION
                      [ in SML module_name M (no_signatures) ]
                      (output_directory "./doc") ]

Class Aazz End
Class Bbyy End
Class Ccxx End
Class Ddww End
Class Eevv End
Class Ffuu < Aazz End
Class Ggtt < Aazz End
Class Hhss < Aazz End
Class Iirr < Aazz End
Class Jjqq < Aazz End
Class Kkpp < Bbyy End
Class Lloo < Bbyy End
Class Mmnn < Bbyy End
Class Nnmm < Bbyy End
Class Ooll < Bbyy End
Class Ppkk < Ccxx End
Class Qqjj < Ccxx End
Class Rrii < Ccxx End
Class Sshh < Ccxx End
Class Ttgg < Ccxx End
Class Uuff < Ddww End
Class Vvee < Ddww End
Class Wwdd < Ddww End
Class Xxcc < Ddww End
Class Yybb < Ddww End
Class Zzaa < Eevv End
Class Baba < Eevv End
Class Bbbb < Eevv End
Class Bcbc < Eevv End
Class Bdbd < Eevv End

(* 30 *)

generation_syntax deep flush_all


end
