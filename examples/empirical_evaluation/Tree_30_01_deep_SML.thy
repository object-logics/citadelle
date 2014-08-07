theory Tree_30_01_deep_SML imports "../../src/OCL_compiler_generator_dynamic" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_30_01_generated_SML)
                      (IMPORTS ["../../../src/OCL_main", "../../../src/OCL_compiler_static"]
                               "../../../src/OCL_compiler_generator_dynamic")
                      SECTION
                      [ in SML module_name M (no_signatures) ]
                      (output_directory "./doc") ]

Class Aazz End
Class Bbyy End
Class Ccxx End
Class Ddww End
Class Eevv End
Class Ffuu End
Class Ggtt End
Class Hhss End
Class Iirr End
Class Jjqq End
Class Kkpp End
Class Lloo End
Class Mmnn End
Class Nnmm End
Class Ooll End
Class Ppkk End
Class Qqjj End
Class Rrii End
Class Sshh End
Class Ttgg End
Class Uuff End
Class Vvee End
Class Wwdd End
Class Xxcc End
Class Yybb End
Class Zzaa End
Class Baba End
Class Bbbb End
Class Bcbc End
Class Bdbd End

(* 30 *)

generation_syntax deep flush_all


end
