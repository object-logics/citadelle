theory Tree_03_03_shallow imports "../../src/OCL_main" "../../src/OCL_compiler_static" begin
generation_syntax [ shallow (generation_semantics [ analysis ]) ]

Class Aazz End
Class Bbyy End
Class Ccxx End
Class Ddww < Aazz End
Class Eevv < Aazz End
Class Ffuu < Aazz End
Class Ggtt < Ddww End
Class Hhss < Ddww End
Class Iirr < Ddww End
Class Jjqq < Eevv End
Class Kkpp < Eevv End
Class Lloo < Eevv End
Class Mmnn < Ffuu End
Class Nnmm < Ffuu End
Class Ooll < Ffuu End
Class Ppkk < Bbyy End
Class Qqjj < Bbyy End
Class Rrii < Bbyy End
Class Sshh < Ppkk End
Class Ttgg < Ppkk End
Class Uuff < Ppkk End
Class Vvee < Qqjj End
Class Wwdd < Qqjj End
Class Xxcc < Qqjj End
Class Yybb < Rrii End
Class Zzaa < Rrii End
Class Baba < Rrii End
Class Bbbb < Ccxx End
Class Bcbc < Ccxx End
Class Bdbd < Ccxx End
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

Class.end

end
