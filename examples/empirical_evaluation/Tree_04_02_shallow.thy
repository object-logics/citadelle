theory Tree_04_02_shallow imports "../../src/OCL_main" "../../src/OCL_compiler_static" begin
generation_syntax [ shallow (generation_semantics [ analysis ]) ]

Class Aazz End
Class Bbyy End
Class Ccxx End
Class Ddww End
Class Eevv < Aazz End
Class Ffuu < Aazz End
Class Ggtt < Aazz End
Class Hhss < Aazz End
Class Iirr < Bbyy End
Class Jjqq < Bbyy End
Class Kkpp < Bbyy End
Class Lloo < Bbyy End
Class Mmnn < Ccxx End
Class Nnmm < Ccxx End
Class Ooll < Ccxx End
Class Ppkk < Ccxx End
Class Qqjj < Ddww End
Class Rrii < Ddww End
Class Sshh < Ddww End
Class Ttgg < Ddww End

(* 20 *)

Class.end

end
