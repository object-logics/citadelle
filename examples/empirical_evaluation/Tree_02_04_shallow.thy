theory Tree_02_04_shallow imports "../../src/OCL_main" "../../src/OCL_class_diagram_static" "../../src/OCL_class_diagram_generator" begin
generation_syntax [ shallow (generation_semantics [ analysis ]) ]

Class Aazz End
Class Bbyy End
Class Ccxx < Aazz End
Class Ddww < Aazz End
Class Eevv < Ccxx End
Class Ffuu < Ccxx End
Class Ggtt < Ddww End
Class Hhss < Ddww End
Class Iirr < Bbyy End
Class Jjqq < Bbyy End
Class Kkpp < Iirr End
Class Lloo < Iirr End
Class Mmnn < Jjqq End
Class Nnmm < Jjqq End

(* 14 *)

Class.end

end
