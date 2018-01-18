theory Tree_01_06_shallow imports "../../src/UML_Main" "../../src/compiler/Static" "../../src/compiler/Generator_dynamic_sequential" begin
generation_syntax [ shallow (generation_semantics [ analysis ]) ]

Class Aazz End
Class Bbyy < Aazz End
Class Ccxx < Bbyy End
Class Ddww < Ccxx End
Class Eevv < Ddww End
Class Ffuu < Eevv End

(* 6 *)

End!

end
