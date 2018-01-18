theory Tree_01_04_shallow imports "../../src/UML_Main" "../../src/compiler/Static" "../../src/compiler/Generator_dynamic_sequential" begin
generation_syntax [ shallow (generation_semantics [ analysis ]) ]

Class Aazz End
Class Bbyy < Aazz End
Class Ccxx < Bbyy End
Class Ddww < Ccxx End

(* 4 *)

End!

end
