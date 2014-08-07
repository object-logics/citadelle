theory Tree_01_03_shallow imports "../../src/OCL_main" "../../src/OCL_compiler_static" begin
generation_syntax [ shallow (generation_semantics [ analysis ]) ]

Class Aazz End
Class Bbyy < Aazz End
Class Ccxx < Bbyy End

(* 3 *)

Class.end

end
