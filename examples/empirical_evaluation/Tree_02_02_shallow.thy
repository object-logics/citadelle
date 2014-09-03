theory Tree_02_02_shallow imports "../../src/UML_Main" "../../src/compiler/OCL_compiler_static" "../../src/compiler/OCL_compiler_generator_dynamic" begin
generation_syntax [ shallow (generation_semantics [ analysis ]) ]

Class Aazz End
Class Bbyy End
Class Ccxx < Aazz End
Class Ddww < Aazz End
Class Eevv < Bbyy End
Class Ffuu < Bbyy End

(* 6 *)

Class.end

end
