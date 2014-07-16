theory Tree_01_04_shallow imports "../../src/OCL_main" "../../src/OCL_class_diagram_static" "../../src/OCL_class_diagram_generator" begin
generation_syntax [ shallow (generation_semantics [ analysis ]) ]

Class Aa End
Class Bb < Aa End
Class Cc < Bb End

(* 3 *)

Class.end

end
