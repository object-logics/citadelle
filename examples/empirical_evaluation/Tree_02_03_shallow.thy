theory Tree_02_03_shallow imports "../../src/OCL_main" "../../src/OCL_class_diagram_static" "../../src/OCL_class_diagram_generator" begin
generation_syntax [ shallow (generation_semantics [ analysis ]) ]

Class Aa End
Class Bb End
Class Cc < Aa End
Class Dd < Aa End
Class Ee < Bb End
Class Ff < Bb End

(* 6 *)

Class.end

end
