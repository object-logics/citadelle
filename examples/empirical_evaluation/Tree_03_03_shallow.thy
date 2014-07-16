theory Tree_03_03_shallow imports "../../src/OCL_main" "../../src/OCL_class_diagram_static" "../../src/OCL_class_diagram_generator" begin
generation_syntax [ shallow (generation_semantics [ analysis ]) ]

Class Aa End
Class Bb End
Class Cc End
Class Dd < Aa End
Class Ee < Aa End
Class Ff < Aa End
Class Gg < Bb End
Class Hh < Bb End
Class Ii < Bb End
Class Jj < Cc End
Class Kk < Cc End
Class Ll < Cc End

(* 12 *)

Class.end

end
