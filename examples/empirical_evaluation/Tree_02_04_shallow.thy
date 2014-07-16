theory Tree_02_04_shallow imports "../../src/OCL_main" "../../src/OCL_class_diagram_static" "../../src/OCL_class_diagram_generator" begin
generation_syntax [ shallow (generation_semantics [ analysis ]) ]

Class Aa End
Class Bb End
Class Cc < Aa End
Class Dd < Aa End
Class Ee < Cc End
Class Ff < Cc End
Class Gg < Dd End
Class Hh < Dd End
Class Ii < Bb End
Class Jj < Bb End
Class Kk < Ii End
Class Ll < Ii End
Class Mm < Jj End
Class Nn < Jj End

(* 14 *)

Class.end

end
