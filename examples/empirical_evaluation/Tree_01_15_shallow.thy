theory Tree_01_15_shallow imports "../../src/OCL_main" "../../src/OCL_class_diagram_static" "../../src/OCL_class_diagram_generator" begin
generation_syntax [ shallow (generation_semantics [ analysis ]) ]

Class Aa End
Class Bb < Aa End
Class Cc < Bb End
Class Dd < Cc End
Class Ee < Dd End
Class Ff < Ee End
Class Gg < Ff End
Class Hh < Gg End
Class Ii < Hh End
Class Jj < Ii End
Class Kk < Jj End
Class Ll < Kk End
Class Mm < Ll End
Class Nn < Mm End

(* 14 *)

Class.end

end
