theory Tree_04_03_shallow imports "../../src/OCL_main" "../../src/OCL_class_diagram_static" "../../src/OCL_class_diagram_generator" begin
generation_syntax [ shallow (generation_semantics [ analysis ]) ]

Class Aa End
Class Bb End
Class Cc End
Class Dd End
Class Ee < Aa End
Class Ff < Aa End
Class Gg < Aa End
Class Hh < Aa End
Class Ii < Bb End
Class Jj < Bb End
Class Kk < Bb End
Class Ll < Bb End
Class Mm < Cc End
Class Nn < Cc End
Class Oo < Cc End
Class Pp < Cc End
Class Qq < Dd End
Class Rr < Dd End
Class Ss < Dd End
Class Tt < Dd End

(* 20 *)

Class.end

end
