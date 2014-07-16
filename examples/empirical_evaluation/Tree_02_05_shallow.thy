theory Tree_02_05_shallow imports "../../src/OCL_main" "../../src/OCL_class_diagram_static" "../../src/OCL_class_diagram_generator" begin
generation_syntax [ shallow (generation_semantics [ analysis ]) ]

Class Aa End
Class Bb End
Class Cc < Aa End
Class Dd < Aa End
Class Ee < Cc End
Class Ff < Cc End
Class Gg < Ee End
Class Hh < Ee End
Class Ii < Ff End
Class Jj < Ff End
Class Kk < Dd End
Class Ll < Dd End
Class Mm < Kk End
Class Nn < Kk End
Class Oo < Ll End
Class Pp < Ll End
Class Qq < Bb End
Class Rr < Bb End
Class Ss < Qq End
Class Tt < Qq End
Class Uu < Ss End
Class Vv < Ss End
Class Ww < Tt End
Class Xx < Tt End
Class Yy < Rr End
Class Zz < Rr End
Class Baba < Yy End
Class Bbbb < Yy End
Class Bcbc < Zz End
Class Bdbd < Zz End

(* 30 *)

Class.end

end
