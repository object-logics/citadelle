lexicon: "!" "!!" "#" "%" "&" "&&&" "(" "()" "(|" ")" "*" "+" "++" "," "-" "-->"
  "-`" "." ".." "..." "..<" "..}" "/" "//" "0" "1" ":" "::" ":=" ":>" ";" "<" "<*>"
  "<*lex*>" "<*mlex*>" "<+>" "<-" "<->" "<.." "<..<" "<..}" "<=" "=" "==" "==>"
  "=>" "=simp=>" ">" ">=" "?" "?!" "@" "ALL" "CHR" "CONST" "CSUM" "EX" "EX!"
  "GREATEST" "INF" "INFM" "INT" "Int" "LEAST" "LIM" "MOST" "O" "OFCLASS" "OO"
  "PROD" "PROP" "SIGMA" "SOME" "SORT_CONSTRAINT" "SUM" "SUP" "TERM" "THE" "TYPE"
  "TYPEREP" "UN" "Un" "WRT" "XCONST" "[" "[↦]" "[]" "[|" "[|->]" "⋀" "∷" "⋂" "⟹"
  "∏" "⇒" "⨅⇩f⇩i⇩n" "⨆⇩f⇩i⇩n" "∑" "⋃" "⇘" "⇙" "⇧*" "⇧*⇧*" "⇧+" "⇧+⇧+" "⇧2" "⇧="
  "⇧=⇧=" "∧" "¦" "∘" "∘⇩m" "…" "≡" "∃" "∃!" "∃⇩F" "∃⇩∞" "∀" "∀⇩F" "∀⇩∞" "≥" "∈"
  "ı" "ℤ" "∩" "¯" "¯¯" "λ" "⟦" "≤" "←" "⟷" "⟶" "⦇" "↦" "ℕ" "¬" "≠" "∉" "∨"
  "⟧" "⇀" "⦈" "ϵ" "⋄" "⊂" "⊆" "⊆⇩m" "⊃" "⊇" "×" "∪" "]" "^" "^*" "^**" "^+" "^++"
  "^--1" "^-1" "^=" "^==" "^^" "_" "`" "``" "case" "chain⇩⊆" "div" "dvd" "else"
  "if" "in" "initial_segment_of" "let" "mod" "o" "o_m" "of" "op" "respects"
  "respects2" "then" "{" "{.." "{..<" "{}" "|" "|)" "|->" "|]" "|`" "}" "~" "~:"
  "~=" "~=>"
prods:
  Fun.updbind = any[0] ":=" any[0] => "_updbind" (1000)
  Fun.updbinds = Fun.updbind[0] "," Fun.updbinds[0] => "_updbinds" (1000)
  Fun.updbinds = Fun.updbind[-1] (-1)
  HOL.case_syn = any[0] "⇒" any[0] => "_case1" (10)
  HOL.case_syn = any[0] "=>" any[0] => "_case1" (10)
  HOL.cases_syn = HOL.case_syn[0] "|" HOL.cases_syn[0] => "_case2" (1000)
  HOL.cases_syn = HOL.case_syn[-1] (-1)
  HOL.letbind = pttrn[0] "=" any[0] => "_bind" (10)
  HOL.letbinds = HOL.letbind[0] ";" HOL.letbinds[0] => "_binds" (1000)
  HOL.letbinds = HOL.letbind[-1] (-1)
  List.lc_qual = logic[0] => "_lc_test" (1000)
  List.lc_qual = any[0] "←" logic[0] => "_lc_gen" (1000)
  List.lc_qual = any[0] "<-" logic[0] => "_lc_gen" (1000)
  List.lc_quals = "," List.lc_qual[0] List.lc_quals[0] => "_lc_quals" (1000)
  List.lc_quals = "]" => "_lc_end" (1000)
  List.lupdbind = any[0] ":=" any[0] => "_lupdbind" (1000)
  List.lupdbinds = List.lupdbind[0] "," List.lupdbinds[0] => "_lupdbinds" (1000)
  List.lupdbinds = List.lupdbind[-1] (-1)
  Map.maplet = any[0] "↦" any[0] => "_maplet" (1000)
  Map.maplet = any[0] "[↦]" any[0] => "_maplets" (1000)
  Map.maplet = any[0] "|->" any[0] => "_maplet" (1000)
  Map.maplet = any[0] "[|->]" any[0] => "_maplets" (1000)
  Map.maplets = Map.maplet[0] "," Map.maplets[0] => "_Maplets" (1000)
  Map.maplets = Map.maplet[-1] (-1)
  Product_Type.patterns = pttrn[0] "," Product_Type.patterns[0] => "_patterns"
    (1000)
  Product_Type.patterns = pttrn[-1] (-1)
  Product_Type.tuple_args = any[0] => "_tuple_arg" (1000)
  Product_Type.tuple_args = any[0] "," Product_Type.tuple_args[0] => "_tuple_args"
    (1000)
  Record.field = Record.ident[0] "=" any[0] => "_field" (1000)
  Record.field_type = Record.ident[0] "::" type[0] => "_field_type" (1000)
  Record.field_types = Record.field_type[0] "," Record.field_types[0]
    => "_field_types" (1000)
  Record.field_types = Record.field_type[-1] (-1)
  Record.field_update = Record.ident[0] ":=" any[0] => "_field_update" (1000)
  Record.field_updates = Record.field_update[0] "," Record.field_updates[0]
    => "_field_updates" (1000)
  Record.field_updates = Record.field_update[-1] (-1)
  Record.fields = Record.field[0] "," Record.fields[0] => "_fields" (1000)
  Record.fields = Record.field[-1] (-1)
  Record.ident = longid => "_constify" (1000)
  Record.ident = id => "_constify" (1000)
  any = prop'[-1] (-1)
  any = logic[-1] (-1)
  aprop = "_" => "\<^const>Pure.dummy_pattern" (1000)
  aprop = "XCONST" longid_position[0] => "_context_xconst" (1000)
  aprop = "XCONST" id_position[0] => "_context_xconst" (1000)
  aprop = "CONST" longid_position[0] => "_context_const" (1000)
  aprop = "CONST" id_position[0] => "_context_const" (1000)
  aprop = "..." => "_DDDOT" (1000)
  aprop = "(" aprop[0] ")" (1000)
  aprop = "…" => "_DDDOT" (1000)
  aprop = logic[1000] cargs[1000] => "_applC" (999)
  aprop = var_position[-1] (-1)
  aprop = longid_position[-1] (-1)
  aprop = id_position[-1] (-1)
  args = any[0] "," args[0] => "_args" (1000)
  args = any[-1] (-1)
  asms = prop[0] ";" asms[0] => "_asms" (1000)
  asms = prop[0] => "_asm" (1000)
  cargs = any[1000] cargs[1000] => "_cargs" (1000)
  cargs = any[-1] (-1)
  cartouche_position = cartouche => "_position" (1000)
  class_name = longid => "_class_name" (1000)
  class_name = id => "_class_name" (1000)
  classes = class_name[0] "," classes[0] => "_classes" (1000)
  classes = class_name[-1] (-1)
  float_const = float_position[0] => "_constify" (1000)
  float_position = float_token => "_position" (1000)
  id_position = id => "_position" (1000)
  idt = "(" idt[0] ")" (1000)
  idt = "_" "::" type[0] => "_idtypdummy" (0)
  idt = "_" => "_idtdummy" (1000)
  idt = "_" "∷" type[0] => "_idtypdummy" (0)
  idt = id_position[0] "::" type[0] => "_idtyp" (0)
  idt = id_position[0] "∷" type[0] => "_idtyp" (0)
  idt = id_position[-1] (-1)
  idts = idt[1] idts[0] => "_idts" (0)
  idts = idt[-1] (-1)
  index = "ı" => "_indexvar" (1000)
  index = => "_indexdefault" (1000)
  index = "⇘" logic[0] "⇙" => "_index" (1000)
  logic = "op" "&&&" => "\<^const>Pure.conjunction" (1000)
  logic = "op" "==>" => "\<^const>Pure.imp" (1000)
  logic = "op" "⟹" => "\<^const>Pure.imp" (1000)
  logic = "op" "≡" => "\<^const>Pure.eq" (1000)
  logic = "op" "==" => "\<^const>Pure.eq" (1000)
  logic = "op" "-->" => "\<^const>HOL.implies" (1000)
  logic = "op" "=" => "\<^const>HOL.eq" (1000)
  logic = "op" "|" => "\<^const>HOL.disj" (1000)
  logic = "op" "&" => "\<^const>HOL.conj" (1000)
  logic = "op" "~=" => "\<^const>HOL.not_equal" (1000)
  logic = "op" "≠" => "\<^const>HOL.not_equal" (1000)
  logic = "op" "⟶" => "\<^const>HOL.implies" (1000)
  logic = "op" "∨" => "\<^const>HOL.disj" (1000)
  logic = "op" "∧" => "\<^const>HOL.conj" (1000)
  logic = "op" "<->" => "\<^const>HOL.iff" (1000)
  logic = "op" "⟷" => "\<^const>HOL.iff" (1000)
  logic = "op" "=simp=>" => "\<^const>HOL.simp_implies" (1000)
  logic = "op" "<" => "\<^const>Orderings.ord_class.less" (1000)
  logic = "op" "<=" => "\<^const>Orderings.ord_class.less_eq" (1000)
  logic = "op" "≤" => "\<^const>Orderings.ord_class.less_eq" (1000)
  logic = "op" ">=" => "\<^const>Orderings.ord_class.greater_eq" (1000)
  logic = "op" "≥" => "\<^const>Orderings.ord_class.greater_eq" (1000)
  logic = "op" ">" => "\<^const>Orderings.ord_class.greater" (1000)
  logic = "op" "+" => "\<^const>Groups.plus_class.plus" (1000)
  logic = "op" "-" => "\<^const>Groups.minus_class.minus" (1000)
  logic = "op" "*" => "\<^const>Groups.times_class.times" (1000)
  logic = "op" ":" => "\<^const>Set.member" (1000)
  logic = "op" "~:" => "\<^const>Set.not_member" (1000)
  logic = "op" "∉" => "\<^const>Set.not_member" (1000)
  logic = "op" "∈" => "\<^const>Set.member" (1000)
  logic = "op" "⊆" => "\<^const>Set.subset_eq" (1000)
  logic = "op" "⊂" => "\<^const>Set.subset" (1000)
  logic = "op" "⊇" => "\<^const>Set.supset_eq" (1000)
  logic = "op" "⊃" => "\<^const>Set.supset" (1000)
  logic = "op" "Int" => "\<^const>Set.inter" (1000)
  logic = "op" "∩" => "\<^const>Set.inter" (1000)
  logic = "op" "Un" => "\<^const>Set.union" (1000)
  logic = "op" "∪" => "\<^const>Set.union" (1000)
  logic = "op" "`" => "\<^const>Set.image" (1000)
  logic = "op" "-`" => "\<^const>Set.vimage" (1000)
  logic = "op" "o" => "\<^const>Fun.comp" (1000)
  logic = "op" "∘" => "\<^const>Fun.comp" (1000)
  logic = "op" "<*>" => "\<^const>Product_Type.Times" (1000)
  logic = "op" "×" => "\<^const>Product_Type.Times" (1000)
  logic = "op" "<+>" => "\<^const>Sum_Type.Plus" (1000)
  logic = "op" "dvd" => "\<^const>Rings.dvd_class.dvd" (1000)
  logic = "op" "/" => "\<^const>Fields.inverse_class.divide" (1000)
  logic = "op" "^^" => "\<^const>Nat.compower" (1000)
  logic = "op" "O" => "\<^const>Relation.relcomp" (1000)
  logic = "op" "OO" => "\<^const>Relation.relcompp" (1000)
  logic = "op" "``" => "\<^const>Relation.Image" (1000)
  logic = "op" "<*lex*>" => "\<^const>Wellfounded.lex_prod" (1000)
  logic = "op" "<*mlex*>" => "\<^const>Wellfounded.mlex_prod" (1000)
  logic = "op" "initial_segment_of" => "\<^const>Zorn.initialSegmentOf" (1000)
  logic = "op" "//" => "\<^const>Equiv_Relations.quotient" (1000)
  logic = "op" "respects" => "\<^const>Equiv_Relations.RESPECTS" (1000)
  logic = "op" "respects2" => "\<^const>Equiv_Relations.RESPECTS2" (1000)
  logic = "op" "^" => "\<^const>Power.power_class.power" (1000)
  logic = "op" "div" => "\<^const>Divides.div_class.div" (1000)
  logic = "op" "mod" => "\<^const>Divides.div_class.mod" (1000)
  logic = "op" "#" => "\<^const>List.list.Cons" (1000)
  logic = "op" "@" => "\<^const>List.append" (1000)
  logic = "op" "!" => "\<^const>List.nth" (1000)
  logic = "op" "o_m" => "\<^const>Map.map_comp" (1000)
  logic = "op" "∘⇩m" => "\<^const>Map.map_comp" (1000)
  logic = "op" "++" => "\<^const>Map.map_add" (1000)
  logic = "op" "|`" => "\<^const>Map.restrict_map" (1000)
  logic = "op" "⊆⇩m" => "\<^const>Map.map_le" (1000)
  logic = "XCONST" longid_position[0] => "_context_xconst" (1000)
  logic = "XCONST" id_position[0] => "_context_xconst" (1000)
  logic = "CONST" longid_position[0] => "_context_const" (1000)
  logic = "CONST" id_position[0] => "_context_const" (1000)
  logic = "⋄" index[1000] => "_struct" (1000)
  logic = "..." => "_DDDOT" (1000)
  logic = "TYPE" "(" type[0] ")" => "_TYPE" (1000)
  logic = "%" pttrns[0] "." any[3] => "_lambda" (3)
  logic = "%" HOL.cases_syn[0] => "_lam_pats_syntax" (10)
  logic = "(" logic[0] ")" (1000)
  logic = "(" any[0] "," Product_Type.tuple_args[0] ")" => "_tuple" (1000)
  logic = "…" => "_DDDOT" (1000)
  logic = "λ" pttrns[0] "." any[3] => "_lambda" (3)
  logic = "λ" HOL.cases_syn[0] => "_lam_pats_syntax" (10)
  logic = "_" => "\<^const>Pure.dummy_pattern" (1000)
  logic = "EX!" idts[0] "." logic[10] => "\<^const>HOL.Ex1_binder" (10)
  logic = "EX!" pttrn[0] ":" logic[0] "." logic[10] => "_Bex1" (10)
  logic = "EX" idts[0] "." logic[10] => "\<^const>HOL.Ex_binder" (10)
  logic = "EX" idt[0] ">=" any[0] "." logic[10] => "_Ex_greater_eq" (10)
  logic = "EX" idt[0] ">" any[0] "." logic[10] => "_Ex_greater" (10)
  logic = "EX" idt[0] "<=" any[0] "." logic[10] => "_Ex_less_eq" (10)
  logic = "EX" idt[0] "<" any[0] "." logic[10] => "_Ex_less" (10)
  logic = "EX" pttrn[0] ":" logic[0] "." logic[10] => "_Bex" (10)
  logic = "ALL" idts[0] "." logic[10] => "\<^const>HOL.All_binder" (10)
  logic = "ALL" idt[0] ">=" any[0] "." logic[10] => "_All_greater_eq" (10)
  logic = "ALL" idt[0] ">" any[0] "." logic[10] => "_All_greater" (10)
  logic = "ALL" idt[0] "<=" any[0] "." logic[10] => "_All_less_eq" (10)
  logic = "ALL" idt[0] "<" any[0] "." logic[10] => "_All_less" (10)
  logic = "ALL" pttrn[0] ":" logic[0] "." logic[10] => "_Ball" (10)
  logic = "~" logic[40] => "\<^const>HOL.Not" (40)
  logic = "¬" logic[40] => "\<^const>HOL.Not" (40)
  logic = "THE" pttrn[0] "." logic[10] => "_The" (10)
  logic = "let" HOL.letbinds[0] "in" any[10] => "_Let" (10)
  logic = "case" any[0] "of" HOL.cases_syn[0] => "_case_syntax" (10)
  logic = "∃!" idts[0] "." logic[10] => "\<^const>HOL.Ex1_binder" (10)
  logic = "∃!" pttrn[0] "∈" logic[0] "." logic[10] => "_Bex1" (10)
  logic = "∃!" idt[0] "⊆" any[0] "." logic[10] => "_setleEx1" (10)
  logic = "∃" idts[0] "." logic[10] => "\<^const>HOL.Ex_binder" (10)
  logic = "∃" idt[0] "≥" any[0] "." logic[10] => "_Ex_greater_eq" (10)
  logic = "∃" idt[0] ">" any[0] "." logic[10] => "_Ex_greater" (10)
  logic = "∃" idt[0] "≤" any[0] "." logic[10] => "_Ex_less_eq" (10)
  logic = "∃" idt[0] "<" any[0] "." logic[10] => "_Ex_less" (10)
  logic = "∃" pttrn[0] "∈" logic[0] "." logic[10] => "_Bex" (10)
  logic = "∃" idt[0] "⊆" any[0] "." logic[10] => "_setleEx" (10)
  logic = "∃" idt[0] "⊂" any[0] "." logic[10] => "_setlessEx" (10)
  logic = "∀" idts[0] "." logic[10] => "\<^const>HOL.All_binder" (10)
  logic = "∀" idt[0] "≥" any[0] "." logic[10] => "_All_greater_eq" (10)
  logic = "∀" idt[0] ">" any[0] "." logic[10] => "_All_greater" (10)
  logic = "∀" idt[0] "≤" any[0] "." logic[10] => "_All_less_eq" (10)
  logic = "∀" idt[0] "<" any[0] "." logic[10] => "_All_less" (10)
  logic = "∀" pttrn[0] "∈" logic[0] "." logic[10] => "_Ball" (10)
  logic = "∀" idt[0] "⊆" any[0] "." logic[10] => "_setleAll" (10)
  logic = "∀" idt[0] "⊂" any[0] "." logic[10] => "_setlessAll" (10)
  logic = "?!" idts[0] "." logic[10] => "\<^const>HOL.Ex1_binder" (10)
  logic = "?!" pttrn[0] ":" logic[0] "." logic[10] => "_Bex1" (10)
  logic = "?" idts[0] "." logic[10] => "\<^const>HOL.Ex_binder" (10)
  logic = "?" idt[0] "<=" any[0] "." logic[10] => "_Ex_less_eq" (10)
  logic = "?" idt[0] "<" any[0] "." logic[10] => "_Ex_less" (10)
  logic = "?" pttrn[0] ":" logic[0] "." logic[10] => "_Bex" (10)
  logic = "!" idts[0] "." logic[10] => "\<^const>HOL.All_binder" (10)
  logic = "!" idt[0] "<=" any[0] "." logic[10] => "_All_less_eq" (10)
  logic = "!" idt[0] "<" any[0] "." logic[10] => "_All_less" (10)
  logic = "!" pttrn[0] ":" logic[0] "." logic[10] => "_Ball" (10)
  logic = "if" logic[0] "then" any[0] "else" any[10] => "\<^const>HOL.If" (10)
  logic = "LEAST" idts[0] "." logic[10]
    => "\<^const>Orderings.ord_class.Least_binder" (10)
  logic = "LEAST" id ":" logic[0] "." logic[10] => "_Bleast" (10)
  logic = "LEAST" id "∈" logic[0] "." logic[10] => "_Bleast" (10)
  logic = "LEAST" pttrn[0] "WRT" logic[4] "." logic[10] => "_LeastM" (10)
  logic = "0" => "\<^const>Groups.zero_class.zero" (1000)
  logic = "-" any[81] => "\<^const>Groups.uminus_class.uminus" (80)
  logic = "¦" any[0] "¦" => "\<^const>Groups.abs_class.abs" (1000)
  logic = "1" => "\<^const>Groups.one_class.one" (1000)
  logic = "{" pttrn[0] "." logic[0] "}" => "_Coll" (1000)
  logic = "{" pttrn[0] ":" logic[0] "." logic[0] "}" => "_Collect" (1000)
  logic = "{" pttrn[0] "∈" logic[0] "." logic[0] "}" => "_Collect" (1000)
  logic = "{" args[0] "}" => "_Finset" (1000)
  logic = "{" any[0] "|" idts[0] "." logic[0] "}" => "_Setcompr" (1000)
  logic = "{" any[0] "<..}" => "\<^const>Set_Interval.ord_class.greaterThan" (1000)
  logic = "{" any[0] "..}" => "\<^const>Set_Interval.ord_class.atLeast" (1000)
  logic = "{" any[0] "<..<" any[0] "}"
    => "\<^const>Set_Interval.ord_class.greaterThanLessThan" (1000)
  logic = "{" any[0] "..<" any[0] "}"
    => "\<^const>Set_Interval.ord_class.atLeastLessThan" (1000)
  logic = "{" any[0] "<.." any[0] "}"
    => "\<^const>Set_Interval.ord_class.greaterThanAtMost" (1000)
  logic = "{" any[0] ".." any[0] "}"
    => "\<^const>Set_Interval.ord_class.atLeastAtMost" (1000)
  logic = "{}" => "\<^const>Set.empty" (1000)
  logic = "SUP" pttrn[0] ":" logic[0] "." any[10] => "_SUP" (10)
  logic = "SUP" pttrns[0] "." any[10] => "_SUP1" (10)
  logic = "INF" pttrn[0] ":" logic[0] "." any[10] => "_INF" (10)
  logic = "INF" pttrns[0] "." any[10] => "_INF1" (10)
  logic = "⋂" logic[900] => "\<^const>Complete_Lattices.Inter" (900)
  logic = "⋂" pttrn[0] "∈" logic[0] "." logic[10] => "_INTER" (10)
  logic = "⋂" pttrns[0] "." logic[10] => "_INTER1" (10)
  logic = "⋂" any[0] "<" any[0] "." logic[10] => "_INTER_less" (10)
  logic = "⋂" any[0] "≤" any[0] "." logic[10] => "_INTER_le" (10)
  logic = "INT" pttrn[0] ":" logic[0] "." logic[10] => "_INTER" (10)
  logic = "INT" pttrns[0] "." logic[10] => "_INTER1" (10)
  logic = "INT" any[0] "<" any[0] "." logic[10] => "_INTER_less" (10)
  logic = "INT" any[0] "<=" any[0] "." logic[10] => "_INTER_le" (10)
  logic = "⋃" logic[900] => "\<^const>Complete_Lattices.Union" (900)
  logic = "⋃" pttrn[0] "∈" logic[0] "." logic[10] => "_UNION" (10)
  logic = "⋃" pttrns[0] "." logic[10] => "_UNION1" (10)
  logic = "⋃" any[0] "<" any[0] "." logic[10] => "_UNION_less" (10)
  logic = "⋃" any[0] "≤" any[0] "." logic[10] => "_UNION_le" (10)
  logic = "UN" pttrn[0] ":" logic[0] "." logic[10] => "_UNION" (10)
  logic = "UN" pttrns[0] "." logic[10] => "_UNION1" (10)
  logic = "UN" any[0] "<" any[0] "." logic[10] => "_UNION_less" (10)
  logic = "UN" any[0] "<=" any[0] "." logic[10] => "_UNION_le" (10)
  logic = "()" => "\<^const>Product_Type.Unity" (1000)
  logic = "SIGMA" pttrn[0] ":" logic[0] "." logic[10] => "_Sigma" (10)
  logic = "ℕ" => "\<^const>Nat.semiring_1_class.Nats" (1000)
  logic = "ϵ" pttrn[0] "." logic[10] => "_Eps" (10)
  logic = "@" pttrn[0] "." logic[10] => "_Eps" (10)
  logic = "SOME" pttrn[0] "." logic[10] => "_Eps" (10)
  logic = "GREATEST" idts[0] "." logic[10]
    => "\<^const>Hilbert_Choice.Greatest_binder" (10)
  logic = "GREATEST" pttrn[0] "WRT" logic[4] "." logic[10] => "_GreatestM" (10)
  logic = "chain⇩⊆" => "\<^const>Zorn.chain_subset" (1000)
  logic = "CSUM" pttrn[0] ":" logic[51] "." logic[10] => "_Csum" (10)
  logic = num_const[0] => "_Numeral" (1000)
  logic = "∑" logic[1000] => "\<^const>Groups_Big.comm_monoid_add_class.Setsum"
    (999)
  logic = "∑" pttrn[0] "∈" logic[51] "." any[10] => "_setsum" (10)
  logic = "∑" pttrn[0] "|" logic[0] "." any[10] => "_qsetsum" (10)
  logic = "∑" idt[0] "≤" any[0] "." any[10] => "_upto_setsum" (10)
  logic = "∑" idt[0] "<" any[0] "." any[10] => "_upt_setsum" (10)
  logic = "∑" idt[0] "=" any[0] "..<" any[0] "." any[10] => "_from_upto_setsum"
    (10)
  logic = "∑" idt[0] "=" any[0] ".." any[0] "." any[10] => "_from_to_setsum" (10)
  logic = "∑" pttrn[0] "←" logic[51] "." any[10] => "_listsum" (10)
  logic = "SUM" pttrn[0] ":" logic[51] "." any[10] => "_setsum" (10)
  logic = "SUM" pttrn[0] "|" logic[0] "." any[10] => "_qsetsum" (10)
  logic = "SUM" idt[0] "<=" any[0] "." any[10] => "_upto_setsum" (10)
  logic = "SUM" idt[0] "<" any[0] "." any[10] => "_upt_setsum" (10)
  logic = "SUM" idt[0] "=" any[0] "..<" any[0] "." any[10] => "_from_upto_setsum"
    (10)
  logic = "SUM" idt[0] "=" any[0] ".." any[0] "." any[10] => "_from_to_setsum" (10)
  logic = "SUM" pttrn[0] "<-" logic[51] "." any[10] => "_listsum" (10)
  logic = "∏" logic[1000] => "\<^const>Groups_Big.comm_monoid_mult_class.Setprod"
    (999)
  logic = "∏" pttrn[0] "∈" logic[51] "." any[10] => "_setprod" (10)
  logic = "∏" pttrn[0] "|" logic[0] "." any[10] => "_qsetprod" (10)
  logic = "∏" idt[0] "≤" any[0] "." any[10] => "_upto_setprod" (10)
  logic = "∏" idt[0] "<" any[0] "." any[10] => "_upt_setprod" (10)
  logic = "∏" idt[0] "=" any[0] "..<" any[0] "." any[10] => "_from_upto_setprod"
    (10)
  logic = "∏" idt[0] "=" any[0] ".." any[0] "." any[10] => "_from_to_setprod" (10)
  logic = "∏" pttrn[0] "←" logic[51] "." any[10] => "_listprod" (10)
  logic = "PROD" pttrn[0] ":" logic[51] "." any[10] => "_setprod" (10)
  logic = "PROD" pttrn[0] "|" logic[0] "." any[10] => "_qsetprod" (10)
  logic = "PROD" idt[0] "<=" any[0] "." any[10] => "_upto_setprod" (10)
  logic = "PROD" idt[0] "<" any[0] "." any[10] => "_upt_setprod" (10)
  logic = "PROD" idt[0] "=" any[0] "..<" any[0] "." any[10] => "_from_upto_setprod"
    (10)
  logic = "PROD" idt[0] "=" any[0] ".." any[0] "." any[10] => "_from_to_setprod"
    (10)
  logic = "PROD" pttrn[0] "<-" logic[51] "." any[10] => "_listprod" (10)
  logic = "ℤ" => "\<^const>Int.ring_1_class.Ints" (1000)
  logic = "⨅⇩f⇩i⇩n" logic[900]
    => "\<^const>Lattices_Big.semilattice_inf_class.Inf_fin" (900)
  logic = "⨆⇩f⇩i⇩n" logic[900]
    => "\<^const>Lattices_Big.semilattice_sup_class.Sup_fin" (900)
  logic = "{..<" any[0] "}" => "\<^const>Set_Interval.ord_class.lessThan" (1000)
  logic = "{.." any[0] "}" => "\<^const>Set_Interval.ord_class.atMost" (1000)
  logic = "[]" => "\<^const>List.list.Nil" (1000)
  logic = "[" args[0] "]" => "_list" (1000)
  logic = "[" pttrn[0] "<-" logic[0] "." logic[0] "]" => "_filter" (1000)
  logic = "[" pttrn[0] "←" logic[0] "." logic[0] "]" => "_filter" (1000)
  logic = "[" logic[0] "..<" logic[0] "]" => "\<^const>List.upt" (1000)
  logic = "[" any[0] "." List.lc_qual[0] List.lc_quals[0] => "_listcompr" (1000)
  logic = "[" logic[0] ".." logic[0] "]" => "\<^const>List.upto" (1000)
  logic = "[" Map.maplets[0] "]" => "_Map" (1000)
  logic = "CHR" str_position[0] => "_Char" (1000)
  logic = str_position[0] => "_String" (1000)
  logic = "TYPEREP" "(" type[0] ")" => "_TYPEREP" (1000)
  logic = "(|" Record.fields[0] "," "..." "=" any[0] "|)" => "_record_scheme"
    (1000)
  logic = "(|" Record.fields[0] "|)" => "_record" (1000)
  logic = "⦇" Record.fields[0] "," "…" "=" any[0] "⦈" => "_record_scheme" (1000)
  logic = "⦇" Record.fields[0] "⦈" => "_record" (1000)
  logic = "∀⇩F" pttrn[0] "in" logic[0] "." logic[10] => "_eventually" (10)
  logic = "∃⇩F" pttrn[0] "in" logic[0] "." logic[10] => "_frequently" (10)
  logic = "INFM" idts[0] "." logic[10] => "\<^const>Filter.Inf_many_binder" (10)
  logic = "MOST" idts[0] "." logic[10] => "\<^const>Filter.Alm_all_binder" (10)
  logic = "∀⇩∞" idts[0] "." logic[10] => "\<^const>Filter.Alm_all_binder" (10)
  logic = "∃⇩∞" idts[0] "." logic[10] => "\<^const>Filter.Inf_many_binder" (10)
  logic = "LIM" pttrns[1000] any[10] "." any[0] ":>" any[10] => "_LIM" (10)
  logic = logic[900] "(" Map.maplets[0] ")" => "_MapUpd" (900)
  logic = logic[51] "⊆⇩m" logic[51] => "\<^const>Map.map_le" (50)
  logic = logic[110] "|`" logic[111] => "\<^const>Map.restrict_map" (110)
  logic = logic[100] "++" logic[101] => "\<^const>Map.map_add" (100)
  logic = logic[55] "∘⇩m" logic[56] => "\<^const>Map.map_comp" (55)
  logic = logic[55] "o_m" logic[56] => "\<^const>Map.map_comp" (55)
  logic = logic[100] "!" logic[101] => "\<^const>List.nth" (100)
  logic = logic[66] "@" logic[65] => "\<^const>List.append" (65)
  logic = logic[81] "respects2" logic[80] => "\<^const>Equiv_Relations.RESPECTS2"
    (80)
  logic = logic[81] "respects" logic[80] => "\<^const>Equiv_Relations.RESPECTS"
    (80)
  logic = logic[90] "//" logic[91] => "\<^const>Equiv_Relations.quotient" (90)
  logic = logic[56] "initial_segment_of" logic[56]
    => "\<^const>Zorn.initialSegmentOf" (55)
  logic = logic[81] "<*mlex*>" logic[80] => "\<^const>Wellfounded.mlex_prod" (80)
  logic = logic[81] "<*lex*>" logic[80] => "\<^const>Wellfounded.lex_prod" (80)
  logic = logic[1000] "⇧*⇧*" => "\<^const>Transitive_Closure.rtranclp" (1000)
  logic = logic[1000] "⇧+⇧+" => "\<^const>Transitive_Closure.tranclp" (1000)
  logic = logic[1000] "⇧=⇧=" => "\<^const>Transitive_Closure.reflclp" (1000)
  logic = logic[1000] "⇧*" => "\<^const>Transitive_Closure.rtrancl" (999)
  logic = logic[1000] "⇧+" => "\<^const>Transitive_Closure.trancl" (999)
  logic = logic[1000] "⇧=" => "\<^const>Transitive_Closure.reflcl" (999)
  logic = logic[1000] "^=" => "\<^const>Transitive_Closure.reflcl" (999)
  logic = logic[1000] "^==" => "\<^const>Transitive_Closure.reflclp" (1000)
  logic = logic[1000] "^**" => "\<^const>Transitive_Closure.rtranclp" (1000)
  logic = logic[1000] "^++" => "\<^const>Transitive_Closure.tranclp" (1000)
  logic = logic[1000] "^+" => "\<^const>Transitive_Closure.trancl" (999)
  logic = logic[1000] "^*" => "\<^const>Transitive_Closure.rtrancl" (999)
  logic = logic[91] "``" logic[90] => "\<^const>Relation.Image" (90)
  logic = logic[1000] "¯¯" => "\<^const>Relation.conversep" (1000)
  logic = logic[1000] "^--1" => "\<^const>Relation.conversep" (1000)
  logic = logic[1000] "¯" => "\<^const>Relation.converse" (999)
  logic = logic[1000] "^-1" => "\<^const>Relation.converse" (999)
  logic = logic[76] "OO" logic[75] => "\<^const>Relation.relcompp" (75)
  logic = logic[76] "O" logic[75] => "\<^const>Relation.relcomp" (75)
  logic = logic[66] "<+>" logic[65] => "\<^const>Sum_Type.Plus" (65)
  logic = logic[81] "×" logic[80] => "\<^const>Product_Type.Times" (80)
  logic = logic[81] "<*>" logic[80] => "\<^const>Product_Type.Times" (80)
  logic = logic[55] "∘" logic[56] => "\<^const>Fun.comp" (55)
  logic = logic[55] "o" logic[56] => "\<^const>Fun.comp" (55)
  logic = logic[91] "-`" logic[90] => "\<^const>Set.vimage" (90)
  logic = logic[91] "`" logic[90] => "\<^const>Set.image" (90)
  logic = logic[65] "∪" logic[66] => "\<^const>Set.union" (65)
  logic = logic[65] "Un" logic[66] => "\<^const>Set.union" (65)
  logic = logic[70] "∩" logic[71] => "\<^const>Set.inter" (70)
  logic = logic[70] "Int" logic[71] => "\<^const>Set.inter" (70)
  logic = logic[51] "⊃" logic[51] => "\<^const>Set.supset" (50)
  logic = logic[51] "⊇" logic[51] => "\<^const>Set.supset_eq" (50)
  logic = logic[51] "⊂" logic[51] => "\<^const>Set.subset" (50)
  logic = logic[51] "⊆" logic[51] => "\<^const>Set.subset_eq" (50)
  logic = logic[26] "⟷" logic[25] => "\<^const>HOL.iff" (25)
  logic = logic[26] "<->" logic[25] => "\<^const>HOL.iff" (25)
  logic = logic[36] "∧" logic[35] => "\<^const>HOL.conj" (35)
  logic = logic[31] "∨" logic[30] => "\<^const>HOL.disj" (30)
  logic = logic[26] "⟶" logic[25] => "\<^const>HOL.implies" (25)
  logic = logic[36] "&" logic[35] => "\<^const>HOL.conj" (35)
  logic = logic[31] "|" logic[30] => "\<^const>HOL.disj" (30)
  logic = logic[26] "-->" logic[25] => "\<^const>HOL.implies" (25)
  logic = logic[4] "∷" type[0] => "_constrain" (3)
  logic = logic[1000] cargs[1000] => "_applC" (999)
  logic = logic[4] "::" type[0] => "_constrain" (3)
  logic = any[900] "⦇" Record.field_updates[0] "⦈" => "_record_update" (900)
  logic = any[900] "(|" Record.field_updates[0] "|)" => "_record_update" (900)
  logic = any[900] "[" List.lupdbinds[0] "]" => "_LUpdate" (900)
  logic = any[66] "#" logic[65] => "\<^const>List.list.Cons" (65)
  logic = any[70] "mod" any[71] => "\<^const>Divides.div_class.mod" (70)
  logic = any[70] "div" any[71] => "\<^const>Divides.div_class.div" (70)
  logic = any[1000] "⇧2" => "\<^const>Power.power_class.power2" (999)
  logic = any[81] "^" logic[80] => "\<^const>Power.power_class.power" (80)
  logic = any[81] "^^" logic[80] => "\<^const>Nat.compower" (80)
  logic = any[70] "/" any[71] => "\<^const>Fields.inverse_class.divide" (70)
  logic = any[51] "dvd" any[51] => "\<^const>Rings.dvd_class.dvd" (50)
  logic = any[1000] "(" Fun.updbinds[0] ")" => "_Update" (900)
  logic = any[51] "∈" logic[51] => "\<^const>Set.member" (50)
  logic = any[51] "∉" logic[51] => "\<^const>Set.not_member" (50)
  logic = any[51] "~:" logic[51] => "\<^const>Set.not_member" (50)
  logic = any[51] ":" logic[51] => "\<^const>Set.member" (50)
  logic = any[70] "*" any[71] => "\<^const>Groups.times_class.times" (70)
  logic = any[65] "-" any[66] => "\<^const>Groups.minus_class.minus" (65)
  logic = any[65] "+" any[66] => "\<^const>Groups.plus_class.plus" (65)
  logic = any[51] ">" any[51] => "\<^const>Orderings.ord_class.greater" (50)
  logic = any[51] "≥" any[51] => "\<^const>Orderings.ord_class.greater_eq" (50)
  logic = any[51] ">=" any[51] => "\<^const>Orderings.ord_class.greater_eq" (50)
  logic = any[51] "≤" any[51] => "\<^const>Orderings.ord_class.less_eq" (50)
  logic = any[51] "<=" any[51] => "\<^const>Orderings.ord_class.less_eq" (50)
  logic = any[51] "<" any[51] => "\<^const>Orderings.ord_class.less" (50)
  logic = any[50] "≠" any[51] => "\<^const>HOL.not_equal" (50)
  logic = any[50] "~=" any[51] => "\<^const>HOL.not_equal" (50)
  logic = any[50] "=" any[51] => "\<^const>HOL.eq" (50)
  logic = var_position[-1] (-1)
  logic = longid_position[-1] (-1)
  logic = id_position[-1] (-1)
  longid_position = longid => "_position" (1000)
  num_const = num_position[0] => "_constify" (1000)
  num_position = num_token => "_position" (1000)
  prop = logic[0] => "\<^const>HOL.Trueprop" (5)
  prop = prop'[-1] (-1)
  prop' = "TERM" logic[0] => "\<^const>Pure.term" (1000)
  prop' = "SORT_CONSTRAINT" "(" type[0] ")" => "_sort_constraint" (1000)
  prop' = "OFCLASS" "(" type[0] "," logic[0] ")" => "_ofclass" (1000)
  prop' = "[|" asms[0] "|]" "==>" prop[1] => "_bigimpl" (1)
  prop' = "PROP" aprop[0] => "_aprop" (1000)
  prop' = "(" prop'[0] ")" (1000)
  prop' = "⟦" asms[0] "⟧" "⟹" prop[1] => "_bigimpl" (1)
  prop' = "⋀" idts[0] "." prop[0] => "\<^const>Pure.all_binder" (0)
  prop' = "!!" idts[0] "." prop[0] => "\<^const>Pure.all_binder" (0)
  prop' = any[3] "==" any[3] => "\<^const>Pure.eq" (2)
  prop' = any[3] "≡" any[3] => "\<^const>Pure.eq" (2)
  prop' = prop[2] "==>" prop[1] => "\<^const>Pure.imp" (1)
  prop' = prop[2] "⟹" prop[1] => "\<^const>Pure.imp" (1)
  prop' = prop[3] "&&&" prop[2] => "\<^const>Pure.conjunction" (2)
  prop' = prop[2] "=simp=>" prop[1] => "\<^const>HOL.simp_implies" (1)
  prop' = prop'[4] "::" type[0] => "_constrain" (3)
  prop' = prop'[4] "∷" type[0] => "_constrain" (3)
  pttrn = "(" pttrn[0] "," Product_Type.patterns[0] ")" => "_pattern" (1000)
  pttrn = idt[-1] (-1)
  pttrns = pttrn[1] pttrns[0] => "_pttrns" (0)
  pttrns = pttrn[-1] (-1)
  sort = "{" classes[0] "}" => "_sort" (1000)
  sort = "{}" => "_topsort" (1000)
  sort = class_name[-1] (-1)
  str_position = str_token => "_position" (1000)
  string_position = string_token => "_position" (1000)
  tid_position = tid => "_position_sort" (1000)
  tvar_position = tvar => "_position_sort" (1000)
  type = "_" => "\<^type>dummy" (1000)
  type = "_" "::" sort[0] => "_dummy_ofsort" (1000)
  type = "(" type[0] ")" (1000)
  type = "(" type[0] "," types[0] ")" type_name[0] => "_tappl" (1000)
  type = "[" types[0] "]" "=>" type[0] => "_bracket" (0)
  type = "[" types[0] "]" "⇒" type[0] => "_bracket" (0)
  type = tvar_position[1000] "::" sort[0] => "_ofsort" (1000)
  type = tid_position[1000] "::" sort[0] => "_ofsort" (1000)
  type = tid_position[1000] "∷" sort[0] => "_ofsort" (1000)
  type = "(|" Record.field_types[0] "," "..." "::" type[0] "|)"
    => "_record_type_scheme" (1000)
  type = "(|" Record.field_types[0] "|)" => "_record_type" (1000)
  type = "⦇" Record.field_types[0] "," "…" "::" type[0] "⦈"
    => "_record_type_scheme" (1000)
  type = type[1] "⇀" type[0] => "\<^type>Map.map" (0)
  type = type[1] "~=>" type[0] => "\<^type>Map.map" (0)
  type = type[11] "+" type[10] => "\<^type>Sum_Type.sum" (10)
  type = type[21] "×" type[20] => "\<^type>Product_Type.prod" (20)
  type = type[21] "*" type[20] => "\<^type>Product_Type.prod" (20)
  type = type[1] "⇒" type[0] => "\<^type>fun" (0)
  type = type[1000] type_name[0] => "_tapp" (1000)
  type = type[1] "=>" type[0] => "\<^type>fun" (0)
  type = "⦇" Record.field_types[0] "⦈" => "_record_type" (1000)
  type = type_name[-1] (-1)
  type = tvar_position[-1] (-1)
  type = tid_position[-1] (-1)
  type_name = longid => "_type_name" (1000)
  type_name = id => "_type_name" (1000)
  types = type[0] "," types[0] => "_types" (1000)
  types = type[-1] (-1)
  var_position = var => "_position" (1000)
print modes: "HOL" "HTML" "epsilon" "iff" "input" "latex" "latex_prod" "latex_sum"
  "xsymbols"
consts: "\<^const>Filter.Alm_all_binder" "\<^const>Filter.Inf_many_binder"
  "\<^const>HOL.All_binder" "\<^const>HOL.Ex1_binder" "\<^const>HOL.Ex_binder"
  "\<^const>Hilbert_Choice.Greatest_binder"
  "\<^const>Orderings.ord_class.Least_binder" "\<^const>Pure.all_binder"
  "_All_greater" "_All_greater_eq" "_All_less" "_All_less_eq" "_Ball" "_Bex"
  "_Bex1" "_Bleast" "_Char" "_Coll" "_Collect" "_Csum" "_DDDOT" "_Eps"
  "_Ex_greater" "_Ex_greater_eq" "_Ex_less" "_Ex_less_eq" "_Finset" "_GreatestM"
  "_INF" "_INF1" "_INTER" "_INTER1" "_INTER_le" "_INTER_less" "_LIM" "_LUpdate"
  "_LeastM" "_Let" "_Map" "_MapUpd" "_Maplets" "_Numeral" "_SUP" "_SUP1"
  "_Setcompr" "_Sigma" "_String" "_TYPE" "_TYPEREP" "_The" "_UNION" "_UNION1"
  "_UNION_le" "_UNION_less" "_Update" "_abs" "_applC" "_aprop" "_args" "_asm"
  "_asms" "_bigimpl" "_bind" "_binds" "_bound" "_bracket" "_cargs" "_case1"
  "_case2" "_case_syntax" "_class_name" "_classes" "_constify" "_constrain"
  "_constrainAbs" "_context_const" "_context_xconst" "_dummy_ofsort" "_eventually"
  "_field" "_field_type" "_field_types" "_field_update" "_field_updates" "_fields"
  "_filter" "_free" "_frequently" "_from_to_setprod" "_from_to_setsum"
  "_from_upto_setprod" "_from_upto_setsum" "_idtdummy" "_idts" "_idtyp"
  "_idtypdummy" "_ignore_type" "_index" "_indexdefault" "_indexvar" "_inner_string"
  "_lam_pats_syntax" "_lambda" "_lc_abs" "_lc_end" "_lc_gen" "_lc_quals" "_lc_test"
  "_list" "_listcompr" "_listprod" "_listsum" "_loose" "_lupdbind" "_lupdbinds"
  "_maplet" "_maplets" "_mk_ofclass" "_numeral" "_ofclass" "_ofsort" "_pattern"
  "_patterns" "_position" "_position_sort" "_pttrns" "_qsetprod" "_qsetsum"
  "_record" "_record_scheme" "_record_type" "_record_type_scheme" "_record_update"
  "_setleAll" "_setleEx" "_setleEx1" "_setlessAll" "_setlessEx" "_setprod"
  "_setsum" "_sort" "_sort_constraint" "_strip_positions" "_struct" "_tapp"
  "_tappl" "_tfree" "_topsort" "_tuple" "_tuple_arg" "_tuple_args" "_tvar"
  "_type_constraint_" "_type_name" "_type_prop" "_types" "_update_name" "_updbind"
  "_updbinds" "_upt_setprod" "_upt_setsum" "_upto_setprod" "_upto_setsum" "_var"
parse_ast_translation: "_Char" "_String" "_appl" "_applC" "_bigimpl" "_bracket"
  "_constify" "_context_const" "_context_xconst" "_idtyp" "_indexdefault"
  "_indexvar" "_lambda" "_strip_positions" "_struct" "_tapp" "_tappl"
parse_rules:
    ("_Bex" x A P)  ->  ("\<^const>Set.Bex" A ("_abs" x P))
    ("_Eps" x P)  ->  ("\<^const>Hilbert_Choice.Eps" ("_abs" x P))
    ("_INF" x A B)  ->
      ("\<^const>Complete_Lattices.Inf_class.INFIMUM" A ("_abs" x B))
    ("_LIM" x F1 f F2)  ->  ("\<^const>Filter.filterlim" ("_abs" x f) F2 F1)
    ("_Let" ("_binds" b bs) e)  ->  ("_Let" b ("_Let" bs e))
    ("_Let" ("_bind" x a) e)  ->  ("\<^const>HOL.Let" a ("_abs" x e))
    ("_Map" ms)  ->  ("_MapUpd" "\<^const>Map.empty" ms)
    ("_SUP" x A B)  ->
      ("\<^const>Complete_Lattices.Sup_class.SUPREMUM" A ("_abs" x B))
    ("_The" x P)  ->  ("\<^const>HOL.The" ("_abs" x P))
    ("_abs" ("_pattern" x ("_patterns" y zs)) b)  ->
      ("\<^const>Product_Type.prod.case_prod"
        ("_abs" x ("_abs" ("_pattern" y zs) b)))
    ("_abs" ("_pattern" x y) b)  ->
      ("\<^const>Product_Type.prod.case_prod" ("_abs" x ("_abs" y b)))
    ("_abs" ("\<^const>Product_Type.Pair" x y) t)  ->  ("_abs" ("_pattern" x y) t)
    ("_Ball" x A P)  ->  ("\<^const>Set.Ball" A ("_abs" x P))
    ("_Bex1" x A P)  ->
      ("\<^const>HOL.Ex1_binder" x
        ("\<^const>HOL.conj" ("\<^const>Set.member" x A) P))
    ("_Coll" x P)  ->  ("\<^const>Set.Collect" ("_abs" x P))
    ("_Csum" i r rs)  ->  ("\<^const>BNF_Cardinal_Arithmetic.Csum" r ("_abs" i rs))
    ("_INF1" ("_pttrns" x y) B)  ->  ("_INF1" x ("_INF1" y B))
    ("_INF1" x B)  ->
      ("\<^const>Complete_Lattices.Inf_class.INFIMUM" "\<^const>Set.UNIV"
        ("_abs" x B))
    ("_INF1" x B)  ->  ("_INF" x "\<^const>Set.UNIV" B)
    ("_SUP1" ("_pttrns" x y) B)  ->  ("_SUP1" x ("_SUP1" y B))
    ("_SUP1" x B)  ->
      ("\<^const>Complete_Lattices.Sup_class.SUPREMUM" "\<^const>Set.UNIV"
        ("_abs" x B))
    ("_SUP1" x B)  ->  ("_SUP" x "\<^const>Set.UNIV" B)
    ("_list" ("_args" x xs))  ->  ("\<^const>List.list.Cons" x ("_list" xs))
    ("_list" x)  ->  ("\<^const>List.list.Cons" x "\<^const>List.list.Nil")
    ("_INTER" x A B)  ->  ("\<^const>Complete_Lattices.INTER" A ("_abs" x B))
    ("_Sigma" x A B)  ->  ("\<^const>Product_Type.Sigma" A ("_abs" x B))
    ("_UNION" x A B)  ->  ("\<^const>Complete_Lattices.UNION" A ("_abs" x B))
    ("_tuple" x ("_tuple_arg" y))  ->  ("\<^const>Product_Type.Pair" x y)
    ("_tuple" x ("_tuple_args" y z))  ->
      ("_tuple" x ("_tuple_arg" ("_tuple" y z)))
    ("_Bleast" x A P)  ->
      ("\<^const>Orderings.ord_class.Least_binder" x
        ("\<^const>HOL.conj" ("\<^const>Set.member" x A) P))
    ("_Finset" ("_args" x xs))  ->  ("\<^const>Set.insert" x ("_Finset" xs))
    ("_Finset" x)  ->  ("\<^const>Set.insert" x "\<^const>Set.empty")
    ("_INTER1" ("_pttrns" x y) B)  ->  ("_INTER1" x ("_INTER1" y B))
    ("_INTER1" x B)  ->
      ("\<^const>Complete_Lattices.INTER" "\<^const>Set.UNIV" ("_abs" x B))
    ("_INTER1" x B)  ->  ("_INTER" x "\<^const>Set.UNIV" B)
    ("_LeastM" x m P)  ->  ("\<^const>Hilbert_Choice.LeastM" m ("_abs" x P))
    ("_MapUpd" m ("_maplets" x y))  ->  ("\<^const>Map.map_upds" m x y)
    ("_MapUpd" m ("_Maplets" xy ms))  ->  ("_MapUpd" ("_MapUpd" m xy) ms)
    ("_MapUpd" m ("_maplet" x y))  ->
      ("_Update" m ("_updbind" x ("\<^const>Option.option.Some" y)))
    ("_UNION1" ("_pttrns" x y) B)  ->  ("_UNION1" x ("_UNION1" y B))
    ("_UNION1" x B)  ->
      ("\<^const>Complete_Lattices.UNION" "\<^const>Set.UNIV" ("_abs" x B))
    ("_UNION1" x B)  ->  ("_UNION" x "\<^const>Set.UNIV" B)
    ("_Update" f ("_updbinds" b bs))  ->  ("_Update" ("_Update" f b) bs)
    ("_Update" f ("_updbind" x y))  ->  ("\<^const>Fun.fun_upd" f x y)
    ("_filter" x xs P)  ->  ("\<^const>List.filter" ("_abs" x P) xs)
    ("_setsum" i A b)  ->
      ("\<^const>Groups_Big.comm_monoid_add_class.setsum" ("_abs" i b) A)
    ("_Collect" p A P)  ->
      ("\<^const>Set.Collect"
        ("_abs" p ("\<^const>HOL.conj" ("\<^const>Set.member" p A) P)))
    ("_Ex_less" x y P)  ->
      ("\<^const>HOL.Ex_binder" x
        ("\<^const>HOL.conj" ("\<^const>Orderings.ord_class.less" x y) P))
    ("_LUpdate" xs ("_lupdbinds" b bs))  ->  ("_LUpdate" ("_LUpdate" xs b) bs)
    ("_LUpdate" xs ("_lupdbind" i x))  ->  ("\<^const>List.list_update" xs i x)
    ("_listsum" x xs b)  ->
      ("\<^const>Groups_List.monoid_add_class.listsum"
        ("\<^const>List.list.map" ("_abs" x b) xs))
    ("_pattern" x y)  ->  ("\<^const>Product_Type.Pair" x y)
    ("_qsetsum" x P t)  ->
      ("\<^const>Groups_Big.comm_monoid_add_class.setsum" ("_abs" x t)
        ("_Coll" x P))
    ("_setleEx" A B P)  ->
      ("\<^const>HOL.Ex_binder" A
        ("\<^const>HOL.conj" ("\<^const>Set.subset_eq" A B) P))
    ("_setprod" i A b)  ->
      ("\<^const>Groups_Big.comm_monoid_mult_class.setprod" ("_abs" i b) A)
    ("_All_less" x y P)  ->
      ("\<^const>HOL.All_binder" x
        ("\<^const>HOL.implies" ("\<^const>Orderings.ord_class.less" x y) P))
    ("_INTER_le" i n A)  ->
      ("_INTER" i ("\<^const>Set_Interval.ord_class.atMost" n) A)
    ("_UNION_le" i n A)  ->
      ("_UNION" i ("\<^const>Set_Interval.ord_class.atMost" n) A)
    ("_listprod" x xs b)  ->
      ("\<^const>Groups_List.monoid_mult_class.listprod"
        ("\<^const>List.list.map" ("_abs" x b) xs))
    ("_patterns" x y)  ->  ("\<^const>Product_Type.Pair" x y)
    ("_qsetprod" x P t)  ->
      ("\<^const>Groups_Big.comm_monoid_mult_class.setprod" ("_abs" x t)
        ("_Coll" x P))
    ("_setleAll" A B P)  ->
      ("\<^const>HOL.All_binder" A
        ("\<^const>HOL.implies" ("\<^const>Set.subset_eq" A B) P))
    ("_setleEx1" A B P)  ->
      ("\<^const>HOL.Ex1_binder" A
        ("\<^const>HOL.conj" ("\<^const>Set.subset_eq" A B) P))
    ("_GreatestM" x m P)  ->  ("\<^const>Hilbert_Choice.GreatestM" m ("_abs" x P))
    ("_setlessEx" A B P)  ->
      ("\<^const>HOL.Ex_binder" A
        ("\<^const>HOL.conj" ("\<^const>Set.subset" A B) P))
    ("_Ex_greater" x y P)  ->
      ("\<^const>HOL.Ex_binder" x
        ("\<^const>HOL.conj" ("\<^const>Orderings.ord_class.greater" x y) P))
    ("_Ex_less_eq" x y P)  ->
      ("\<^const>HOL.Ex_binder" x
        ("\<^const>HOL.conj" ("\<^const>Orderings.ord_class.less_eq" x y) P))
    ("_INTER_less" i n A)  ->
      ("_INTER" i ("\<^const>Set_Interval.ord_class.lessThan" n) A)
    ("_UNION_less" i n A)  ->
      ("_UNION" i ("\<^const>Set_Interval.ord_class.lessThan" n) A)
    ("_eventually" x F P)  ->  ("\<^const>Filter.eventually" ("_abs" x P) F)
    ("_frequently" x F P)  ->  ("\<^const>Filter.frequently" ("_abs" x P) F)
    ("_setlessAll" A B P)  ->
      ("\<^const>HOL.All_binder" A
        ("\<^const>HOL.implies" ("\<^const>Set.subset" A B) P))
    ("_upt_setsum" i n t)  ->
      ("\<^const>Groups_Big.comm_monoid_add_class.setsum" ("_abs" i t)
        ("\<^const>Set_Interval.ord_class.lessThan" n))
    ("_All_greater" x y P)  ->
      ("\<^const>HOL.All_binder" x
        ("\<^const>HOL.implies" ("\<^const>Orderings.ord_class.greater" x y) P))
    ("_All_less_eq" x y P)  ->
      ("\<^const>HOL.All_binder" x
        ("\<^const>HOL.implies" ("\<^const>Orderings.ord_class.less_eq" x y) P))
    ("_upt_setprod" i n t)  ->
      ("\<^const>Groups_Big.comm_monoid_mult_class.setprod" ("_abs" i t)
        ("\<^const>Set_Interval.ord_class.lessThan" n))
    ("_upto_setsum" i n t)  ->
      ("\<^const>Groups_Big.comm_monoid_add_class.setsum" ("_abs" i t)
        ("\<^const>Set_Interval.ord_class.atMost" n))
    ("_upto_setprod" i n t)  ->
      ("\<^const>Groups_Big.comm_monoid_mult_class.setprod" ("_abs" i t)
        ("\<^const>Set_Interval.ord_class.atMost" n))
    ("_Ex_greater_eq" x y P)  ->
      ("\<^const>HOL.Ex_binder" x
        ("\<^const>HOL.conj" ("\<^const>Orderings.ord_class.greater_eq" x y) P))
    ("_All_greater_eq" x y P)  ->
      ("\<^const>HOL.All_binder" x
        ("\<^const>HOL.implies" ("\<^const>Orderings.ord_class.greater_eq" x y) P))
    ("_from_to_setsum" x a b t)  ->
      ("\<^const>Groups_Big.comm_monoid_add_class.setsum" ("_abs" x t)
        ("\<^const>Set_Interval.ord_class.atLeastAtMost" a b))
    ("_from_to_setprod" x a b t)  ->
      ("\<^const>Groups_Big.comm_monoid_mult_class.setprod" ("_abs" x t)
        ("\<^const>Set_Interval.ord_class.atLeastAtMost" a b))
    ("_from_upto_setsum" x a b t)  ->
      ("\<^const>Groups_Big.comm_monoid_add_class.setsum" ("_abs" x t)
        ("\<^const>Set_Interval.ord_class.atLeastLessThan" a b))
    ("_from_upto_setprod" x a b t)  ->
      ("\<^const>Groups_Big.comm_monoid_mult_class.setprod" ("_abs" x t)
        ("\<^const>Set_Interval.ord_class.atLeastLessThan" a b))
parse_translation: "\<^const>Filter.Alm_all_binder"
  "\<^const>Filter.Inf_many_binder" "\<^const>HOL.All_binder"
  "\<^const>HOL.Ex1_binder" "\<^const>HOL.Ex_binder"
  "\<^const>Hilbert_Choice.Greatest_binder"
  "\<^const>Orderings.ord_class.Least_binder" "\<^const>Pure.all_binder" "_DDDOT"
  "_Numeral" "_Setcompr" "_TYPE" "_TYPEREP" "_abs" "_aprop" "_case_syntax" "_index"
  "_lam_pats_syntax" "_listcompr" "_ofclass" "_record" "_record_scheme"
  "_record_type" "_record_type_scheme" "_record_update" "_sort_constraint"
  "_struct" "_update_name"
print_translation: "\<^const>Complete_Lattices.INTER"
  "\<^const>Complete_Lattices.Inf_class.INFIMUM"
  "\<^const>Complete_Lattices.Sup_class.SUPREMUM"
  "\<^const>Complete_Lattices.UNION" "\<^const>Ctr_Sugar.case_guard"
  "\<^const>Filter.Alm_all" "\<^const>Filter.Inf_many"
  "\<^const>Groups.one_class.one" "\<^const>Groups.zero_class.zero"
  "\<^const>Groups_Big.comm_monoid_add_class.setsum" "\<^const>HOL.All"
  "\<^const>HOL.All_binder" "\<^const>HOL.Ex" "\<^const>HOL.Ex1"
  "\<^const>HOL.Ex_binder" "\<^const>HOL.The" "\<^const>Hilbert_Choice.Eps"
  "\<^const>Hilbert_Choice.Greatest" "\<^const>Num.numeral_class.numeral"
  "\<^const>Orderings.ord_class.Least" "\<^const>Product_Type.prod.case_prod"
  "\<^const>Pure.all" "\<^const>Pure.type" "\<^const>Set.Ball" "\<^const>Set.Bex"
  "\<^const>Set.Collect" "\<^const>Typerep.typerep_class.typerep"
  "_type_constraint_" "_type_prop"
print_rules:
    ("_INF" x "\<^const>Set.UNIV" B)  ->  ("_INF1" x B)
    ("_Let" b ("_Let" bs e))  ->  ("_Let" ("_binds" b bs) e)
    ("_SUP" x "\<^const>Set.UNIV" B)  ->  ("_SUP1" x B)
    ("_INF1" x ("_INF1" y B))  ->  ("_INF1" ("_pttrns" x y) B)
    ("_SUP1" x ("_SUP1" y B))  ->  ("_SUP1" ("_pttrns" x y) B)
    ("_INTER" i ("\<^const>Set_Interval.ord_class.atMost" n) A)  ->
      ("_INTER_le" i n A)
    ("_INTER" i ("\<^const>Set_Interval.ord_class.lessThan" n) A)  ->
      ("_INTER_less" i n A)
    ("_INTER" x "\<^const>Set.UNIV" B)  ->  ("_INTER1" x B)
    ("_UNION" i ("\<^const>Set_Interval.ord_class.atMost" n) A)  ->
      ("_UNION_le" i n A)
    ("_UNION" i ("\<^const>Set_Interval.ord_class.lessThan" n) A)  ->
      ("_UNION_less" i n A)
    ("_UNION" x "\<^const>Set.UNIV" B)  ->  ("_UNION1" x B)
    ("_tuple" x ("_tuple_arg" ("_tuple" y z)))  ->
      ("_tuple" x ("_tuple_args" y z))
    ("_INTER1" x ("_INTER1" y B))  ->  ("_INTER1" ("_pttrns" x y) B)
    ("_MapUpd" ("_MapUpd" m xy) ms)  ->  ("_MapUpd" m ("_Maplets" xy ms))
    ("_MapUpd" "\<^const>Map.empty" ms)  ->  ("_Map" ms)
    ("_MapUpd" ("_Map" ms1) ms2)  ->  ("_Map" ("_Maplets" ms1 ms2))
    ("_UNION1" x ("_UNION1" y B))  ->  ("_UNION1" ("_pttrns" x y) B)
    ("_Update" m ("_updbind" x ("\<^const>Option.option.Some" y)))  ->
      ("_MapUpd" m ("_maplet" x y))
    ("_Update" ("_Update" f b) bs)  ->  ("_Update" f ("_updbinds" b bs))
    ("_LUpdate" ("_LUpdate" xs b) bs)  ->  ("_LUpdate" xs ("_lupdbinds" b bs))
    ("_Maplets" ("_Maplets" ms1 ms2) ms3)  ->
      ("_Maplets" ms1 ("_Maplets" ms2 ms3))
    ("\<^const>HOL.Let" a ("_abs" x e))  ->  ("_Let" ("_bind" x a) e)
    ("\<^const>HOL.The" ("_abs" x P))  ->  ("_The" x P)
    ("\<^const>Set.Bex" A ("_abs" x P))  ->  ("_Bex" x A P)
    ("\<^const>Set.Ball" A ("_abs" x P))  ->  ("_Ball" x A P)
    ("\<^const>Set.insert" x ("_Finset" xs))  ->  ("_Finset" ("_args" x xs))
    ("\<^const>Set.insert" x "\<^const>Set.empty")  ->  ("_Finset" x)
    ("\<^const>Fun.fun_upd" f x y)  ->  ("_Update" f ("_updbind" x y))
    ("\<^const>List.filter" ("_abs" x P) xs)  ->  ("_filter" x xs P)
    ("\<^const>Set.Collect" ("_abs" x P))  ->  ("_Coll" x P)
    ("\<^const>Map.map_upds" m x y)  ->  ("_MapUpd" m ("_maplets" x y))
    ("\<^const>HOL.not_equal" ("\<^const>Set.range" f) "\<^const>Set.UNIV")  ->
      ("\<^const>HOL.Not" ("\<^const>Fun.surj" f))
    ("\<^const>List.list.Cons" x ("_list" xs))  ->  ("_list" ("_args" x xs))
    ("\<^const>List.list.Cons" x "\<^const>List.list.Nil")  ->  ("_list" x)
    ("\<^const>Filter.filterlim" ("_abs" x f) F2 F1)  ->  ("_LIM" x F1 f F2)
    ("\<^const>List.list_update" xs i x)  ->  ("_LUpdate" xs ("_lupdbind" i x))
    ("\<^const>Filter.eventually" ("_abs" x P) F)  ->  ("_eventually" x F P)
    ("\<^const>Filter.frequently" ("_abs" x P) F)  ->  ("_frequently" x F P)
    ("\<^const>Product_Type.Pair" x y)  ->  ("_tuple" x ("_tuple_arg" y))
    ("\<^const>Hilbert_Choice.Eps" ("_abs" x P))  ->  ("_Eps" x P)
    ("\<^const>Product_Type.Sigma" A ("_abs" x B))  ->  ("_Sigma" x A B)
    ("\<^const>Hilbert_Choice.LeastM" m ("_abs" x P))  ->  ("_LeastM" x m P)
    ("\<^const>Complete_Lattices.INTER" "\<^const>Set.UNIV" ("_abs" x B))  ->
      ("_INTER1" x B)
    ("\<^const>Complete_Lattices.INTER" A ("_abs" x B))  ->  ("_INTER" x A B)
    ("\<^const>Complete_Lattices.UNION" "\<^const>Set.UNIV" ("_abs" x B))  ->
      ("_UNION1" x B)
    ("\<^const>Complete_Lattices.UNION" A ("_abs" x B))  ->  ("_UNION" x A B)
    ("\<^const>Hilbert_Choice.GreatestM" m ("_abs" x P))  ->  ("_GreatestM" x m P)
    ("\<^const>Product_Type.prod.case_prod"
      ("_abs" x ("_abs" ("_pattern" y zs) b)))  ->
      ("_abs" ("_pattern" x ("_patterns" y zs)) b)
    ("\<^const>Product_Type.prod.case_prod" ("_abs" x ("_abs" y b)))  ->
      ("_abs" ("_pattern" x y) b)
    ("\<^const>BNF_Cardinal_Arithmetic.Csum" r ("_abs" i rs))  ->  ("_Csum" i r rs)
    ("\<^const>Complete_Lattices.Inf_class.INFIMUM" "\<^const>Set.UNIV"
      ("_abs" x B))  ->
      ("_INF1" x B)
    ("\<^const>Complete_Lattices.Inf_class.INFIMUM" A ("_abs" x B))  ->
      ("_INF" x A B)
    ("\<^const>Complete_Lattices.Sup_class.SUPREMUM" "\<^const>Set.UNIV"
      ("_abs" x B))  ->
      ("_SUP1" x B)
    ("\<^const>Complete_Lattices.Sup_class.SUPREMUM" A ("_abs" x B))  ->
      ("_SUP" x A B)
    ("\<^const>Groups_List.monoid_add_class.listsum"
      ("\<^const>List.list.map" ("_abs" x b) xs))  ->
      ("_listsum" x xs b)
    ("\<^const>Groups_List.monoid_mult_class.listprod"
      ("\<^const>List.list.map" ("_abs" x b) xs))  ->
      ("_listprod" x xs b)
    ("\<^const>Groups_Big.comm_monoid_add_class.setsum" ("_abs" x t)
      ("\<^const>Set_Interval.ord_class.atLeastAtMost" a b))  ->
      ("_from_to_setsum" x a b t)
    ("\<^const>Groups_Big.comm_monoid_add_class.setsum" ("_abs" x t)
      ("\<^const>Set_Interval.ord_class.atLeastLessThan" a b))  ->
      ("_from_upto_setsum" x a b t)
    ("\<^const>Groups_Big.comm_monoid_add_class.setsum" ("_abs" i t)
      ("\<^const>Set_Interval.ord_class.atMost" n))  ->
      ("_upto_setsum" i n t)
    ("\<^const>Groups_Big.comm_monoid_add_class.setsum" ("_abs" i t)
      ("\<^const>Set_Interval.ord_class.lessThan" n))  ->
      ("_upt_setsum" i n t)
    ("\<^const>Groups_Big.comm_monoid_add_class.setsum" ("_abs" i b) A)  ->
      ("_setsum" i A b)
    ("\<^const>Groups_Big.comm_monoid_mult_class.setprod" ("_abs" x t)
      ("\<^const>Set_Interval.ord_class.atLeastAtMost" a b))  ->
      ("_from_to_setprod" x a b t)
    ("\<^const>Groups_Big.comm_monoid_mult_class.setprod" ("_abs" x t)
      ("\<^const>Set_Interval.ord_class.atLeastLessThan" a b))  ->
      ("_from_upto_setprod" x a b t)
    ("\<^const>Groups_Big.comm_monoid_mult_class.setprod" ("_abs" i t)
      ("\<^const>Set_Interval.ord_class.atMost" n))  ->
      ("_upto_setprod" i n t)
    ("\<^const>Groups_Big.comm_monoid_mult_class.setprod" ("_abs" i t)
      ("\<^const>Set_Interval.ord_class.lessThan" n))  ->
      ("_upt_setprod" i n t)
    ("\<^const>Groups_Big.comm_monoid_mult_class.setprod" ("_abs" i b) A)  ->
      ("_setprod" i A b)
print_ast_translation: "\<^const>Pure.imp" "\<^const>String.char.Char"
  "\<^type>fun" "_abs" "_idts" "_index" "_list" "_pttrns" "_struct"