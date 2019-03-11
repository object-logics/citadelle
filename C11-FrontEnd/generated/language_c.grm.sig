structure MlyValue = 
struct
datatype svalue0 = VOID | ntVOID of unit | clangcversion of  (ClangCVersion) | x5f_x5f_builtin_types_compatible_p of  (string) | x5f_x5f_builtin_offsetof of  (string) | x5f_x5f_builtin_va_arg of  (string) | x5f_x5f_imag_x5f_x5f of  (string) | x5f_x5f_real_x5f_x5f of  (string) | x5f_x5f_extension_x5f_x5f of  (string) | x5f_x5f_attribute_x5f_x5f of  (string) | tyident of  (ident) | ident of  (ident) | cstr of  (cString) | cfloat of  (cFloat) | cint of  (cInteger) | cchar of  (cChar) | while0 of  (string) | volatile of  (string) | void of  (string) | unsigned of  (string) | union of  (string) | x5f_x5f_thread of  (string) | typeof of  (string) | typedef of  (string) | switch of  (string) | struct0 of  (string) | x5f_Static_assert of  (string) | static of  (string) | sizeof of  (string) | signed of  (string) | short of  (string) | return0 of  (string) | restrict of  (string) | register of  (string) | x5f_Nonnull of  (string) | x5f_Nullable of  (string) | x5f_Noreturn of  (string) | x5f_x5f_label_x5f_x5f of  (string) | long of  (string) | x5f_x5f_int_x31_x32_x38 of  (string) | int of  (string) | inline of  (string) | if0 of  (string) | goto of  (string) | x5f_Generic of  (string) | for0 of  (string) | float of  (string) | extern of  (string) | enum of  (string) | else0 of  (string) | double of  (string) | do0 of  (string) | default of  (string) | x5f_Complex of  (string) | continue of  (string) | const of  (string) | char of  (string) | case0 of  (string) | x5f_Bool of  (string) | break of  (string) | auto of  (string) | asm of  (string) | x5f_Atomic of  (string) | alignas of  (string) | alignof of  (string) | x2e_x2e_x2e of  (string) | x7d of  (string) | x7b of  (string) | x3b of  (string) | x2c of  (string) | x3e_x3e_x3d of  (string) | x3c_x3c_x3d of  (string) | x7c_x3d of  (string) | x5e_x3d of  (string) | x26_x3d of  (string) | x25_x3d of  (string) | x2f_x3d of  (string) | x2a_x3d of  (string) | x2d_x3d of  (string) | x2b_x3d of  (string) | x3d of  (string) | x3a of  (string) | x3f of  (string) | x7c_x7c of  (string) | x26_x26 of  (string) | x7c of  (string) | x5e of  (string) | x21_x3d of  (string) | x3d_x3d of  (string) | x3e_x3d of  (string) | x3e of  (string) | x3c_x3d of  (string) | x3c of  (string) | x3e_x3e of  (string) | x3c_x3c of  (string) | x26 of  (string) | x25 of  (string) | x2f of  (string) | x2a of  (string) | x2d of  (string) | x2b of  (string) | x2d_x2d of  (string) | x2b_x2b of  (string) | x7e of  (string) | x21 of  (string) | x2e of  (string) | x2d_x3e of  (string) | x5d of  (string) | x5b of  (string) | x29 of  (string) | x28 of  (string) | attribute_params of  ( ( CExpr list )  Reversed) | attribute of  (CAttr Maybe) | attribute_list of  ( ( CAttr list )  Reversed) | attr of  (CAttr list) | attrs of  (CAttr list) | attrs_opt of  (CAttr list) | identifier of  (Ident) | clang_version_literal of  (ClangCVersion) | string_literal_list of  ( ( CString list )  Reversed) | string_literal of  (CStrLit) | constant of  (CConst) | constant_expression of  (CExpr) | assignment_expression_opt of  (CExpr Maybe) | expression_opt of  (CExpr Maybe) | comma_expression of  ( ( CExpr list )  Reversed) | expression of  (CExpr) | assignment_operator of  (CAssignOp Located) | assignment_expression of  (CExpr) | conditional_expression of  (CExpr) | logical_or_expression of  (CExpr) | logical_and_expression of  (CExpr) | inclusive_or_expression of  (CExpr) | exclusive_or_expression of  (CExpr) | and_expression of  (CExpr) | equality_expression of  (CExpr) | relational_expression of  (CExpr) | shift_expression of  (CExpr) | additive_expression of  (CExpr) | multiplicative_expression of  (CExpr) | cast_expression of  (CExpr) | unary_operator of  (CUnaryOp Located) | unary_expression of  (CExpr) | argument_expression_list of  ( ( CExpr list )  Reversed) | postfix_expression of  (CExpr) | offsetof_member_designator of  ( ( CDesignator list )  Reversed) | generic_assoc of  ( ( CDecl Maybe * CExpr ) ) | generic_assoc_list of  ( ( ((CDecl Maybe * CExpr)) list )  Reversed) | primary_expression of  (CExpr) | array_designator of  (CDesignator) | designator of  (CDesignator) | designator_list of  ( ( CDesignator list )  Reversed) | designation of  (CDesignator list) | initializer_list of  (CInitList Reversed) | initializer_opt of  (CInit Maybe) | initializer of  (CInit) | postfix_abstract_declarator of  (CDeclrR) | unary_abstract_declarator of  (CDeclrR) | postfix_array_abstract_declarator of  ( ( CDeclrR -> CDeclrR ) ) | array_abstract_declarator of  ( ( CDeclrR -> CDeclrR ) ) | postfixing_abstract_declarator of  ( ( CDeclrR -> CDeclrR ) ) | abstract_declarator of  (CDeclrR) | type_name of  (CDecl) | identifier_list of  ( ( Ident list )  Reversed) | parameter_declaration of  (CDecl) | parameter_list of  ( ( CDecl list )  Reversed) | parameter_type_list of  ( ( CDecl list * Bool ) ) | postfix_old_function_declarator of  (CDeclrR) | old_function_declarator of  (CDeclrR) | function_declarator_old of  (CDeclr) | paren_identifier_declarator of  (CDeclrR) | postfix_identifier_declarator of  (CDeclrR) | unary_identifier_declarator of  (CDeclrR) | identifier_declarator of  (CDeclrR) | simple_paren_typedef_declarator of  (CDeclrR) | paren_postfix_typedef_declarator of  (CDeclrR) | paren_typedef_declarator of  (CDeclrR) | clean_postfix_typedef_declarator of  (CDeclrR) | clean_typedef_declarator of  (CDeclrR) | parameter_typedef_declarator of  (CDeclrR) | typedef_declarator of  (CDeclrR) | asm_opt of  (CStrLit Maybe) | declarator of  (CDeclrR) | type_qualifier_list of  ( ( CTypeQual list )  Reversed) | type_qualifier of  (CTypeQual) | enumerator of  ( ( Ident * CExpr Maybe ) ) | enumerator_list of  ( ( ((Ident * CExpr Maybe)) list )  Reversed) | enum_specifier of  (CEnum) | struct_identifier_declarator of  ( ( CDeclr Maybe * CExpr Maybe ) ) | struct_declarator of  ( ( CDeclr Maybe * CExpr Maybe ) ) | struct_declaring_list of  (CDecl) | struct_default_declaring_list of  (CDecl) | struct_declaration of  (CDecl) | struct_declaration_list of  ( ( CDecl list )  Reversed) | struct_or_union of  (CStructTag Located) | struct_or_union_specifier of  (CStructUnion) | elaborated_type_name of  (CTypeSpec) | typedef_type_specifier of  ( ( CDeclSpec list )  Reversed) | typedef_declaration_specifier of  ( ( CDeclSpec list )  Reversed) | sue_type_specifier of  ( ( CDeclSpec list )  Reversed) | sue_declaration_specifier of  ( ( CDeclSpec list )  Reversed) | basic_type_specifier of  ( ( CDeclSpec list )  Reversed) | basic_declaration_specifier of  ( ( CDeclSpec list )  Reversed) | basic_type_name of  (CTypeSpec) | type_specifier of  (CDeclSpec list) | alignment_specifier of  (CAlignSpec) | function_specifier of  (CFunSpec) | storage_class of  (CStorageSpec) | declaration_qualifier_without_types of  (CDeclSpec) | declaration_qualifier of  (CDeclSpec) | declaration_qualifier_list of  ( ( CDeclSpec list )  Reversed) | declaration_specifier of  (CDeclSpec list) | declaring_list of  (CDecl) | asm_attrs_opt of  ( ( CStrLit Maybe * CAttr list ) ) | default_declaring_list of  (CDecl) | declaration_list of  ( ( CDecl list )  Reversed) | declaration of  (CDecl) | asm_clobbers of  ( ( CStrLit list )  Reversed) | asm_operand of  (CAsmOperand) | nonnull_asm_operands of  ( ( CAsmOperand list )  Reversed) | asm_operands of  (CAsmOperand list) | maybe_type_qualifier of  (CTypeQual Maybe) | asm_statement of  (CAsmStmt) | jump_statement of  (CStat) | iteration_statement of  (CStat) | selection_statement of  (CStat) | expression_statement of  (CStat) | label_declarations of  ( ( Ident list )  Reversed) | nested_function_definition of  (CFunDef) | nested_declaration of  (CBlockItem) | block_item of  (CBlockItem) | block_item_list of  ( ( CBlockItem list )  Reversed) | leave_scope of  (unit) | enter_scope of  (unit) | compound_statement of  (CStat) | labeled_statement of  (CStat) | statement of  (CStat) | function_declarator of  (CDeclr) | function_definition of  (CFunDef) | external_declaration of  (CExtDecl) | ext_decl_list of  ( ( CExtDecl list )  Reversed) | translation_unit of  (CTranslUnit)
val type_reduce = fn
  0 => " (CTranslUnit)" |
  1 => " ( ( CExtDecl list )  Reversed)" |
  2 => " ( ( CExtDecl list )  Reversed)" |
  3 => " ( ( CExtDecl list )  Reversed)" |
  4 => " (CExtDecl)" |
  5 => " (CExtDecl)" |
  6 => " (CExtDecl)" |
  7 => " (CExtDecl)" |
  8 => " (CFunDef)" |
  9 => " (CFunDef)" |
  10 => " (CFunDef)" |
  11 => " (CFunDef)" |
  12 => " (CFunDef)" |
  13 => " (CFunDef)" |
  14 => " (CFunDef)" |
  15 => " (CFunDef)" |
  16 => " (CFunDef)" |
  17 => " (CFunDef)" |
  18 => " (CFunDef)" |
  19 => " (CFunDef)" |
  20 => " (CFunDef)" |
  21 => " (CFunDef)" |
  22 => " (CDeclr)" |
  23 => " (CStat)" |
  24 => " (CStat)" |
  25 => " (CStat)" |
  26 => " (CStat)" |
  27 => " (CStat)" |
  28 => " (CStat)" |
  29 => " (CStat)" |
  30 => " (CStat)" |
  31 => " (CStat)" |
  32 => " (CStat)" |
  33 => " (CStat)" |
  34 => " (CStat)" |
  35 => " (CStat)" |
  36 => " (unit)" |
  37 => " (unit)" |
  38 => " ( ( CBlockItem list )  Reversed)" |
  39 => " ( ( CBlockItem list )  Reversed)" |
  40 => " (CBlockItem)" |
  41 => " (CBlockItem)" |
  42 => " (CBlockItem)" |
  43 => " (CBlockItem)" |
  44 => " (CBlockItem)" |
  45 => " (CFunDef)" |
  46 => " (CFunDef)" |
  47 => " (CFunDef)" |
  48 => " (CFunDef)" |
  49 => " (CFunDef)" |
  50 => " ( ( Ident list )  Reversed)" |
  51 => " ( ( Ident list )  Reversed)" |
  52 => " (CStat)" |
  53 => " (CStat)" |
  54 => " (CStat)" |
  55 => " (CStat)" |
  56 => " (CStat)" |
  57 => " (CStat)" |
  58 => " (CStat)" |
  59 => " (CStat)" |
  60 => " (CStat)" |
  61 => " (CStat)" |
  62 => " (CStat)" |
  63 => " (CStat)" |
  64 => " (CStat)" |
  65 => " (CStat)" |
  66 => " (CAsmStmt)" |
  67 => " (CAsmStmt)" |
  68 => " (CAsmStmt)" |
  69 => " (CAsmStmt)" |
  70 => " (CTypeQual Maybe)" |
  71 => " (CTypeQual Maybe)" |
  72 => " (CAsmOperand list)" |
  73 => " (CAsmOperand list)" |
  74 => " ( ( CAsmOperand list )  Reversed)" |
  75 => " ( ( CAsmOperand list )  Reversed)" |
  76 => " (CAsmOperand)" |
  77 => " (CAsmOperand)" |
  78 => " (CAsmOperand)" |
  79 => " ( ( CStrLit list )  Reversed)" |
  80 => " ( ( CStrLit list )  Reversed)" |
  81 => " (CDecl)" |
  82 => " (CDecl)" |
  83 => " (CDecl)" |
  84 => " (CDecl)" |
  85 => " (CDecl)" |
  86 => " ( ( CDecl list )  Reversed)" |
  87 => " ( ( CDecl list )  Reversed)" |
  88 => " (CDecl)" |
  89 => " (CDecl)" |
  90 => " (CDecl)" |
  91 => " (CDecl)" |
  92 => " (CDecl)" |
  93 => " ( ( CStrLit Maybe * CAttr list ) )" |
  94 => " (CDecl)" |
  95 => " (CDecl)" |
  96 => " (CDecl)" |
  97 => " (CDeclSpec list)" |
  98 => " (CDeclSpec list)" |
  99 => " (CDeclSpec list)" |
  100 => " ( ( CDeclSpec list )  Reversed)" |
  101 => " ( ( CDeclSpec list )  Reversed)" |
  102 => " ( ( CDeclSpec list )  Reversed)" |
  103 => " ( ( CDeclSpec list )  Reversed)" |
  104 => " ( ( CDeclSpec list )  Reversed)" |
  105 => " ( ( CDeclSpec list )  Reversed)" |
  106 => " (CDeclSpec)" |
  107 => " (CDeclSpec)" |
  108 => " (CDeclSpec)" |
  109 => " (CDeclSpec)" |
  110 => " (CDeclSpec)" |
  111 => " (CDeclSpec)" |
  112 => " (CDeclSpec)" |
  113 => " (CStorageSpec)" |
  114 => " (CStorageSpec)" |
  115 => " (CStorageSpec)" |
  116 => " (CStorageSpec)" |
  117 => " (CStorageSpec)" |
  118 => " (CStorageSpec)" |
  119 => " (CFunSpec)" |
  120 => " (CFunSpec)" |
  121 => " (CAlignSpec)" |
  122 => " (CAlignSpec)" |
  123 => " (CDeclSpec list)" |
  124 => " (CDeclSpec list)" |
  125 => " (CDeclSpec list)" |
  126 => " (CTypeSpec)" |
  127 => " (CTypeSpec)" |
  128 => " (CTypeSpec)" |
  129 => " (CTypeSpec)" |
  130 => " (CTypeSpec)" |
  131 => " (CTypeSpec)" |
  132 => " (CTypeSpec)" |
  133 => " (CTypeSpec)" |
  134 => " (CTypeSpec)" |
  135 => " (CTypeSpec)" |
  136 => " (CTypeSpec)" |
  137 => " (CTypeSpec)" |
  138 => " ( ( CDeclSpec list )  Reversed)" |
  139 => " ( ( CDeclSpec list )  Reversed)" |
  140 => " ( ( CDeclSpec list )  Reversed)" |
  141 => " ( ( CDeclSpec list )  Reversed)" |
  142 => " ( ( CDeclSpec list )  Reversed)" |
  143 => " ( ( CDeclSpec list )  Reversed)" |
  144 => " ( ( CDeclSpec list )  Reversed)" |
  145 => " ( ( CDeclSpec list )  Reversed)" |
  146 => " ( ( CDeclSpec list )  Reversed)" |
  147 => " ( ( CDeclSpec list )  Reversed)" |
  148 => " ( ( CDeclSpec list )  Reversed)" |
  149 => " ( ( CDeclSpec list )  Reversed)" |
  150 => " ( ( CDeclSpec list )  Reversed)" |
  151 => " ( ( CDeclSpec list )  Reversed)" |
  152 => " ( ( CDeclSpec list )  Reversed)" |
  153 => " ( ( CDeclSpec list )  Reversed)" |
  154 => " ( ( CDeclSpec list )  Reversed)" |
  155 => " ( ( CDeclSpec list )  Reversed)" |
  156 => " ( ( CDeclSpec list )  Reversed)" |
  157 => " ( ( CDeclSpec list )  Reversed)" |
  158 => " ( ( CDeclSpec list )  Reversed)" |
  159 => " ( ( CDeclSpec list )  Reversed)" |
  160 => " ( ( CDeclSpec list )  Reversed)" |
  161 => " ( ( CDeclSpec list )  Reversed)" |
  162 => " ( ( CDeclSpec list )  Reversed)" |
  163 => " ( ( CDeclSpec list )  Reversed)" |
  164 => " ( ( CDeclSpec list )  Reversed)" |
  165 => " ( ( CDeclSpec list )  Reversed)" |
  166 => " ( ( CDeclSpec list )  Reversed)" |
  167 => " ( ( CDeclSpec list )  Reversed)" |
  168 => " ( ( CDeclSpec list )  Reversed)" |
  169 => " ( ( CDeclSpec list )  Reversed)" |
  170 => " ( ( CDeclSpec list )  Reversed)" |
  171 => " ( ( CDeclSpec list )  Reversed)" |
  172 => " ( ( CDeclSpec list )  Reversed)" |
  173 => " ( ( CDeclSpec list )  Reversed)" |
  174 => " ( ( CDeclSpec list )  Reversed)" |
  175 => " ( ( CDeclSpec list )  Reversed)" |
  176 => " ( ( CDeclSpec list )  Reversed)" |
  177 => " ( ( CDeclSpec list )  Reversed)" |
  178 => " ( ( CDeclSpec list )  Reversed)" |
  179 => " ( ( CDeclSpec list )  Reversed)" |
  180 => " (CTypeSpec)" |
  181 => " (CTypeSpec)" |
  182 => " (CStructUnion)" |
  183 => " (CStructUnion)" |
  184 => " (CStructUnion)" |
  185 => " (CStructTag Located)" |
  186 => " (CStructTag Located)" |
  187 => " ( ( CDecl list )  Reversed)" |
  188 => " ( ( CDecl list )  Reversed)" |
  189 => " ( ( CDecl list )  Reversed)" |
  190 => " (CDecl)" |
  191 => " (CDecl)" |
  192 => " (CDecl)" |
  193 => " (CDecl)" |
  194 => " (CDecl)" |
  195 => " (CDecl)" |
  196 => " (CDecl)" |
  197 => " (CDecl)" |
  198 => " (CDecl)" |
  199 => " ( ( CDeclr Maybe * CExpr Maybe ) )" |
  200 => " ( ( CDeclr Maybe * CExpr Maybe ) )" |
  201 => " ( ( CDeclr Maybe * CExpr Maybe ) )" |
  202 => " ( ( CDeclr Maybe * CExpr Maybe ) )" |
  203 => " ( ( CDeclr Maybe * CExpr Maybe ) )" |
  204 => " ( ( CDeclr Maybe * CExpr Maybe ) )" |
  205 => " ( ( CDeclr Maybe * CExpr Maybe ) )" |
  206 => " (CEnum)" |
  207 => " (CEnum)" |
  208 => " (CEnum)" |
  209 => " (CEnum)" |
  210 => " (CEnum)" |
  211 => " ( ( ((Ident * CExpr Maybe)) list )  Reversed)" |
  212 => " ( ( ((Ident * CExpr Maybe)) list )  Reversed)" |
  213 => " ( ( Ident * CExpr Maybe ) )" |
  214 => " ( ( Ident * CExpr Maybe ) )" |
  215 => " ( ( Ident * CExpr Maybe ) )" |
  216 => " ( ( Ident * CExpr Maybe ) )" |
  217 => " (CTypeQual)" |
  218 => " (CTypeQual)" |
  219 => " (CTypeQual)" |
  220 => " (CTypeQual)" |
  221 => " (CTypeQual)" |
  222 => " (CTypeQual)" |
  223 => " ( ( CTypeQual list )  Reversed)" |
  224 => " ( ( CTypeQual list )  Reversed)" |
  225 => " ( ( CTypeQual list )  Reversed)" |
  226 => " (CDeclrR)" |
  227 => " (CDeclrR)" |
  228 => " (CStrLit Maybe)" |
  229 => " (CStrLit Maybe)" |
  230 => " (CDeclrR)" |
  231 => " (CDeclrR)" |
  232 => " (CDeclrR)" |
  233 => " (CDeclrR)" |
  234 => " (CDeclrR)" |
  235 => " (CDeclrR)" |
  236 => " (CDeclrR)" |
  237 => " (CDeclrR)" |
  238 => " (CDeclrR)" |
  239 => " (CDeclrR)" |
  240 => " (CDeclrR)" |
  241 => " (CDeclrR)" |
  242 => " (CDeclrR)" |
  243 => " (CDeclrR)" |
  244 => " (CDeclrR)" |
  245 => " (CDeclrR)" |
  246 => " (CDeclrR)" |
  247 => " (CDeclrR)" |
  248 => " (CDeclrR)" |
  249 => " (CDeclrR)" |
  250 => " (CDeclrR)" |
  251 => " (CDeclrR)" |
  252 => " (CDeclrR)" |
  253 => " (CDeclrR)" |
  254 => " (CDeclrR)" |
  255 => " (CDeclrR)" |
  256 => " (CDeclrR)" |
  257 => " (CDeclrR)" |
  258 => " (CDeclrR)" |
  259 => " (CDeclrR)" |
  260 => " (CDeclrR)" |
  261 => " (CDeclrR)" |
  262 => " (CDeclrR)" |
  263 => " (CDeclrR)" |
  264 => " (CDeclrR)" |
  265 => " (CDeclrR)" |
  266 => " (CDeclrR)" |
  267 => " (CDeclrR)" |
  268 => " (CDeclrR)" |
  269 => " (CDeclrR)" |
  270 => " (CDeclrR)" |
  271 => " (CDeclr)" |
  272 => " (CDeclrR)" |
  273 => " (CDeclrR)" |
  274 => " (CDeclrR)" |
  275 => " (CDeclrR)" |
  276 => " (CDeclrR)" |
  277 => " (CDeclrR)" |
  278 => " ( ( CDecl list * Bool ) )" |
  279 => " ( ( CDecl list * Bool ) )" |
  280 => " ( ( CDecl list * Bool ) )" |
  281 => " ( ( CDecl list )  Reversed)" |
  282 => " ( ( CDecl list )  Reversed)" |
  283 => " (CDecl)" |
  284 => " (CDecl)" |
  285 => " (CDecl)" |
  286 => " (CDecl)" |
  287 => " (CDecl)" |
  288 => " (CDecl)" |
  289 => " (CDecl)" |
  290 => " (CDecl)" |
  291 => " (CDecl)" |
  292 => " (CDecl)" |
  293 => " (CDecl)" |
  294 => " (CDecl)" |
  295 => " (CDecl)" |
  296 => " (CDecl)" |
  297 => " (CDecl)" |
  298 => " ( ( Ident list )  Reversed)" |
  299 => " ( ( Ident list )  Reversed)" |
  300 => " (CDecl)" |
  301 => " (CDecl)" |
  302 => " (CDecl)" |
  303 => " (CDecl)" |
  304 => " (CDeclrR)" |
  305 => " (CDeclrR)" |
  306 => " (CDeclrR)" |
  307 => " ( ( CDeclrR -> CDeclrR ) )" |
  308 => " ( ( CDeclrR -> CDeclrR ) )" |
  309 => " ( ( CDeclrR -> CDeclrR ) )" |
  310 => " ( ( CDeclrR -> CDeclrR ) )" |
  311 => " ( ( CDeclrR -> CDeclrR ) )" |
  312 => " ( ( CDeclrR -> CDeclrR ) )" |
  313 => " ( ( CDeclrR -> CDeclrR ) )" |
  314 => " ( ( CDeclrR -> CDeclrR ) )" |
  315 => " ( ( CDeclrR -> CDeclrR ) )" |
  316 => " ( ( CDeclrR -> CDeclrR ) )" |
  317 => " ( ( CDeclrR -> CDeclrR ) )" |
  318 => " ( ( CDeclrR -> CDeclrR ) )" |
  319 => " ( ( CDeclrR -> CDeclrR ) )" |
  320 => " ( ( CDeclrR -> CDeclrR ) )" |
  321 => " ( ( CDeclrR -> CDeclrR ) )" |
  322 => " (CDeclrR)" |
  323 => " (CDeclrR)" |
  324 => " (CDeclrR)" |
  325 => " (CDeclrR)" |
  326 => " (CDeclrR)" |
  327 => " (CDeclrR)" |
  328 => " (CDeclrR)" |
  329 => " (CDeclrR)" |
  330 => " (CDeclrR)" |
  331 => " (CDeclrR)" |
  332 => " (CDeclrR)" |
  333 => " (CDeclrR)" |
  334 => " (CDeclrR)" |
  335 => " (CDeclrR)" |
  336 => " (CDeclrR)" |
  337 => " (CInit)" |
  338 => " (CInit)" |
  339 => " (CInit)" |
  340 => " (CInit Maybe)" |
  341 => " (CInit Maybe)" |
  342 => " (CInitList Reversed)" |
  343 => " (CInitList Reversed)" |
  344 => " (CInitList Reversed)" |
  345 => " (CInitList Reversed)" |
  346 => " (CInitList Reversed)" |
  347 => " (CDesignator list)" |
  348 => " (CDesignator list)" |
  349 => " (CDesignator list)" |
  350 => " ( ( CDesignator list )  Reversed)" |
  351 => " ( ( CDesignator list )  Reversed)" |
  352 => " (CDesignator)" |
  353 => " (CDesignator)" |
  354 => " (CDesignator)" |
  355 => " (CDesignator)" |
  356 => " (CExpr)" |
  357 => " (CExpr)" |
  358 => " (CExpr)" |
  359 => " (CExpr)" |
  360 => " (CExpr)" |
  361 => " (CExpr)" |
  362 => " (CExpr)" |
  363 => " (CExpr)" |
  364 => " (CExpr)" |
  365 => " ( ( ((CDecl Maybe * CExpr)) list )  Reversed)" |
  366 => " ( ( ((CDecl Maybe * CExpr)) list )  Reversed)" |
  367 => " ( ( CDecl Maybe * CExpr ) )" |
  368 => " ( ( CDecl Maybe * CExpr ) )" |
  369 => " ( ( CDesignator list )  Reversed)" |
  370 => " ( ( CDesignator list )  Reversed)" |
  371 => " ( ( CDesignator list )  Reversed)" |
  372 => " (CExpr)" |
  373 => " (CExpr)" |
  374 => " (CExpr)" |
  375 => " (CExpr)" |
  376 => " (CExpr)" |
  377 => " (CExpr)" |
  378 => " (CExpr)" |
  379 => " (CExpr)" |
  380 => " (CExpr)" |
  381 => " (CExpr)" |
  382 => " ( ( CExpr list )  Reversed)" |
  383 => " ( ( CExpr list )  Reversed)" |
  384 => " (CExpr)" |
  385 => " (CExpr)" |
  386 => " (CExpr)" |
  387 => " (CExpr)" |
  388 => " (CExpr)" |
  389 => " (CExpr)" |
  390 => " (CExpr)" |
  391 => " (CExpr)" |
  392 => " (CExpr)" |
  393 => " (CExpr)" |
  394 => " (CExpr)" |
  395 => " (CExpr)" |
  396 => " (CUnaryOp Located)" |
  397 => " (CUnaryOp Located)" |
  398 => " (CUnaryOp Located)" |
  399 => " (CUnaryOp Located)" |
  400 => " (CUnaryOp Located)" |
  401 => " (CUnaryOp Located)" |
  402 => " (CExpr)" |
  403 => " (CExpr)" |
  404 => " (CExpr)" |
  405 => " (CExpr)" |
  406 => " (CExpr)" |
  407 => " (CExpr)" |
  408 => " (CExpr)" |
  409 => " (CExpr)" |
  410 => " (CExpr)" |
  411 => " (CExpr)" |
  412 => " (CExpr)" |
  413 => " (CExpr)" |
  414 => " (CExpr)" |
  415 => " (CExpr)" |
  416 => " (CExpr)" |
  417 => " (CExpr)" |
  418 => " (CExpr)" |
  419 => " (CExpr)" |
  420 => " (CExpr)" |
  421 => " (CExpr)" |
  422 => " (CExpr)" |
  423 => " (CExpr)" |
  424 => " (CExpr)" |
  425 => " (CExpr)" |
  426 => " (CExpr)" |
  427 => " (CExpr)" |
  428 => " (CExpr)" |
  429 => " (CExpr)" |
  430 => " (CExpr)" |
  431 => " (CExpr)" |
  432 => " (CExpr)" |
  433 => " (CExpr)" |
  434 => " (CExpr)" |
  435 => " (CExpr)" |
  436 => " (CExpr)" |
  437 => " (CAssignOp Located)" |
  438 => " (CAssignOp Located)" |
  439 => " (CAssignOp Located)" |
  440 => " (CAssignOp Located)" |
  441 => " (CAssignOp Located)" |
  442 => " (CAssignOp Located)" |
  443 => " (CAssignOp Located)" |
  444 => " (CAssignOp Located)" |
  445 => " (CAssignOp Located)" |
  446 => " (CAssignOp Located)" |
  447 => " (CAssignOp Located)" |
  448 => " (CExpr)" |
  449 => " (CExpr)" |
  450 => " ( ( CExpr list )  Reversed)" |
  451 => " ( ( CExpr list )  Reversed)" |
  452 => " (CExpr Maybe)" |
  453 => " (CExpr Maybe)" |
  454 => " (CExpr Maybe)" |
  455 => " (CExpr Maybe)" |
  456 => " (CExpr)" |
  457 => " (CConst)" |
  458 => " (CConst)" |
  459 => " (CConst)" |
  460 => " (CStrLit)" |
  461 => " (CStrLit)" |
  462 => " ( ( CString list )  Reversed)" |
  463 => " ( ( CString list )  Reversed)" |
  464 => " (ClangCVersion)" |
  465 => " (Ident)" |
  466 => " (Ident)" |
  467 => " (CAttr list)" |
  468 => " (CAttr list)" |
  469 => " (CAttr list)" |
  470 => " (CAttr list)" |
  471 => " (CAttr list)" |
  472 => " ( ( CAttr list )  Reversed)" |
  473 => " ( ( CAttr list )  Reversed)" |
  474 => " (CAttr Maybe)" |
  475 => " (CAttr Maybe)" |
  476 => " (CAttr Maybe)" |
  477 => " (CAttr Maybe)" |
  478 => " (CAttr Maybe)" |
  479 => " ( ( CExpr list )  Reversed)" |
  480 => " ( ( CExpr list )  Reversed)" |
  481 => " ( ( CExpr list )  Reversed)" |
  482 => " ( ( CExpr list )  Reversed)" |
  483 => " ( ( CExpr list )  Reversed)" |
  484 => " ( ( CExpr list )  Reversed)" |
  _ => error "reduce type not found"
val string_reduce = fn
  0 => "translation_unit" |
  1 => "ext_decl_list1" |
  2 => "ext_decl_list2" |
  3 => "ext_decl_list3" |
  4 => "external_declaration1" |
  5 => "external_declaration2" |
  6 => "external_declaration3" |
  7 => "external_declaration4" |
  8 => "function_definition1" |
  9 => "function_definition2" |
  10 => "function_definition3" |
  11 => "function_definition4" |
  12 => "function_definition5" |
  13 => "function_definition6" |
  14 => "function_definition7" |
  15 => "function_definition8" |
  16 => "function_definition9" |
  17 => "function_definition10" |
  18 => "function_definition11" |
  19 => "function_definition12" |
  20 => "function_definition13" |
  21 => "function_definition14" |
  22 => "function_declarator" |
  23 => "statement1" |
  24 => "statement2" |
  25 => "statement3" |
  26 => "statement4" |
  27 => "statement5" |
  28 => "statement6" |
  29 => "statement7" |
  30 => "labeled_statement1" |
  31 => "labeled_statement2" |
  32 => "labeled_statement3" |
  33 => "labeled_statement4" |
  34 => "compound_statement1" |
  35 => "compound_statement2" |
  36 => "enter_scope" |
  37 => "leave_scope" |
  38 => "block_item_list1" |
  39 => "block_item_list2" |
  40 => "block_item1" |
  41 => "block_item2" |
  42 => "nested_declaration1" |
  43 => "nested_declaration2" |
  44 => "nested_declaration3" |
  45 => "nested_function_definition1" |
  46 => "nested_function_definition2" |
  47 => "nested_function_definition3" |
  48 => "nested_function_definition4" |
  49 => "nested_function_definition5" |
  50 => "label_declarations1" |
  51 => "label_declarations2" |
  52 => "expression_statement1" |
  53 => "expression_statement2" |
  54 => "selection_statement1" |
  55 => "selection_statement2" |
  56 => "selection_statement3" |
  57 => "iteration_statement1" |
  58 => "iteration_statement2" |
  59 => "iteration_statement3" |
  60 => "iteration_statement4" |
  61 => "jump_statement1" |
  62 => "jump_statement2" |
  63 => "jump_statement3" |
  64 => "jump_statement4" |
  65 => "jump_statement5" |
  66 => "asm_statement1" |
  67 => "asm_statement2" |
  68 => "asm_statement3" |
  69 => "asm_statement4" |
  70 => "maybe_type_qualifier1" |
  71 => "maybe_type_qualifier2" |
  72 => "asm_operands1" |
  73 => "asm_operands2" |
  74 => "nonnull_asm_operands1" |
  75 => "nonnull_asm_operands2" |
  76 => "asm_operand1" |
  77 => "asm_operand2" |
  78 => "asm_operand3" |
  79 => "asm_clobbers1" |
  80 => "asm_clobbers2" |
  81 => "declaration1" |
  82 => "declaration2" |
  83 => "declaration3" |
  84 => "declaration4" |
  85 => "declaration5" |
  86 => "declaration_list1" |
  87 => "declaration_list2" |
  88 => "default_declaring_list1" |
  89 => "default_declaring_list2" |
  90 => "default_declaring_list3" |
  91 => "default_declaring_list4" |
  92 => "default_declaring_list5" |
  93 => "asm_attrs_opt" |
  94 => "declaring_list1" |
  95 => "declaring_list2" |
  96 => "declaring_list3" |
  97 => "declaration_specifier1" |
  98 => "declaration_specifier2" |
  99 => "declaration_specifier3" |
  100 => "declaration_qualifier_list1" |
  101 => "declaration_qualifier_list2" |
  102 => "declaration_qualifier_list3" |
  103 => "declaration_qualifier_list4" |
  104 => "declaration_qualifier_list5" |
  105 => "declaration_qualifier_list6" |
  106 => "declaration_qualifier1" |
  107 => "declaration_qualifier2" |
  108 => "declaration_qualifier3" |
  109 => "declaration_qualifier4" |
  110 => "declaration_qualifier_without_types1" |
  111 => "declaration_qualifier_without_types2" |
  112 => "declaration_qualifier_without_types3" |
  113 => "storage_class1" |
  114 => "storage_class2" |
  115 => "storage_class3" |
  116 => "storage_class4" |
  117 => "storage_class5" |
  118 => "storage_class6" |
  119 => "function_specifier1" |
  120 => "function_specifier2" |
  121 => "alignment_specifier1" |
  122 => "alignment_specifier2" |
  123 => "type_specifier1" |
  124 => "type_specifier2" |
  125 => "type_specifier3" |
  126 => "basic_type_name1" |
  127 => "basic_type_name2" |
  128 => "basic_type_name3" |
  129 => "basic_type_name4" |
  130 => "basic_type_name5" |
  131 => "basic_type_name6" |
  132 => "basic_type_name7" |
  133 => "basic_type_name8" |
  134 => "basic_type_name9" |
  135 => "basic_type_name10" |
  136 => "basic_type_name11" |
  137 => "basic_type_name12" |
  138 => "basic_declaration_specifier1" |
  139 => "basic_declaration_specifier2" |
  140 => "basic_declaration_specifier3" |
  141 => "basic_declaration_specifier4" |
  142 => "basic_declaration_specifier5" |
  143 => "basic_type_specifier1" |
  144 => "basic_type_specifier2" |
  145 => "basic_type_specifier3" |
  146 => "basic_type_specifier4" |
  147 => "basic_type_specifier5" |
  148 => "basic_type_specifier6" |
  149 => "basic_type_specifier7" |
  150 => "sue_declaration_specifier1" |
  151 => "sue_declaration_specifier2" |
  152 => "sue_declaration_specifier3" |
  153 => "sue_declaration_specifier4" |
  154 => "sue_type_specifier1" |
  155 => "sue_type_specifier2" |
  156 => "sue_type_specifier3" |
  157 => "sue_type_specifier4" |
  158 => "sue_type_specifier5" |
  159 => "sue_type_specifier6" |
  160 => "typedef_declaration_specifier1" |
  161 => "typedef_declaration_specifier2" |
  162 => "typedef_declaration_specifier3" |
  163 => "typedef_declaration_specifier4" |
  164 => "typedef_declaration_specifier5" |
  165 => "typedef_declaration_specifier6" |
  166 => "typedef_type_specifier1" |
  167 => "typedef_type_specifier2" |
  168 => "typedef_type_specifier3" |
  169 => "typedef_type_specifier4" |
  170 => "typedef_type_specifier5" |
  171 => "typedef_type_specifier6" |
  172 => "typedef_type_specifier7" |
  173 => "typedef_type_specifier8" |
  174 => "typedef_type_specifier9" |
  175 => "typedef_type_specifier10" |
  176 => "typedef_type_specifier11" |
  177 => "typedef_type_specifier12" |
  178 => "typedef_type_specifier13" |
  179 => "typedef_type_specifier14" |
  180 => "elaborated_type_name1" |
  181 => "elaborated_type_name2" |
  182 => "struct_or_union_specifier1" |
  183 => "struct_or_union_specifier2" |
  184 => "struct_or_union_specifier3" |
  185 => "struct_or_union1" |
  186 => "struct_or_union2" |
  187 => "struct_declaration_list1" |
  188 => "struct_declaration_list2" |
  189 => "struct_declaration_list3" |
  190 => "struct_declaration1" |
  191 => "struct_declaration2" |
  192 => "struct_declaration3" |
  193 => "struct_default_declaring_list1" |
  194 => "struct_default_declaring_list2" |
  195 => "struct_default_declaring_list3" |
  196 => "struct_declaring_list1" |
  197 => "struct_declaring_list2" |
  198 => "struct_declaring_list3" |
  199 => "struct_declarator1" |
  200 => "struct_declarator2" |
  201 => "struct_declarator3" |
  202 => "struct_identifier_declarator1" |
  203 => "struct_identifier_declarator2" |
  204 => "struct_identifier_declarator3" |
  205 => "struct_identifier_declarator4" |
  206 => "enum_specifier1" |
  207 => "enum_specifier2" |
  208 => "enum_specifier3" |
  209 => "enum_specifier4" |
  210 => "enum_specifier5" |
  211 => "enumerator_list1" |
  212 => "enumerator_list2" |
  213 => "enumerator1" |
  214 => "enumerator2" |
  215 => "enumerator3" |
  216 => "enumerator4" |
  217 => "type_qualifier1" |
  218 => "type_qualifier2" |
  219 => "type_qualifier3" |
  220 => "type_qualifier4" |
  221 => "type_qualifier5" |
  222 => "type_qualifier6" |
  223 => "type_qualifier_list1" |
  224 => "type_qualifier_list2" |
  225 => "type_qualifier_list3" |
  226 => "declarator1" |
  227 => "declarator2" |
  228 => "asm_opt1" |
  229 => "asm_opt2" |
  230 => "typedef_declarator1" |
  231 => "typedef_declarator2" |
  232 => "parameter_typedef_declarator1" |
  233 => "parameter_typedef_declarator2" |
  234 => "parameter_typedef_declarator3" |
  235 => "clean_typedef_declarator1" |
  236 => "clean_typedef_declarator2" |
  237 => "clean_typedef_declarator3" |
  238 => "clean_typedef_declarator4" |
  239 => "clean_typedef_declarator5" |
  240 => "clean_postfix_typedef_declarator1" |
  241 => "clean_postfix_typedef_declarator2" |
  242 => "clean_postfix_typedef_declarator3" |
  243 => "clean_postfix_typedef_declarator4" |
  244 => "paren_typedef_declarator1" |
  245 => "paren_typedef_declarator2" |
  246 => "paren_typedef_declarator3" |
  247 => "paren_typedef_declarator4" |
  248 => "paren_typedef_declarator5" |
  249 => "paren_typedef_declarator6" |
  250 => "paren_typedef_declarator7" |
  251 => "paren_postfix_typedef_declarator1" |
  252 => "paren_postfix_typedef_declarator2" |
  253 => "paren_postfix_typedef_declarator3" |
  254 => "simple_paren_typedef_declarator1" |
  255 => "simple_paren_typedef_declarator2" |
  256 => "identifier_declarator1" |
  257 => "identifier_declarator2" |
  258 => "unary_identifier_declarator1" |
  259 => "unary_identifier_declarator2" |
  260 => "unary_identifier_declarator3" |
  261 => "unary_identifier_declarator4" |
  262 => "unary_identifier_declarator5" |
  263 => "postfix_identifier_declarator1" |
  264 => "postfix_identifier_declarator2" |
  265 => "postfix_identifier_declarator3" |
  266 => "postfix_identifier_declarator4" |
  267 => "postfix_identifier_declarator5" |
  268 => "paren_identifier_declarator1" |
  269 => "paren_identifier_declarator2" |
  270 => "paren_identifier_declarator3" |
  271 => "function_declarator_old" |
  272 => "old_function_declarator1" |
  273 => "old_function_declarator2" |
  274 => "old_function_declarator3" |
  275 => "postfix_old_function_declarator1" |
  276 => "postfix_old_function_declarator2" |
  277 => "postfix_old_function_declarator3" |
  278 => "parameter_type_list1" |
  279 => "parameter_type_list2" |
  280 => "parameter_type_list3" |
  281 => "parameter_list1" |
  282 => "parameter_list2" |
  283 => "parameter_declaration1" |
  284 => "parameter_declaration2" |
  285 => "parameter_declaration3" |
  286 => "parameter_declaration4" |
  287 => "parameter_declaration5" |
  288 => "parameter_declaration6" |
  289 => "parameter_declaration7" |
  290 => "parameter_declaration8" |
  291 => "parameter_declaration9" |
  292 => "parameter_declaration10" |
  293 => "parameter_declaration11" |
  294 => "parameter_declaration12" |
  295 => "parameter_declaration13" |
  296 => "parameter_declaration14" |
  297 => "parameter_declaration15" |
  298 => "identifier_list1" |
  299 => "identifier_list2" |
  300 => "type_name1" |
  301 => "type_name2" |
  302 => "type_name3" |
  303 => "type_name4" |
  304 => "abstract_declarator1" |
  305 => "abstract_declarator2" |
  306 => "abstract_declarator3" |
  307 => "postfixing_abstract_declarator1" |
  308 => "postfixing_abstract_declarator2" |
  309 => "array_abstract_declarator1" |
  310 => "array_abstract_declarator2" |
  311 => "postfix_array_abstract_declarator1" |
  312 => "postfix_array_abstract_declarator2" |
  313 => "postfix_array_abstract_declarator3" |
  314 => "postfix_array_abstract_declarator4" |
  315 => "postfix_array_abstract_declarator5" |
  316 => "postfix_array_abstract_declarator6" |
  317 => "postfix_array_abstract_declarator7" |
  318 => "postfix_array_abstract_declarator8" |
  319 => "postfix_array_abstract_declarator9" |
  320 => "postfix_array_abstract_declarator10" |
  321 => "postfix_array_abstract_declarator11" |
  322 => "unary_abstract_declarator1" |
  323 => "unary_abstract_declarator2" |
  324 => "unary_abstract_declarator3" |
  325 => "unary_abstract_declarator4" |
  326 => "unary_abstract_declarator5" |
  327 => "unary_abstract_declarator6" |
  328 => "postfix_abstract_declarator1" |
  329 => "postfix_abstract_declarator2" |
  330 => "postfix_abstract_declarator3" |
  331 => "postfix_abstract_declarator4" |
  332 => "postfix_abstract_declarator5" |
  333 => "postfix_abstract_declarator6" |
  334 => "postfix_abstract_declarator7" |
  335 => "postfix_abstract_declarator8" |
  336 => "postfix_abstract_declarator9" |
  337 => "initializer1" |
  338 => "initializer2" |
  339 => "initializer3" |
  340 => "initializer_opt1" |
  341 => "initializer_opt2" |
  342 => "initializer_list1" |
  343 => "initializer_list2" |
  344 => "initializer_list3" |
  345 => "initializer_list4" |
  346 => "initializer_list5" |
  347 => "designation1" |
  348 => "designation2" |
  349 => "designation3" |
  350 => "designator_list1" |
  351 => "designator_list2" |
  352 => "designator1" |
  353 => "designator2" |
  354 => "designator3" |
  355 => "array_designator" |
  356 => "primary_expression1" |
  357 => "primary_expression2" |
  358 => "primary_expression3" |
  359 => "primary_expression4" |
  360 => "primary_expression5" |
  361 => "primary_expression6" |
  362 => "primary_expression7" |
  363 => "primary_expression8" |
  364 => "primary_expression9" |
  365 => "generic_assoc_list1" |
  366 => "generic_assoc_list2" |
  367 => "generic_assoc1" |
  368 => "generic_assoc2" |
  369 => "offsetof_member_designator1" |
  370 => "offsetof_member_designator2" |
  371 => "offsetof_member_designator3" |
  372 => "postfix_expression1" |
  373 => "postfix_expression2" |
  374 => "postfix_expression3" |
  375 => "postfix_expression4" |
  376 => "postfix_expression5" |
  377 => "postfix_expression6" |
  378 => "postfix_expression7" |
  379 => "postfix_expression8" |
  380 => "postfix_expression9" |
  381 => "postfix_expression10" |
  382 => "argument_expression_list1" |
  383 => "argument_expression_list2" |
  384 => "unary_expression1" |
  385 => "unary_expression2" |
  386 => "unary_expression3" |
  387 => "unary_expression4" |
  388 => "unary_expression5" |
  389 => "unary_expression6" |
  390 => "unary_expression7" |
  391 => "unary_expression8" |
  392 => "unary_expression9" |
  393 => "unary_expression10" |
  394 => "unary_expression11" |
  395 => "unary_expression12" |
  396 => "unary_operator1" |
  397 => "unary_operator2" |
  398 => "unary_operator3" |
  399 => "unary_operator4" |
  400 => "unary_operator5" |
  401 => "unary_operator6" |
  402 => "cast_expression1" |
  403 => "cast_expression2" |
  404 => "multiplicative_expression1" |
  405 => "multiplicative_expression2" |
  406 => "multiplicative_expression3" |
  407 => "multiplicative_expression4" |
  408 => "additive_expression1" |
  409 => "additive_expression2" |
  410 => "additive_expression3" |
  411 => "shift_expression1" |
  412 => "shift_expression2" |
  413 => "shift_expression3" |
  414 => "relational_expression1" |
  415 => "relational_expression2" |
  416 => "relational_expression3" |
  417 => "relational_expression4" |
  418 => "relational_expression5" |
  419 => "equality_expression1" |
  420 => "equality_expression2" |
  421 => "equality_expression3" |
  422 => "and_expression1" |
  423 => "and_expression2" |
  424 => "exclusive_or_expression1" |
  425 => "exclusive_or_expression2" |
  426 => "inclusive_or_expression1" |
  427 => "inclusive_or_expression2" |
  428 => "logical_and_expression1" |
  429 => "logical_and_expression2" |
  430 => "logical_or_expression1" |
  431 => "logical_or_expression2" |
  432 => "conditional_expression1" |
  433 => "conditional_expression2" |
  434 => "conditional_expression3" |
  435 => "assignment_expression1" |
  436 => "assignment_expression2" |
  437 => "assignment_operator1" |
  438 => "assignment_operator2" |
  439 => "assignment_operator3" |
  440 => "assignment_operator4" |
  441 => "assignment_operator5" |
  442 => "assignment_operator6" |
  443 => "assignment_operator7" |
  444 => "assignment_operator8" |
  445 => "assignment_operator9" |
  446 => "assignment_operator10" |
  447 => "assignment_operator11" |
  448 => "expression1" |
  449 => "expression2" |
  450 => "comma_expression1" |
  451 => "comma_expression2" |
  452 => "expression_opt1" |
  453 => "expression_opt2" |
  454 => "assignment_expression_opt1" |
  455 => "assignment_expression_opt2" |
  456 => "constant_expression" |
  457 => "constant1" |
  458 => "constant2" |
  459 => "constant3" |
  460 => "string_literal1" |
  461 => "string_literal2" |
  462 => "string_literal_list1" |
  463 => "string_literal_list2" |
  464 => "clang_version_literal" |
  465 => "identifier1" |
  466 => "identifier2" |
  467 => "attrs_opt1" |
  468 => "attrs_opt2" |
  469 => "attrs1" |
  470 => "attrs2" |
  471 => "attr" |
  472 => "attribute_list1" |
  473 => "attribute_list2" |
  474 => "attribute1" |
  475 => "attribute2" |
  476 => "attribute3" |
  477 => "attribute4" |
  478 => "attribute5" |
  479 => "attribute_params1" |
  480 => "attribute_params2" |
  481 => "attribute_params3" |
  482 => "attribute_params4" |
  483 => "attribute_params5" |
  484 => "attribute_params6" |
  _ => error "reduce type not found"
val reduce0 = fn translation_unit x => x | _ => error "Only expecting translation_unit"
val reduce1 = fn ext_decl_list x => x | _ => error "Only expecting ext_decl_list"
val reduce2 = fn ext_decl_list x => x | _ => error "Only expecting ext_decl_list"
val reduce3 = fn ext_decl_list x => x | _ => error "Only expecting ext_decl_list"
val reduce4 = fn external_declaration x => x | _ => error "Only expecting external_declaration"
val reduce5 = fn external_declaration x => x | _ => error "Only expecting external_declaration"
val reduce6 = fn external_declaration x => x | _ => error "Only expecting external_declaration"
val reduce7 = fn external_declaration x => x | _ => error "Only expecting external_declaration"
val reduce8 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce9 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce10 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce11 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce12 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce13 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce14 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce15 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce16 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce17 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce18 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce19 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce20 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce21 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce22 = fn function_declarator x => x | _ => error "Only expecting function_declarator"
val reduce23 = fn statement x => x | _ => error "Only expecting statement"
val reduce24 = fn statement x => x | _ => error "Only expecting statement"
val reduce25 = fn statement x => x | _ => error "Only expecting statement"
val reduce26 = fn statement x => x | _ => error "Only expecting statement"
val reduce27 = fn statement x => x | _ => error "Only expecting statement"
val reduce28 = fn statement x => x | _ => error "Only expecting statement"
val reduce29 = fn statement x => x | _ => error "Only expecting statement"
val reduce30 = fn labeled_statement x => x | _ => error "Only expecting labeled_statement"
val reduce31 = fn labeled_statement x => x | _ => error "Only expecting labeled_statement"
val reduce32 = fn labeled_statement x => x | _ => error "Only expecting labeled_statement"
val reduce33 = fn labeled_statement x => x | _ => error "Only expecting labeled_statement"
val reduce34 = fn compound_statement x => x | _ => error "Only expecting compound_statement"
val reduce35 = fn compound_statement x => x | _ => error "Only expecting compound_statement"
val reduce36 = fn enter_scope x => x | _ => error "Only expecting enter_scope"
val reduce37 = fn leave_scope x => x | _ => error "Only expecting leave_scope"
val reduce38 = fn block_item_list x => x | _ => error "Only expecting block_item_list"
val reduce39 = fn block_item_list x => x | _ => error "Only expecting block_item_list"
val reduce40 = fn block_item x => x | _ => error "Only expecting block_item"
val reduce41 = fn block_item x => x | _ => error "Only expecting block_item"
val reduce42 = fn nested_declaration x => x | _ => error "Only expecting nested_declaration"
val reduce43 = fn nested_declaration x => x | _ => error "Only expecting nested_declaration"
val reduce44 = fn nested_declaration x => x | _ => error "Only expecting nested_declaration"
val reduce45 = fn nested_function_definition x => x | _ => error "Only expecting nested_function_definition"
val reduce46 = fn nested_function_definition x => x | _ => error "Only expecting nested_function_definition"
val reduce47 = fn nested_function_definition x => x | _ => error "Only expecting nested_function_definition"
val reduce48 = fn nested_function_definition x => x | _ => error "Only expecting nested_function_definition"
val reduce49 = fn nested_function_definition x => x | _ => error "Only expecting nested_function_definition"
val reduce50 = fn label_declarations x => x | _ => error "Only expecting label_declarations"
val reduce51 = fn label_declarations x => x | _ => error "Only expecting label_declarations"
val reduce52 = fn expression_statement x => x | _ => error "Only expecting expression_statement"
val reduce53 = fn expression_statement x => x | _ => error "Only expecting expression_statement"
val reduce54 = fn selection_statement x => x | _ => error "Only expecting selection_statement"
val reduce55 = fn selection_statement x => x | _ => error "Only expecting selection_statement"
val reduce56 = fn selection_statement x => x | _ => error "Only expecting selection_statement"
val reduce57 = fn iteration_statement x => x | _ => error "Only expecting iteration_statement"
val reduce58 = fn iteration_statement x => x | _ => error "Only expecting iteration_statement"
val reduce59 = fn iteration_statement x => x | _ => error "Only expecting iteration_statement"
val reduce60 = fn iteration_statement x => x | _ => error "Only expecting iteration_statement"
val reduce61 = fn jump_statement x => x | _ => error "Only expecting jump_statement"
val reduce62 = fn jump_statement x => x | _ => error "Only expecting jump_statement"
val reduce63 = fn jump_statement x => x | _ => error "Only expecting jump_statement"
val reduce64 = fn jump_statement x => x | _ => error "Only expecting jump_statement"
val reduce65 = fn jump_statement x => x | _ => error "Only expecting jump_statement"
val reduce66 = fn asm_statement x => x | _ => error "Only expecting asm_statement"
val reduce67 = fn asm_statement x => x | _ => error "Only expecting asm_statement"
val reduce68 = fn asm_statement x => x | _ => error "Only expecting asm_statement"
val reduce69 = fn asm_statement x => x | _ => error "Only expecting asm_statement"
val reduce70 = fn maybe_type_qualifier x => x | _ => error "Only expecting maybe_type_qualifier"
val reduce71 = fn maybe_type_qualifier x => x | _ => error "Only expecting maybe_type_qualifier"
val reduce72 = fn asm_operands x => x | _ => error "Only expecting asm_operands"
val reduce73 = fn asm_operands x => x | _ => error "Only expecting asm_operands"
val reduce74 = fn nonnull_asm_operands x => x | _ => error "Only expecting nonnull_asm_operands"
val reduce75 = fn nonnull_asm_operands x => x | _ => error "Only expecting nonnull_asm_operands"
val reduce76 = fn asm_operand x => x | _ => error "Only expecting asm_operand"
val reduce77 = fn asm_operand x => x | _ => error "Only expecting asm_operand"
val reduce78 = fn asm_operand x => x | _ => error "Only expecting asm_operand"
val reduce79 = fn asm_clobbers x => x | _ => error "Only expecting asm_clobbers"
val reduce80 = fn asm_clobbers x => x | _ => error "Only expecting asm_clobbers"
val reduce81 = fn declaration x => x | _ => error "Only expecting declaration"
val reduce82 = fn declaration x => x | _ => error "Only expecting declaration"
val reduce83 = fn declaration x => x | _ => error "Only expecting declaration"
val reduce84 = fn declaration x => x | _ => error "Only expecting declaration"
val reduce85 = fn declaration x => x | _ => error "Only expecting declaration"
val reduce86 = fn declaration_list x => x | _ => error "Only expecting declaration_list"
val reduce87 = fn declaration_list x => x | _ => error "Only expecting declaration_list"
val reduce88 = fn default_declaring_list x => x | _ => error "Only expecting default_declaring_list"
val reduce89 = fn default_declaring_list x => x | _ => error "Only expecting default_declaring_list"
val reduce90 = fn default_declaring_list x => x | _ => error "Only expecting default_declaring_list"
val reduce91 = fn default_declaring_list x => x | _ => error "Only expecting default_declaring_list"
val reduce92 = fn default_declaring_list x => x | _ => error "Only expecting default_declaring_list"
val reduce93 = fn asm_attrs_opt x => x | _ => error "Only expecting asm_attrs_opt"
val reduce94 = fn declaring_list x => x | _ => error "Only expecting declaring_list"
val reduce95 = fn declaring_list x => x | _ => error "Only expecting declaring_list"
val reduce96 = fn declaring_list x => x | _ => error "Only expecting declaring_list"
val reduce97 = fn declaration_specifier x => x | _ => error "Only expecting declaration_specifier"
val reduce98 = fn declaration_specifier x => x | _ => error "Only expecting declaration_specifier"
val reduce99 = fn declaration_specifier x => x | _ => error "Only expecting declaration_specifier"
val reduce100 = fn declaration_qualifier_list x => x | _ => error "Only expecting declaration_qualifier_list"
val reduce101 = fn declaration_qualifier_list x => x | _ => error "Only expecting declaration_qualifier_list"
val reduce102 = fn declaration_qualifier_list x => x | _ => error "Only expecting declaration_qualifier_list"
val reduce103 = fn declaration_qualifier_list x => x | _ => error "Only expecting declaration_qualifier_list"
val reduce104 = fn declaration_qualifier_list x => x | _ => error "Only expecting declaration_qualifier_list"
val reduce105 = fn declaration_qualifier_list x => x | _ => error "Only expecting declaration_qualifier_list"
val reduce106 = fn declaration_qualifier x => x | _ => error "Only expecting declaration_qualifier"
val reduce107 = fn declaration_qualifier x => x | _ => error "Only expecting declaration_qualifier"
val reduce108 = fn declaration_qualifier x => x | _ => error "Only expecting declaration_qualifier"
val reduce109 = fn declaration_qualifier x => x | _ => error "Only expecting declaration_qualifier"
val reduce110 = fn declaration_qualifier_without_types x => x | _ => error "Only expecting declaration_qualifier_without_types"
val reduce111 = fn declaration_qualifier_without_types x => x | _ => error "Only expecting declaration_qualifier_without_types"
val reduce112 = fn declaration_qualifier_without_types x => x | _ => error "Only expecting declaration_qualifier_without_types"
val reduce113 = fn storage_class x => x | _ => error "Only expecting storage_class"
val reduce114 = fn storage_class x => x | _ => error "Only expecting storage_class"
val reduce115 = fn storage_class x => x | _ => error "Only expecting storage_class"
val reduce116 = fn storage_class x => x | _ => error "Only expecting storage_class"
val reduce117 = fn storage_class x => x | _ => error "Only expecting storage_class"
val reduce118 = fn storage_class x => x | _ => error "Only expecting storage_class"
val reduce119 = fn function_specifier x => x | _ => error "Only expecting function_specifier"
val reduce120 = fn function_specifier x => x | _ => error "Only expecting function_specifier"
val reduce121 = fn alignment_specifier x => x | _ => error "Only expecting alignment_specifier"
val reduce122 = fn alignment_specifier x => x | _ => error "Only expecting alignment_specifier"
val reduce123 = fn type_specifier x => x | _ => error "Only expecting type_specifier"
val reduce124 = fn type_specifier x => x | _ => error "Only expecting type_specifier"
val reduce125 = fn type_specifier x => x | _ => error "Only expecting type_specifier"
val reduce126 = fn basic_type_name x => x | _ => error "Only expecting basic_type_name"
val reduce127 = fn basic_type_name x => x | _ => error "Only expecting basic_type_name"
val reduce128 = fn basic_type_name x => x | _ => error "Only expecting basic_type_name"
val reduce129 = fn basic_type_name x => x | _ => error "Only expecting basic_type_name"
val reduce130 = fn basic_type_name x => x | _ => error "Only expecting basic_type_name"
val reduce131 = fn basic_type_name x => x | _ => error "Only expecting basic_type_name"
val reduce132 = fn basic_type_name x => x | _ => error "Only expecting basic_type_name"
val reduce133 = fn basic_type_name x => x | _ => error "Only expecting basic_type_name"
val reduce134 = fn basic_type_name x => x | _ => error "Only expecting basic_type_name"
val reduce135 = fn basic_type_name x => x | _ => error "Only expecting basic_type_name"
val reduce136 = fn basic_type_name x => x | _ => error "Only expecting basic_type_name"
val reduce137 = fn basic_type_name x => x | _ => error "Only expecting basic_type_name"
val reduce138 = fn basic_declaration_specifier x => x | _ => error "Only expecting basic_declaration_specifier"
val reduce139 = fn basic_declaration_specifier x => x | _ => error "Only expecting basic_declaration_specifier"
val reduce140 = fn basic_declaration_specifier x => x | _ => error "Only expecting basic_declaration_specifier"
val reduce141 = fn basic_declaration_specifier x => x | _ => error "Only expecting basic_declaration_specifier"
val reduce142 = fn basic_declaration_specifier x => x | _ => error "Only expecting basic_declaration_specifier"
val reduce143 = fn basic_type_specifier x => x | _ => error "Only expecting basic_type_specifier"
val reduce144 = fn basic_type_specifier x => x | _ => error "Only expecting basic_type_specifier"
val reduce145 = fn basic_type_specifier x => x | _ => error "Only expecting basic_type_specifier"
val reduce146 = fn basic_type_specifier x => x | _ => error "Only expecting basic_type_specifier"
val reduce147 = fn basic_type_specifier x => x | _ => error "Only expecting basic_type_specifier"
val reduce148 = fn basic_type_specifier x => x | _ => error "Only expecting basic_type_specifier"
val reduce149 = fn basic_type_specifier x => x | _ => error "Only expecting basic_type_specifier"
val reduce150 = fn sue_declaration_specifier x => x | _ => error "Only expecting sue_declaration_specifier"
val reduce151 = fn sue_declaration_specifier x => x | _ => error "Only expecting sue_declaration_specifier"
val reduce152 = fn sue_declaration_specifier x => x | _ => error "Only expecting sue_declaration_specifier"
val reduce153 = fn sue_declaration_specifier x => x | _ => error "Only expecting sue_declaration_specifier"
val reduce154 = fn sue_type_specifier x => x | _ => error "Only expecting sue_type_specifier"
val reduce155 = fn sue_type_specifier x => x | _ => error "Only expecting sue_type_specifier"
val reduce156 = fn sue_type_specifier x => x | _ => error "Only expecting sue_type_specifier"
val reduce157 = fn sue_type_specifier x => x | _ => error "Only expecting sue_type_specifier"
val reduce158 = fn sue_type_specifier x => x | _ => error "Only expecting sue_type_specifier"
val reduce159 = fn sue_type_specifier x => x | _ => error "Only expecting sue_type_specifier"
val reduce160 = fn typedef_declaration_specifier x => x | _ => error "Only expecting typedef_declaration_specifier"
val reduce161 = fn typedef_declaration_specifier x => x | _ => error "Only expecting typedef_declaration_specifier"
val reduce162 = fn typedef_declaration_specifier x => x | _ => error "Only expecting typedef_declaration_specifier"
val reduce163 = fn typedef_declaration_specifier x => x | _ => error "Only expecting typedef_declaration_specifier"
val reduce164 = fn typedef_declaration_specifier x => x | _ => error "Only expecting typedef_declaration_specifier"
val reduce165 = fn typedef_declaration_specifier x => x | _ => error "Only expecting typedef_declaration_specifier"
val reduce166 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce167 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce168 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce169 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce170 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce171 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce172 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce173 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce174 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce175 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce176 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce177 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce178 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce179 = fn typedef_type_specifier x => x | _ => error "Only expecting typedef_type_specifier"
val reduce180 = fn elaborated_type_name x => x | _ => error "Only expecting elaborated_type_name"
val reduce181 = fn elaborated_type_name x => x | _ => error "Only expecting elaborated_type_name"
val reduce182 = fn struct_or_union_specifier x => x | _ => error "Only expecting struct_or_union_specifier"
val reduce183 = fn struct_or_union_specifier x => x | _ => error "Only expecting struct_or_union_specifier"
val reduce184 = fn struct_or_union_specifier x => x | _ => error "Only expecting struct_or_union_specifier"
val reduce185 = fn struct_or_union x => x | _ => error "Only expecting struct_or_union"
val reduce186 = fn struct_or_union x => x | _ => error "Only expecting struct_or_union"
val reduce187 = fn struct_declaration_list x => x | _ => error "Only expecting struct_declaration_list"
val reduce188 = fn struct_declaration_list x => x | _ => error "Only expecting struct_declaration_list"
val reduce189 = fn struct_declaration_list x => x | _ => error "Only expecting struct_declaration_list"
val reduce190 = fn struct_declaration x => x | _ => error "Only expecting struct_declaration"
val reduce191 = fn struct_declaration x => x | _ => error "Only expecting struct_declaration"
val reduce192 = fn struct_declaration x => x | _ => error "Only expecting struct_declaration"
val reduce193 = fn struct_default_declaring_list x => x | _ => error "Only expecting struct_default_declaring_list"
val reduce194 = fn struct_default_declaring_list x => x | _ => error "Only expecting struct_default_declaring_list"
val reduce195 = fn struct_default_declaring_list x => x | _ => error "Only expecting struct_default_declaring_list"
val reduce196 = fn struct_declaring_list x => x | _ => error "Only expecting struct_declaring_list"
val reduce197 = fn struct_declaring_list x => x | _ => error "Only expecting struct_declaring_list"
val reduce198 = fn struct_declaring_list x => x | _ => error "Only expecting struct_declaring_list"
val reduce199 = fn struct_declarator x => x | _ => error "Only expecting struct_declarator"
val reduce200 = fn struct_declarator x => x | _ => error "Only expecting struct_declarator"
val reduce201 = fn struct_declarator x => x | _ => error "Only expecting struct_declarator"
val reduce202 = fn struct_identifier_declarator x => x | _ => error "Only expecting struct_identifier_declarator"
val reduce203 = fn struct_identifier_declarator x => x | _ => error "Only expecting struct_identifier_declarator"
val reduce204 = fn struct_identifier_declarator x => x | _ => error "Only expecting struct_identifier_declarator"
val reduce205 = fn struct_identifier_declarator x => x | _ => error "Only expecting struct_identifier_declarator"
val reduce206 = fn enum_specifier x => x | _ => error "Only expecting enum_specifier"
val reduce207 = fn enum_specifier x => x | _ => error "Only expecting enum_specifier"
val reduce208 = fn enum_specifier x => x | _ => error "Only expecting enum_specifier"
val reduce209 = fn enum_specifier x => x | _ => error "Only expecting enum_specifier"
val reduce210 = fn enum_specifier x => x | _ => error "Only expecting enum_specifier"
val reduce211 = fn enumerator_list x => x | _ => error "Only expecting enumerator_list"
val reduce212 = fn enumerator_list x => x | _ => error "Only expecting enumerator_list"
val reduce213 = fn enumerator x => x | _ => error "Only expecting enumerator"
val reduce214 = fn enumerator x => x | _ => error "Only expecting enumerator"
val reduce215 = fn enumerator x => x | _ => error "Only expecting enumerator"
val reduce216 = fn enumerator x => x | _ => error "Only expecting enumerator"
val reduce217 = fn type_qualifier x => x | _ => error "Only expecting type_qualifier"
val reduce218 = fn type_qualifier x => x | _ => error "Only expecting type_qualifier"
val reduce219 = fn type_qualifier x => x | _ => error "Only expecting type_qualifier"
val reduce220 = fn type_qualifier x => x | _ => error "Only expecting type_qualifier"
val reduce221 = fn type_qualifier x => x | _ => error "Only expecting type_qualifier"
val reduce222 = fn type_qualifier x => x | _ => error "Only expecting type_qualifier"
val reduce223 = fn type_qualifier_list x => x | _ => error "Only expecting type_qualifier_list"
val reduce224 = fn type_qualifier_list x => x | _ => error "Only expecting type_qualifier_list"
val reduce225 = fn type_qualifier_list x => x | _ => error "Only expecting type_qualifier_list"
val reduce226 = fn declarator x => x | _ => error "Only expecting declarator"
val reduce227 = fn declarator x => x | _ => error "Only expecting declarator"
val reduce228 = fn asm_opt x => x | _ => error "Only expecting asm_opt"
val reduce229 = fn asm_opt x => x | _ => error "Only expecting asm_opt"
val reduce230 = fn typedef_declarator x => x | _ => error "Only expecting typedef_declarator"
val reduce231 = fn typedef_declarator x => x | _ => error "Only expecting typedef_declarator"
val reduce232 = fn parameter_typedef_declarator x => x | _ => error "Only expecting parameter_typedef_declarator"
val reduce233 = fn parameter_typedef_declarator x => x | _ => error "Only expecting parameter_typedef_declarator"
val reduce234 = fn parameter_typedef_declarator x => x | _ => error "Only expecting parameter_typedef_declarator"
val reduce235 = fn clean_typedef_declarator x => x | _ => error "Only expecting clean_typedef_declarator"
val reduce236 = fn clean_typedef_declarator x => x | _ => error "Only expecting clean_typedef_declarator"
val reduce237 = fn clean_typedef_declarator x => x | _ => error "Only expecting clean_typedef_declarator"
val reduce238 = fn clean_typedef_declarator x => x | _ => error "Only expecting clean_typedef_declarator"
val reduce239 = fn clean_typedef_declarator x => x | _ => error "Only expecting clean_typedef_declarator"
val reduce240 = fn clean_postfix_typedef_declarator x => x | _ => error "Only expecting clean_postfix_typedef_declarator"
val reduce241 = fn clean_postfix_typedef_declarator x => x | _ => error "Only expecting clean_postfix_typedef_declarator"
val reduce242 = fn clean_postfix_typedef_declarator x => x | _ => error "Only expecting clean_postfix_typedef_declarator"
val reduce243 = fn clean_postfix_typedef_declarator x => x | _ => error "Only expecting clean_postfix_typedef_declarator"
val reduce244 = fn paren_typedef_declarator x => x | _ => error "Only expecting paren_typedef_declarator"
val reduce245 = fn paren_typedef_declarator x => x | _ => error "Only expecting paren_typedef_declarator"
val reduce246 = fn paren_typedef_declarator x => x | _ => error "Only expecting paren_typedef_declarator"
val reduce247 = fn paren_typedef_declarator x => x | _ => error "Only expecting paren_typedef_declarator"
val reduce248 = fn paren_typedef_declarator x => x | _ => error "Only expecting paren_typedef_declarator"
val reduce249 = fn paren_typedef_declarator x => x | _ => error "Only expecting paren_typedef_declarator"
val reduce250 = fn paren_typedef_declarator x => x | _ => error "Only expecting paren_typedef_declarator"
val reduce251 = fn paren_postfix_typedef_declarator x => x | _ => error "Only expecting paren_postfix_typedef_declarator"
val reduce252 = fn paren_postfix_typedef_declarator x => x | _ => error "Only expecting paren_postfix_typedef_declarator"
val reduce253 = fn paren_postfix_typedef_declarator x => x | _ => error "Only expecting paren_postfix_typedef_declarator"
val reduce254 = fn simple_paren_typedef_declarator x => x | _ => error "Only expecting simple_paren_typedef_declarator"
val reduce255 = fn simple_paren_typedef_declarator x => x | _ => error "Only expecting simple_paren_typedef_declarator"
val reduce256 = fn identifier_declarator x => x | _ => error "Only expecting identifier_declarator"
val reduce257 = fn identifier_declarator x => x | _ => error "Only expecting identifier_declarator"
val reduce258 = fn unary_identifier_declarator x => x | _ => error "Only expecting unary_identifier_declarator"
val reduce259 = fn unary_identifier_declarator x => x | _ => error "Only expecting unary_identifier_declarator"
val reduce260 = fn unary_identifier_declarator x => x | _ => error "Only expecting unary_identifier_declarator"
val reduce261 = fn unary_identifier_declarator x => x | _ => error "Only expecting unary_identifier_declarator"
val reduce262 = fn unary_identifier_declarator x => x | _ => error "Only expecting unary_identifier_declarator"
val reduce263 = fn postfix_identifier_declarator x => x | _ => error "Only expecting postfix_identifier_declarator"
val reduce264 = fn postfix_identifier_declarator x => x | _ => error "Only expecting postfix_identifier_declarator"
val reduce265 = fn postfix_identifier_declarator x => x | _ => error "Only expecting postfix_identifier_declarator"
val reduce266 = fn postfix_identifier_declarator x => x | _ => error "Only expecting postfix_identifier_declarator"
val reduce267 = fn postfix_identifier_declarator x => x | _ => error "Only expecting postfix_identifier_declarator"
val reduce268 = fn paren_identifier_declarator x => x | _ => error "Only expecting paren_identifier_declarator"
val reduce269 = fn paren_identifier_declarator x => x | _ => error "Only expecting paren_identifier_declarator"
val reduce270 = fn paren_identifier_declarator x => x | _ => error "Only expecting paren_identifier_declarator"
val reduce271 = fn function_declarator_old x => x | _ => error "Only expecting function_declarator_old"
val reduce272 = fn old_function_declarator x => x | _ => error "Only expecting old_function_declarator"
val reduce273 = fn old_function_declarator x => x | _ => error "Only expecting old_function_declarator"
val reduce274 = fn old_function_declarator x => x | _ => error "Only expecting old_function_declarator"
val reduce275 = fn postfix_old_function_declarator x => x | _ => error "Only expecting postfix_old_function_declarator"
val reduce276 = fn postfix_old_function_declarator x => x | _ => error "Only expecting postfix_old_function_declarator"
val reduce277 = fn postfix_old_function_declarator x => x | _ => error "Only expecting postfix_old_function_declarator"
val reduce278 = fn parameter_type_list x => x | _ => error "Only expecting parameter_type_list"
val reduce279 = fn parameter_type_list x => x | _ => error "Only expecting parameter_type_list"
val reduce280 = fn parameter_type_list x => x | _ => error "Only expecting parameter_type_list"
val reduce281 = fn parameter_list x => x | _ => error "Only expecting parameter_list"
val reduce282 = fn parameter_list x => x | _ => error "Only expecting parameter_list"
val reduce283 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce284 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce285 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce286 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce287 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce288 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce289 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce290 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce291 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce292 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce293 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce294 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce295 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce296 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce297 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce298 = fn identifier_list x => x | _ => error "Only expecting identifier_list"
val reduce299 = fn identifier_list x => x | _ => error "Only expecting identifier_list"
val reduce300 = fn type_name x => x | _ => error "Only expecting type_name"
val reduce301 = fn type_name x => x | _ => error "Only expecting type_name"
val reduce302 = fn type_name x => x | _ => error "Only expecting type_name"
val reduce303 = fn type_name x => x | _ => error "Only expecting type_name"
val reduce304 = fn abstract_declarator x => x | _ => error "Only expecting abstract_declarator"
val reduce305 = fn abstract_declarator x => x | _ => error "Only expecting abstract_declarator"
val reduce306 = fn abstract_declarator x => x | _ => error "Only expecting abstract_declarator"
val reduce307 = fn postfixing_abstract_declarator x => x | _ => error "Only expecting postfixing_abstract_declarator"
val reduce308 = fn postfixing_abstract_declarator x => x | _ => error "Only expecting postfixing_abstract_declarator"
val reduce309 = fn array_abstract_declarator x => x | _ => error "Only expecting array_abstract_declarator"
val reduce310 = fn array_abstract_declarator x => x | _ => error "Only expecting array_abstract_declarator"
val reduce311 = fn postfix_array_abstract_declarator x => x | _ => error "Only expecting postfix_array_abstract_declarator"
val reduce312 = fn postfix_array_abstract_declarator x => x | _ => error "Only expecting postfix_array_abstract_declarator"
val reduce313 = fn postfix_array_abstract_declarator x => x | _ => error "Only expecting postfix_array_abstract_declarator"
val reduce314 = fn postfix_array_abstract_declarator x => x | _ => error "Only expecting postfix_array_abstract_declarator"
val reduce315 = fn postfix_array_abstract_declarator x => x | _ => error "Only expecting postfix_array_abstract_declarator"
val reduce316 = fn postfix_array_abstract_declarator x => x | _ => error "Only expecting postfix_array_abstract_declarator"
val reduce317 = fn postfix_array_abstract_declarator x => x | _ => error "Only expecting postfix_array_abstract_declarator"
val reduce318 = fn postfix_array_abstract_declarator x => x | _ => error "Only expecting postfix_array_abstract_declarator"
val reduce319 = fn postfix_array_abstract_declarator x => x | _ => error "Only expecting postfix_array_abstract_declarator"
val reduce320 = fn postfix_array_abstract_declarator x => x | _ => error "Only expecting postfix_array_abstract_declarator"
val reduce321 = fn postfix_array_abstract_declarator x => x | _ => error "Only expecting postfix_array_abstract_declarator"
val reduce322 = fn unary_abstract_declarator x => x | _ => error "Only expecting unary_abstract_declarator"
val reduce323 = fn unary_abstract_declarator x => x | _ => error "Only expecting unary_abstract_declarator"
val reduce324 = fn unary_abstract_declarator x => x | _ => error "Only expecting unary_abstract_declarator"
val reduce325 = fn unary_abstract_declarator x => x | _ => error "Only expecting unary_abstract_declarator"
val reduce326 = fn unary_abstract_declarator x => x | _ => error "Only expecting unary_abstract_declarator"
val reduce327 = fn unary_abstract_declarator x => x | _ => error "Only expecting unary_abstract_declarator"
val reduce328 = fn postfix_abstract_declarator x => x | _ => error "Only expecting postfix_abstract_declarator"
val reduce329 = fn postfix_abstract_declarator x => x | _ => error "Only expecting postfix_abstract_declarator"
val reduce330 = fn postfix_abstract_declarator x => x | _ => error "Only expecting postfix_abstract_declarator"
val reduce331 = fn postfix_abstract_declarator x => x | _ => error "Only expecting postfix_abstract_declarator"
val reduce332 = fn postfix_abstract_declarator x => x | _ => error "Only expecting postfix_abstract_declarator"
val reduce333 = fn postfix_abstract_declarator x => x | _ => error "Only expecting postfix_abstract_declarator"
val reduce334 = fn postfix_abstract_declarator x => x | _ => error "Only expecting postfix_abstract_declarator"
val reduce335 = fn postfix_abstract_declarator x => x | _ => error "Only expecting postfix_abstract_declarator"
val reduce336 = fn postfix_abstract_declarator x => x | _ => error "Only expecting postfix_abstract_declarator"
val reduce337 = fn initializer x => x | _ => error "Only expecting initializer"
val reduce338 = fn initializer x => x | _ => error "Only expecting initializer"
val reduce339 = fn initializer x => x | _ => error "Only expecting initializer"
val reduce340 = fn initializer_opt x => x | _ => error "Only expecting initializer_opt"
val reduce341 = fn initializer_opt x => x | _ => error "Only expecting initializer_opt"
val reduce342 = fn initializer_list x => x | _ => error "Only expecting initializer_list"
val reduce343 = fn initializer_list x => x | _ => error "Only expecting initializer_list"
val reduce344 = fn initializer_list x => x | _ => error "Only expecting initializer_list"
val reduce345 = fn initializer_list x => x | _ => error "Only expecting initializer_list"
val reduce346 = fn initializer_list x => x | _ => error "Only expecting initializer_list"
val reduce347 = fn designation x => x | _ => error "Only expecting designation"
val reduce348 = fn designation x => x | _ => error "Only expecting designation"
val reduce349 = fn designation x => x | _ => error "Only expecting designation"
val reduce350 = fn designator_list x => x | _ => error "Only expecting designator_list"
val reduce351 = fn designator_list x => x | _ => error "Only expecting designator_list"
val reduce352 = fn designator x => x | _ => error "Only expecting designator"
val reduce353 = fn designator x => x | _ => error "Only expecting designator"
val reduce354 = fn designator x => x | _ => error "Only expecting designator"
val reduce355 = fn array_designator x => x | _ => error "Only expecting array_designator"
val reduce356 = fn primary_expression x => x | _ => error "Only expecting primary_expression"
val reduce357 = fn primary_expression x => x | _ => error "Only expecting primary_expression"
val reduce358 = fn primary_expression x => x | _ => error "Only expecting primary_expression"
val reduce359 = fn primary_expression x => x | _ => error "Only expecting primary_expression"
val reduce360 = fn primary_expression x => x | _ => error "Only expecting primary_expression"
val reduce361 = fn primary_expression x => x | _ => error "Only expecting primary_expression"
val reduce362 = fn primary_expression x => x | _ => error "Only expecting primary_expression"
val reduce363 = fn primary_expression x => x | _ => error "Only expecting primary_expression"
val reduce364 = fn primary_expression x => x | _ => error "Only expecting primary_expression"
val reduce365 = fn generic_assoc_list x => x | _ => error "Only expecting generic_assoc_list"
val reduce366 = fn generic_assoc_list x => x | _ => error "Only expecting generic_assoc_list"
val reduce367 = fn generic_assoc x => x | _ => error "Only expecting generic_assoc"
val reduce368 = fn generic_assoc x => x | _ => error "Only expecting generic_assoc"
val reduce369 = fn offsetof_member_designator x => x | _ => error "Only expecting offsetof_member_designator"
val reduce370 = fn offsetof_member_designator x => x | _ => error "Only expecting offsetof_member_designator"
val reduce371 = fn offsetof_member_designator x => x | _ => error "Only expecting offsetof_member_designator"
val reduce372 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce373 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce374 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce375 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce376 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce377 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce378 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce379 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce380 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce381 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce382 = fn argument_expression_list x => x | _ => error "Only expecting argument_expression_list"
val reduce383 = fn argument_expression_list x => x | _ => error "Only expecting argument_expression_list"
val reduce384 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce385 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce386 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce387 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce388 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce389 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce390 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce391 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce392 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce393 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce394 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce395 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce396 = fn unary_operator x => x | _ => error "Only expecting unary_operator"
val reduce397 = fn unary_operator x => x | _ => error "Only expecting unary_operator"
val reduce398 = fn unary_operator x => x | _ => error "Only expecting unary_operator"
val reduce399 = fn unary_operator x => x | _ => error "Only expecting unary_operator"
val reduce400 = fn unary_operator x => x | _ => error "Only expecting unary_operator"
val reduce401 = fn unary_operator x => x | _ => error "Only expecting unary_operator"
val reduce402 = fn cast_expression x => x | _ => error "Only expecting cast_expression"
val reduce403 = fn cast_expression x => x | _ => error "Only expecting cast_expression"
val reduce404 = fn multiplicative_expression x => x | _ => error "Only expecting multiplicative_expression"
val reduce405 = fn multiplicative_expression x => x | _ => error "Only expecting multiplicative_expression"
val reduce406 = fn multiplicative_expression x => x | _ => error "Only expecting multiplicative_expression"
val reduce407 = fn multiplicative_expression x => x | _ => error "Only expecting multiplicative_expression"
val reduce408 = fn additive_expression x => x | _ => error "Only expecting additive_expression"
val reduce409 = fn additive_expression x => x | _ => error "Only expecting additive_expression"
val reduce410 = fn additive_expression x => x | _ => error "Only expecting additive_expression"
val reduce411 = fn shift_expression x => x | _ => error "Only expecting shift_expression"
val reduce412 = fn shift_expression x => x | _ => error "Only expecting shift_expression"
val reduce413 = fn shift_expression x => x | _ => error "Only expecting shift_expression"
val reduce414 = fn relational_expression x => x | _ => error "Only expecting relational_expression"
val reduce415 = fn relational_expression x => x | _ => error "Only expecting relational_expression"
val reduce416 = fn relational_expression x => x | _ => error "Only expecting relational_expression"
val reduce417 = fn relational_expression x => x | _ => error "Only expecting relational_expression"
val reduce418 = fn relational_expression x => x | _ => error "Only expecting relational_expression"
val reduce419 = fn equality_expression x => x | _ => error "Only expecting equality_expression"
val reduce420 = fn equality_expression x => x | _ => error "Only expecting equality_expression"
val reduce421 = fn equality_expression x => x | _ => error "Only expecting equality_expression"
val reduce422 = fn and_expression x => x | _ => error "Only expecting and_expression"
val reduce423 = fn and_expression x => x | _ => error "Only expecting and_expression"
val reduce424 = fn exclusive_or_expression x => x | _ => error "Only expecting exclusive_or_expression"
val reduce425 = fn exclusive_or_expression x => x | _ => error "Only expecting exclusive_or_expression"
val reduce426 = fn inclusive_or_expression x => x | _ => error "Only expecting inclusive_or_expression"
val reduce427 = fn inclusive_or_expression x => x | _ => error "Only expecting inclusive_or_expression"
val reduce428 = fn logical_and_expression x => x | _ => error "Only expecting logical_and_expression"
val reduce429 = fn logical_and_expression x => x | _ => error "Only expecting logical_and_expression"
val reduce430 = fn logical_or_expression x => x | _ => error "Only expecting logical_or_expression"
val reduce431 = fn logical_or_expression x => x | _ => error "Only expecting logical_or_expression"
val reduce432 = fn conditional_expression x => x | _ => error "Only expecting conditional_expression"
val reduce433 = fn conditional_expression x => x | _ => error "Only expecting conditional_expression"
val reduce434 = fn conditional_expression x => x | _ => error "Only expecting conditional_expression"
val reduce435 = fn assignment_expression x => x | _ => error "Only expecting assignment_expression"
val reduce436 = fn assignment_expression x => x | _ => error "Only expecting assignment_expression"
val reduce437 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce438 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce439 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce440 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce441 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce442 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce443 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce444 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce445 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce446 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce447 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce448 = fn expression x => x | _ => error "Only expecting expression"
val reduce449 = fn expression x => x | _ => error "Only expecting expression"
val reduce450 = fn comma_expression x => x | _ => error "Only expecting comma_expression"
val reduce451 = fn comma_expression x => x | _ => error "Only expecting comma_expression"
val reduce452 = fn expression_opt x => x | _ => error "Only expecting expression_opt"
val reduce453 = fn expression_opt x => x | _ => error "Only expecting expression_opt"
val reduce454 = fn assignment_expression_opt x => x | _ => error "Only expecting assignment_expression_opt"
val reduce455 = fn assignment_expression_opt x => x | _ => error "Only expecting assignment_expression_opt"
val reduce456 = fn constant_expression x => x | _ => error "Only expecting constant_expression"
val reduce457 = fn constant x => x | _ => error "Only expecting constant"
val reduce458 = fn constant x => x | _ => error "Only expecting constant"
val reduce459 = fn constant x => x | _ => error "Only expecting constant"
val reduce460 = fn string_literal x => x | _ => error "Only expecting string_literal"
val reduce461 = fn string_literal x => x | _ => error "Only expecting string_literal"
val reduce462 = fn string_literal_list x => x | _ => error "Only expecting string_literal_list"
val reduce463 = fn string_literal_list x => x | _ => error "Only expecting string_literal_list"
val reduce464 = fn clang_version_literal x => x | _ => error "Only expecting clang_version_literal"
val reduce465 = fn identifier x => x | _ => error "Only expecting identifier"
val reduce466 = fn identifier x => x | _ => error "Only expecting identifier"
val reduce467 = fn attrs_opt x => x | _ => error "Only expecting attrs_opt"
val reduce468 = fn attrs_opt x => x | _ => error "Only expecting attrs_opt"
val reduce469 = fn attrs x => x | _ => error "Only expecting attrs"
val reduce470 = fn attrs x => x | _ => error "Only expecting attrs"
val reduce471 = fn attr x => x | _ => error "Only expecting attr"
val reduce472 = fn attribute_list x => x | _ => error "Only expecting attribute_list"
val reduce473 = fn attribute_list x => x | _ => error "Only expecting attribute_list"
val reduce474 = fn attribute x => x | _ => error "Only expecting attribute"
val reduce475 = fn attribute x => x | _ => error "Only expecting attribute"
val reduce476 = fn attribute x => x | _ => error "Only expecting attribute"
val reduce477 = fn attribute x => x | _ => error "Only expecting attribute"
val reduce478 = fn attribute x => x | _ => error "Only expecting attribute"
val reduce479 = fn attribute_params x => x | _ => error "Only expecting attribute_params"
val reduce480 = fn attribute_params x => x | _ => error "Only expecting attribute_params"
val reduce481 = fn attribute_params x => x | _ => error "Only expecting attribute_params"
val reduce482 = fn attribute_params x => x | _ => error "Only expecting attribute_params"
val reduce483 = fn attribute_params x => x | _ => error "Only expecting attribute_params"
val reduce484 = fn attribute_params x => x | _ => error "Only expecting attribute_params"
end
structure MlyValueM = 
struct
fun translation_unit _ = return ()
fun ext_decl_list1 _ = return ()
fun ext_decl_list2 _ = return ()
fun ext_decl_list3 _ = return ()
fun external_declaration1 _ = return ()
fun external_declaration2 _ = return ()
fun external_declaration3 _ = return ()
fun external_declaration4 _ = return ()
fun function_definition1 _ = return ()
fun function_definition2 _ = return ()
fun function_definition3 _ = return ()
fun function_definition4 _ = return ()
fun function_definition5 _ = return ()
fun function_definition6 _ = return ()
fun function_definition7 _ = return ()
fun function_definition8 _ = return ()
fun function_definition9 _ = return ()
fun function_definition10 _ = return ()
fun function_definition11 _ = return ()
fun function_definition12 _ = return ()
fun function_definition13 _ = return ()
fun function_definition14 _ = return ()
fun function_declarator _ = return ()
fun statement1 _ = return ()
fun statement2 _ = return ()
fun statement3 _ = return ()
fun statement4 _ = return ()
fun statement5 _ = return ()
fun statement6 _ = return ()
fun statement7 _ = return ()
fun labeled_statement1 _ = return ()
fun labeled_statement2 _ = return ()
fun labeled_statement3 _ = return ()
fun labeled_statement4 _ = return ()
fun compound_statement1 _ = return ()
fun compound_statement2 _ = return ()
fun enter_scope _ = return ()
fun leave_scope _ = return ()
fun block_item_list1 _ = return ()
fun block_item_list2 _ = return ()
fun block_item1 _ = return ()
fun block_item2 _ = return ()
fun nested_declaration1 _ = return ()
fun nested_declaration2 _ = return ()
fun nested_declaration3 _ = return ()
fun nested_function_definition1 _ = return ()
fun nested_function_definition2 _ = return ()
fun nested_function_definition3 _ = return ()
fun nested_function_definition4 _ = return ()
fun nested_function_definition5 _ = return ()
fun label_declarations1 _ = return ()
fun label_declarations2 _ = return ()
fun expression_statement1 _ = return ()
fun expression_statement2 _ = return ()
fun selection_statement1 _ = return ()
fun selection_statement2 _ = return ()
fun selection_statement3 _ = return ()
fun iteration_statement1 _ = return ()
fun iteration_statement2 _ = return ()
fun iteration_statement3 _ = return ()
fun iteration_statement4 _ = return ()
fun jump_statement1 _ = return ()
fun jump_statement2 _ = return ()
fun jump_statement3 _ = return ()
fun jump_statement4 _ = return ()
fun jump_statement5 _ = return ()
fun asm_statement1 _ = return ()
fun asm_statement2 _ = return ()
fun asm_statement3 _ = return ()
fun asm_statement4 _ = return ()
fun maybe_type_qualifier1 _ = return ()
fun maybe_type_qualifier2 _ = return ()
fun asm_operands1 _ = return ()
fun asm_operands2 _ = return ()
fun nonnull_asm_operands1 _ = return ()
fun nonnull_asm_operands2 _ = return ()
fun asm_operand1 _ = return ()
fun asm_operand2 _ = return ()
fun asm_operand3 _ = return ()
fun asm_clobbers1 _ = return ()
fun asm_clobbers2 _ = return ()
fun declaration1 _ = return ()
fun declaration2 _ = return ()
fun declaration3 _ = return ()
fun declaration4 _ = return ()
fun declaration5 _ = return ()
fun declaration_list1 _ = return ()
fun declaration_list2 _ = return ()
fun default_declaring_list1 _ = return ()
fun default_declaring_list2 _ = return ()
fun default_declaring_list3 _ = return ()
fun default_declaring_list4 _ = return ()
fun default_declaring_list5 _ = return ()
fun asm_attrs_opt _ = return ()
fun declaring_list1 _ = return ()
fun declaring_list2 _ = return ()
fun declaring_list3 _ = return ()
fun declaration_specifier1 _ = return ()
fun declaration_specifier2 _ = return ()
fun declaration_specifier3 _ = return ()
fun declaration_qualifier_list1 _ = return ()
fun declaration_qualifier_list2 _ = return ()
fun declaration_qualifier_list3 _ = return ()
fun declaration_qualifier_list4 _ = return ()
fun declaration_qualifier_list5 _ = return ()
fun declaration_qualifier_list6 _ = return ()
fun declaration_qualifier1 _ = return ()
fun declaration_qualifier2 _ = return ()
fun declaration_qualifier3 _ = return ()
fun declaration_qualifier4 _ = return ()
fun declaration_qualifier_without_types1 _ = return ()
fun declaration_qualifier_without_types2 _ = return ()
fun declaration_qualifier_without_types3 _ = return ()
fun storage_class1 _ = return ()
fun storage_class2 _ = return ()
fun storage_class3 _ = return ()
fun storage_class4 _ = return ()
fun storage_class5 _ = return ()
fun storage_class6 _ = return ()
fun function_specifier1 _ = return ()
fun function_specifier2 _ = return ()
fun alignment_specifier1 _ = return ()
fun alignment_specifier2 _ = return ()
fun type_specifier1 _ = return ()
fun type_specifier2 _ = return ()
fun type_specifier3 _ = return ()
fun basic_type_name1 _ = return ()
fun basic_type_name2 _ = return ()
fun basic_type_name3 _ = return ()
fun basic_type_name4 _ = return ()
fun basic_type_name5 _ = return ()
fun basic_type_name6 _ = return ()
fun basic_type_name7 _ = return ()
fun basic_type_name8 _ = return ()
fun basic_type_name9 _ = return ()
fun basic_type_name10 _ = return ()
fun basic_type_name11 _ = return ()
fun basic_type_name12 _ = return ()
fun basic_declaration_specifier1 _ = return ()
fun basic_declaration_specifier2 _ = return ()
fun basic_declaration_specifier3 _ = return ()
fun basic_declaration_specifier4 _ = return ()
fun basic_declaration_specifier5 _ = return ()
fun basic_type_specifier1 _ = return ()
fun basic_type_specifier2 _ = return ()
fun basic_type_specifier3 _ = return ()
fun basic_type_specifier4 _ = return ()
fun basic_type_specifier5 _ = return ()
fun basic_type_specifier6 _ = return ()
fun basic_type_specifier7 _ = return ()
fun sue_declaration_specifier1 _ = return ()
fun sue_declaration_specifier2 _ = return ()
fun sue_declaration_specifier3 _ = return ()
fun sue_declaration_specifier4 _ = return ()
fun sue_type_specifier1 _ = return ()
fun sue_type_specifier2 _ = return ()
fun sue_type_specifier3 _ = return ()
fun sue_type_specifier4 _ = return ()
fun sue_type_specifier5 _ = return ()
fun sue_type_specifier6 _ = return ()
fun typedef_declaration_specifier1 _ = return ()
fun typedef_declaration_specifier2 _ = return ()
fun typedef_declaration_specifier3 _ = return ()
fun typedef_declaration_specifier4 _ = return ()
fun typedef_declaration_specifier5 _ = return ()
fun typedef_declaration_specifier6 _ = return ()
fun typedef_type_specifier1 _ = return ()
fun typedef_type_specifier2 _ = return ()
fun typedef_type_specifier3 _ = return ()
fun typedef_type_specifier4 _ = return ()
fun typedef_type_specifier5 _ = return ()
fun typedef_type_specifier6 _ = return ()
fun typedef_type_specifier7 _ = return ()
fun typedef_type_specifier8 _ = return ()
fun typedef_type_specifier9 _ = return ()
fun typedef_type_specifier10 _ = return ()
fun typedef_type_specifier11 _ = return ()
fun typedef_type_specifier12 _ = return ()
fun typedef_type_specifier13 _ = return ()
fun typedef_type_specifier14 _ = return ()
fun elaborated_type_name1 _ = return ()
fun elaborated_type_name2 _ = return ()
fun struct_or_union_specifier1 _ = return ()
fun struct_or_union_specifier2 _ = return ()
fun struct_or_union_specifier3 _ = return ()
fun struct_or_union1 _ = return ()
fun struct_or_union2 _ = return ()
fun struct_declaration_list1 _ = return ()
fun struct_declaration_list2 _ = return ()
fun struct_declaration_list3 _ = return ()
fun struct_declaration1 _ = return ()
fun struct_declaration2 _ = return ()
fun struct_declaration3 _ = return ()
fun struct_default_declaring_list1 _ = return ()
fun struct_default_declaring_list2 _ = return ()
fun struct_default_declaring_list3 _ = return ()
fun struct_declaring_list1 _ = return ()
fun struct_declaring_list2 _ = return ()
fun struct_declaring_list3 _ = return ()
fun struct_declarator1 _ = return ()
fun struct_declarator2 _ = return ()
fun struct_declarator3 _ = return ()
fun struct_identifier_declarator1 _ = return ()
fun struct_identifier_declarator2 _ = return ()
fun struct_identifier_declarator3 _ = return ()
fun struct_identifier_declarator4 _ = return ()
fun enum_specifier1 _ = return ()
fun enum_specifier2 _ = return ()
fun enum_specifier3 _ = return ()
fun enum_specifier4 _ = return ()
fun enum_specifier5 _ = return ()
fun enumerator_list1 _ = return ()
fun enumerator_list2 _ = return ()
fun enumerator1 _ = return ()
fun enumerator2 _ = return ()
fun enumerator3 _ = return ()
fun enumerator4 _ = return ()
fun type_qualifier1 _ = return ()
fun type_qualifier2 _ = return ()
fun type_qualifier3 _ = return ()
fun type_qualifier4 _ = return ()
fun type_qualifier5 _ = return ()
fun type_qualifier6 _ = return ()
fun type_qualifier_list1 _ = return ()
fun type_qualifier_list2 _ = return ()
fun type_qualifier_list3 _ = return ()
fun declarator1 _ = return ()
fun declarator2 _ = return ()
fun asm_opt1 _ = return ()
fun asm_opt2 _ = return ()
fun typedef_declarator1 _ = return ()
fun typedef_declarator2 _ = return ()
fun parameter_typedef_declarator1 _ = return ()
fun parameter_typedef_declarator2 _ = return ()
fun parameter_typedef_declarator3 _ = return ()
fun clean_typedef_declarator1 _ = return ()
fun clean_typedef_declarator2 _ = return ()
fun clean_typedef_declarator3 _ = return ()
fun clean_typedef_declarator4 _ = return ()
fun clean_typedef_declarator5 _ = return ()
fun clean_postfix_typedef_declarator1 _ = return ()
fun clean_postfix_typedef_declarator2 _ = return ()
fun clean_postfix_typedef_declarator3 _ = return ()
fun clean_postfix_typedef_declarator4 _ = return ()
fun paren_typedef_declarator1 _ = return ()
fun paren_typedef_declarator2 _ = return ()
fun paren_typedef_declarator3 _ = return ()
fun paren_typedef_declarator4 _ = return ()
fun paren_typedef_declarator5 _ = return ()
fun paren_typedef_declarator6 _ = return ()
fun paren_typedef_declarator7 _ = return ()
fun paren_postfix_typedef_declarator1 _ = return ()
fun paren_postfix_typedef_declarator2 _ = return ()
fun paren_postfix_typedef_declarator3 _ = return ()
fun simple_paren_typedef_declarator1 _ = return ()
fun simple_paren_typedef_declarator2 _ = return ()
fun identifier_declarator1 _ = return ()
fun identifier_declarator2 _ = return ()
fun unary_identifier_declarator1 _ = return ()
fun unary_identifier_declarator2 _ = return ()
fun unary_identifier_declarator3 _ = return ()
fun unary_identifier_declarator4 _ = return ()
fun unary_identifier_declarator5 _ = return ()
fun postfix_identifier_declarator1 _ = return ()
fun postfix_identifier_declarator2 _ = return ()
fun postfix_identifier_declarator3 _ = return ()
fun postfix_identifier_declarator4 _ = return ()
fun postfix_identifier_declarator5 _ = return ()
fun paren_identifier_declarator1 _ = return ()
fun paren_identifier_declarator2 _ = return ()
fun paren_identifier_declarator3 _ = return ()
fun function_declarator_old _ = return ()
fun old_function_declarator1 _ = return ()
fun old_function_declarator2 _ = return ()
fun old_function_declarator3 _ = return ()
fun postfix_old_function_declarator1 _ = return ()
fun postfix_old_function_declarator2 _ = return ()
fun postfix_old_function_declarator3 _ = return ()
fun parameter_type_list1 _ = return ()
fun parameter_type_list2 _ = return ()
fun parameter_type_list3 _ = return ()
fun parameter_list1 _ = return ()
fun parameter_list2 _ = return ()
fun parameter_declaration1 _ = return ()
fun parameter_declaration2 _ = return ()
fun parameter_declaration3 _ = return ()
fun parameter_declaration4 _ = return ()
fun parameter_declaration5 _ = return ()
fun parameter_declaration6 _ = return ()
fun parameter_declaration7 _ = return ()
fun parameter_declaration8 _ = return ()
fun parameter_declaration9 _ = return ()
fun parameter_declaration10 _ = return ()
fun parameter_declaration11 _ = return ()
fun parameter_declaration12 _ = return ()
fun parameter_declaration13 _ = return ()
fun parameter_declaration14 _ = return ()
fun parameter_declaration15 _ = return ()
fun identifier_list1 _ = return ()
fun identifier_list2 _ = return ()
fun type_name1 _ = return ()
fun type_name2 _ = return ()
fun type_name3 _ = return ()
fun type_name4 _ = return ()
fun abstract_declarator1 _ = return ()
fun abstract_declarator2 _ = return ()
fun abstract_declarator3 _ = return ()
fun postfixing_abstract_declarator1 _ = return ()
fun postfixing_abstract_declarator2 _ = return ()
fun array_abstract_declarator1 _ = return ()
fun array_abstract_declarator2 _ = return ()
fun postfix_array_abstract_declarator1 _ = return ()
fun postfix_array_abstract_declarator2 _ = return ()
fun postfix_array_abstract_declarator3 _ = return ()
fun postfix_array_abstract_declarator4 _ = return ()
fun postfix_array_abstract_declarator5 _ = return ()
fun postfix_array_abstract_declarator6 _ = return ()
fun postfix_array_abstract_declarator7 _ = return ()
fun postfix_array_abstract_declarator8 _ = return ()
fun postfix_array_abstract_declarator9 _ = return ()
fun postfix_array_abstract_declarator10 _ = return ()
fun postfix_array_abstract_declarator11 _ = return ()
fun unary_abstract_declarator1 _ = return ()
fun unary_abstract_declarator2 _ = return ()
fun unary_abstract_declarator3 _ = return ()
fun unary_abstract_declarator4 _ = return ()
fun unary_abstract_declarator5 _ = return ()
fun unary_abstract_declarator6 _ = return ()
fun postfix_abstract_declarator1 _ = return ()
fun postfix_abstract_declarator2 _ = return ()
fun postfix_abstract_declarator3 _ = return ()
fun postfix_abstract_declarator4 _ = return ()
fun postfix_abstract_declarator5 _ = return ()
fun postfix_abstract_declarator6 _ = return ()
fun postfix_abstract_declarator7 _ = return ()
fun postfix_abstract_declarator8 _ = return ()
fun postfix_abstract_declarator9 _ = return ()
fun initializer1 _ = return ()
fun initializer2 _ = return ()
fun initializer3 _ = return ()
fun initializer_opt1 _ = return ()
fun initializer_opt2 _ = return ()
fun initializer_list1 _ = return ()
fun initializer_list2 _ = return ()
fun initializer_list3 _ = return ()
fun initializer_list4 _ = return ()
fun initializer_list5 _ = return ()
fun designation1 _ = return ()
fun designation2 _ = return ()
fun designation3 _ = return ()
fun designator_list1 _ = return ()
fun designator_list2 _ = return ()
fun designator1 _ = return ()
fun designator2 _ = return ()
fun designator3 _ = return ()
fun array_designator _ = return ()
fun primary_expression1 _ = return ()
fun primary_expression2 _ = return ()
fun primary_expression3 _ = return ()
fun primary_expression4 _ = return ()
fun primary_expression5 _ = return ()
fun primary_expression6 _ = return ()
fun primary_expression7 _ = return ()
fun primary_expression8 _ = return ()
fun primary_expression9 _ = return ()
fun generic_assoc_list1 _ = return ()
fun generic_assoc_list2 _ = return ()
fun generic_assoc1 _ = return ()
fun generic_assoc2 _ = return ()
fun offsetof_member_designator1 _ = return ()
fun offsetof_member_designator2 _ = return ()
fun offsetof_member_designator3 _ = return ()
fun postfix_expression1 _ = return ()
fun postfix_expression2 _ = return ()
fun postfix_expression3 _ = return ()
fun postfix_expression4 _ = return ()
fun postfix_expression5 _ = return ()
fun postfix_expression6 _ = return ()
fun postfix_expression7 _ = return ()
fun postfix_expression8 _ = return ()
fun postfix_expression9 _ = return ()
fun postfix_expression10 _ = return ()
fun argument_expression_list1 _ = return ()
fun argument_expression_list2 _ = return ()
fun unary_expression1 _ = return ()
fun unary_expression2 _ = return ()
fun unary_expression3 _ = return ()
fun unary_expression4 _ = return ()
fun unary_expression5 _ = return ()
fun unary_expression6 _ = return ()
fun unary_expression7 _ = return ()
fun unary_expression8 _ = return ()
fun unary_expression9 _ = return ()
fun unary_expression10 _ = return ()
fun unary_expression11 _ = return ()
fun unary_expression12 _ = return ()
fun unary_operator1 _ = return ()
fun unary_operator2 _ = return ()
fun unary_operator3 _ = return ()
fun unary_operator4 _ = return ()
fun unary_operator5 _ = return ()
fun unary_operator6 _ = return ()
fun cast_expression1 _ = return ()
fun cast_expression2 _ = return ()
fun multiplicative_expression1 _ = return ()
fun multiplicative_expression2 _ = return ()
fun multiplicative_expression3 _ = return ()
fun multiplicative_expression4 _ = return ()
fun additive_expression1 _ = return ()
fun additive_expression2 _ = return ()
fun additive_expression3 _ = return ()
fun shift_expression1 _ = return ()
fun shift_expression2 _ = return ()
fun shift_expression3 _ = return ()
fun relational_expression1 _ = return ()
fun relational_expression2 _ = return ()
fun relational_expression3 _ = return ()
fun relational_expression4 _ = return ()
fun relational_expression5 _ = return ()
fun equality_expression1 _ = return ()
fun equality_expression2 _ = return ()
fun equality_expression3 _ = return ()
fun and_expression1 _ = return ()
fun and_expression2 _ = return ()
fun exclusive_or_expression1 _ = return ()
fun exclusive_or_expression2 _ = return ()
fun inclusive_or_expression1 _ = return ()
fun inclusive_or_expression2 _ = return ()
fun logical_and_expression1 _ = return ()
fun logical_and_expression2 _ = return ()
fun logical_or_expression1 _ = return ()
fun logical_or_expression2 _ = return ()
fun conditional_expression1 _ = return ()
fun conditional_expression2 _ = return ()
fun conditional_expression3 _ = return ()
fun assignment_expression1 _ = return ()
fun assignment_expression2 _ = return ()
fun assignment_operator1 _ = return ()
fun assignment_operator2 _ = return ()
fun assignment_operator3 _ = return ()
fun assignment_operator4 _ = return ()
fun assignment_operator5 _ = return ()
fun assignment_operator6 _ = return ()
fun assignment_operator7 _ = return ()
fun assignment_operator8 _ = return ()
fun assignment_operator9 _ = return ()
fun assignment_operator10 _ = return ()
fun assignment_operator11 _ = return ()
fun expression1 _ = return ()
fun expression2 _ = return ()
fun comma_expression1 _ = return ()
fun comma_expression2 _ = return ()
fun expression_opt1 _ = return ()
fun expression_opt2 _ = return ()
fun assignment_expression_opt1 _ = return ()
fun assignment_expression_opt2 _ = return ()
fun constant_expression _ = return ()
fun constant1 _ = return ()
fun constant2 _ = return ()
fun constant3 _ = return ()
fun string_literal1 _ = return ()
fun string_literal2 _ = return ()
fun string_literal_list1 _ = return ()
fun string_literal_list2 _ = return ()
fun clang_version_literal _ = return ()
fun identifier1 _ = return ()
fun identifier2 _ = return ()
fun attrs_opt1 _ = return ()
fun attrs_opt2 _ = return ()
fun attrs1 _ = return ()
fun attrs2 _ = return ()
fun attr _ = return ()
fun attribute_list1 _ = return ()
fun attribute_list2 _ = return ()
fun attribute1 _ = return ()
fun attribute2 _ = return ()
fun attribute3 _ = return ()
fun attribute4 _ = return ()
fun attribute5 _ = return ()
fun attribute_params1 _ = return ()
fun attribute_params2 _ = return ()
fun attribute_params3 _ = return ()
fun attribute_params4 _ = return ()
fun attribute_params5 _ = return ()
fun attribute_params6 _ = return ()
end
signature StrictC_TOKENS =
sig
type ('a,'b) token
type arg
type svalue0
type svalue = arg -> svalue0 * arg
val x25_eof:  'a * 'a -> (svalue,'a) token
val clangcversion: (ClangCVersion) *  'a * 'a -> (svalue,'a) token
val x5f_x5f_builtin_types_compatible_p: (string) *  'a * 'a -> (svalue,'a) token
val x5f_x5f_builtin_offsetof: (string) *  'a * 'a -> (svalue,'a) token
val x5f_x5f_builtin_va_arg: (string) *  'a * 'a -> (svalue,'a) token
val x5f_x5f_imag_x5f_x5f: (string) *  'a * 'a -> (svalue,'a) token
val x5f_x5f_real_x5f_x5f: (string) *  'a * 'a -> (svalue,'a) token
val x5f_x5f_extension_x5f_x5f: (string) *  'a * 'a -> (svalue,'a) token
val x5f_x5f_attribute_x5f_x5f: (string) *  'a * 'a -> (svalue,'a) token
val tyident: (ident) *  'a * 'a -> (svalue,'a) token
val ident: (ident) *  'a * 'a -> (svalue,'a) token
val cstr: (cString) *  'a * 'a -> (svalue,'a) token
val cfloat: (cFloat) *  'a * 'a -> (svalue,'a) token
val cint: (cInteger) *  'a * 'a -> (svalue,'a) token
val cchar: (cChar) *  'a * 'a -> (svalue,'a) token
val while0: (string) *  'a * 'a -> (svalue,'a) token
val volatile: (string) *  'a * 'a -> (svalue,'a) token
val void: (string) *  'a * 'a -> (svalue,'a) token
val unsigned: (string) *  'a * 'a -> (svalue,'a) token
val union: (string) *  'a * 'a -> (svalue,'a) token
val x5f_x5f_thread: (string) *  'a * 'a -> (svalue,'a) token
val typeof: (string) *  'a * 'a -> (svalue,'a) token
val typedef: (string) *  'a * 'a -> (svalue,'a) token
val switch: (string) *  'a * 'a -> (svalue,'a) token
val struct0: (string) *  'a * 'a -> (svalue,'a) token
val x5f_Static_assert: (string) *  'a * 'a -> (svalue,'a) token
val static: (string) *  'a * 'a -> (svalue,'a) token
val sizeof: (string) *  'a * 'a -> (svalue,'a) token
val signed: (string) *  'a * 'a -> (svalue,'a) token
val short: (string) *  'a * 'a -> (svalue,'a) token
val return0: (string) *  'a * 'a -> (svalue,'a) token
val restrict: (string) *  'a * 'a -> (svalue,'a) token
val register: (string) *  'a * 'a -> (svalue,'a) token
val x5f_Nonnull: (string) *  'a * 'a -> (svalue,'a) token
val x5f_Nullable: (string) *  'a * 'a -> (svalue,'a) token
val x5f_Noreturn: (string) *  'a * 'a -> (svalue,'a) token
val x5f_x5f_label_x5f_x5f: (string) *  'a * 'a -> (svalue,'a) token
val long: (string) *  'a * 'a -> (svalue,'a) token
val x5f_x5f_int_x31_x32_x38: (string) *  'a * 'a -> (svalue,'a) token
val int: (string) *  'a * 'a -> (svalue,'a) token
val inline: (string) *  'a * 'a -> (svalue,'a) token
val if0: (string) *  'a * 'a -> (svalue,'a) token
val goto: (string) *  'a * 'a -> (svalue,'a) token
val x5f_Generic: (string) *  'a * 'a -> (svalue,'a) token
val for0: (string) *  'a * 'a -> (svalue,'a) token
val float: (string) *  'a * 'a -> (svalue,'a) token
val extern: (string) *  'a * 'a -> (svalue,'a) token
val enum: (string) *  'a * 'a -> (svalue,'a) token
val else0: (string) *  'a * 'a -> (svalue,'a) token
val double: (string) *  'a * 'a -> (svalue,'a) token
val do0: (string) *  'a * 'a -> (svalue,'a) token
val default: (string) *  'a * 'a -> (svalue,'a) token
val x5f_Complex: (string) *  'a * 'a -> (svalue,'a) token
val continue: (string) *  'a * 'a -> (svalue,'a) token
val const: (string) *  'a * 'a -> (svalue,'a) token
val char: (string) *  'a * 'a -> (svalue,'a) token
val case0: (string) *  'a * 'a -> (svalue,'a) token
val x5f_Bool: (string) *  'a * 'a -> (svalue,'a) token
val break: (string) *  'a * 'a -> (svalue,'a) token
val auto: (string) *  'a * 'a -> (svalue,'a) token
val asm: (string) *  'a * 'a -> (svalue,'a) token
val x5f_Atomic: (string) *  'a * 'a -> (svalue,'a) token
val alignas: (string) *  'a * 'a -> (svalue,'a) token
val alignof: (string) *  'a * 'a -> (svalue,'a) token
val x2e_x2e_x2e: (string) *  'a * 'a -> (svalue,'a) token
val x7d: (string) *  'a * 'a -> (svalue,'a) token
val x7b: (string) *  'a * 'a -> (svalue,'a) token
val x3b: (string) *  'a * 'a -> (svalue,'a) token
val x2c: (string) *  'a * 'a -> (svalue,'a) token
val x3e_x3e_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x3c_x3c_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x7c_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x5e_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x26_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x25_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x2f_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x2a_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x2d_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x2b_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x3d: (string) *  'a * 'a -> (svalue,'a) token
val x3a: (string) *  'a * 'a -> (svalue,'a) token
val x3f: (string) *  'a * 'a -> (svalue,'a) token
val x7c_x7c: (string) *  'a * 'a -> (svalue,'a) token
val x26_x26: (string) *  'a * 'a -> (svalue,'a) token
val x7c: (string) *  'a * 'a -> (svalue,'a) token
val x5e: (string) *  'a * 'a -> (svalue,'a) token
val x21_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x3d_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x3e_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x3e: (string) *  'a * 'a -> (svalue,'a) token
val x3c_x3d: (string) *  'a * 'a -> (svalue,'a) token
val x3c: (string) *  'a * 'a -> (svalue,'a) token
val x3e_x3e: (string) *  'a * 'a -> (svalue,'a) token
val x3c_x3c: (string) *  'a * 'a -> (svalue,'a) token
val x26: (string) *  'a * 'a -> (svalue,'a) token
val x25: (string) *  'a * 'a -> (svalue,'a) token
val x2f: (string) *  'a * 'a -> (svalue,'a) token
val x2a: (string) *  'a * 'a -> (svalue,'a) token
val x2d: (string) *  'a * 'a -> (svalue,'a) token
val x2b: (string) *  'a * 'a -> (svalue,'a) token
val x2d_x2d: (string) *  'a * 'a -> (svalue,'a) token
val x2b_x2b: (string) *  'a * 'a -> (svalue,'a) token
val x7e: (string) *  'a * 'a -> (svalue,'a) token
val x21: (string) *  'a * 'a -> (svalue,'a) token
val x2e: (string) *  'a * 'a -> (svalue,'a) token
val x2d_x3e: (string) *  'a * 'a -> (svalue,'a) token
val x5d: (string) *  'a * 'a -> (svalue,'a) token
val x5b: (string) *  'a * 'a -> (svalue,'a) token
val x29: (string) *  'a * 'a -> (svalue,'a) token
val x28: (string) *  'a * 'a -> (svalue,'a) token
val error:  'a * 'a -> (svalue,'a) token
end
signature StrictC_LRVALS=
sig
structure Tokens : StrictC_TOKENS
structure ParserData:PARSER_DATA1
sharing type ParserData.Token.token = Tokens.token
end
