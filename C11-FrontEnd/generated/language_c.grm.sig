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
