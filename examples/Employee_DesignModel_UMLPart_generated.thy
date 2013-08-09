theory Employee_DesignModel_UMLPart_generated imports "../src/OCL_main" begin

(* 1 *********************************** *)
datatype type\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d = mk\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d 
datatype typeoid\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d = mkoid\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d oid type\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d
datatype type\<^isub>V\<^isub>o\<^isub>i\<^isub>d = mk\<^isub>V\<^isub>o\<^isub>i\<^isub>d_\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d type\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d
                        | mk\<^isub>V\<^isub>o\<^isub>i\<^isub>d 
datatype typeoid\<^isub>V\<^isub>o\<^isub>i\<^isub>d = mkoid\<^isub>V\<^isub>o\<^isub>i\<^isub>d oid type\<^isub>V\<^isub>o\<^isub>i\<^isub>d
datatype type\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n = mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d type\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d
                        | mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_\<^isub>V\<^isub>o\<^isub>i\<^isub>d type\<^isub>V\<^isub>o\<^isub>i\<^isub>d
                        | mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n "int option" "oid option"
datatype typeoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n = mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid type\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n
datatype type\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y = mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d type\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d
                        | mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>V\<^isub>o\<^isub>i\<^isub>d type\<^isub>V\<^isub>o\<^isub>i\<^isub>d
                        | mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n type\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n
                        | mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y 
datatype typeoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y = mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y oid type\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y

(* 2 *********************************** *)
datatype \<AA> = in\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d typeoid\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d
                        | in\<^isub>V\<^isub>o\<^isub>i\<^isub>d typeoid\<^isub>V\<^isub>o\<^isub>i\<^isub>d
                        | in\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n typeoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n
                        | in\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y typeoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y

(* 3 *********************************** *)
type_synonym Boolean = "\<AA> Boolean"
type_synonym Invalid = "(\<AA>, typeoid\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d option option) val"
type_synonym Void = "(\<AA>, typeoid\<^isub>V\<^isub>o\<^isub>i\<^isub>d option option) val"
type_synonym Person = "(\<AA>, typeoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n option option) val"
type_synonym OclAny = "(\<AA>, typeoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y option option) val"

(* 4 *********************************** *)
instantiation typeoid\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d :: object
begin
  definition oid_of_typeoid\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_def : "oid_of x = (case x of mkoid\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d oid _ \<Rightarrow> oid)"
  instance ..
end
instantiation typeoid\<^isub>V\<^isub>o\<^isub>i\<^isub>d :: object
begin
  definition oid_of_typeoid\<^isub>V\<^isub>o\<^isub>i\<^isub>d_def : "oid_of x = (case x of mkoid\<^isub>V\<^isub>o\<^isub>i\<^isub>d oid _ \<Rightarrow> oid)"
  instance ..
end
instantiation typeoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n :: object
begin
  definition oid_of_typeoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_def : "oid_of x = (case x of mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid _ \<Rightarrow> oid)"
  instance ..
end
instantiation typeoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y :: object
begin
  definition oid_of_typeoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_def : "oid_of x = (case x of mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y oid _ \<Rightarrow> oid)"
  instance ..
end

(* 5 *********************************** *)
instantiation \<AA> :: object
begin
  definition oid_of_\<AA>_def : "oid_of x = (case x of in\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d Invalid \<Rightarrow> oid_of Invalid
    | in\<^isub>V\<^isub>o\<^isub>i\<^isub>d Void \<Rightarrow> oid_of Void
    | in\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n Person \<Rightarrow> oid_of Person
    | in\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y OclAny \<Rightarrow> oid_of OclAny)"
  instance ..
end

(* 6 *********************************** *)
defs(overloaded) StrictRefEq\<^isub>O\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d : "(x::Invalid) \<doteq> y \<equiv> StrictRefEq\<^isub>O\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t x y"
defs(overloaded) StrictRefEq\<^isub>O\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_\<^isub>V\<^isub>o\<^isub>i\<^isub>d : "(x::Void) \<doteq> y \<equiv> StrictRefEq\<^isub>O\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t x y"
defs(overloaded) StrictRefEq\<^isub>O\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n : "(x::Person) \<doteq> y \<equiv> StrictRefEq\<^isub>O\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t x y"
defs(overloaded) StrictRefEq\<^isub>O\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y : "(x::OclAny) \<doteq> y \<equiv> StrictRefEq\<^isub>O\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t x y"

(* 7 *********************************** *)
consts OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d :: "'\<alpha> \<Rightarrow> Invalid" ("(_) .oclAsType'(Invalid')")
consts OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d :: "'\<alpha> \<Rightarrow> Void" ("(_) .oclAsType'(Void')")
consts OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n :: "'\<alpha> \<Rightarrow> Person" ("(_) .oclAsType'(Person')")
consts OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y :: "'\<alpha> \<Rightarrow> OclAny" ("(_) .oclAsType'(OclAny')")

(* 8 *********************************** *)
definition "OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_\<AA> = (\<lambda>u. (case u of (in\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y ((mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (oid) ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d (Invalid)))))) \<Rightarrow> \<lfloor>mkoid\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d oid Invalid\<rfloor>
    | (in\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n ((mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (oid) ((mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d (Invalid)))))) \<Rightarrow> \<lfloor>mkoid\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d oid Invalid\<rfloor>
    | (in\<^isub>V\<^isub>o\<^isub>i\<^isub>d ((mkoid\<^isub>V\<^isub>o\<^isub>i\<^isub>d (oid) ((mk\<^isub>V\<^isub>o\<^isub>i\<^isub>d_\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d (Invalid)))))) \<Rightarrow> \<lfloor>mkoid\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d oid Invalid\<rfloor>
    | (in\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d (Invalid)) \<Rightarrow> \<lfloor>Invalid\<rfloor>
    | _ \<Rightarrow> None))"
definition "OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_\<AA> = (\<lambda>u. (case u of (in\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y ((mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (oid) ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>V\<^isub>o\<^isub>i\<^isub>d (Void)))))) \<Rightarrow> \<lfloor>mkoid\<^isub>V\<^isub>o\<^isub>i\<^isub>d oid Void\<rfloor>
    | (in\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n ((mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (oid) ((mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_\<^isub>V\<^isub>o\<^isub>i\<^isub>d (Void)))))) \<Rightarrow> \<lfloor>mkoid\<^isub>V\<^isub>o\<^isub>i\<^isub>d oid Void\<rfloor>
    | (in\<^isub>V\<^isub>o\<^isub>i\<^isub>d (Void)) \<Rightarrow> \<lfloor>Void\<rfloor>
    | (in\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d (mkoid\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d oid Invalid)) \<Rightarrow> \<lfloor>(mkoid\<^isub>V\<^isub>o\<^isub>i\<^isub>d (oid) ((mk\<^isub>V\<^isub>o\<^isub>i\<^isub>d_\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d (Invalid))))\<rfloor>
    | _ \<Rightarrow> None))"
definition "OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_\<AA> = (\<lambda>u. (case u of (in\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y ((mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (oid) ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person)))))) \<Rightarrow> \<lfloor>mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid Person\<rfloor>
    | (in\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person)) \<Rightarrow> \<lfloor>Person\<rfloor>
    | (in\<^isub>V\<^isub>o\<^isub>i\<^isub>d (mkoid\<^isub>V\<^isub>o\<^isub>i\<^isub>d oid Void)) \<Rightarrow> \<lfloor>(mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (oid) ((mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_\<^isub>V\<^isub>o\<^isub>i\<^isub>d (Void))))\<rfloor>
    | (in\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d (mkoid\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d oid Invalid)) \<Rightarrow> \<lfloor>(mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (oid) ((mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d (Invalid))))\<rfloor>
    | _ \<Rightarrow> None))"
definition "OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<AA> = (\<lambda>u. \<lfloor>(case u of (in\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (OclAny)) \<Rightarrow> OclAny
    | (in\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid Person)) \<Rightarrow> (mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (oid) ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person))))
    | (in\<^isub>V\<^isub>o\<^isub>i\<^isub>d (mkoid\<^isub>V\<^isub>o\<^isub>i\<^isub>d oid Void)) \<Rightarrow> (mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (oid) ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>V\<^isub>o\<^isub>i\<^isub>d (Void))))
    | (in\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d (mkoid\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d oid Invalid)) \<Rightarrow> (mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (oid) ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d (Invalid)))))\<rfloor>)"

(* 9 *********************************** *)
defs(overloaded) OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny : "(x::OclAny) .oclAsType(Invalid) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (oid) ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d (Invalid))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>mkoid\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d oid Invalid\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person : "(x::Person) .oclAsType(Invalid) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (oid) ((mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d (Invalid))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>mkoid\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d oid Invalid\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void : "(x::Void) .oclAsType(Invalid) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>V\<^isub>o\<^isub>i\<^isub>d (oid) ((mk\<^isub>V\<^isub>o\<^isub>i\<^isub>d_\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d (Invalid))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>mkoid\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d oid Invalid\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid : "(x::Invalid) .oclAsType(Invalid) \<equiv> x"
defs(overloaded) OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny : "(x::OclAny) .oclAsType(Void) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (oid) ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>V\<^isub>o\<^isub>i\<^isub>d (Void))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>mkoid\<^isub>V\<^isub>o\<^isub>i\<^isub>d oid Void\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person : "(x::Person) .oclAsType(Void) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (oid) ((mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_\<^isub>V\<^isub>o\<^isub>i\<^isub>d (Void))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>mkoid\<^isub>V\<^isub>o\<^isub>i\<^isub>d oid Void\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void : "(x::Void) .oclAsType(Void) \<equiv> x"
defs(overloaded) OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid : "(x::Invalid) .oclAsType(Void) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>mkoid\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d oid Invalid\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^isub>V\<^isub>o\<^isub>i\<^isub>d (oid) ((mk\<^isub>V\<^isub>o\<^isub>i\<^isub>d_\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d (Invalid))))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny : "(x::OclAny) .oclAsType(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (oid) ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid Person\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person : "(x::Person) .oclAsType(Person) \<equiv> x"
defs(overloaded) OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void : "(x::Void) .oclAsType(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>mkoid\<^isub>V\<^isub>o\<^isub>i\<^isub>d oid Void\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (oid) ((mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_\<^isub>V\<^isub>o\<^isub>i\<^isub>d (Void))))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid : "(x::Invalid) .oclAsType(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>mkoid\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d oid Invalid\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (oid) ((mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d (Invalid))))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny : "(x::OclAny) .oclAsType(OclAny) \<equiv> x"
defs(overloaded) OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person : "(x::Person) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid Person\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (oid) ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person))))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void : "(x::Void) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>mkoid\<^isub>V\<^isub>o\<^isub>i\<^isub>d oid Void\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (oid) ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>V\<^isub>o\<^isub>i\<^isub>d (Void))))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid : "(x::Invalid) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>mkoid\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d oid Invalid\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (oid) ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d (Invalid))))\<rfloor>\<rfloor>))"

(* 10 *********************************** *)
lemmas [simp] = OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid
                OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void
                OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person
                OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny

(* 11 *********************************** *)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp_all)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp_all)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp_all)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp_all)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclAsType(OclAny)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclAsType(OclAny)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::Person) .oclAsType(OclAny)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::Person) .oclAsType(OclAny)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Void) .oclAsType(OclAny)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Void) .oclAsType(OclAny)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::Void) .oclAsType(OclAny)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::Void) .oclAsType(OclAny)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Invalid) .oclAsType(OclAny)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Invalid) .oclAsType(OclAny)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::Invalid) .oclAsType(OclAny)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::Invalid) .oclAsType(OclAny)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclAsType(Person)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclAsType(Person)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::OclAny) .oclAsType(Person)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::OclAny) .oclAsType(Person)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclAsType(Person)))))"
by(rule cpI1, simp_all)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclAsType(Person)))))"
by(rule cpI1, simp_all)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::Person) .oclAsType(Person)))))"
by(rule cpI1, simp_all)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::Person) .oclAsType(Person)))))"
by(rule cpI1, simp_all)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Void) .oclAsType(Person)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Void) .oclAsType(Person)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::Void) .oclAsType(Person)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::Void) .oclAsType(Person)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Invalid) .oclAsType(Person)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Invalid) .oclAsType(Person)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::Invalid) .oclAsType(Person)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::Invalid) .oclAsType(Person)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid)
lemma cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclAsType(Void)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny)
lemma cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclAsType(Void)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny)
lemma cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::OclAny) .oclAsType(Void)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny)
lemma cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::OclAny) .oclAsType(Void)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny)
lemma cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclAsType(Void)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person)
lemma cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclAsType(Void)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person)
lemma cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::Person) .oclAsType(Void)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person)
lemma cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::Person) .oclAsType(Void)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person)
lemma cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Void) .oclAsType(Void)))))"
by(rule cpI1, simp_all)
lemma cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Void) .oclAsType(Void)))))"
by(rule cpI1, simp_all)
lemma cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::Void) .oclAsType(Void)))))"
by(rule cpI1, simp_all)
lemma cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::Void) .oclAsType(Void)))))"
by(rule cpI1, simp_all)
lemma cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Invalid) .oclAsType(Void)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid)
lemma cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Invalid) .oclAsType(Void)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid)
lemma cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::Invalid) .oclAsType(Void)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid)
lemma cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::Invalid) .oclAsType(Void)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid)
lemma cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclAsType(Invalid)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny)
lemma cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclAsType(Invalid)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny)
lemma cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::OclAny) .oclAsType(Invalid)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny)
lemma cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::OclAny) .oclAsType(Invalid)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny)
lemma cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclAsType(Invalid)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person)
lemma cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclAsType(Invalid)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person)
lemma cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::Person) .oclAsType(Invalid)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person)
lemma cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::Person) .oclAsType(Invalid)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person)
lemma cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Void) .oclAsType(Invalid)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void)
lemma cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Void) .oclAsType(Invalid)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void)
lemma cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::Void) .oclAsType(Invalid)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void)
lemma cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::Void) .oclAsType(Invalid)))))"
by(rule cpI1, simp_all add: OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void)
lemma cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Invalid) .oclAsType(Invalid)))))"
by(rule cpI1, simp_all)
lemma cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Invalid) .oclAsType(Invalid)))))"
by(rule cpI1, simp_all)
lemma cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::Invalid) .oclAsType(Invalid)))))"
by(rule cpI1, simp_all)
lemma cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::Invalid) .oclAsType(Invalid)))))"
by(rule cpI1, simp_all)

(* 12 *********************************** *)
lemmas [simp] = cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_OclAny
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_OclAny
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void_OclAny
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid_OclAny
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Person
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Person
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void_Person
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid_Person
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Void
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Void
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void_Void
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid_Void
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Invalid
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Invalid
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void_Invalid
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid_Invalid
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_OclAny
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_OclAny
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void_OclAny
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid_OclAny
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Person
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Person
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void_Person
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid_Person
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Void
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Void
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void_Void
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid_Void
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Invalid
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Invalid
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void_Invalid
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid_Invalid
                cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny_OclAny
                cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person_OclAny
                cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void_OclAny
                cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid_OclAny
                cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny_Person
                cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person_Person
                cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void_Person
                cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid_Person
                cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny_Void
                cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person_Void
                cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void_Void
                cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid_Void
                cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny_Invalid
                cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person_Invalid
                cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void_Invalid
                cp_OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid_Invalid
                cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny_OclAny
                cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person_OclAny
                cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void_OclAny
                cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid_OclAny
                cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny_Person
                cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person_Person
                cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void_Person
                cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid_Person
                cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny_Void
                cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person_Void
                cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void_Void
                cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid_Void
                cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny_Invalid
                cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person_Invalid
                cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void_Invalid
                cp_OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid_Invalid

(* 13 *********************************** *)
lemma OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_invalid : "((invalid::OclAny) .oclAsType(OclAny)) = invalid"
by(simp)
lemma OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_invalid : "((invalid::Person) .oclAsType(OclAny)) = invalid"
by(rule ext, simp add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person bot_option_def invalid_def)
lemma OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void_invalid : "((invalid::Void) .oclAsType(OclAny)) = invalid"
by(rule ext, simp add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void bot_option_def invalid_def)
lemma OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid_invalid : "((invalid::Invalid) .oclAsType(OclAny)) = invalid"
by(rule ext, simp add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid bot_option_def invalid_def)
lemma OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_null : "((null::OclAny) .oclAsType(OclAny)) = null"
by(simp)
lemma OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_null : "((null::Person) .oclAsType(OclAny)) = null"
by(rule ext, simp add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void_null : "((null::Void) .oclAsType(OclAny)) = null"
by(rule ext, simp add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid_null : "((null::Invalid) .oclAsType(OclAny)) = null"
by(rule ext, simp add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_invalid : "((invalid::OclAny) .oclAsType(Person)) = invalid"
by(rule ext, simp add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny bot_option_def invalid_def)
lemma OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_invalid : "((invalid::Person) .oclAsType(Person)) = invalid"
by(simp)
lemma OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void_invalid : "((invalid::Void) .oclAsType(Person)) = invalid"
by(rule ext, simp add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void bot_option_def invalid_def)
lemma OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid_invalid : "((invalid::Invalid) .oclAsType(Person)) = invalid"
by(rule ext, simp add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid bot_option_def invalid_def)
lemma OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_null : "((null::OclAny) .oclAsType(Person)) = null"
by(rule ext, simp add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_null : "((null::Person) .oclAsType(Person)) = null"
by(simp)
lemma OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void_null : "((null::Void) .oclAsType(Person)) = null"
by(rule ext, simp add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid_null : "((null::Invalid) .oclAsType(Person)) = null"
by(rule ext, simp add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny_invalid : "((invalid::OclAny) .oclAsType(Void)) = invalid"
by(rule ext, simp add: OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny bot_option_def invalid_def)
lemma OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person_invalid : "((invalid::Person) .oclAsType(Void)) = invalid"
by(rule ext, simp add: OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person bot_option_def invalid_def)
lemma OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void_invalid : "((invalid::Void) .oclAsType(Void)) = invalid"
by(simp)
lemma OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid_invalid : "((invalid::Invalid) .oclAsType(Void)) = invalid"
by(rule ext, simp add: OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid bot_option_def invalid_def)
lemma OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny_null : "((null::OclAny) .oclAsType(Void)) = null"
by(rule ext, simp add: OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person_null : "((null::Person) .oclAsType(Void)) = null"
by(rule ext, simp add: OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void_null : "((null::Void) .oclAsType(Void)) = null"
by(simp)
lemma OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid_null : "((null::Invalid) .oclAsType(Void)) = null"
by(rule ext, simp add: OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny_invalid : "((invalid::OclAny) .oclAsType(Invalid)) = invalid"
by(rule ext, simp add: OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny bot_option_def invalid_def)
lemma OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person_invalid : "((invalid::Person) .oclAsType(Invalid)) = invalid"
by(rule ext, simp add: OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person bot_option_def invalid_def)
lemma OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void_invalid : "((invalid::Void) .oclAsType(Invalid)) = invalid"
by(rule ext, simp add: OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void bot_option_def invalid_def)
lemma OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid_invalid : "((invalid::Invalid) .oclAsType(Invalid)) = invalid"
by(simp)
lemma OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny_null : "((null::OclAny) .oclAsType(Invalid)) = null"
by(rule ext, simp add: OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person_null : "((null::Person) .oclAsType(Invalid)) = null"
by(rule ext, simp add: OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void_null : "((null::Void) .oclAsType(Invalid)) = null"
by(rule ext, simp add: OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid_null : "((null::Invalid) .oclAsType(Invalid)) = null"
by(simp)

(* 14 *********************************** *)
lemmas [simp] = OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_invalid
                OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_invalid
                OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void_invalid
                OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid_invalid
                OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_null
                OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_null
                OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void_null
                OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid_null
                OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_invalid
                OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_invalid
                OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void_invalid
                OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid_invalid
                OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_null
                OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_null
                OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void_null
                OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid_null
                OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny_invalid
                OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person_invalid
                OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void_invalid
                OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid_invalid
                OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny_null
                OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person_null
                OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void_null
                OclAsType\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid_null
                OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny_invalid
                OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person_invalid
                OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void_invalid
                OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid_invalid
                OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny_null
                OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person_null
                OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void_null
                OclAsType\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid_null

(* 15 *********************************** *)
consts OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Invalid')")
consts OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Void')")
consts OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Person')")
consts OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(OclAny')")

(* 16 *********************************** *)
defs(overloaded) OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny : "(x::OclAny) .oclIsTypeOf(Invalid) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (_) ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person : "(x::Person) .oclIsTypeOf(Invalid) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (_) ((mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void : "(x::Void) .oclIsTypeOf(Invalid) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>V\<^isub>o\<^isub>i\<^isub>d (_) ((mk\<^isub>V\<^isub>o\<^isub>i\<^isub>d_\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid : "(x::Invalid) .oclIsTypeOf(Invalid) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d (_) ((mk\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d )))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny : "(x::OclAny) .oclIsTypeOf(Void) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (_) ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>V\<^isub>o\<^isub>i\<^isub>d (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person : "(x::Person) .oclIsTypeOf(Void) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (_) ((mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_\<^isub>V\<^isub>o\<^isub>i\<^isub>d (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void : "(x::Void) .oclIsTypeOf(Void) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>V\<^isub>o\<^isub>i\<^isub>d (_) ((mk\<^isub>V\<^isub>o\<^isub>i\<^isub>d )))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid : "(x::Invalid) .oclIsTypeOf(Void) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny : "(x::OclAny) .oclIsTypeOf(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (_) ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person : "(x::Person) .oclIsTypeOf(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (_) ((mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (_) (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void : "(x::Void) .oclIsTypeOf(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid : "(x::Invalid) .oclIsTypeOf(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny : "(x::OclAny) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (_) ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y )))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person : "(x::Person) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void : "(x::Void) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid : "(x::Invalid) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"

(* 17 *********************************** *)
lemmas [simp] = OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid
                OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void
                OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person
                OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny

(* 18 *********************************** *)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::Person) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::Person) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Void) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Void) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::Void) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::Void) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Invalid) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Invalid) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::Invalid) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::Invalid) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::OclAny) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::OclAny) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::Person) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::Person) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Void) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Void) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::Void) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::Void) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Invalid) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Invalid) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::Invalid) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::Invalid) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid)
lemma cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsTypeOf(Void)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny)
lemma cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsTypeOf(Void)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny)
lemma cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::OclAny) .oclIsTypeOf(Void)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny)
lemma cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::OclAny) .oclIsTypeOf(Void)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny)
lemma cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsTypeOf(Void)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person)
lemma cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsTypeOf(Void)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person)
lemma cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::Person) .oclIsTypeOf(Void)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person)
lemma cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::Person) .oclIsTypeOf(Void)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person)
lemma cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Void) .oclIsTypeOf(Void)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void)
lemma cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Void) .oclIsTypeOf(Void)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void)
lemma cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::Void) .oclIsTypeOf(Void)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void)
lemma cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::Void) .oclIsTypeOf(Void)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void)
lemma cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Invalid) .oclIsTypeOf(Void)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid)
lemma cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Invalid) .oclIsTypeOf(Void)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid)
lemma cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::Invalid) .oclIsTypeOf(Void)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid)
lemma cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::Invalid) .oclIsTypeOf(Void)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid)
lemma cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsTypeOf(Invalid)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny)
lemma cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsTypeOf(Invalid)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny)
lemma cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::OclAny) .oclIsTypeOf(Invalid)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny)
lemma cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::OclAny) .oclIsTypeOf(Invalid)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny)
lemma cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsTypeOf(Invalid)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person)
lemma cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsTypeOf(Invalid)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person)
lemma cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::Person) .oclIsTypeOf(Invalid)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person)
lemma cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::Person) .oclIsTypeOf(Invalid)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person)
lemma cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Void) .oclIsTypeOf(Invalid)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void)
lemma cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Void) .oclIsTypeOf(Invalid)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void)
lemma cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::Void) .oclIsTypeOf(Invalid)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void)
lemma cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid_Void : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::Void) .oclIsTypeOf(Invalid)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void)
lemma cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Invalid) .oclIsTypeOf(Invalid)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid)
lemma cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Invalid) .oclIsTypeOf(Invalid)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid)
lemma cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Void)))::Invalid) .oclIsTypeOf(Invalid)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid)
lemma cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid_Invalid : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Invalid)))::Invalid) .oclIsTypeOf(Invalid)))))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid)

(* 19 *********************************** *)
lemmas [simp] = cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_OclAny
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_OclAny
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void_OclAny
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid_OclAny
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Person
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Person
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void_Person
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid_Person
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Void
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Void
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void_Void
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid_Void
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Invalid
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Invalid
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void_Invalid
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid_Invalid
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_OclAny
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_OclAny
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void_OclAny
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid_OclAny
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Person
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Person
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void_Person
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid_Person
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Void
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Void
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void_Void
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid_Void
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Invalid
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Invalid
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void_Invalid
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid_Invalid
                cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny_OclAny
                cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person_OclAny
                cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void_OclAny
                cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid_OclAny
                cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny_Person
                cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person_Person
                cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void_Person
                cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid_Person
                cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny_Void
                cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person_Void
                cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void_Void
                cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid_Void
                cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny_Invalid
                cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person_Invalid
                cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void_Invalid
                cp_OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid_Invalid
                cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny_OclAny
                cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person_OclAny
                cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void_OclAny
                cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid_OclAny
                cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny_Person
                cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person_Person
                cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void_Person
                cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid_Person
                cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny_Void
                cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person_Void
                cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void_Void
                cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid_Void
                cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny_Invalid
                cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person_Invalid
                cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void_Invalid
                cp_OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid_Invalid

(* 20 *********************************** *)
lemma OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_invalid : "((invalid::OclAny) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_invalid : "((invalid::Person) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void_invalid : "((invalid::Void) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid_invalid : "((invalid::Invalid) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_null : "((null::OclAny) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_null : "((null::Person) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void_null : "((null::Void) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid_null : "((null::Invalid) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_invalid : "((invalid::OclAny) .oclIsTypeOf(Person)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_invalid : "((invalid::Person) .oclIsTypeOf(Person)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void_invalid : "((invalid::Void) .oclIsTypeOf(Person)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid_invalid : "((invalid::Invalid) .oclIsTypeOf(Person)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_null : "((null::OclAny) .oclIsTypeOf(Person)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_null : "((null::Person) .oclIsTypeOf(Person)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void_null : "((null::Void) .oclIsTypeOf(Person)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid_null : "((null::Invalid) .oclIsTypeOf(Person)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny_invalid : "((invalid::OclAny) .oclIsTypeOf(Void)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person_invalid : "((invalid::Person) .oclIsTypeOf(Void)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void_invalid : "((invalid::Void) .oclIsTypeOf(Void)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid_invalid : "((invalid::Invalid) .oclIsTypeOf(Void)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny_null : "((null::OclAny) .oclIsTypeOf(Void)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person_null : "((null::Person) .oclIsTypeOf(Void)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void_null : "((null::Void) .oclIsTypeOf(Void)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid_null : "((null::Invalid) .oclIsTypeOf(Void)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny_invalid : "((invalid::OclAny) .oclIsTypeOf(Invalid)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person_invalid : "((invalid::Person) .oclIsTypeOf(Invalid)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void_invalid : "((invalid::Void) .oclIsTypeOf(Invalid)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid_invalid : "((invalid::Invalid) .oclIsTypeOf(Invalid)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny_null : "((null::OclAny) .oclIsTypeOf(Invalid)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person_null : "((null::Person) .oclIsTypeOf(Invalid)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void_null : "((null::Void) .oclIsTypeOf(Invalid)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid_null : "((null::Invalid) .oclIsTypeOf(Invalid)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid bot_option_def null_fun_def null_option_def)

(* 21 *********************************** *)
lemmas [simp] = OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_invalid
                OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_invalid
                OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void_invalid
                OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid_invalid
                OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_null
                OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_null
                OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void_null
                OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid_null
                OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_invalid
                OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_invalid
                OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void_invalid
                OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid_invalid
                OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_null
                OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_null
                OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void_null
                OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid_null
                OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny_invalid
                OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person_invalid
                OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void_invalid
                OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid_invalid
                OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny_null
                OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person_null
                OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void_null
                OclIsTypeOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid_null
                OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny_invalid
                OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person_invalid
                OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void_invalid
                OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid_invalid
                OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny_null
                OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person_null
                OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void_null
                OclIsTypeOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid_null

(* 22 *********************************** *)
consts OclIsKindOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Invalid')")
consts OclIsKindOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Void')")
consts OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Person')")
consts OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(OclAny')")

(* 23 *********************************** *)
defs(overloaded) OclIsKindOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_OclAny : "(x::OclAny) .oclIsKindOf(Invalid) \<equiv> (x .oclIsTypeOf(Invalid))"
defs(overloaded) OclIsKindOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Person : "(x::Person) .oclIsKindOf(Invalid) \<equiv> (x .oclIsTypeOf(Invalid))"
defs(overloaded) OclIsKindOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Void : "(x::Void) .oclIsKindOf(Invalid) \<equiv> (x .oclIsTypeOf(Invalid))"
defs(overloaded) OclIsKindOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid : "(x::Invalid) .oclIsKindOf(Invalid) \<equiv> (x .oclIsTypeOf(Invalid))"
defs(overloaded) OclIsKindOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_OclAny : "(x::OclAny) .oclIsKindOf(Void) \<equiv> (x .oclIsTypeOf(Void)) or (x .oclIsKindOf(Invalid))"
defs(overloaded) OclIsKindOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Person : "(x::Person) .oclIsKindOf(Void) \<equiv> (x .oclIsTypeOf(Void)) or (x .oclIsKindOf(Invalid))"
defs(overloaded) OclIsKindOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void : "(x::Void) .oclIsKindOf(Void) \<equiv> (x .oclIsTypeOf(Void)) or (x .oclIsKindOf(Invalid))"
defs(overloaded) OclIsKindOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Invalid : "(x::Invalid) .oclIsKindOf(Void) \<equiv> (x .oclIsTypeOf(Void)) or (x .oclIsKindOf(Invalid))"
defs(overloaded) OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny : "(x::OclAny) .oclIsKindOf(Person) \<equiv> (x .oclIsTypeOf(Person)) or (x .oclIsKindOf(Void))"
defs(overloaded) OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person : "(x::Person) .oclIsKindOf(Person) \<equiv> (x .oclIsTypeOf(Person)) or (x .oclIsKindOf(Void))"
defs(overloaded) OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Void : "(x::Void) .oclIsKindOf(Person) \<equiv> (x .oclIsTypeOf(Person)) or (x .oclIsKindOf(Void))"
defs(overloaded) OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Invalid : "(x::Invalid) .oclIsKindOf(Person) \<equiv> (x .oclIsTypeOf(Person)) or (x .oclIsKindOf(Void))"
defs(overloaded) OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny : "(x::OclAny) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Person))"
defs(overloaded) OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person : "(x::Person) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Person))"
defs(overloaded) OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Void : "(x::Void) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Person))"
defs(overloaded) OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Invalid : "(x::Invalid) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Person))"

(* 24 *********************************** *)
lemmas [simp] = OclIsKindOf\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d_Invalid
                OclIsKindOf\<^isub>V\<^isub>o\<^isub>i\<^isub>d_Void
                OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person
                OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny

(* 25 *********************************** *)
definition "eval_extract x f = (\<lambda>\<tau>. (case x \<tau> of \<lfloor>\<lfloor>obj\<rfloor>\<rfloor> \<Rightarrow> (f ((oid_of (obj))) (\<tau>))
    | _ \<Rightarrow> invalid \<tau>))"
definition "in_pre_state = fst"
definition "in_post_state = snd"
definition "reconst_basetype = (\<lambda>convert x. (convert (x)))"

(* 26 *********************************** *)
definition "deref_oid\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^isub>I\<^isub>n\<^isub>v\<^isub>a\<^isub>l\<^isub>i\<^isub>d obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"
definition "deref_oid\<^isub>V\<^isub>o\<^isub>i\<^isub>d fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^isub>V\<^isub>o\<^isub>i\<^isub>d obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"
definition "deref_oid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"
definition "deref_oid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"

(* 27 *********************************** *)
definition "select\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>s\<^isup>a\<^isup>l\<^isup>a\<^isup>r\<^isup>y f = (\<lambda>x. (case x of (mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (_) ((mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (\<bottom>) (_)))) \<Rightarrow> null
    | (mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (_) ((mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (\<lfloor>salary\<rfloor>) (_)))) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (salary))
    | _ \<Rightarrow> invalid))"
definition "select\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>b\<^isup>o\<^isup>s\<^isup>s f = (\<lambda>x. (case x of (mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (_) ((mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (_) (\<bottom>)))) \<Rightarrow> null
    | (mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (_) ((mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (_) (\<lfloor>boss\<rfloor>)))) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (boss))
    | _ \<Rightarrow> invalid))"

(* 28 *********************************** *)
definition dot\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>s\<^isup>a\<^isup>l\<^isup>a\<^isup>r\<^isup>y ("(1(_) .salary)" 50)
  where "(x) .salary = (eval_extract (x) ((deref_oid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (in_post_state) ((select\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>s\<^isup>a\<^isup>l\<^isup>a\<^isup>r\<^isup>y (reconst_basetype))))))"
definition dot\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>b\<^isup>o\<^isup>s\<^isup>s ("(1(_) .boss)" 50)
  where "(x) .boss = (eval_extract (x) ((deref_oid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (in_post_state) ((select\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>b\<^isup>o\<^isup>s\<^isup>s ((deref_oid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (in_post_state))))))))"
definition dot\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>s\<^isup>a\<^isup>l\<^isup>a\<^isup>r\<^isup>y_at_pre ("(1(_) .salary@pre)" 50)
  where "(x) .salary@pre = (eval_extract (x) ((deref_oid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (in_pre_state) ((select\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>s\<^isup>a\<^isup>l\<^isup>a\<^isup>r\<^isup>y (reconst_basetype))))))"
definition dot\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>b\<^isup>o\<^isup>s\<^isup>s_at_pre ("(1(_) .boss@pre)" 50)
  where "(x) .boss@pre = (eval_extract (x) ((deref_oid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (in_pre_state) ((select\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>b\<^isup>o\<^isup>s\<^isup>s ((deref_oid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (in_pre_state))))))))"

end
