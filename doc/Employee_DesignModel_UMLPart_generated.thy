theory Employee_DesignModel_UMLPart_generated imports "../src/OCL_main" begin

(* 1 *********************************** *)
datatype type\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n = mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n oid "nat option" "unit option" "bool option"
datatype typeoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n = mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n type\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n "int option" "oid option"
datatype type\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t = mk\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n typeoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n
                        | mk\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t oid "unit option" "bool option"
datatype typeoid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t = mkoid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t type\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t "nat option"
datatype type\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y = mk\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n typeoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n
                        | mk\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t typeoid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t
                        | mk\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y oid
datatype typeoid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y = mkoid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y type\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y "unit option" "bool option"
datatype type\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y = mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n typeoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n
                        | mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t typeoid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t
                        | mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y typeoid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y
                        | mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y oid
datatype typeoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y = mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y type\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y

(* 2 *********************************** *)
datatype \<AA> = in\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n typeoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n
                        | in\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t typeoid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t
                        | in\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y typeoid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y
                        | in\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y typeoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y

(* 3 *********************************** *)
type_synonym Boolean = "\<AA> Boolean"
type_synonym Person = "(\<AA>, typeoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n option option) val"
type_synonym Planet = "(\<AA>, typeoid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t option option) val"
type_synonym Galaxy = "(\<AA>, typeoid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y option option) val"
type_synonym OclAny = "(\<AA>, typeoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y option option) val"

(* 4 *********************************** *)
instantiation typeoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n :: object
begin
  definition oid_of_typeoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_def : "oid_of = (\<lambda> mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n t _ _ \<Rightarrow> (case t of (mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (t) (_) (_) (_)) \<Rightarrow> t))"
  instance ..
end
instantiation typeoid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t :: object
begin
  definition oid_of_typeoid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_def : "oid_of = (\<lambda> mkoid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t t _ \<Rightarrow> (case t of (mk\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (t) (_) (_)) \<Rightarrow> t
    | (mk\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (t)) \<Rightarrow> (oid_of (t))))"
  instance ..
end
instantiation typeoid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y :: object
begin
  definition oid_of_typeoid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_def : "oid_of = (\<lambda> mkoid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y t _ _ \<Rightarrow> (case t of (mk\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (t)) \<Rightarrow> t
    | (mk\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (t)) \<Rightarrow> (oid_of (t))
    | (mk\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (t)) \<Rightarrow> (oid_of (t))))"
  instance ..
end
instantiation typeoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y :: object
begin
  definition oid_of_typeoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_def : "oid_of = (\<lambda> mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y t \<Rightarrow> (case t of (mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (t)) \<Rightarrow> t
    | (mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (t)) \<Rightarrow> (oid_of (t))
    | (mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (t)) \<Rightarrow> (oid_of (t))
    | (mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (t)) \<Rightarrow> (oid_of (t))))"
  instance ..
end

(* 5 *********************************** *)
instantiation \<AA> :: object
begin
  definition oid_of_\<AA>_def : "oid_of = (\<lambda> in\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n Person \<Rightarrow> oid_of Person
    | in\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t Planet \<Rightarrow> oid_of Planet
    | in\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y Galaxy \<Rightarrow> oid_of Galaxy
    | in\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y OclAny \<Rightarrow> oid_of OclAny)"
  instance ..
end

(* 6 *********************************** *)
defs(overloaded) StrictRefEq\<^isub>O\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n : "(x::Person) \<doteq> y \<equiv> StrictRefEq\<^isub>O\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t x y"
defs(overloaded) StrictRefEq\<^isub>O\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t : "(x::Planet) \<doteq> y \<equiv> StrictRefEq\<^isub>O\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t x y"
defs(overloaded) StrictRefEq\<^isub>O\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y : "(x::Galaxy) \<doteq> y \<equiv> StrictRefEq\<^isub>O\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t x y"
defs(overloaded) StrictRefEq\<^isub>O\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t_\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y : "(x::OclAny) \<doteq> y \<equiv> StrictRefEq\<^isub>O\<^isub>b\<^isub>j\<^isub>e\<^isub>c\<^isub>t x y"

(* 7 *********************************** *)
consts OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n :: "'\<alpha> \<Rightarrow> Person" ("(_) .oclAsType'(Person')")
consts OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t :: "'\<alpha> \<Rightarrow> Planet" ("(_) .oclAsType'(Planet')")
consts OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y :: "'\<alpha> \<Rightarrow> Galaxy" ("(_) .oclAsType'(Galaxy')")
consts OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y :: "'\<alpha> \<Rightarrow> OclAny" ("(_) .oclAsType'(OclAny')")

(* 8 *********************************** *)
defs(overloaded) OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny : "(x::OclAny) .oclAsType(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Person\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy : "(x::Galaxy) .oclAsType(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y ((mk\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Person\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet : "(x::Planet) .oclAsType(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t ((mk\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person))) (_))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Person\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person : "(x::Person) .oclAsType(Person) \<equiv> x"
defs(overloaded) OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny : "(x::OclAny) .oclAsType(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (Planet))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Planet\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy : "(x::Galaxy) .oclAsType(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y ((mk\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (Planet))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Planet\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet : "(x::Planet) .oclAsType(Planet) \<equiv> x"
defs(overloaded) OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person : "(x::Person) .oclAsType(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Person\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t ((mk\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person))) (None))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny : "(x::OclAny) .oclAsType(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (Galaxy))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Galaxy\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy : "(x::Galaxy) .oclAsType(Galaxy) \<equiv> x"
defs(overloaded) OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet : "(x::Planet) .oclAsType(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Planet\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y ((mk\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (Planet))) (None) (None))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person : "(x::Person) .oclAsType(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Person\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y ((mk\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person))) (None) (None))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny : "(x::OclAny) .oclAsType(OclAny) \<equiv> x"
defs(overloaded) OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy : "(x::Galaxy) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Galaxy\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (Galaxy))))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet : "(x::Planet) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Planet\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (Planet))))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person : "(x::Person) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Person\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person))))\<rfloor>\<rfloor>))"

(* 9 *********************************** *)
definition "OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_\<AA> = (\<lambda> (in\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y ((mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person)))))) \<Rightarrow> \<lfloor>Person\<rfloor>
    | (in\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y ((mkoid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y ((mk\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person))) (_) (_)))) \<Rightarrow> \<lfloor>Person\<rfloor>
    | (in\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t ((mkoid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t ((mk\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person))) (_)))) \<Rightarrow> \<lfloor>Person\<rfloor>
    | (in\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person)) \<Rightarrow> \<lfloor>Person\<rfloor>
    | _ \<Rightarrow> None)"
definition "OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_\<AA> = (\<lambda> (in\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y ((mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (Planet)))))) \<Rightarrow> \<lfloor>Planet\<rfloor>
    | (in\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y ((mkoid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y ((mk\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (Planet))) (_) (_)))) \<Rightarrow> \<lfloor>Planet\<rfloor>
    | (in\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (Planet)) \<Rightarrow> \<lfloor>Planet\<rfloor>
    | (in\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person)) \<Rightarrow> \<lfloor>(mkoid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t ((mk\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person))) (None))\<rfloor>
    | _ \<Rightarrow> None)"
definition "OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_\<AA> = (\<lambda> (in\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y ((mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (Galaxy)))))) \<Rightarrow> \<lfloor>Galaxy\<rfloor>
    | (in\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (Galaxy)) \<Rightarrow> \<lfloor>Galaxy\<rfloor>
    | (in\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (Planet)) \<Rightarrow> \<lfloor>(mkoid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y ((mk\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (Planet))) (None) (None))\<rfloor>
    | (in\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person)) \<Rightarrow> \<lfloor>(mkoid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y ((mk\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person))) (None) (None))\<rfloor>
    | _ \<Rightarrow> None)"
definition "OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<AA> = \<lfloor>\<lambda> (in\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (OclAny)) \<Rightarrow> OclAny
    | (in\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (Galaxy)) \<Rightarrow> (mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (Galaxy))))
    | (in\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (Planet)) \<Rightarrow> (mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (Planet))))
    | (in\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person)) \<Rightarrow> (mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person))))\<rfloor>"

(* 10 *********************************** *)
lemmas [simp] = OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person
                OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet
                OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy
                OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny

(* 11 *********************************** *)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person)
lemma cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person)
lemma cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny)
lemma cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny)
lemma cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny)
lemma cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny)
lemma cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclAsType(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclAsType(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclAsType(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclAsType(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet)
lemma cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet)
lemma cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet)
lemma cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet)
lemma cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person)
lemma cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person)
lemma cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person)
lemma cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person)
lemma cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny)
lemma cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny)
lemma cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny)
lemma cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny)
lemma cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy)
lemma cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy)
lemma cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy)
lemma cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy)
lemma cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclAsType(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclAsType(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclAsType(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclAsType(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person)
lemma cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person)
lemma cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person)
lemma cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclAsType(Person)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclAsType(Person)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclAsType(Person)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclAsType(Person)))))"
by(rule cpI1, simp)

(* 12 *********************************** *)
lemmas [simp] = cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_OclAny
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_OclAny
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_OclAny
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_OclAny
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Galaxy
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_Galaxy
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_Galaxy
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Galaxy
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Planet
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_Planet
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_Planet
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Planet
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Person
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_Person
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_Person
                cp_OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Person
                cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_OclAny
                cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_OclAny
                cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_OclAny
                cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_OclAny
                cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_Galaxy
                cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_Galaxy
                cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_Galaxy
                cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_Galaxy
                cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_Planet
                cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_Planet
                cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_Planet
                cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_Planet
                cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_Person
                cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_Person
                cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_Person
                cp_OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_Person
                cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_OclAny
                cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_OclAny
                cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_OclAny
                cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_OclAny
                cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_Galaxy
                cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_Galaxy
                cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_Galaxy
                cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_Galaxy
                cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_Planet
                cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_Planet
                cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_Planet
                cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_Planet
                cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_Person
                cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_Person
                cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_Person
                cp_OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_Person
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_OclAny
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_OclAny
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_OclAny
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_OclAny
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Galaxy
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_Galaxy
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_Galaxy
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Galaxy
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Planet
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_Planet
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_Planet
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Planet
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Person
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_Person
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_Person
                cp_OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Person

(* 13 *********************************** *)
lemma OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_invalid : "((invalid::OclAny) .oclAsType(OclAny)) = invalid"
by(simp)
lemma OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_invalid : "((invalid::Galaxy) .oclAsType(OclAny)) = invalid"
by(rule ext, simp add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy bot_option_def invalid_def)
lemma OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_invalid : "((invalid::Planet) .oclAsType(OclAny)) = invalid"
by(rule ext, simp add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet bot_option_def invalid_def)
lemma OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_invalid : "((invalid::Person) .oclAsType(OclAny)) = invalid"
by(rule ext, simp add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person bot_option_def invalid_def)
lemma OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_null : "((null::OclAny) .oclAsType(OclAny)) = null"
by(simp)
lemma OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_null : "((null::Galaxy) .oclAsType(OclAny)) = null"
by(rule ext, simp add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_null : "((null::Planet) .oclAsType(OclAny)) = null"
by(rule ext, simp add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_null : "((null::Person) .oclAsType(OclAny)) = null"
by(rule ext, simp add: OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_invalid : "((invalid::OclAny) .oclAsType(Galaxy)) = invalid"
by(rule ext, simp add: OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny bot_option_def invalid_def)
lemma OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_invalid : "((invalid::Galaxy) .oclAsType(Galaxy)) = invalid"
by(simp)
lemma OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_invalid : "((invalid::Planet) .oclAsType(Galaxy)) = invalid"
by(rule ext, simp add: OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet bot_option_def invalid_def)
lemma OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_invalid : "((invalid::Person) .oclAsType(Galaxy)) = invalid"
by(rule ext, simp add: OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person bot_option_def invalid_def)
lemma OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_null : "((null::OclAny) .oclAsType(Galaxy)) = null"
by(rule ext, simp add: OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_null : "((null::Galaxy) .oclAsType(Galaxy)) = null"
by(simp)
lemma OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_null : "((null::Planet) .oclAsType(Galaxy)) = null"
by(rule ext, simp add: OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_null : "((null::Person) .oclAsType(Galaxy)) = null"
by(rule ext, simp add: OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_invalid : "((invalid::OclAny) .oclAsType(Planet)) = invalid"
by(rule ext, simp add: OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny bot_option_def invalid_def)
lemma OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_invalid : "((invalid::Galaxy) .oclAsType(Planet)) = invalid"
by(rule ext, simp add: OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy bot_option_def invalid_def)
lemma OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_invalid : "((invalid::Planet) .oclAsType(Planet)) = invalid"
by(simp)
lemma OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_invalid : "((invalid::Person) .oclAsType(Planet)) = invalid"
by(rule ext, simp add: OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person bot_option_def invalid_def)
lemma OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_null : "((null::OclAny) .oclAsType(Planet)) = null"
by(rule ext, simp add: OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_null : "((null::Galaxy) .oclAsType(Planet)) = null"
by(rule ext, simp add: OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_null : "((null::Planet) .oclAsType(Planet)) = null"
by(simp)
lemma OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_null : "((null::Person) .oclAsType(Planet)) = null"
by(rule ext, simp add: OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_invalid : "((invalid::OclAny) .oclAsType(Person)) = invalid"
by(rule ext, simp add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny bot_option_def invalid_def)
lemma OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_invalid : "((invalid::Galaxy) .oclAsType(Person)) = invalid"
by(rule ext, simp add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy bot_option_def invalid_def)
lemma OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_invalid : "((invalid::Planet) .oclAsType(Person)) = invalid"
by(rule ext, simp add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet bot_option_def invalid_def)
lemma OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_invalid : "((invalid::Person) .oclAsType(Person)) = invalid"
by(simp)
lemma OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_null : "((null::OclAny) .oclAsType(Person)) = null"
by(rule ext, simp add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_null : "((null::Galaxy) .oclAsType(Person)) = null"
by(rule ext, simp add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_null : "((null::Planet) .oclAsType(Person)) = null"
by(rule ext, simp add: OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_null : "((null::Person) .oclAsType(Person)) = null"
by(simp)

(* 14 *********************************** *)
lemmas [simp] = OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_invalid
                OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_invalid
                OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_invalid
                OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_invalid
                OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_null
                OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_null
                OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_null
                OclAsType\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_null
                OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_invalid
                OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_invalid
                OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_invalid
                OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_invalid
                OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_null
                OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_null
                OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_null
                OclAsType\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_null
                OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_invalid
                OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_invalid
                OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_invalid
                OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_invalid
                OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_null
                OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_null
                OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_null
                OclAsType\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_null
                OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_invalid
                OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_invalid
                OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_invalid
                OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_invalid
                OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_null
                OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_null
                OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_null
                OclAsType\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_null

(* 15 *********************************** *)
consts OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Person')")
consts OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Planet')")
consts OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Galaxy')")
consts OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(OclAny')")

(* 16 *********************************** *)
defs(overloaded) OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny : "(x::OclAny) .oclIsTypeOf(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy : "(x::Galaxy) .oclIsTypeOf(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y ((mk\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet : "(x::Planet) .oclIsTypeOf(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t ((mk\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (_))) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person : "(x::Person) .oclIsTypeOf(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n ((mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (_) (_) (_) (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny : "(x::OclAny) .oclIsTypeOf(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy : "(x::Galaxy) .oclIsTypeOf(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y ((mk\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet : "(x::Planet) .oclIsTypeOf(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t ((mk\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (_) (_) (_))) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person : "(x::Person) .oclIsTypeOf(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny : "(x::OclAny) .oclIsTypeOf(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy : "(x::Galaxy) .oclIsTypeOf(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y ((mk\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet : "(x::Planet) .oclIsTypeOf(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person : "(x::Person) .oclIsTypeOf(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny : "(x::OclAny) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y ((mk\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy : "(x::Galaxy) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet : "(x::Planet) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person : "(x::Person) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"

(* 17 *********************************** *)
definition "OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_\<AA> = (\<lambda> (in\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsTypeOf(Person))
    | (in\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsTypeOf(Person))
    | (in\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsTypeOf(Person))
    | (in\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsTypeOf(Person)))"
definition "OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_\<AA> = (\<lambda> (in\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsTypeOf(Planet))
    | (in\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsTypeOf(Planet))
    | (in\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsTypeOf(Planet))
    | (in\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsTypeOf(Planet)))"
definition "OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_\<AA> = (\<lambda> (in\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsTypeOf(Galaxy))
    | (in\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsTypeOf(Galaxy))
    | (in\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsTypeOf(Galaxy))
    | (in\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsTypeOf(Galaxy)))"
definition "OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<AA> = (\<lambda> (in\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsTypeOf(OclAny))
    | (in\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsTypeOf(OclAny))
    | (in\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsTypeOf(OclAny))
    | (in\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsTypeOf(OclAny)))"

(* 18 *********************************** *)
lemmas [simp] = OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person
                OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet
                OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy
                OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny

(* 19 *********************************** *)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person)
lemma cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person)
lemma cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny)
lemma cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny)
lemma cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny)
lemma cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny)
lemma cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet)
lemma cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet)
lemma cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet)
lemma cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet)
lemma cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person)
lemma cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person)
lemma cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person)
lemma cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp)

(* 20 *********************************** *)
lemmas [simp] = cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_OclAny
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_OclAny
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_OclAny
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_OclAny
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Galaxy
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_Galaxy
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_Galaxy
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Galaxy
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Planet
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_Planet
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_Planet
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Planet
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Person
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_Person
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_Person
                cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Person
                cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_OclAny
                cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_OclAny
                cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_OclAny
                cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_OclAny
                cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_Galaxy
                cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_Galaxy
                cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_Galaxy
                cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_Galaxy
                cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_Planet
                cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_Planet
                cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_Planet
                cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_Planet
                cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_Person
                cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_Person
                cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_Person
                cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_Person
                cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_OclAny
                cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_OclAny
                cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_OclAny
                cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_OclAny
                cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_Galaxy
                cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_Galaxy
                cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_Galaxy
                cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_Galaxy
                cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_Planet
                cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_Planet
                cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_Planet
                cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_Planet
                cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_Person
                cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_Person
                cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_Person
                cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_Person
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_OclAny
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_OclAny
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_OclAny
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_OclAny
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Galaxy
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_Galaxy
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_Galaxy
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Galaxy
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Planet
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_Planet
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_Planet
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Planet
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Person
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_Person
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_Person
                cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Person

(* 21 *********************************** *)
lemma OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_invalid : "((invalid::OclAny) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_invalid : "((invalid::Galaxy) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_invalid : "((invalid::Planet) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_invalid : "((invalid::Person) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_null : "((null::OclAny) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_null : "((null::Galaxy) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_null : "((null::Planet) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_null : "((null::Person) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_invalid : "((invalid::OclAny) .oclIsTypeOf(Galaxy)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_invalid : "((invalid::Galaxy) .oclIsTypeOf(Galaxy)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_invalid : "((invalid::Planet) .oclIsTypeOf(Galaxy)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_invalid : "((invalid::Person) .oclIsTypeOf(Galaxy)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_null : "((null::OclAny) .oclIsTypeOf(Galaxy)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_null : "((null::Galaxy) .oclIsTypeOf(Galaxy)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_null : "((null::Planet) .oclIsTypeOf(Galaxy)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_null : "((null::Person) .oclIsTypeOf(Galaxy)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_invalid : "((invalid::OclAny) .oclIsTypeOf(Planet)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_invalid : "((invalid::Galaxy) .oclIsTypeOf(Planet)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_invalid : "((invalid::Planet) .oclIsTypeOf(Planet)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_invalid : "((invalid::Person) .oclIsTypeOf(Planet)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_null : "((null::OclAny) .oclIsTypeOf(Planet)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_null : "((null::Galaxy) .oclIsTypeOf(Planet)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_null : "((null::Planet) .oclIsTypeOf(Planet)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_null : "((null::Person) .oclIsTypeOf(Planet)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_invalid : "((invalid::OclAny) .oclIsTypeOf(Person)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_invalid : "((invalid::Galaxy) .oclIsTypeOf(Person)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_invalid : "((invalid::Planet) .oclIsTypeOf(Person)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_invalid : "((invalid::Person) .oclIsTypeOf(Person)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_null : "((null::OclAny) .oclIsTypeOf(Person)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_null : "((null::Galaxy) .oclIsTypeOf(Person)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_null : "((null::Planet) .oclIsTypeOf(Person)) = true"
by(rule ext, simp add: OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_null : "((null::Person) .oclIsTypeOf(Person)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)

(* 22 *********************************** *)
lemmas [simp] = OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_invalid
                OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_invalid
                OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_invalid
                OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_invalid
                OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_null
                OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_null
                OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_null
                OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_null
                OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_invalid
                OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_invalid
                OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_invalid
                OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_invalid
                OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_null
                OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_null
                OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_null
                OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_null
                OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_invalid
                OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_invalid
                OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_invalid
                OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_invalid
                OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_null
                OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_null
                OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_null
                OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_null
                OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_invalid
                OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_invalid
                OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_invalid
                OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_invalid
                OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_null
                OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_null
                OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_null
                OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_null

(* 23 *********************************** *)
consts OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Person')")
consts OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Planet')")
consts OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Galaxy')")
consts OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(OclAny')")

(* 24 *********************************** *)
defs(overloaded) OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny : "(x::OclAny) .oclIsKindOf(Person) \<equiv> (x .oclIsTypeOf(Person))"
defs(overloaded) OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy : "(x::Galaxy) .oclIsKindOf(Person) \<equiv> (x .oclIsTypeOf(Person))"
defs(overloaded) OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet : "(x::Planet) .oclIsKindOf(Person) \<equiv> (x .oclIsTypeOf(Person))"
defs(overloaded) OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person : "(x::Person) .oclIsKindOf(Person) \<equiv> (x .oclIsTypeOf(Person))"
defs(overloaded) OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny : "(x::OclAny) .oclIsKindOf(Planet) \<equiv> (x .oclIsTypeOf(Planet)) or (x .oclIsKindOf(Person))"
defs(overloaded) OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy : "(x::Galaxy) .oclIsKindOf(Planet) \<equiv> (x .oclIsTypeOf(Planet)) or (x .oclIsKindOf(Person))"
defs(overloaded) OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet : "(x::Planet) .oclIsKindOf(Planet) \<equiv> (x .oclIsTypeOf(Planet)) or (x .oclIsKindOf(Person))"
defs(overloaded) OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person : "(x::Person) .oclIsKindOf(Planet) \<equiv> (x .oclIsTypeOf(Planet)) or (x .oclIsKindOf(Person))"
defs(overloaded) OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny : "(x::OclAny) .oclIsKindOf(Galaxy) \<equiv> (x .oclIsTypeOf(Galaxy)) or (x .oclIsKindOf(Planet))"
defs(overloaded) OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy : "(x::Galaxy) .oclIsKindOf(Galaxy) \<equiv> (x .oclIsTypeOf(Galaxy)) or (x .oclIsKindOf(Planet))"
defs(overloaded) OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet : "(x::Planet) .oclIsKindOf(Galaxy) \<equiv> (x .oclIsTypeOf(Galaxy)) or (x .oclIsKindOf(Planet))"
defs(overloaded) OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person : "(x::Person) .oclIsKindOf(Galaxy) \<equiv> (x .oclIsTypeOf(Galaxy)) or (x .oclIsKindOf(Planet))"
defs(overloaded) OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny : "(x::OclAny) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Galaxy))"
defs(overloaded) OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy : "(x::Galaxy) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Galaxy))"
defs(overloaded) OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet : "(x::Planet) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Galaxy))"
defs(overloaded) OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person : "(x::Person) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Galaxy))"

(* 25 *********************************** *)
definition "OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_\<AA> = (\<lambda> (in\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsKindOf(Person))
    | (in\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsKindOf(Person))
    | (in\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsKindOf(Person))
    | (in\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsKindOf(Person)))"
definition "OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_\<AA> = (\<lambda> (in\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsKindOf(Planet))
    | (in\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsKindOf(Planet))
    | (in\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsKindOf(Planet))
    | (in\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsKindOf(Planet)))"
definition "OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_\<AA> = (\<lambda> (in\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsKindOf(Galaxy))
    | (in\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsKindOf(Galaxy))
    | (in\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsKindOf(Galaxy))
    | (in\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsKindOf(Galaxy)))"
definition "OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_\<AA> = (\<lambda> (in\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsKindOf(OclAny))
    | (in\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsKindOf(OclAny))
    | (in\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsKindOf(OclAny))
    | (in\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsKindOf(OclAny)))"

(* 26 *********************************** *)
lemmas [simp] = OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person
                OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet
                OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy
                OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny

(* 27 *********************************** *)
lemma cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person, simp only: cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Person)
lemma cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person, simp only: cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_Person)
lemma cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person, simp only: cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_Person)
lemma cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person, simp only: cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Person)
lemma cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet, simp only: cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Planet)
lemma cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet, simp only: cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_Planet)
lemma cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet, simp only: cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_Planet)
lemma cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet, simp only: cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Planet)
lemma cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy, simp only: cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Galaxy)
lemma cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy, simp only: cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_Galaxy)
lemma cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy, simp only: cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_Galaxy)
lemma cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy, simp only: cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Galaxy)
lemma cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny, simp only: cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_OclAny)
lemma cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny, simp only: cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_OclAny)
lemma cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny, simp only: cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_OclAny)
lemma cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny, simp only: cp_OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_OclAny)
lemma cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_Person, simp only: cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Person)
lemma cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_Person, simp only: cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_Person)
lemma cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_Person, simp only: cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_Person)
lemma cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_Person, simp only: cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Person)
lemma cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_Planet, simp only: cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Planet)
lemma cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_Planet, simp only: cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_Planet)
lemma cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_Planet, simp only: cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_Planet)
lemma cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_Planet, simp only: cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Planet)
lemma cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_Galaxy, simp only: cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Galaxy)
lemma cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_Galaxy, simp only: cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_Galaxy)
lemma cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_Galaxy, simp only: cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_Galaxy)
lemma cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_Galaxy, simp only: cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Galaxy)
lemma cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_OclAny, simp only: cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_OclAny)
lemma cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_OclAny, simp only: cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_OclAny)
lemma cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_OclAny, simp only: cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_OclAny)
lemma cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_OclAny, simp only: cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_OclAny)
lemma cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_Person, simp only: cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_Person)
lemma cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_Person, simp only: cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_Person)
lemma cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_Person, simp only: cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_Person)
lemma cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_Person, simp only: cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_Person)
lemma cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_Planet, simp only: cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_Planet)
lemma cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_Planet, simp only: cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_Planet)
lemma cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_Planet, simp only: cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_Planet)
lemma cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_Planet, simp only: cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_Planet)
lemma cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_Galaxy, simp only: cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_Galaxy)
lemma cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_Galaxy, simp only: cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_Galaxy)
lemma cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_Galaxy, simp only: cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_Galaxy)
lemma cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_Galaxy, simp only: cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_Galaxy)
lemma cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_OclAny, simp only: cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_OclAny)
lemma cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_OclAny, simp only: cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_OclAny)
lemma cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_OclAny, simp only: cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_OclAny)
lemma cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_OclAny, simp only: cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_OclAny)
lemma cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Person, simp only: cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_Person)
lemma cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_Person, simp only: cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_Person)
lemma cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_Person, simp only: cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_Person)
lemma cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Person, simp only: cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_Person)
lemma cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Planet, simp only: cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_Planet)
lemma cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_Planet, simp only: cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_Planet)
lemma cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_Planet, simp only: cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_Planet)
lemma cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Planet, simp only: cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_Planet)
lemma cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Galaxy, simp only: cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_Galaxy)
lemma cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_Galaxy, simp only: cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_Galaxy)
lemma cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_Galaxy, simp only: cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_Galaxy)
lemma cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Galaxy, simp only: cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_Galaxy)
lemma cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_OclAny, simp only: cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_OclAny)
lemma cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_OclAny, simp only: cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_OclAny)
lemma cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_OclAny, simp only: cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_OclAny)
lemma cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_OclAny, simp only: cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_OclAny)

(* 28 *********************************** *)
lemmas [simp] = cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_OclAny
                cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_OclAny
                cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_OclAny
                cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_OclAny
                cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Galaxy
                cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_Galaxy
                cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_Galaxy
                cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Galaxy
                cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Planet
                cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_Planet
                cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_Planet
                cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Planet
                cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_Person
                cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_Person
                cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_Person
                cp_OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_Person
                cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_OclAny
                cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_OclAny
                cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_OclAny
                cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_OclAny
                cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_Galaxy
                cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_Galaxy
                cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_Galaxy
                cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_Galaxy
                cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_Planet
                cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_Planet
                cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_Planet
                cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_Planet
                cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_Person
                cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_Person
                cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_Person
                cp_OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_Person
                cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_OclAny
                cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_OclAny
                cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_OclAny
                cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_OclAny
                cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_Galaxy
                cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_Galaxy
                cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_Galaxy
                cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_Galaxy
                cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_Planet
                cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_Planet
                cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_Planet
                cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_Planet
                cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_Person
                cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_Person
                cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_Person
                cp_OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_Person
                cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_OclAny
                cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_OclAny
                cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_OclAny
                cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_OclAny
                cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Galaxy
                cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_Galaxy
                cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_Galaxy
                cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Galaxy
                cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Planet
                cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_Planet
                cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_Planet
                cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Planet
                cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_Person
                cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_Person
                cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_Person
                cp_OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_Person

(* 29 *********************************** *)
lemma OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_invalid : "((invalid::OclAny) .oclIsKindOf(Person)) = invalid"
by(simp only: OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_invalid)
lemma OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_invalid : "((invalid::Galaxy) .oclIsKindOf(Person)) = invalid"
by(simp only: OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_invalid)
lemma OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_invalid : "((invalid::Planet) .oclIsKindOf(Person)) = invalid"
by(simp only: OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_invalid)
lemma OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_invalid : "((invalid::Person) .oclIsKindOf(Person)) = invalid"
by(simp only: OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_invalid)
lemma OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_null : "((null::OclAny) .oclIsKindOf(Person)) = true"
by(simp only: OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_null)
lemma OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_null : "((null::Galaxy) .oclIsKindOf(Person)) = true"
by(simp only: OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_null)
lemma OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_null : "((null::Planet) .oclIsKindOf(Person)) = true"
by(simp only: OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_null)
lemma OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_null : "((null::Person) .oclIsKindOf(Person)) = true"
by(simp only: OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person OclIsTypeOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_null)
lemma OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_invalid : "((invalid::OclAny) .oclIsKindOf(Planet)) = invalid"
by(simp only: OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_invalid OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_invalid, simp)
lemma OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_invalid : "((invalid::Galaxy) .oclIsKindOf(Planet)) = invalid"
by(simp only: OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_invalid OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_invalid, simp)
lemma OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_invalid : "((invalid::Planet) .oclIsKindOf(Planet)) = invalid"
by(simp only: OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_invalid OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_invalid, simp)
lemma OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_invalid : "((invalid::Person) .oclIsKindOf(Planet)) = invalid"
by(simp only: OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_invalid OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_invalid, simp)
lemma OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_null : "((null::OclAny) .oclIsKindOf(Planet)) = true"
by(simp only: OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_null OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_null, simp)
lemma OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_null : "((null::Galaxy) .oclIsKindOf(Planet)) = true"
by(simp only: OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_null OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_null, simp)
lemma OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_null : "((null::Planet) .oclIsKindOf(Planet)) = true"
by(simp only: OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_null OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_null, simp)
lemma OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_null : "((null::Person) .oclIsKindOf(Planet)) = true"
by(simp only: OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person OclIsTypeOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_null OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_null, simp)
lemma OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_invalid : "((invalid::OclAny) .oclIsKindOf(Galaxy)) = invalid"
by(simp only: OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_invalid OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_invalid, simp)
lemma OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_invalid : "((invalid::Galaxy) .oclIsKindOf(Galaxy)) = invalid"
by(simp only: OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_invalid OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_invalid, simp)
lemma OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_invalid : "((invalid::Planet) .oclIsKindOf(Galaxy)) = invalid"
by(simp only: OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_invalid OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_invalid, simp)
lemma OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_invalid : "((invalid::Person) .oclIsKindOf(Galaxy)) = invalid"
by(simp only: OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_invalid OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_invalid, simp)
lemma OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_null : "((null::OclAny) .oclIsKindOf(Galaxy)) = true"
by(simp only: OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_null OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_null, simp)
lemma OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_null : "((null::Galaxy) .oclIsKindOf(Galaxy)) = true"
by(simp only: OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_null OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_null, simp)
lemma OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_null : "((null::Planet) .oclIsKindOf(Galaxy)) = true"
by(simp only: OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_null OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_null, simp)
lemma OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_null : "((null::Person) .oclIsKindOf(Galaxy)) = true"
by(simp only: OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person OclIsTypeOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_null OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_null, simp)
lemma OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_invalid : "((invalid::OclAny) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_invalid OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_invalid, simp)
lemma OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_invalid : "((invalid::Galaxy) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_invalid OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_invalid, simp)
lemma OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_invalid : "((invalid::Planet) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_invalid OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_invalid, simp)
lemma OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_invalid : "((invalid::Person) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_invalid OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_invalid, simp)
lemma OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_null : "((null::OclAny) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_null OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_null, simp)
lemma OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_null : "((null::Galaxy) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_null OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_null, simp)
lemma OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_null : "((null::Planet) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_null OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_null, simp)
lemma OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_null : "((null::Person) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person OclIsTypeOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_null OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_null, simp)

(* 30 *********************************** *)
lemmas [simp] = OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_invalid
                OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_invalid
                OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_invalid
                OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_invalid
                OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_OclAny_null
                OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Galaxy_null
                OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Planet_null
                OclIsKindOf\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y_Person_null
                OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_invalid
                OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_invalid
                OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_invalid
                OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_invalid
                OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_OclAny_null
                OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Galaxy_null
                OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Planet_null
                OclIsKindOf\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y_Person_null
                OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_invalid
                OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_invalid
                OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_invalid
                OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_invalid
                OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_OclAny_null
                OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Galaxy_null
                OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Planet_null
                OclIsKindOf\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t_Person_null
                OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_invalid
                OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_invalid
                OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_invalid
                OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_invalid
                OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_OclAny_null
                OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Galaxy_null
                OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Planet_null
                OclIsKindOf\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n_Person_null

(* 31 *********************************** *)
definition "eval_extract x f = (\<lambda>\<tau>. (case x \<tau> of \<lfloor>\<lfloor>obj\<rfloor>\<rfloor> \<Rightarrow> (f ((oid_of (obj))) (\<tau>))
    | _ \<Rightarrow> invalid \<tau>))"
definition "in_pre_state = fst"
definition "in_post_state = snd"
definition "reconst_basetype = id"

(* 32 *********************************** *)
definition "deref_oid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"
definition "deref_oid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"
definition "deref_oid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"
definition "deref_oid\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^isub>O\<^isub>c\<^isub>l\<^isub>A\<^isub>n\<^isub>y obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"

(* 33 *********************************** *)
definition "select\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>s\<^isup>a\<^isup>l\<^isup>a\<^isup>r\<^isup>y f = (\<lambda> (mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (_) (\<bottom>) (_)) \<Rightarrow> null
    | (mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (_) (\<lfloor>salary\<rfloor>) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (salary)))"
definition "select\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>b\<^isup>o\<^isup>s\<^isup>s f = (\<lambda> (mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (_) (_) (\<bottom>)) \<Rightarrow> null
    | (mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (_) (_) (\<lfloor>boss\<rfloor>)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (boss)))"
definition "select\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t\<^isup>w\<^isup>e\<^isup>i\<^isup>g\<^isup>h\<^isup>t f = (\<lambda> (mkoid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (_) (\<bottom>)) \<Rightarrow> null
    | (mkoid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (_) (\<lfloor>weight\<rfloor>)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (weight)))"
definition "select\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y\<^isup>s\<^isup>o\<^isup>u\<^isup>n\<^isup>d f = (\<lambda> (mkoid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (_) (\<bottom>) (_)) \<Rightarrow> null
    | (mkoid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (_) (\<lfloor>sound\<rfloor>) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (sound)))"
definition "select\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y\<^isup>m\<^isup>o\<^isup>v\<^isup>i\<^isup>n\<^isup>g f = (\<lambda> (mkoid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (_) (_) (\<bottom>)) \<Rightarrow> null
    | (mkoid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (_) (_) (\<lfloor>moving\<rfloor>)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (moving)))"

(* 34 *********************************** *)
definition "select\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>w\<^isup>e\<^isup>i\<^isup>g\<^isup>h\<^isup>t f = (\<lambda> (mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n ((mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (_) (\<bottom>) (_) (_))) (_) (_)) \<Rightarrow> null
    | (mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n ((mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (_) (\<lfloor>weight\<rfloor>) (_) (_))) (_) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (weight)))"
definition "select\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>s\<^isup>o\<^isup>u\<^isup>n\<^isup>d f = (\<lambda> (mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n ((mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (_) (_) (\<bottom>) (_))) (_) (_)) \<Rightarrow> null
    | (mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n ((mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (_) (_) (\<lfloor>sound\<rfloor>) (_))) (_) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (sound)))"
definition "select\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>m\<^isup>o\<^isup>v\<^isup>i\<^isup>n\<^isup>g f = (\<lambda> (mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n ((mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (_) (_) (_) (\<bottom>))) (_) (_)) \<Rightarrow> null
    | (mkoid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n ((mk\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (_) (_) (_) (\<lfloor>moving\<rfloor>))) (_) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (moving)))"
definition "select\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t\<^isup>s\<^isup>o\<^isup>u\<^isup>n\<^isup>d f = (\<lambda> (mkoid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t ((mk\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (_) (\<bottom>) (_))) (_)) \<Rightarrow> null
    | (mkoid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t ((mk\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (_) (\<lfloor>sound\<rfloor>) (_))) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (sound))
    | _ \<Rightarrow> invalid)"
definition "select\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t\<^isup>m\<^isup>o\<^isup>v\<^isup>i\<^isup>n\<^isup>g f = (\<lambda> (mkoid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t ((mk\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (_) (_) (\<bottom>))) (_)) \<Rightarrow> null
    | (mkoid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t ((mk\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (_) (_) (\<lfloor>moving\<rfloor>))) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (moving))
    | _ \<Rightarrow> invalid)"

(* 35 *********************************** *)
definition dot\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>s\<^isup>a\<^isup>l\<^isup>a\<^isup>r\<^isup>y ("(1(_) .salary)" 50)
  where "(x) .salary = (eval_extract (x) ((deref_oid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (in_post_state) ((select\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>s\<^isup>a\<^isup>l\<^isup>a\<^isup>r\<^isup>y (reconst_basetype))))))"
definition dot\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>b\<^isup>o\<^isup>s\<^isup>s ("(1(_) .boss)" 50)
  where "(x) .boss = (eval_extract (x) ((deref_oid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (in_post_state) ((select\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>b\<^isup>o\<^isup>s\<^isup>s ((deref_oid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (in_post_state))))))))"
definition dot\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>s\<^isup>a\<^isup>l\<^isup>a\<^isup>r\<^isup>y_at_pre ("(1(_) .salary@pre)" 50)
  where "(x) .salary@pre = (eval_extract (x) ((deref_oid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (in_pre_state) ((select\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>s\<^isup>a\<^isup>l\<^isup>a\<^isup>r\<^isup>y (reconst_basetype))))))"
definition dot\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>b\<^isup>o\<^isup>s\<^isup>s_at_pre ("(1(_) .boss@pre)" 50)
  where "(x) .boss@pre = (eval_extract (x) ((deref_oid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (in_pre_state) ((select\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>b\<^isup>o\<^isup>s\<^isup>s ((deref_oid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (in_pre_state))))))))"
definition dot\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t\<^isup>w\<^isup>e\<^isup>i\<^isup>g\<^isup>h\<^isup>t ("(1(_) .weight)" 50)
  where "(x) .weight = (eval_extract (x) ((deref_oid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (in_post_state) ((select\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t\<^isup>w\<^isup>e\<^isup>i\<^isup>g\<^isup>h\<^isup>t (reconst_basetype))))))"
definition dot\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t\<^isup>w\<^isup>e\<^isup>i\<^isup>g\<^isup>h\<^isup>t_at_pre ("(1(_) .weight@pre)" 50)
  where "(x) .weight@pre = (eval_extract (x) ((deref_oid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (in_pre_state) ((select\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t\<^isup>w\<^isup>e\<^isup>i\<^isup>g\<^isup>h\<^isup>t (reconst_basetype))))))"
definition dot\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y\<^isup>s\<^isup>o\<^isup>u\<^isup>n\<^isup>d ("(1(_) .sound)" 50)
  where "(x) .sound = (eval_extract (x) ((deref_oid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (in_post_state) ((select\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y\<^isup>s\<^isup>o\<^isup>u\<^isup>n\<^isup>d (reconst_basetype))))))"
definition dot\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y\<^isup>m\<^isup>o\<^isup>v\<^isup>i\<^isup>n\<^isup>g ("(1(_) .moving)" 50)
  where "(x) .moving = (eval_extract (x) ((deref_oid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (in_post_state) ((select\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y\<^isup>m\<^isup>o\<^isup>v\<^isup>i\<^isup>n\<^isup>g (reconst_basetype))))))"
definition dot\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y\<^isup>s\<^isup>o\<^isup>u\<^isup>n\<^isup>d_at_pre ("(1(_) .sound@pre)" 50)
  where "(x) .sound@pre = (eval_extract (x) ((deref_oid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (in_pre_state) ((select\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y\<^isup>s\<^isup>o\<^isup>u\<^isup>n\<^isup>d (reconst_basetype))))))"
definition dot\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y\<^isup>m\<^isup>o\<^isup>v\<^isup>i\<^isup>n\<^isup>g_at_pre ("(1(_) .moving@pre)" 50)
  where "(x) .moving@pre = (eval_extract (x) ((deref_oid\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y (in_pre_state) ((select\<^isub>G\<^isub>a\<^isub>l\<^isub>a\<^isub>x\<^isub>y\<^isup>m\<^isup>o\<^isup>v\<^isup>i\<^isup>n\<^isup>g (reconst_basetype))))))"

(* 36 *********************************** *)
definition "dot\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>w\<^isup>e\<^isup>i\<^isup>g\<^isup>h\<^isup>t = (\<lambda>x. (eval_extract (x) ((deref_oid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (in_post_state) ((select\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>w\<^isup>e\<^isup>i\<^isup>g\<^isup>h\<^isup>t (reconst_basetype)))))))"
definition "dot\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>s\<^isup>o\<^isup>u\<^isup>n\<^isup>d = (\<lambda>x. (eval_extract (x) ((deref_oid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (in_post_state) ((select\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>s\<^isup>o\<^isup>u\<^isup>n\<^isup>d (reconst_basetype)))))))"
definition "dot\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>m\<^isup>o\<^isup>v\<^isup>i\<^isup>n\<^isup>g = (\<lambda>x. (eval_extract (x) ((deref_oid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (in_post_state) ((select\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>m\<^isup>o\<^isup>v\<^isup>i\<^isup>n\<^isup>g (reconst_basetype)))))))"
definition "dot\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>w\<^isup>e\<^isup>i\<^isup>g\<^isup>h\<^isup>t_at_pre = (\<lambda>x. (eval_extract (x) ((deref_oid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (in_pre_state) ((select\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>w\<^isup>e\<^isup>i\<^isup>g\<^isup>h\<^isup>t (reconst_basetype)))))))"
definition "dot\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>s\<^isup>o\<^isup>u\<^isup>n\<^isup>d_at_pre = (\<lambda>x. (eval_extract (x) ((deref_oid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (in_pre_state) ((select\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>s\<^isup>o\<^isup>u\<^isup>n\<^isup>d (reconst_basetype)))))))"
definition "dot\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>m\<^isup>o\<^isup>v\<^isup>i\<^isup>n\<^isup>g_at_pre = (\<lambda>x. (eval_extract (x) ((deref_oid\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n (in_pre_state) ((select\<^isub>P\<^isub>e\<^isub>r\<^isub>s\<^isub>o\<^isub>n\<^isup>m\<^isup>o\<^isup>v\<^isup>i\<^isup>n\<^isup>g (reconst_basetype)))))))"
definition "dot\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t\<^isup>s\<^isup>o\<^isup>u\<^isup>n\<^isup>d = (\<lambda>x. (eval_extract (x) ((deref_oid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (in_post_state) ((select\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t\<^isup>s\<^isup>o\<^isup>u\<^isup>n\<^isup>d (reconst_basetype)))))))"
definition "dot\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t\<^isup>m\<^isup>o\<^isup>v\<^isup>i\<^isup>n\<^isup>g = (\<lambda>x. (eval_extract (x) ((deref_oid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (in_post_state) ((select\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t\<^isup>m\<^isup>o\<^isup>v\<^isup>i\<^isup>n\<^isup>g (reconst_basetype)))))))"
definition "dot\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t\<^isup>s\<^isup>o\<^isup>u\<^isup>n\<^isup>d_at_pre = (\<lambda>x. (eval_extract (x) ((deref_oid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (in_pre_state) ((select\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t\<^isup>s\<^isup>o\<^isup>u\<^isup>n\<^isup>d (reconst_basetype)))))))"
definition "dot\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t\<^isup>m\<^isup>o\<^isup>v\<^isup>i\<^isup>n\<^isup>g_at_pre = (\<lambda>x. (eval_extract (x) ((deref_oid\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t (in_pre_state) ((select\<^isub>P\<^isub>l\<^isub>a\<^isub>n\<^isub>e\<^isub>t\<^isup>m\<^isup>o\<^isup>v\<^isup>i\<^isup>n\<^isup>g (reconst_basetype)))))))"

end
