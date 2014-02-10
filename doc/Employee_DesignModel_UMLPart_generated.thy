theory Employee_DesignModel_UMLPart_generated imports "../src/OCL_main" begin

(* 1 *********************************** *)
section{* Introduction *}

(* 2 *********************************** *)
subsection{* Outlining the Example *}

(* 3 *********************************** *)
section{* Example Data-Universe and its Infrastructure *}

(* 4 *********************************** *)
datatype type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n = mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n oid "nat option" "unit option" "bool option"
datatype typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n = mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n "int option" "oid option"
datatype type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t = mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n
                        | mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t oid "unit option" "bool option"
datatype typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t = mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t "nat option"
datatype type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y = mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n
                        | mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t
                        | mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y oid
datatype typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y = mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y "unit option" "bool option"
datatype type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n
                        | mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t
                        | mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y
                        | mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y oid
datatype typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y

(* 5 *********************************** *)
datatype \<AA> = in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n
                        | in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t
                        | in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y
                        | in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y

(* 6 *********************************** *)
type_synonym Boolean = "\<AA> Boolean"
type_synonym Person = "(\<AA>, typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n option option) val"
type_synonym Planet = "(\<AA>, typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t option option) val"
type_synonym Galaxy = "(\<AA>, typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y option option) val"
type_synonym OclAny = "(\<AA>, typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y option option) val"

(* 7 *********************************** *)
instantiation typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: object
begin
  definition oid_of_typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def : "oid_of = (\<lambda> mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n t _ _ \<Rightarrow> (case t of (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t) (_) (_) (_)) \<Rightarrow> t))"
  instance ..
end
instantiation typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t :: object
begin
  definition oid_of_typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_def : "oid_of = (\<lambda> mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t t _ \<Rightarrow> (case t of (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t) (_) (_)) \<Rightarrow> t
    | (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t)) \<Rightarrow> (oid_of (t))))"
  instance ..
end
instantiation typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :: object
begin
  definition oid_of_typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_def : "oid_of = (\<lambda> mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y t _ _ \<Rightarrow> (case t of (mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (t)) \<Rightarrow> t
    | (mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t)) \<Rightarrow> (oid_of (t))
    | (mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t)) \<Rightarrow> (oid_of (t))))"
  instance ..
end
instantiation typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: object
begin
  definition oid_of_typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def : "oid_of = (\<lambda> mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y t \<Rightarrow> (case t of (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (t)) \<Rightarrow> t
    | (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (t)) \<Rightarrow> (oid_of (t))
    | (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t)) \<Rightarrow> (oid_of (t))
    | (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t)) \<Rightarrow> (oid_of (t))))"
  instance ..
end

(* 8 *********************************** *)
instantiation \<AA> :: object
begin
  definition oid_of_\<AA>_def : "oid_of = (\<lambda> in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n Person \<Rightarrow> oid_of Person
    | in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t Planet \<Rightarrow> oid_of Planet
    | in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y Galaxy \<Rightarrow> oid_of Galaxy
    | in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y OclAny \<Rightarrow> oid_of OclAny)"
  instance ..
end

(* 9 *********************************** *)
section{* Instantiation of the Generic Strict Equality *}

(* 10 *********************************** *)
defs(overloaded) StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n : "(x::Person) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
defs(overloaded) StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t : "(x::Planet) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
defs(overloaded) StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y : "(x::Galaxy) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
defs(overloaded) StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : "(x::OclAny) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"

(* 11 *********************************** *)
section{* OclAsType *}

(* 12 *********************************** *)
subsection{* Definition *}

(* 13 *********************************** *)
consts OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: "'\<alpha> \<Rightarrow> Person" ("(_) .oclAsType'(Person')")
consts OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t :: "'\<alpha> \<Rightarrow> Planet" ("(_) .oclAsType'(Planet')")
consts OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :: "'\<alpha> \<Rightarrow> Galaxy" ("(_) .oclAsType'(Galaxy')")
consts OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: "'\<alpha> \<Rightarrow> OclAny" ("(_) .oclAsType'(OclAny')")

(* 14 *********************************** *)
defs(overloaded) OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny : "(x::OclAny) .oclAsType(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Person\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy : "(x::Galaxy) .oclAsType(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Person\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet : "(x::Planet) .oclAsType(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (_))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Person\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person : "(x::Person) .oclAsType(Person) \<equiv> x"
defs(overloaded) OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny : "(x::OclAny) .oclAsType(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Planet\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy : "(x::Galaxy) .oclAsType(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Planet\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet : "(x::Planet) .oclAsType(Planet) \<equiv> x"
defs(overloaded) OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person : "(x::Person) .oclAsType(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Person\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (None))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny : "(x::OclAny) .oclAsType(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Galaxy\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy : "(x::Galaxy) .oclAsType(Galaxy) \<equiv> x"
defs(overloaded) OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet : "(x::Planet) .oclAsType(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Planet\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))) (None) (None))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person : "(x::Person) .oclAsType(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Person\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (None) (None))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny : "(x::OclAny) .oclAsType(OclAny) \<equiv> x"
defs(overloaded) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy : "(x::Galaxy) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Galaxy\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy))))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet : "(x::Planet) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Planet\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person : "(x::Person) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Person\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))))\<rfloor>\<rfloor>))"

(* 15 *********************************** *)
definition "OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)))))) \<Rightarrow> \<lfloor>Person\<rfloor>
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (_) (_)))) \<Rightarrow> \<lfloor>Person\<rfloor>
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (_)))) \<Rightarrow> \<lfloor>Person\<rfloor>
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> \<lfloor>Person\<rfloor>
    | _ \<Rightarrow> None)"
definition "OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)))))) \<Rightarrow> \<lfloor>Planet\<rfloor>
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))) (_) (_)))) \<Rightarrow> \<lfloor>Planet\<rfloor>
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> \<lfloor>Planet\<rfloor>
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> \<lfloor>(mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (None))\<rfloor>
    | _ \<Rightarrow> None)"
definition "OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)))))) \<Rightarrow> \<lfloor>Galaxy\<rfloor>
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> \<lfloor>Galaxy\<rfloor>
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> \<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))) (None) (None))\<rfloor>
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> \<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (None) (None))\<rfloor>
    | _ \<Rightarrow> None)"
definition "OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> = \<lfloor>\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> OclAny
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy))))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))))\<rfloor>"

(* 16 *********************************** *)
lemmas [simp] = OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person
                OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet
                OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy
                OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny

(* 17 *********************************** *)
subsection{* Context Passing *}

(* 18 *********************************** *)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclAsType(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclAsType(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclAsType(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclAsType(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
lemma cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclAsType(Galaxy)))))"
by(rule cpI1, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclAsType(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclAsType(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclAsType(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclAsType(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
lemma cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclAsType(Planet)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclAsType(Person)))))"
by(rule cpI1, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclAsType(Person)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclAsType(Person)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclAsType(Person)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclAsType(Person)))))"
by(rule cpI1, simp)

(* 19 *********************************** *)
lemmas [simp] = cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_OclAny
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_OclAny
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Galaxy
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Galaxy
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Galaxy
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Galaxy
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Planet
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Planet
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Planet
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Planet
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Person
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Person
                cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person
                cp_OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person
                cp_OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person
                cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person

(* 20 *********************************** *)
subsection{* Execution with Invalid or Null as Argument *}

(* 21 *********************************** *)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid : "((invalid::OclAny) .oclAsType(OclAny)) = invalid"
by(simp)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_invalid : "((invalid::Galaxy) .oclAsType(OclAny)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy bot_option_def invalid_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_invalid : "((invalid::Planet) .oclAsType(OclAny)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet bot_option_def invalid_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_invalid : "((invalid::Person) .oclAsType(OclAny)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person bot_option_def invalid_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null : "((null::OclAny) .oclAsType(OclAny)) = null"
by(simp)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_null : "((null::Galaxy) .oclAsType(OclAny)) = null"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_null : "((null::Planet) .oclAsType(OclAny)) = null"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_null : "((null::Person) .oclAsType(OclAny)) = null"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid : "((invalid::OclAny) .oclAsType(Galaxy)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny bot_option_def invalid_def)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid : "((invalid::Galaxy) .oclAsType(Galaxy)) = invalid"
by(simp)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid : "((invalid::Planet) .oclAsType(Galaxy)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet bot_option_def invalid_def)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid : "((invalid::Person) .oclAsType(Galaxy)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person bot_option_def invalid_def)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null : "((null::OclAny) .oclAsType(Galaxy)) = null"
by(rule ext, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null : "((null::Galaxy) .oclAsType(Galaxy)) = null"
by(simp)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null : "((null::Planet) .oclAsType(Galaxy)) = null"
by(rule ext, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null : "((null::Person) .oclAsType(Galaxy)) = null"
by(rule ext, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid : "((invalid::OclAny) .oclAsType(Planet)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny bot_option_def invalid_def)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid : "((invalid::Galaxy) .oclAsType(Planet)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy bot_option_def invalid_def)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid : "((invalid::Planet) .oclAsType(Planet)) = invalid"
by(simp)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid : "((invalid::Person) .oclAsType(Planet)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person bot_option_def invalid_def)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null : "((null::OclAny) .oclAsType(Planet)) = null"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null : "((null::Galaxy) .oclAsType(Planet)) = null"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null : "((null::Planet) .oclAsType(Planet)) = null"
by(simp)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null : "((null::Person) .oclAsType(Planet)) = null"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid : "((invalid::OclAny) .oclAsType(Person)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny bot_option_def invalid_def)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid : "((invalid::Galaxy) .oclAsType(Person)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy bot_option_def invalid_def)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid : "((invalid::Planet) .oclAsType(Person)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet bot_option_def invalid_def)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid : "((invalid::Person) .oclAsType(Person)) = invalid"
by(simp)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null : "((null::OclAny) .oclAsType(Person)) = null"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null : "((null::Galaxy) .oclAsType(Person)) = null"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null : "((null::Planet) .oclAsType(Person)) = null"
by(rule ext, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null : "((null::Person) .oclAsType(Person)) = null"
by(simp)

(* 22 *********************************** *)
lemmas [simp] = OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid
                OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_invalid
                OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_invalid
                OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_invalid
                OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null
                OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_null
                OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_null
                OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_null
                OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid
                OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid
                OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid
                OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid
                OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null
                OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null
                OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null
                OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null
                OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid
                OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid
                OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid
                OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid
                OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null
                OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null
                OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null
                OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null
                OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid
                OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid
                OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid
                OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid
                OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null
                OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null
                OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null
                OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null

(* 23 *********************************** *)
subsection{* Validity and Definedness Properties *}

(* 24 *********************************** *)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclAsType(Planet)))"
  using isdef
by(auto simp: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person foundation16 null_option_def bot_option_def)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclAsType(Galaxy)))"
  using isdef
by(auto simp: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet foundation16 null_option_def bot_option_def)
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclAsType(Galaxy)))"
  using isdef
by(auto simp: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person foundation16 null_option_def bot_option_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclAsType(OclAny)))"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy foundation16 null_option_def bot_option_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclAsType(OclAny)))"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet foundation16 null_option_def bot_option_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclAsType(OclAny)))"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person foundation16 null_option_def bot_option_def)

(* 25 *********************************** *)
subsection{* Up Down Casting *}

(* 26 *********************************** *)
lemma up\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast0 : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::Person) .oclAsType(Planet)) .oclAsType(Person)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet foundation22 foundation16 null_option_def bot_option_def split: type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split)
lemma up\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast0 : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::Person) .oclAsType(Galaxy)) .oclAsType(Person)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy foundation22 foundation16 null_option_def bot_option_def split: type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split)
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast0 : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::Person) .oclAsType(OclAny)) .oclAsType(Person)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny foundation22 foundation16 null_option_def bot_option_def split: type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split)
lemma up\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_down\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_cast0 : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::Planet) .oclAsType(Galaxy)) .oclAsType(Planet)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy foundation22 foundation16 null_option_def bot_option_def split: type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split)
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_cast0 : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::Planet) .oclAsType(OclAny)) .oclAsType(Planet)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split)
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_cast0 : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::Galaxy) .oclAsType(OclAny)) .oclAsType(Galaxy)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny foundation22 foundation16 null_option_def bot_option_def split: type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split)

(* 27 *********************************** *)
lemma up\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast : 
shows "(((X::Person) .oclAsType(Planet)) .oclAsType(Person)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast0)
  apply(simp add: def_split_local, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done
lemma up\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast : 
shows "(((X::Person) .oclAsType(Galaxy)) .oclAsType(Person)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast0)
  apply(simp add: def_split_local, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast : 
shows "(((X::Person) .oclAsType(OclAny)) .oclAsType(Person)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast0)
  apply(simp add: def_split_local, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done
lemma up\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_down\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_cast : 
shows "(((X::Planet) .oclAsType(Galaxy)) .oclAsType(Planet)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_down\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_cast0)
  apply(simp add: def_split_local, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_cast : 
shows "(((X::Planet) .oclAsType(OclAny)) .oclAsType(Planet)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_cast0)
  apply(simp add: def_split_local, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_cast : 
shows "(((X::Galaxy) .oclAsType(OclAny)) .oclAsType(Galaxy)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_cast0)
  apply(simp add: def_split_local, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done

(* 28 *********************************** *)
section{* OclIsTypeOf *}

(* 29 *********************************** *)
subsection{* Definition *}

(* 30 *********************************** *)
consts OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Person')")
consts OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Planet')")
consts OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Galaxy')")
consts OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(OclAny')")

(* 31 *********************************** *)
defs(overloaded) OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny : "(x::OclAny) .oclIsTypeOf(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy : "(x::Galaxy) .oclIsTypeOf(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet : "(x::Planet) .oclIsTypeOf(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_))) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person : "(x::Person) .oclIsTypeOf(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (_) (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny : "(x::OclAny) .oclIsTypeOf(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy : "(x::Galaxy) .oclIsTypeOf(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet : "(x::Planet) .oclIsTypeOf(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (_) (_))) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person : "(x::Person) .oclIsTypeOf(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny : "(x::OclAny) .oclIsTypeOf(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy : "(x::Galaxy) .oclIsTypeOf(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet : "(x::Planet) .oclIsTypeOf(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person : "(x::Person) .oclIsTypeOf(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny : "(x::OclAny) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy : "(x::Galaxy) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet : "(x::Planet) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person : "(x::Person) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"

(* 32 *********************************** *)
definition "OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsTypeOf(Person))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsTypeOf(Person))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsTypeOf(Person))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsTypeOf(Person)))"
definition "OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsTypeOf(Planet))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsTypeOf(Planet))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsTypeOf(Planet))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsTypeOf(Planet)))"
definition "OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsTypeOf(Galaxy))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsTypeOf(Galaxy))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsTypeOf(Galaxy))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsTypeOf(Galaxy)))"
definition "OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsTypeOf(OclAny))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsTypeOf(OclAny))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsTypeOf(OclAny))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsTypeOf(OclAny)))"

(* 33 *********************************** *)
lemmas [simp] = OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person
                OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet
                OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy
                OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny

(* 34 *********************************** *)
subsection{* Context Passing *}

(* 35 *********************************** *)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsTypeOf(Galaxy)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsTypeOf(Planet)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsTypeOf(Person)))))"
by(rule cpI1, simp)

(* 36 *********************************** *)
lemmas [simp] = cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_OclAny
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_OclAny
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Galaxy
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Galaxy
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Galaxy
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Galaxy
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Planet
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Planet
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Planet
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Planet
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Person
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Person
                cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person
                cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person
                cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person
                cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person

(* 37 *********************************** *)
subsection{* Execution with Invalid or Null as Argument *}

(* 38 *********************************** *)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid : "((invalid::OclAny) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_invalid : "((invalid::Galaxy) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_invalid : "((invalid::Planet) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_invalid : "((invalid::Person) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null : "((null::OclAny) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_null : "((null::Galaxy) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_null : "((null::Planet) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_null : "((null::Person) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid : "((invalid::OclAny) .oclIsTypeOf(Galaxy)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid : "((invalid::Galaxy) .oclIsTypeOf(Galaxy)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid : "((invalid::Planet) .oclIsTypeOf(Galaxy)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid : "((invalid::Person) .oclIsTypeOf(Galaxy)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null : "((null::OclAny) .oclIsTypeOf(Galaxy)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null : "((null::Galaxy) .oclIsTypeOf(Galaxy)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null : "((null::Planet) .oclIsTypeOf(Galaxy)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null : "((null::Person) .oclIsTypeOf(Galaxy)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid : "((invalid::OclAny) .oclIsTypeOf(Planet)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid : "((invalid::Galaxy) .oclIsTypeOf(Planet)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid : "((invalid::Planet) .oclIsTypeOf(Planet)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid : "((invalid::Person) .oclIsTypeOf(Planet)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null : "((null::OclAny) .oclIsTypeOf(Planet)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null : "((null::Galaxy) .oclIsTypeOf(Planet)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null : "((null::Planet) .oclIsTypeOf(Planet)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null : "((null::Person) .oclIsTypeOf(Planet)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid : "((invalid::OclAny) .oclIsTypeOf(Person)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid : "((invalid::Galaxy) .oclIsTypeOf(Person)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid : "((invalid::Planet) .oclIsTypeOf(Person)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid : "((invalid::Person) .oclIsTypeOf(Person)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null : "((null::OclAny) .oclIsTypeOf(Person)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null : "((null::Galaxy) .oclIsTypeOf(Person)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null : "((null::Planet) .oclIsTypeOf(Person)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null : "((null::Person) .oclIsTypeOf(Person)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)

(* 39 *********************************** *)
lemmas [simp] = OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid
                OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_invalid
                OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_invalid
                OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_invalid
                OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null
                OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_null
                OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_null
                OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_null
                OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid
                OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid
                OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid
                OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid
                OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null
                OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null
                OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null
                OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null
                OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid
                OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid
                OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid
                OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid
                OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null
                OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null
                OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null
                OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null
                OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid
                OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid
                OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid
                OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid
                OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null
                OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null
                OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null
                OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null

(* 40 *********************************** *)
subsection{* Validity and Definedness Properties *}

(* 41 *********************************** *)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(Person)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny split: option.split type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsTypeOf(Person)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy split: option.split type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsTypeOf(Person)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet split: option.split type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsTypeOf(Person)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person split: option.split type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(Planet)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny split: option.split type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsTypeOf(Planet)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy split: option.split type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsTypeOf(Planet)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet split: option.split type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split)
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsTypeOf(Planet)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person split: option.split type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(Galaxy)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny split: option.split type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsTypeOf(Galaxy)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy split: option.split type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsTypeOf(Galaxy)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet split: option.split type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split)
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsTypeOf(Galaxy)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person split: option.split type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(OclAny)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny split: option.split type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsTypeOf(OclAny)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy split: option.split type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsTypeOf(OclAny)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet split: option.split type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsTypeOf(OclAny)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person split: option.split type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split)

(* 42 *********************************** *)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(Person)))"
by(rule OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsTypeOf(Person)))"
by(rule OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsTypeOf(Person)))"
by(rule OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsTypeOf(Person)))"
by(rule OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(Planet)))"
by(rule OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsTypeOf(Planet)))"
by(rule OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsTypeOf(Planet)))"
by(rule OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsTypeOf(Planet)))"
by(rule OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(Galaxy)))"
by(rule OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsTypeOf(Galaxy)))"
by(rule OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsTypeOf(Galaxy)))"
by(rule OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsTypeOf(Galaxy)))"
by(rule OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(OclAny)))"
by(rule OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsTypeOf(OclAny)))"
by(rule OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsTypeOf(OclAny)))"
by(rule OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_defined[OF isdef[THEN foundation20]])
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsTypeOf(OclAny)))"
by(rule OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_defined[OF isdef[THEN foundation20]])

(* 43 *********************************** *)
subsection{* Up Down Casting *}

(* 44 *********************************** *)
lemma actualType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Person) .oclIsTypeOf(Planet)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person foundation22 foundation16 null_option_def bot_option_def)
lemma actualType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Person) .oclIsTypeOf(Galaxy)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person foundation22 foundation16 null_option_def bot_option_def)
lemma actualType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Person) .oclIsTypeOf(OclAny)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person foundation22 foundation16 null_option_def bot_option_def)
lemma actualType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_larger_staticType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Planet) .oclIsTypeOf(Galaxy)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet foundation22 foundation16 null_option_def bot_option_def)
lemma actualType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_larger_staticType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Planet) .oclIsTypeOf(OclAny)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet foundation22 foundation16 null_option_def bot_option_def)
lemma actualType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_larger_staticType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Galaxy) .oclIsTypeOf(OclAny)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy foundation22 foundation16 null_option_def bot_option_def)

(* 45 *********************************** *)
lemma down_cast_type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_from_Planet_to_Person : 
assumes istyp: "\<tau> \<Turnstile> ((X::Planet) .oclIsTypeOf(Planet))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet foundation22 foundation16 null_option_def bot_option_def split: type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split)
by(simp add: OclValid_def false_def true_def)
lemma down_cast_type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_Galaxy_to_Person : 
assumes istyp: "\<tau> \<Turnstile> ((X::Galaxy) .oclIsTypeOf(Galaxy))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy foundation22 foundation16 null_option_def bot_option_def split: type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split)
by(simp add: OclValid_def false_def true_def)
lemma down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Person : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(OclAny))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny foundation22 foundation16 null_option_def bot_option_def split: type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclValid_def false_def true_def)
lemma down_cast_type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_Galaxy_to_Planet : 
assumes istyp: "\<tau> \<Turnstile> ((X::Galaxy) .oclIsTypeOf(Galaxy))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Planet)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy foundation22 foundation16 null_option_def bot_option_def split: type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split)
by(simp add: OclValid_def false_def true_def)
lemma down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Planet : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(OclAny))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Planet)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclValid_def false_def true_def)
lemma down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Galaxy : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(OclAny))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Galaxy)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny foundation22 foundation16 null_option_def bot_option_def split: type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclValid_def false_def true_def)
lemma down_cast_type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_from_Galaxy_to_Person : 
assumes istyp: "\<tau> \<Turnstile> ((X::Galaxy) .oclIsTypeOf(Planet))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy foundation22 foundation16 null_option_def bot_option_def split: type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy OclValid_def false_def true_def)
lemma down_cast_type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_from_OclAny_to_Person : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Planet))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny foundation22 foundation16 null_option_def bot_option_def split: type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny OclValid_def false_def true_def)
lemma down_cast_type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_OclAny_to_Person : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Galaxy))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny foundation22 foundation16 null_option_def bot_option_def split: type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny OclValid_def false_def true_def)
lemma down_cast_type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_OclAny_to_Planet : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Galaxy))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Planet)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny OclValid_def false_def true_def)

(* 46 *********************************** *)
section{* OclIsKindOf *}

(* 47 *********************************** *)
subsection{* Definition *}

(* 48 *********************************** *)
consts OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Person')")
consts OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Planet')")
consts OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Galaxy')")
consts OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(OclAny')")

(* 49 *********************************** *)
defs(overloaded) OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny : "(x::OclAny) .oclIsKindOf(Person) \<equiv> (x .oclIsTypeOf(Person))"
defs(overloaded) OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy : "(x::Galaxy) .oclIsKindOf(Person) \<equiv> (x .oclIsTypeOf(Person))"
defs(overloaded) OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet : "(x::Planet) .oclIsKindOf(Person) \<equiv> (x .oclIsTypeOf(Person))"
defs(overloaded) OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person : "(x::Person) .oclIsKindOf(Person) \<equiv> (x .oclIsTypeOf(Person))"
defs(overloaded) OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny : "(x::OclAny) .oclIsKindOf(Planet) \<equiv> (x .oclIsTypeOf(Planet)) or (x .oclIsKindOf(Person))"
defs(overloaded) OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy : "(x::Galaxy) .oclIsKindOf(Planet) \<equiv> (x .oclIsTypeOf(Planet)) or (x .oclIsKindOf(Person))"
defs(overloaded) OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet : "(x::Planet) .oclIsKindOf(Planet) \<equiv> (x .oclIsTypeOf(Planet)) or (x .oclIsKindOf(Person))"
defs(overloaded) OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person : "(x::Person) .oclIsKindOf(Planet) \<equiv> (x .oclIsTypeOf(Planet)) or (x .oclIsKindOf(Person))"
defs(overloaded) OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny : "(x::OclAny) .oclIsKindOf(Galaxy) \<equiv> (x .oclIsTypeOf(Galaxy)) or (x .oclIsKindOf(Planet))"
defs(overloaded) OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy : "(x::Galaxy) .oclIsKindOf(Galaxy) \<equiv> (x .oclIsTypeOf(Galaxy)) or (x .oclIsKindOf(Planet))"
defs(overloaded) OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet : "(x::Planet) .oclIsKindOf(Galaxy) \<equiv> (x .oclIsTypeOf(Galaxy)) or (x .oclIsKindOf(Planet))"
defs(overloaded) OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person : "(x::Person) .oclIsKindOf(Galaxy) \<equiv> (x .oclIsTypeOf(Galaxy)) or (x .oclIsKindOf(Planet))"
defs(overloaded) OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny : "(x::OclAny) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Galaxy))"
defs(overloaded) OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy : "(x::Galaxy) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Galaxy))"
defs(overloaded) OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet : "(x::Planet) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Galaxy))"
defs(overloaded) OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person : "(x::Person) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Galaxy))"

(* 50 *********************************** *)
definition "OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsKindOf(Person))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsKindOf(Person))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsKindOf(Person))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsKindOf(Person)))"
definition "OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsKindOf(Planet))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsKindOf(Planet))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsKindOf(Planet))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsKindOf(Planet)))"
definition "OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsKindOf(Galaxy))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsKindOf(Galaxy))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsKindOf(Galaxy))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsKindOf(Galaxy)))"
definition "OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsKindOf(OclAny))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsKindOf(OclAny))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsKindOf(OclAny))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsKindOf(OclAny)))"

(* 51 *********************************** *)
lemmas [simp] = OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person
                OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet
                OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy
                OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny

(* 52 *********************************** *)
subsection{* Context Passing *}

(* 53 *********************************** *)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny, simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny, simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Person, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Person, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Planet, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Planet, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Planet, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Planet, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Galaxy, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Galaxy, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Galaxy, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Galaxy, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_OclAny, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_OclAny, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply(rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)
by(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny, simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny)

(* 54 *********************************** *)
lemmas [simp] = cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_OclAny
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_OclAny
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Galaxy
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Galaxy
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Galaxy
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Galaxy
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Planet
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Planet
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Planet
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Planet
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Person
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Person
                cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person
                cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person
                cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person
                cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person

(* 55 *********************************** *)
subsection{* Execution with Invalid or Null as Argument *}

(* 56 *********************************** *)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid : "((invalid::OclAny) .oclIsKindOf(Person)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid : "((invalid::Galaxy) .oclIsKindOf(Person)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid : "((invalid::Planet) .oclIsKindOf(Person)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid : "((invalid::Person) .oclIsKindOf(Person)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null : "((null::OclAny) .oclIsKindOf(Person)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null : "((null::Galaxy) .oclIsKindOf(Person)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null : "((null::Planet) .oclIsKindOf(Person)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null : "((null::Person) .oclIsKindOf(Person)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid : "((invalid::OclAny) .oclIsKindOf(Planet)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid : "((invalid::Galaxy) .oclIsKindOf(Planet)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid : "((invalid::Planet) .oclIsKindOf(Planet)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid : "((invalid::Person) .oclIsKindOf(Planet)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null : "((null::OclAny) .oclIsKindOf(Planet)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null : "((null::Galaxy) .oclIsKindOf(Planet)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null : "((null::Planet) .oclIsKindOf(Planet)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null : "((null::Person) .oclIsKindOf(Planet)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid : "((invalid::OclAny) .oclIsKindOf(Galaxy)) = invalid"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid : "((invalid::Galaxy) .oclIsKindOf(Galaxy)) = invalid"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid : "((invalid::Planet) .oclIsKindOf(Galaxy)) = invalid"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid : "((invalid::Person) .oclIsKindOf(Galaxy)) = invalid"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null : "((null::OclAny) .oclIsKindOf(Galaxy)) = true"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null : "((null::Galaxy) .oclIsKindOf(Galaxy)) = true"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null : "((null::Planet) .oclIsKindOf(Galaxy)) = true"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null : "((null::Person) .oclIsKindOf(Galaxy)) = true"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid : "((invalid::OclAny) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_invalid : "((invalid::Galaxy) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_invalid OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_invalid : "((invalid::Planet) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_invalid OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_invalid : "((invalid::Person) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_invalid OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null : "((null::OclAny) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_null : "((null::Galaxy) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_null OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_null : "((null::Planet) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_null OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_null : "((null::Person) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_null OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null, simp)

(* 57 *********************************** *)
lemmas [simp] = OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid
                OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_invalid
                OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_invalid
                OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_invalid
                OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null
                OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_null
                OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_null
                OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_null
                OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid
                OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid
                OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid
                OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid
                OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null
                OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null
                OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null
                OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null
                OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid
                OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid
                OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid
                OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid
                OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null
                OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null
                OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null
                OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null
                OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid
                OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid
                OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid
                OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid
                OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null
                OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null
                OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null
                OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null

(* 58 *********************************** *)
subsection{* Validity and Definedness Properties *}

(* 59 *********************************** *)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(Person)))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny, rule OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined[OF isdef])
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsKindOf(Person)))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy, rule OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined[OF isdef])
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsKindOf(Person)))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet, rule OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined[OF isdef])
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsKindOf(Person)))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person, rule OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_defined[OF isdef])
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(Planet)))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny, rule defined_or_I[OF OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined[OF isdef]])
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsKindOf(Planet)))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy, rule defined_or_I[OF OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined[OF isdef]])
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsKindOf(Planet)))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet, rule defined_or_I[OF OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined[OF isdef]])
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsKindOf(Planet)))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person, rule defined_or_I[OF OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_defined[OF isdef]])
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(Galaxy)))"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny, rule defined_or_I[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined[OF isdef]])
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsKindOf(Galaxy)))"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy, rule defined_or_I[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined[OF isdef]])
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsKindOf(Galaxy)))"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet, rule defined_or_I[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined[OF isdef]])
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsKindOf(Galaxy)))"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person, rule defined_or_I[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined[OF isdef]])
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(OclAny)))"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny, rule defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined[OF isdef], OF OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined[OF isdef]])
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsKindOf(OclAny)))"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy, rule defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_defined[OF isdef], OF OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined[OF isdef]])
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsKindOf(OclAny)))"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet, rule defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_defined[OF isdef], OF OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined[OF isdef]])
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsKindOf(OclAny)))"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person, rule defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_defined[OF isdef], OF OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined[OF isdef]])

(* 60 *********************************** *)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(Person)))"
by(rule OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsKindOf(Person)))"
by(rule OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsKindOf(Person)))"
by(rule OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsKindOf(Person)))"
by(rule OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(Planet)))"
by(rule OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsKindOf(Planet)))"
by(rule OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsKindOf(Planet)))"
by(rule OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsKindOf(Planet)))"
by(rule OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(Galaxy)))"
by(rule OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsKindOf(Galaxy)))"
by(rule OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsKindOf(Galaxy)))"
by(rule OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsKindOf(Galaxy)))"
by(rule OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(OclAny)))"
by(rule OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsKindOf(OclAny)))"
by(rule OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsKindOf(OclAny)))"
by(rule OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_defined[OF isdef[THEN foundation20]])
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsKindOf(OclAny)))"
by(rule OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_defined[OF isdef[THEN foundation20]])

(* 61 *********************************** *)
subsection{* Up Down Casting *}

(* 62 *********************************** *)
lemma actual_eq_static\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Person) .oclIsKindOf(Person))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person OclValid_def, insert isdef)
by(auto simp: foundation16 bot_option_def split: option.split type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split)
lemma actual_eq_static\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Planet) .oclIsKindOf(Planet))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet OclValid_def, insert isdef)
by((subst cp_OclOr, auto simp: cp_OclOr[symmetric ] foundation16 bot_option_def OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet split: option.split type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split)+)
lemma actual_eq_static\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Galaxy) .oclIsKindOf(Galaxy))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy OclValid_def, insert isdef)
by((subst cp_OclOr, auto simp: cp_OclOr[symmetric ] foundation16 bot_option_def OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy split: option.split type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split)+)
lemma actual_eq_static\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(OclAny))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny OclValid_def, insert isdef)
by((subst cp_OclOr, auto simp: cp_OclOr[symmetric ] foundation16 bot_option_def OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny split: option.split type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split)+)

(* 63 *********************************** *)
lemma actualKind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticKind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Person) .oclIsKindOf(Planet))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
  apply(insert actual_eq_static\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n[OF isdef] actualType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t[OF isdef])
  apply(rule foundation11[THEN iffD2])
by((simp add: OclNot_defargs foundation6 foundation14)+)
lemma actualKind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticKind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Person) .oclIsKindOf(Galaxy))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
  apply(insert actualKind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticKind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t[OF isdef] actualType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y[OF isdef])
  apply(rule foundation11[THEN iffD2])
by((simp add: OclNot_defargs foundation6 foundation14)+)
lemma actualKind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Person) .oclIsKindOf(OclAny))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
  apply(insert actualKind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticKind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y[OF isdef] actualType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[OF isdef])
  apply(rule foundation11[THEN iffD2])
by((simp add: OclNot_defargs foundation6 foundation14)+)
lemma actualKind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_larger_staticKind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Planet) .oclIsKindOf(Galaxy))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
  apply(insert actual_eq_static\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t[OF isdef] actualType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_larger_staticType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y[OF isdef])
  apply(rule foundation11[THEN iffD2])
by((simp add: OclNot_defargs foundation6 foundation14)+)
lemma actualKind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Planet) .oclIsKindOf(OclAny))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
  apply(insert actualKind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_larger_staticKind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y[OF isdef] actualType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_larger_staticType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[OF isdef])
  apply(rule foundation11[THEN iffD2])
by((simp add: OclNot_defargs foundation6 foundation14)+)
lemma actualKind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Galaxy) .oclIsKindOf(OclAny))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
  apply(insert actual_eq_static\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y[OF isdef] actualType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_larger_staticType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[OF isdef])
  apply(rule foundation11[THEN iffD2])
by((simp add: OclNot_defargs foundation6 foundation14)+)

(* 64 *********************************** *)
lemma not_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_then_Planet_OclIsTypeOf_others : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::Planet) .oclIsKindOf(Person))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Planet) .oclIsTypeOf(Planet))"
  using actual_eq_static\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet foundation11[OF OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined'[OF isdef]])
by(simp add: iskin)
lemma not_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_then_Galaxy_OclIsTypeOf_others : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::Galaxy) .oclIsKindOf(Person))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Galaxy) .oclIsTypeOf(Galaxy)) \<or> \<tau> \<Turnstile> ((X::Galaxy) .oclIsTypeOf(Planet))"
  using actual_eq_static\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy foundation11[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined'[OF isdef]])
  apply(erule disjE, simp, rule disjI2)
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy foundation11[OF OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined'[OF isdef]])
by(simp add: iskin)
lemma not_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_then_OclAny_OclIsTypeOf_others : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Person))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(OclAny)) \<or> \<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Galaxy)) \<or> \<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Planet))"
  using actual_eq_static\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny foundation11[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined'[OF isdef]])
  apply(erule disjE, simp, rule disjI2)
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny foundation11[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined'[OF isdef]])
  apply(erule disjE, simp, rule disjI2)
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny foundation11[OF OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined'[OF isdef]])
by(simp add: iskin)
lemma not_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_then_Galaxy_OclIsTypeOf_others : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::Galaxy) .oclIsKindOf(Planet))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Galaxy) .oclIsTypeOf(Galaxy))"
  using actual_eq_static\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy foundation11[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined'[OF isdef]])
by(simp add: iskin)
lemma not_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_then_OclAny_OclIsTypeOf_others : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Planet))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(OclAny)) \<or> \<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Galaxy))"
  using actual_eq_static\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny foundation11[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined'[OF isdef]])
  apply(erule disjE, simp, rule disjI2)
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny foundation11[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined'[OF isdef]])
by(simp add: iskin)
lemma not_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_then_OclAny_OclIsTypeOf_others : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Galaxy))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(OclAny))"
  using actual_eq_static\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny foundation11[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined'[OF isdef]])
by(simp add: iskin)

(* 65 *********************************** *)
lemma down_cast_kind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_from_Planet_to_Person : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::Planet) .oclIsKindOf(Person))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_then_Planet_OclIsTypeOf_others[OF iskin, OF isdef])
  apply(rule down_cast_type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_from_Planet_to_Person, simp only: , simp only: isdef)
done
lemma down_cast_kind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_from_Galaxy_to_Person : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::Galaxy) .oclIsKindOf(Person))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_then_Galaxy_OclIsTypeOf_others[OF iskin, OF isdef], elim disjE)
  apply(rule down_cast_type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_Galaxy_to_Person, simp only: , simp only: isdef)
  apply(rule down_cast_type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_from_Galaxy_to_Person, simp only: , simp only: isdef)
done
lemma down_cast_kind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_from_OclAny_to_Person : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Person))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_then_OclAny_OclIsTypeOf_others[OF iskin, OF isdef], elim disjE)
  apply(rule down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Person, simp only: , simp only: isdef)
  apply(rule down_cast_type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_OclAny_to_Person, simp only: , simp only: isdef)
  apply(rule down_cast_type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_from_OclAny_to_Person, simp only: , simp only: isdef)
done
lemma down_cast_kind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_from_Galaxy_to_Planet : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::Galaxy) .oclIsKindOf(Planet))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Planet)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_then_Galaxy_OclIsTypeOf_others[OF iskin, OF isdef])
  apply(rule down_cast_type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_Galaxy_to_Planet, simp only: , simp only: isdef)
done
lemma down_cast_kind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_from_OclAny_to_Planet : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Planet))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Planet)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_then_OclAny_OclIsTypeOf_others[OF iskin, OF isdef], elim disjE)
  apply(rule down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Planet, simp only: , simp only: isdef)
  apply(rule down_cast_type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_OclAny_to_Planet, simp only: , simp only: isdef)
done
lemma down_cast_kind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_OclAny_to_Galaxy : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Galaxy))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Galaxy)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_then_OclAny_OclIsTypeOf_others[OF iskin, OF isdef])
  apply(rule down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Galaxy, simp only: , simp only: isdef)
done
lemma down_cast_kind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_from_Galaxy_to_Person : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::Galaxy) .oclIsKindOf(Planet))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_then_Galaxy_OclIsTypeOf_others[OF iskin, OF isdef])
  apply(rule down_cast_type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_Galaxy_to_Person, simp only: , simp only: isdef)
done
lemma down_cast_kind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_from_OclAny_to_Person : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Planet))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_then_OclAny_OclIsTypeOf_others[OF iskin, OF isdef], elim disjE)
  apply(rule down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Person, simp only: , simp only: isdef)
  apply(rule down_cast_type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_OclAny_to_Person, simp only: , simp only: isdef)
done
lemma down_cast_kind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_OclAny_to_Person : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Galaxy))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_then_OclAny_OclIsTypeOf_others[OF iskin, OF isdef])
  apply(rule down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Person, simp only: , simp only: isdef)
done
lemma down_cast_kind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_OclAny_to_Planet : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Galaxy))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Planet)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_then_OclAny_OclIsTypeOf_others[OF iskin, OF isdef])
  apply(rule down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Planet, simp only: , simp only: isdef)
done

(* 66 *********************************** *)
section{* OclAllInstances *}

(* 67 *********************************** *)
definition "Person = OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>"
definition "Planet = OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA>"
definition "Galaxy = OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA>"
definition "OclAny = OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>"

(* 68 *********************************** *)
lemmas [simp] = Person_def
                Planet_def
                Galaxy_def
                OclAny_def

(* 69 *********************************** *)
subsection{* OclIsTypeOf *}

(* 70 *********************************** *)
subsection{* OclIsKindOf *}

(* 71 *********************************** *)
section{* The Accessors *}

(* 72 *********************************** *)
subsection{* Definition *}

(* 73 *********************************** *)
definition "eval_extract x f = (\<lambda>\<tau>. (case x \<tau> of \<lfloor>\<lfloor>obj\<rfloor>\<rfloor> \<Rightarrow> (f ((oid_of (obj))) (\<tau>))
    | _ \<Rightarrow> invalid \<tau>))"
definition "in_pre_state = fst"
definition "in_post_state = snd"
definition "reconst_basetype = id"

(* 74 *********************************** *)
definition "deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"
definition "deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"
definition "deref_oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"
definition "deref_oid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"

(* 75 *********************************** *)
definition "select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y> f = (\<lambda> (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (\<bottom>) (_)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (\<lfloor>salary\<rfloor>) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (salary)))"
definition "select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S> f = (\<lambda> (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (\<bottom>)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (\<lfloor>boss\<rfloor>)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (boss)))"
definition "select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T> f = (\<lambda> (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (\<bottom>)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (\<lfloor>weight\<rfloor>)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (weight)))"
definition "select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D> f = (\<lambda> (mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_) (\<bottom>) (_)) \<Rightarrow> null
    | (mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_) (\<lfloor>sound\<rfloor>) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (sound)))"
definition "select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G> f = (\<lambda> (mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_) (_) (\<bottom>)) \<Rightarrow> null
    | (mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_) (_) (\<lfloor>moving\<rfloor>)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (moving)))"
definition "select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T> f = (\<lambda> (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (\<bottom>) (_) (_))) (_) (_)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (\<lfloor>weight\<rfloor>) (_) (_))) (_) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (weight)))"
definition "select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D> f = (\<lambda> (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (\<bottom>) (_))) (_) (_)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (\<lfloor>sound\<rfloor>) (_))) (_) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (sound)))"
definition "select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G> f = (\<lambda> (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (_) (\<bottom>))) (_) (_)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (_) (\<lfloor>moving\<rfloor>))) (_) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (moving)))"
definition "select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D> f = (\<lambda> (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (\<bottom>) (_))) (_)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (\<lfloor>sound\<rfloor>) (_))) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (sound))
    | (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (person))) (_)) \<Rightarrow> (select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D> (f) (person)))"
definition "select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G> f = (\<lambda> (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (_) (\<bottom>))) (_)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (_) (\<lfloor>moving\<rfloor>))) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (moving))
    | (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (person))) (_)) \<Rightarrow> (select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G> (f) (person)))"

(* 76 *********************************** *)
definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y> ("(1(_) .salary)" 50)
  where "(x) .salary = (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y> (reconst_basetype))))))"
definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S> ("(1(_) .boss)" 50)
  where "(x) .boss = (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S> ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state))))))))"
definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_at_pre ("(1(_) .salary@pre)" 50)
  where "(x) .salary@pre = (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y> (reconst_basetype))))))"
definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_at_pre ("(1(_) .boss@pre)" 50)
  where "(x) .boss@pre = (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S> ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state))))))))"
definition dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T> ("(1(_) .weight)" 50)
  where "(x) .weight = (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_post_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T> (reconst_basetype))))))"
definition dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>_at_pre ("(1(_) .weight@pre)" 50)
  where "(x) .weight@pre = (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_pre_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T> (reconst_basetype))))))"
definition dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D> ("(1(_) .sound)" 50)
  where "(x) .sound = (eval_extract (x) ((deref_oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (in_post_state) ((select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D> (reconst_basetype))))))"
definition dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G> ("(1(_) .moving)" 50)
  where "(x) .moving = (eval_extract (x) ((deref_oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (in_post_state) ((select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G> (reconst_basetype))))))"
definition dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>_at_pre ("(1(_) .sound@pre)" 50)
  where "(x) .sound@pre = (eval_extract (x) ((deref_oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (in_pre_state) ((select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D> (reconst_basetype))))))"
definition dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>_at_pre ("(1(_) .moving@pre)" 50)
  where "(x) .moving@pre = (eval_extract (x) ((deref_oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (in_pre_state) ((select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G> (reconst_basetype))))))"
definition "dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T> = (\<lambda>x. (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T> (reconst_basetype)))))))"
definition "dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D> = (\<lambda>x. (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D> (reconst_basetype)))))))"
definition "dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G> = (\<lambda>x. (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G> (reconst_basetype)))))))"
definition "dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>_at_pre = (\<lambda>x. (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T> (reconst_basetype)))))))"
definition "dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>_at_pre = (\<lambda>x. (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D> (reconst_basetype)))))))"
definition "dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>_at_pre = (\<lambda>x. (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G> (reconst_basetype)))))))"
definition "dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D> = (\<lambda>x. (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_post_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D> (reconst_basetype)))))))"
definition "dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G> = (\<lambda>x. (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_post_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G> (reconst_basetype)))))))"
definition "dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>_at_pre = (\<lambda>x. (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_pre_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D> (reconst_basetype)))))))"
definition "dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>_at_pre = (\<lambda>x. (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_pre_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G> (reconst_basetype)))))))"

(* 77 *********************************** *)
lemmas [simp] = dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_def
                dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_def
                dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_at_pre_def
                dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_at_pre_def
                dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>_def
                dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>_at_pre_def
                dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>_def
                dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>_def
                dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>_at_pre_def
                dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>_at_pre_def
                dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>_def
                dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>_def
                dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>_def
                dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>_at_pre_def
                dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>_at_pre_def
                dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>_at_pre_def
                dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>_def
                dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>_def
                dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>_at_pre_def
                dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>_at_pre_def

(* 78 *********************************** *)
subsection{* Context Passing *}

(* 79 *********************************** *)
lemmas [simp] = eval_extract_def

(* 80 *********************************** *)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y> : "(((X) .salary) (\<tau>)) = ((((\<lambda>_. (X (\<tau>)))) .salary) (\<tau>))"
by(simp)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S> : "(((X) .boss) (\<tau>)) = ((((\<lambda>_. (X (\<tau>)))) .boss) (\<tau>))"
by(simp)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_at_pre : "(((X) .salary@pre) (\<tau>)) = ((((\<lambda>_. (X (\<tau>)))) .salary@pre) (\<tau>))"
by(simp)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_at_pre : "(((X) .boss@pre) (\<tau>)) = ((((\<lambda>_. (X (\<tau>)))) .boss@pre) (\<tau>))"
by(simp)
lemma cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T> : "(((X) .weight) (\<tau>)) = ((((\<lambda>_. (X (\<tau>)))) .weight) (\<tau>))"
by(simp)
lemma cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>_at_pre : "(((X) .weight@pre) (\<tau>)) = ((((\<lambda>_. (X (\<tau>)))) .weight@pre) (\<tau>))"
by(simp)
lemma cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D> : "(((X) .sound) (\<tau>)) = ((((\<lambda>_. (X (\<tau>)))) .sound) (\<tau>))"
by(simp)
lemma cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G> : "(((X) .moving) (\<tau>)) = ((((\<lambda>_. (X (\<tau>)))) .moving) (\<tau>))"
by(simp)
lemma cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>_at_pre : "(((X) .sound@pre) (\<tau>)) = ((((\<lambda>_. (X (\<tau>)))) .sound@pre) (\<tau>))"
by(simp)
lemma cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>_at_pre : "(((X) .moving@pre) (\<tau>)) = ((((\<lambda>_. (X (\<tau>)))) .moving@pre) (\<tau>))"
by(simp)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T> : "(((X) .weight) (\<tau>)) = ((((\<lambda>_. (X (\<tau>)))) .weight) (\<tau>))"
by(simp)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D> : "(((X) .sound) (\<tau>)) = ((((\<lambda>_. (X (\<tau>)))) .sound) (\<tau>))"
by(simp)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G> : "(((X) .moving) (\<tau>)) = ((((\<lambda>_. (X (\<tau>)))) .moving) (\<tau>))"
by(simp)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>_at_pre : "(((X) .weight@pre) (\<tau>)) = ((((\<lambda>_. (X (\<tau>)))) .weight@pre) (\<tau>))"
by(simp)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>_at_pre : "(((X) .sound@pre) (\<tau>)) = ((((\<lambda>_. (X (\<tau>)))) .sound@pre) (\<tau>))"
by(simp)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>_at_pre : "(((X) .moving@pre) (\<tau>)) = ((((\<lambda>_. (X (\<tau>)))) .moving@pre) (\<tau>))"
by(simp)
lemma cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D> : "(((X) .sound) (\<tau>)) = ((((\<lambda>_. (X (\<tau>)))) .sound) (\<tau>))"
by(simp)
lemma cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G> : "(((X) .moving) (\<tau>)) = ((((\<lambda>_. (X (\<tau>)))) .moving) (\<tau>))"
by(simp)
lemma cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>_at_pre : "(((X) .sound@pre) (\<tau>)) = ((((\<lambda>_. (X (\<tau>)))) .sound@pre) (\<tau>))"
by(simp)
lemma cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>_at_pre : "(((X) .moving@pre) (\<tau>)) = ((((\<lambda>_. (X (\<tau>)))) .moving@pre) (\<tau>))"
by(simp)

(* 81 *********************************** *)
lemmas cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_I [simp] = cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>[THEN allI[THEN allI], of "(\<lambda>X _. X)" "(\<lambda>_ \<tau>. \<tau>)", THEN cpI1]
lemmas cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_I [simp] = cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>[THEN allI[THEN allI], of "(\<lambda>X _. X)" "(\<lambda>_ \<tau>. \<tau>)", THEN cpI1]
lemmas cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_at_pre_I [simp] = cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_at_pre[THEN allI[THEN allI], of "(\<lambda>X _. X)" "(\<lambda>_ \<tau>. \<tau>)", THEN cpI1]
lemmas cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_at_pre_I [simp] = cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_at_pre[THEN allI[THEN allI], of "(\<lambda>X _. X)" "(\<lambda>_ \<tau>. \<tau>)", THEN cpI1]
lemmas cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>_I [simp] = cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>[THEN allI[THEN allI], of "(\<lambda>X _. X)" "(\<lambda>_ \<tau>. \<tau>)", THEN cpI1]
lemmas cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>_at_pre_I [simp] = cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>_at_pre[THEN allI[THEN allI], of "(\<lambda>X _. X)" "(\<lambda>_ \<tau>. \<tau>)", THEN cpI1]
lemmas cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>_I [simp] = cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>[THEN allI[THEN allI], of "(\<lambda>X _. X)" "(\<lambda>_ \<tau>. \<tau>)", THEN cpI1]
lemmas cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>_I [simp] = cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>[THEN allI[THEN allI], of "(\<lambda>X _. X)" "(\<lambda>_ \<tau>. \<tau>)", THEN cpI1]
lemmas cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>_at_pre_I [simp] = cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>_at_pre[THEN allI[THEN allI], of "(\<lambda>X _. X)" "(\<lambda>_ \<tau>. \<tau>)", THEN cpI1]
lemmas cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>_at_pre_I [simp] = cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>_at_pre[THEN allI[THEN allI], of "(\<lambda>X _. X)" "(\<lambda>_ \<tau>. \<tau>)", THEN cpI1]
lemmas cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>_I [simp] = cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>[THEN allI[THEN allI], of "(\<lambda>X _. X)" "(\<lambda>_ \<tau>. \<tau>)", THEN cpI1]
lemmas cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>_I [simp] = cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>[THEN allI[THEN allI], of "(\<lambda>X _. X)" "(\<lambda>_ \<tau>. \<tau>)", THEN cpI1]
lemmas cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>_I [simp] = cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>[THEN allI[THEN allI], of "(\<lambda>X _. X)" "(\<lambda>_ \<tau>. \<tau>)", THEN cpI1]
lemmas cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>_at_pre_I [simp] = cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>_at_pre[THEN allI[THEN allI], of "(\<lambda>X _. X)" "(\<lambda>_ \<tau>. \<tau>)", THEN cpI1]
lemmas cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>_at_pre_I [simp] = cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>_at_pre[THEN allI[THEN allI], of "(\<lambda>X _. X)" "(\<lambda>_ \<tau>. \<tau>)", THEN cpI1]
lemmas cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>_at_pre_I [simp] = cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>_at_pre[THEN allI[THEN allI], of "(\<lambda>X _. X)" "(\<lambda>_ \<tau>. \<tau>)", THEN cpI1]
lemmas cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>_I [simp] = cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>[THEN allI[THEN allI], of "(\<lambda>X _. X)" "(\<lambda>_ \<tau>. \<tau>)", THEN cpI1]
lemmas cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>_I [simp] = cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>[THEN allI[THEN allI], of "(\<lambda>X _. X)" "(\<lambda>_ \<tau>. \<tau>)", THEN cpI1]
lemmas cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>_at_pre_I [simp] = cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>_at_pre[THEN allI[THEN allI], of "(\<lambda>X _. X)" "(\<lambda>_ \<tau>. \<tau>)", THEN cpI1]
lemmas cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>_at_pre_I [simp] = cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>_at_pre[THEN allI[THEN allI], of "(\<lambda>X _. X)" "(\<lambda>_ \<tau>. \<tau>)", THEN cpI1]

(* 82 *********************************** *)
subsection{* Execution with Invalid or Null as Argument *}

(* 83 *********************************** *)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_invalid : "(invalid) .salary = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_null : "(null) .salary = invalid"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_invalid : "(invalid) .boss = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_null : "(null) .boss = invalid"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_at_pre_invalid : "(invalid) .salary@pre = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_at_pre_null : "(null) .salary@pre = invalid"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_at_pre_invalid : "(invalid) .boss@pre = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_at_pre_null : "(null) .boss@pre = invalid"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>_invalid : "(invalid) .weight = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>_null : "(null) .weight = invalid"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>_at_pre_invalid : "(invalid) .weight@pre = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>_at_pre_null : "(null) .weight@pre = invalid"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>_invalid : "(invalid) .sound = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>_null : "(null) .sound = invalid"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>_invalid : "(invalid) .moving = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>_null : "(null) .moving = invalid"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>_at_pre_invalid : "(invalid) .sound@pre = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>_at_pre_null : "(null) .sound@pre = invalid"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>_at_pre_invalid : "(invalid) .moving@pre = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>_at_pre_null : "(null) .moving@pre = invalid"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>_invalid : "(invalid) .weight = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>_null : "(null) .weight = invalid"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>_invalid : "(invalid) .sound = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>_null : "(null) .sound = invalid"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>_invalid : "(invalid) .moving = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>_null : "(null) .moving = invalid"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>_at_pre_invalid : "(invalid) .weight@pre = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>_at_pre_null : "(null) .weight@pre = invalid"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>_at_pre_invalid : "(invalid) .sound@pre = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>_at_pre_null : "(null) .sound@pre = invalid"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>_at_pre_invalid : "(invalid) .moving@pre = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>_at_pre_null : "(null) .moving@pre = invalid"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>_invalid : "(invalid) .sound = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>_null : "(null) .sound = invalid"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>_invalid : "(invalid) .moving = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>_null : "(null) .moving = invalid"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>_at_pre_invalid : "(invalid) .sound@pre = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>_at_pre_null : "(null) .sound@pre = invalid"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>_at_pre_invalid : "(invalid) .moving@pre = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>_at_pre_null : "(null) .moving@pre = invalid"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)

(* 84 *********************************** *)
section{* A Little Infra-structure on Example States *}

end
