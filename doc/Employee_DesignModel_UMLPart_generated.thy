theory Employee_DesignModel_UMLPart_generated imports "../src/UML_Main"   "../src/compiler/OCL_compiler_static"   "../src/compiler/OCL_compiler_generator_dynamic" begin

(* 1 ************************************ 0 + 1 *)
text{* 
   \label{ex:employee-design:uml}  *}

(* 2 ************************************ 1 + 1 *)
text{*  *}

(* 3 ************************************ 2 + 1 *)
section{* Introduction *}

(* 4 ************************************ 3 + 1 *)
text{* 

  For certain concepts like classes and class-types, only a generic
  definition for its resulting semantics can be given. Generic means,
  there is a function outside HOL that ``compiles'' a concrete,
  closed-world class diagram into a ``theory'' of this data model,
  consisting of a bunch of definitions for classes, accessors, method,
  casts, and tests for actual types, as well as proofs for the
  fundamental properties of these operations in this concrete data
  model.  *}

(* 5 ************************************ 4 + 1 *)
text{* 
   Such generic function or ``compiler'' can be implemented in
  Isabelle on the ML level.  This has been done, for a semantics
  following the open-world assumption, for UML 2.0
  in~\cite{brucker.ea:extensible:2008-b, brucker:interactive:2007}. In
  this paper, we follow another approach for UML 2.4: we define the
  concepts of the compilation informally, and present a concrete
  example which is verified in Isabelle/HOL.  *}

(* 6 ************************************ 5 + 1 *)
subsection{* Outlining the Example *}

(* 7 ************************************ 6 + 1 *)
text{* 
   We are presenting here a ``design-model'' of the (slightly
modified) example Figure 7.3, page 20 of
the OCL standard~\cite{omg:ocl:2012}. To be precise, this theory contains the formalization of
the data-part covered by the UML class model (see \autoref{fig:person}): *}

(* 8 ************************************ 7 + 1 *)
text{*  *}

(* 9 ************************************ 8 + 1 *)
text{* 

\begin{figure}
  \centering\scalebox{.3}{\includegraphics{figures/person.png}}%
  \caption{A simple UML class model drawn from Figure 7.3,
  page 20 of~\cite{omg:ocl:2012}. \label{fig:person}}
\end{figure}
 *}

(* 10 ************************************ 9 + 1 *)
text{*  *}

(* 11 ************************************ 10 + 1 *)
text{* 
   This means that the association (attached to the association class
\inlineocl{EmployeeRanking}) with the association ends \inlineocl+boss+ and \inlineocl+employees+ is implemented
by the attribute  \inlineocl+boss+ and the operation \inlineocl+employees+ (to be discussed in the OCL part
captured by the subsequent theory).
 *}

(* 12 ************************************ 11 + 1 *)
section{* Example Data-Universe and its Infrastructure *}

(* 13 ************************************ 12 + 1 *)
text{* 
   Our data universe  consists in the concrete class diagram just of node's,
and implicitly of the class object. Each class implies the existence of a class
type defined for the corresponding object representations as follows:  *}

(* 14 ************************************ 13 + 8 *)
datatype type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n = mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n oid "nat option" "int option" "unit option" "bool option"
datatype typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n = mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n "oid list option" "int option"
datatype type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t = mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n
                        | mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t oid "unit option" "bool option"
datatype typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t = mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t "nat option" "int option"
datatype type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y = mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t
                        | mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n
                        | mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y oid
datatype typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y = mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y "unit option" "bool option"
datatype type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y
                        | mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t
                        | mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n
                        | mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y oid
datatype typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y

(* 15 ************************************ 21 + 1 *)
text{* 
   Now, we construct a concrete ``universe of OclAny types'' by injection into a
sum type containing the class types. This type of OclAny will be used as instance
for all respective type-variables.  *}

(* 16 ************************************ 22 + 1 *)
datatype \<AA> = in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n
                        | in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t
                        | in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y
                        | in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y

(* 17 ************************************ 23 + 1 *)
text{* 
   Having fixed the object universe, we can introduce type synonyms that exactly correspond
to OCL types. Again, we exploit that our representation of OCL is a ``shallow embedding'' with a
one-to-one correspondance of OCL-types to types of the meta-language HOL.  *}

(* 18 ************************************ 24 + 9 *)
type_synonym Void = "\<AA> Void"
type_synonym Boolean = "\<AA> Boolean"
type_synonym Integer = "\<AA> Integer"
type_synonym Real = "\<AA> Real"
type_synonym String = "\<AA> String"
type_synonym Person = "(\<AA>, typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n option option) val"
type_synonym Planet = "(\<AA>, typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t option option) val"
type_synonym Galaxy = "(\<AA>, typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y option option) val"
type_synonym OclAny = "(\<AA>, typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y option option) val"

(* 19 ************************************ 33 + 4 *)
type_synonym Set_Person = "(\<AA>, typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n option option) Set"
type_synonym Set_Planet = "(\<AA>, typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t option option) Set"
type_synonym Set_Galaxy = "(\<AA>, typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y option option) Set"
type_synonym Set_OclAny = "(\<AA>, typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y option option) Set"

(* 20 ************************************ 37 + 4 *)
type_synonym Sequence_Person = "(\<AA>, typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n option option) Sequence"
type_synonym Sequence_Planet = "(\<AA>, typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t option option) Sequence"
type_synonym Sequence_Galaxy = "(\<AA>, typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y option option) Sequence"
type_synonym Sequence_OclAny = "(\<AA>, typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y option option) Sequence"

(* 21 ************************************ 41 + 1 *)
text{* 
   To reuse key-elements of the library like referential equality, we have
to show that the object universe belongs to the type class ``oclany,'' \ie,
 each class type has to provide a function @{term oid_of} yielding the object id (oid) of the object.  *}

(* 22 ************************************ 42 + 4 *)
instantiation typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: object
begin
  definition oid_of_typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def : "oid_of = (\<lambda> mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n t _ _ \<Rightarrow> (case t of (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t) (_) (_) (_) (_)) \<Rightarrow> t))"
  instance ..
end
instantiation typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t :: object
begin
  definition oid_of_typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_def : "oid_of = (\<lambda> mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t t _ _ \<Rightarrow> (case t of (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t) (_) (_)) \<Rightarrow> t
    | (mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t)) \<Rightarrow> (oid_of (t))))"
  instance ..
end
instantiation typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :: object
begin
  definition oid_of_typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_def : "oid_of = (\<lambda> mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y t _ _ \<Rightarrow> (case t of (mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (t)) \<Rightarrow> t
    | (mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t)) \<Rightarrow> (oid_of (t))
    | (mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t)) \<Rightarrow> (oid_of (t))))"
  instance ..
end
instantiation typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: object
begin
  definition oid_of_typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def : "oid_of = (\<lambda> mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y t \<Rightarrow> (case t of (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (t)) \<Rightarrow> t
    | (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (t)) \<Rightarrow> (oid_of (t))
    | (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (t)) \<Rightarrow> (oid_of (t))
    | (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (t)) \<Rightarrow> (oid_of (t))))"
  instance ..
end

(* 23 ************************************ 46 + 1 *)
instantiation \<AA> :: object
begin
  definition oid_of_\<AA>_def : "oid_of = (\<lambda> in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n Person \<Rightarrow> oid_of Person
    | in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t Planet \<Rightarrow> oid_of Planet
    | in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y Galaxy \<Rightarrow> oid_of Galaxy
    | in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y OclAny \<Rightarrow> oid_of OclAny)"
  instance ..
end

(* 24 ************************************ 47 + 1 *)
section{* Instantiation of the Generic Strict Equality *}

(* 25 ************************************ 48 + 1 *)
text{* 
   We instantiate the referential equality
on @{text "Person"} and @{text "OclAny"}  *}

(* 26 ************************************ 49 + 4 *)
defs(overloaded) StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n : "(x::Person) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
defs(overloaded) StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t : "(x::Planet) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
defs(overloaded) StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y : "(x::Galaxy) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
defs(overloaded) StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : "(x::OclAny) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"

(* 27 ************************************ 53 + 1 *)
lemmas[simp,code_unfold] = StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n
                            StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t
                            StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y
                            StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y

(* 28 ************************************ 54 + 1 *)
text{* 
   For each Class \emph{C}, we will have a casting operation \inlineocl{.oclAsType($C$)},
   a test on the actual type \inlineocl{.oclIsTypeOf($C$)} as well as its relaxed form
   \inlineocl{.oclIsKindOf($C$)} (corresponding exactly to Java's \verb+instanceof+-operator.
 *}

(* 29 ************************************ 55 + 1 *)
text{* 
   Thus, since we have two class-types in our concrete class hierarchy, we have
two operations to declare and to provide two overloading definitions for the two static types.
 *}

(* 30 ************************************ 56 + 1 *)
section{* OclAsType *}

(* 31 ************************************ 57 + 1 *)
subsection{* Definition *}

(* 32 ************************************ 58 + 4 *)
consts OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: "'\<alpha> \<Rightarrow> Person" ("(_) .oclAsType'(Person')")
consts OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t :: "'\<alpha> \<Rightarrow> Planet" ("(_) .oclAsType'(Planet')")
consts OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :: "'\<alpha> \<Rightarrow> Galaxy" ("(_) .oclAsType'(Galaxy')")
consts OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: "'\<alpha> \<Rightarrow> OclAny" ("(_) .oclAsType'(OclAny')")

(* 33 ************************************ 62 + 16 *)
defs(overloaded) OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person : "(x::Person) .oclAsType(Person) \<equiv> x"
defs(overloaded) OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet : "(x::Planet) .oclAsType(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Person\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy : "(x::Galaxy) .oclAsType(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Person\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny : "(x::OclAny) .oclAsType(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Person\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet : "(x::Planet) .oclAsType(Planet) \<equiv> x"
defs(overloaded) OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy : "(x::Galaxy) .oclAsType(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Planet\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny : "(x::OclAny) .oclAsType(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Planet\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person : "(x::Person) .oclAsType(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Person\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (None) (None))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy : "(x::Galaxy) .oclAsType(Galaxy) \<equiv> x"
defs(overloaded) OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny : "(x::OclAny) .oclAsType(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Galaxy\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person : "(x::Person) .oclAsType(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Person\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (None) (None))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet : "(x::Planet) .oclAsType(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Planet\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))) (None) (None))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny : "(x::OclAny) .oclAsType(OclAny) \<equiv> x"
defs(overloaded) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person : "(x::Person) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Person\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet : "(x::Planet) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Planet\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy : "(x::Galaxy) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Galaxy\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy))))\<rfloor>\<rfloor>))"

(* 34 ************************************ 78 + 4 *)
definition "OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA> = (\<lambda> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> \<lfloor>Person\<rfloor>
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (_) (_)))) \<Rightarrow> \<lfloor>Person\<rfloor>
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (_) (_)))) \<Rightarrow> \<lfloor>Person\<rfloor>
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)))))) \<Rightarrow> \<lfloor>Person\<rfloor>
    | _ \<Rightarrow> None)"
definition "OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA> = (\<lambda> (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> \<lfloor>Planet\<rfloor>
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))) (_) (_)))) \<Rightarrow> \<lfloor>Planet\<rfloor>
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)))))) \<Rightarrow> \<lfloor>Planet\<rfloor>
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> \<lfloor>(mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (None) (None))\<rfloor>
    | _ \<Rightarrow> None)"
definition "OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA> = (\<lambda> (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> \<lfloor>Galaxy\<rfloor>
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)))))) \<Rightarrow> \<lfloor>Galaxy\<rfloor>
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> \<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))) (None) (None))\<rfloor>
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> \<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))) (None) (None))\<rfloor>
    | _ \<Rightarrow> None)"
definition "OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> = Some o (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> OclAny
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person))))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet))))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)))))"

(* 35 ************************************ 82 + 1 *)
lemmas[simp,code_unfold] = OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person
                            OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet
                            OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny

(* 36 ************************************ 83 + 1 *)
subsection{* Context Passing *}

(* 37 ************************************ 84 + 64 *)
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

(* 38 ************************************ 148 + 1 *)
lemmas[simp,code_unfold] = cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny
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

(* 39 ************************************ 149 + 1 *)
subsection{* Execution with Invalid or Null as Argument *}

(* 40 ************************************ 150 + 32 *)
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

(* 41 ************************************ 182 + 1 *)
lemmas[simp,code_unfold] = OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid
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

(* 42 ************************************ 183 + 1 *)
subsection{* Validity and Definedness Properties *}

(* 43 ************************************ 184 + 6 *)
lemma OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclAsType(Planet)))"
  using isdef
by(auto simp: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person foundation16 null_option_def bot_option_def) 
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclAsType(Galaxy)))"
  using isdef
by(auto simp: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person foundation16 null_option_def bot_option_def) 
lemma OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclAsType(Galaxy)))"
  using isdef
by(auto simp: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet foundation16 null_option_def bot_option_def) 
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclAsType(OclAny)))"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person foundation16 null_option_def bot_option_def) 
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclAsType(OclAny)))"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet foundation16 null_option_def bot_option_def) 
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclAsType(OclAny)))"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy foundation16 null_option_def bot_option_def) 

(* 44 ************************************ 190 + 1 *)
subsection{* Up Down Casting *}

(* 45 ************************************ 191 + 6 *)
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

(* 46 ************************************ 197 + 6 *)
lemma up\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast : 
shows "(((X::Person) .oclAsType(Planet)) .oclAsType(Person)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done 
lemma up\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast : 
shows "(((X::Person) .oclAsType(Galaxy)) .oclAsType(Person)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done 
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast : 
shows "(((X::Person) .oclAsType(OclAny)) .oclAsType(Person)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done 
lemma up\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_down\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_cast : 
shows "(((X::Planet) .oclAsType(Galaxy)) .oclAsType(Planet)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_down\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done 
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_cast : 
shows "(((X::Planet) .oclAsType(OclAny)) .oclAsType(Planet)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done 
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_cast : 
shows "(((X::Galaxy) .oclAsType(OclAny)) .oclAsType(Galaxy)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done 

(* 47 ************************************ 203 + 6 *)
lemma down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_up\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_cast : 
assumes def_X: "X = ((Y::Person) .oclAsType(Planet))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Person)) .oclAsType(Planet)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym) 
lemma down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_up\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_cast : 
assumes def_X: "X = ((Y::Person) .oclAsType(Galaxy))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Person)) .oclAsType(Galaxy)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym) 
lemma down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_cast : 
assumes def_X: "X = ((Y::Person) .oclAsType(OclAny))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Person)) .oclAsType(OclAny)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym) 
lemma down\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_up\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_cast : 
assumes def_X: "X = ((Y::Planet) .oclAsType(Galaxy))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Planet)) .oclAsType(Galaxy)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_down\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym) 
lemma down\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_cast : 
assumes def_X: "X = ((Y::Planet) .oclAsType(OclAny))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Planet)) .oclAsType(OclAny)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym) 
lemma down\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_cast : 
assumes def_X: "X = ((Y::Galaxy) .oclAsType(OclAny))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Galaxy)) .oclAsType(OclAny)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym) 

(* 48 ************************************ 209 + 1 *)
section{* OclIsTypeOf *}

(* 49 ************************************ 210 + 1 *)
subsection{* Definition *}

(* 50 ************************************ 211 + 4 *)
consts OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Person')")
consts OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Planet')")
consts OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Galaxy')")
consts OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(OclAny')")

(* 51 ************************************ 215 + 16 *)
defs(overloaded) OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person : "(x::Person) .oclIsTypeOf(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (_) (_) (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet : "(x::Planet) .oclIsTypeOf(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy : "(x::Galaxy) .oclIsTypeOf(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny : "(x::OclAny) .oclIsTypeOf(Person) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet : "(x::Planet) .oclIsTypeOf(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (_) (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy : "(x::Galaxy) .oclIsTypeOf(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny : "(x::OclAny) .oclIsTypeOf(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person : "(x::Person) .oclIsTypeOf(Planet) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy : "(x::Galaxy) .oclIsTypeOf(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny : "(x::OclAny) .oclIsTypeOf(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person : "(x::Person) .oclIsTypeOf(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet : "(x::Planet) .oclIsTypeOf(Galaxy) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny : "(x::OclAny) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person : "(x::Person) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet : "(x::Planet) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy : "(x::Galaxy) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"

(* 52 ************************************ 231 + 4 *)
definition "OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA> = (\<lambda> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsTypeOf(Person))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsTypeOf(Person))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsTypeOf(Person))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsTypeOf(Person)))"
definition "OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA> = (\<lambda> (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsTypeOf(Planet))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsTypeOf(Planet))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsTypeOf(Planet))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsTypeOf(Planet)))"
definition "OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA> = (\<lambda> (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsTypeOf(Galaxy))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsTypeOf(Galaxy))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsTypeOf(Galaxy))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsTypeOf(Galaxy)))"
definition "OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsTypeOf(OclAny))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsTypeOf(OclAny))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsTypeOf(OclAny))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsTypeOf(OclAny)))"

(* 53 ************************************ 235 + 1 *)
lemmas[simp,code_unfold] = OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person
                            OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet
                            OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy
                            OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny

(* 54 ************************************ 236 + 1 *)
subsection{* Context Passing *}

(* 55 ************************************ 237 + 64 *)
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

(* 56 ************************************ 301 + 1 *)
lemmas[simp,code_unfold] = cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny
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

(* 57 ************************************ 302 + 1 *)
subsection{* Execution with Invalid or Null as Argument *}

(* 58 ************************************ 303 + 32 *)
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

(* 59 ************************************ 335 + 1 *)
lemmas[simp,code_unfold] = OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid
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

(* 60 ************************************ 336 + 1 *)
subsection{* Validity and Definedness Properties *}

(* 61 ************************************ 337 + 16 *)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsTypeOf(Person)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person split: option.split type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split) 
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsTypeOf(Person)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet split: option.split type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsTypeOf(Person)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy split: option.split type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split) 
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(Person)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny split: option.split type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split) 
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsTypeOf(Planet)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet split: option.split type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsTypeOf(Planet)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy split: option.split type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split) 
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(Planet)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny split: option.split type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split) 
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsTypeOf(Planet)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person split: option.split type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split) 
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsTypeOf(Galaxy)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy split: option.split type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split) 
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(Galaxy)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny split: option.split type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split) 
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsTypeOf(Galaxy)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person split: option.split type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split) 
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsTypeOf(Galaxy)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet split: option.split type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(OclAny)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny split: option.split type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsTypeOf(OclAny)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person split: option.split type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsTypeOf(OclAny)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet split: option.split type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsTypeOf(OclAny)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy split: option.split type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split) 

(* 62 ************************************ 353 + 16 *)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsTypeOf(Person)))"
by(rule OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsTypeOf(Person)))"
by(rule OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsTypeOf(Person)))"
by(rule OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(Person)))"
by(rule OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsTypeOf(Planet)))"
by(rule OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsTypeOf(Planet)))"
by(rule OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(Planet)))"
by(rule OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsTypeOf(Planet)))"
by(rule OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsTypeOf(Galaxy)))"
by(rule OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(Galaxy)))"
by(rule OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsTypeOf(Galaxy)))"
by(rule OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsTypeOf(Galaxy)))"
by(rule OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(OclAny)))"
by(rule OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsTypeOf(OclAny)))"
by(rule OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsTypeOf(OclAny)))"
by(rule OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsTypeOf(OclAny)))"
by(rule OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_defined[OF isdef[THEN foundation20]]) 

(* 63 ************************************ 369 + 1 *)
subsection{* Up Down Casting *}

(* 64 ************************************ 370 + 6 *)
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

(* 65 ************************************ 376 + 10 *)
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
lemma down_cast_type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_OclAny_to_Planet : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Galaxy))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Planet)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Galaxy : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(OclAny))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Galaxy)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny foundation22 foundation16 null_option_def bot_option_def split: type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclValid_def false_def true_def) 

(* 66 ************************************ 386 + 1 *)
section{* OclIsKindOf *}

(* 67 ************************************ 387 + 1 *)
subsection{* Definition *}

(* 68 ************************************ 388 + 4 *)
consts OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Person')")
consts OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Planet')")
consts OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Galaxy')")
consts OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(OclAny')")

(* 69 ************************************ 392 + 16 *)
defs(overloaded) OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person : "(x::Person) .oclIsKindOf(Person) \<equiv> (x .oclIsTypeOf(Person))"
defs(overloaded) OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet : "(x::Planet) .oclIsKindOf(Person) \<equiv> (x .oclIsTypeOf(Person))"
defs(overloaded) OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy : "(x::Galaxy) .oclIsKindOf(Person) \<equiv> (x .oclIsTypeOf(Person))"
defs(overloaded) OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny : "(x::OclAny) .oclIsKindOf(Person) \<equiv> (x .oclIsTypeOf(Person))"
defs(overloaded) OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet : "(x::Planet) .oclIsKindOf(Planet) \<equiv> (x .oclIsTypeOf(Planet)) or (x .oclIsKindOf(Person))"
defs(overloaded) OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy : "(x::Galaxy) .oclIsKindOf(Planet) \<equiv> (x .oclIsTypeOf(Planet)) or (x .oclIsKindOf(Person))"
defs(overloaded) OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny : "(x::OclAny) .oclIsKindOf(Planet) \<equiv> (x .oclIsTypeOf(Planet)) or (x .oclIsKindOf(Person))"
defs(overloaded) OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person : "(x::Person) .oclIsKindOf(Planet) \<equiv> (x .oclIsTypeOf(Planet)) or (x .oclIsKindOf(Person))"
defs(overloaded) OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy : "(x::Galaxy) .oclIsKindOf(Galaxy) \<equiv> (x .oclIsTypeOf(Galaxy)) or (x .oclIsKindOf(Planet))"
defs(overloaded) OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny : "(x::OclAny) .oclIsKindOf(Galaxy) \<equiv> (x .oclIsTypeOf(Galaxy)) or (x .oclIsKindOf(Planet))"
defs(overloaded) OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person : "(x::Person) .oclIsKindOf(Galaxy) \<equiv> (x .oclIsTypeOf(Galaxy)) or (x .oclIsKindOf(Planet))"
defs(overloaded) OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet : "(x::Planet) .oclIsKindOf(Galaxy) \<equiv> (x .oclIsTypeOf(Galaxy)) or (x .oclIsKindOf(Planet))"
defs(overloaded) OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny : "(x::OclAny) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Galaxy))"
defs(overloaded) OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person : "(x::Person) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Galaxy))"
defs(overloaded) OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet : "(x::Planet) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Galaxy))"
defs(overloaded) OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy : "(x::Galaxy) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Galaxy))"

(* 70 ************************************ 408 + 4 *)
definition "OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA> = (\<lambda> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsKindOf(Person))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsKindOf(Person))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsKindOf(Person))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsKindOf(Person)))"
definition "OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA> = (\<lambda> (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsKindOf(Planet))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsKindOf(Planet))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsKindOf(Planet))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsKindOf(Planet)))"
definition "OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA> = (\<lambda> (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsKindOf(Galaxy))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsKindOf(Galaxy))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsKindOf(Galaxy))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsKindOf(Galaxy)))"
definition "OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsKindOf(OclAny))
    | (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (Person)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Person))::Person) .oclIsKindOf(OclAny))
    | (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (Planet)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Planet))::Planet) .oclIsKindOf(OclAny))
    | (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (Galaxy)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Galaxy))::Galaxy) .oclIsKindOf(OclAny)))"

(* 71 ************************************ 412 + 1 *)
lemmas[simp,code_unfold] = OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person
                            OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet
                            OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy
                            OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny

(* 72 ************************************ 413 + 1 *)
subsection{* Context Passing *}

(* 73 ************************************ 414 + 64 *)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsKindOf(Person)))))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny, simp only: cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Planet)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Galaxy)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsKindOf(Planet)))))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Galaxy)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Galaxy)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Galaxy)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Galaxy)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_OclAny)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_OclAny)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_OclAny)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Person)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Person)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Person)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Person)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_Planet)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_Planet)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_Planet)
lemma cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsKindOf(Galaxy)))))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet)
by(simp only: cp_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_Planet)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Person) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Person)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Person) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Person)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Person) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Person)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Person)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Person : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Person) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Person)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Person)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Planet) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Planet)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Planet)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Planet) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Planet)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Planet)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Planet) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Planet)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Planet)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Planet : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Planet) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Planet)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Planet)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Galaxy) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Galaxy)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_Galaxy)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Person)))::Galaxy) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Galaxy)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_Galaxy)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Planet)))::Galaxy) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_Galaxy)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_Galaxy)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Galaxy : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Galaxy)))::Galaxy) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_Galaxy)
by(simp only: cp_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_Galaxy)

(* 74 ************************************ 478 + 1 *)
lemmas[simp,code_unfold] = cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny
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

(* 75 ************************************ 479 + 1 *)
subsection{* Execution with Invalid or Null as Argument *}

(* 76 ************************************ 480 + 32 *)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid : "((invalid::Person) .oclIsKindOf(Person)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null : "((null::Person) .oclIsKindOf(Person)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid : "((invalid::Planet) .oclIsKindOf(Person)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null : "((null::Planet) .oclIsKindOf(Person)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid : "((invalid::Galaxy) .oclIsKindOf(Person)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null : "((null::Galaxy) .oclIsKindOf(Person)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid : "((invalid::OclAny) .oclIsKindOf(Person)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null : "((null::OclAny) .oclIsKindOf(Person)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid : "((invalid::Planet) .oclIsKindOf(Planet)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_invalid, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null : "((null::Planet) .oclIsKindOf(Planet)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_null, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid : "((invalid::Galaxy) .oclIsKindOf(Planet)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_invalid, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null : "((null::Galaxy) .oclIsKindOf(Planet)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_null, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid : "((invalid::OclAny) .oclIsKindOf(Planet)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_invalid, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null : "((null::OclAny) .oclIsKindOf(Planet)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_null, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid : "((invalid::Person) .oclIsKindOf(Planet)) = invalid"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_invalid, simp)
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null : "((null::Person) .oclIsKindOf(Planet)) = true"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_null, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid : "((invalid::Galaxy) .oclIsKindOf(Galaxy)) = invalid"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_invalid, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null : "((null::Galaxy) .oclIsKindOf(Galaxy)) = true"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_null, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid : "((invalid::OclAny) .oclIsKindOf(Galaxy)) = invalid"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_invalid, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null : "((null::OclAny) .oclIsKindOf(Galaxy)) = true"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_null, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid : "((invalid::Person) .oclIsKindOf(Galaxy)) = invalid"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_invalid, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null : "((null::Person) .oclIsKindOf(Galaxy)) = true"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_null, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid : "((invalid::Planet) .oclIsKindOf(Galaxy)) = invalid"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_invalid, simp)
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null : "((null::Planet) .oclIsKindOf(Galaxy)) = true"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid : "((invalid::OclAny) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null : "((null::OclAny) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_invalid : "((invalid::Person) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_invalid OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_null : "((null::Person) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_null OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_invalid : "((invalid::Planet) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_invalid OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_null : "((null::Planet) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_null OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_invalid : "((invalid::Galaxy) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_invalid OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_null : "((null::Galaxy) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_null OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_null, simp)

(* 77 ************************************ 512 + 1 *)
lemmas[simp,code_unfold] = OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid
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

(* 78 ************************************ 513 + 1 *)
subsection{* Validity and Definedness Properties *}

(* 79 ************************************ 514 + 16 *)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsKindOf(Person)))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person, rule OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsKindOf(Person)))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet, rule OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsKindOf(Person)))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy, rule OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(Person)))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny, rule OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsKindOf(Planet)))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet, rule defined_or_I[OF OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsKindOf(Planet)))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy, rule defined_or_I[OF OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(Planet)))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny, rule defined_or_I[OF OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsKindOf(Planet)))"
by(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person, rule defined_or_I[OF OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsKindOf(Galaxy)))"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy, rule defined_or_I[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(Galaxy)))"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny, rule defined_or_I[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsKindOf(Galaxy)))"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person, rule defined_or_I[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsKindOf(Galaxy)))"
by(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet, rule defined_or_I[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(OclAny)))"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny, rule defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined[OF isdef], OF OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsKindOf(OclAny)))"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person, rule defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_defined[OF isdef], OF OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsKindOf(OclAny)))"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet, rule defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_defined[OF isdef], OF OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsKindOf(OclAny)))"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy, rule defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_defined[OF isdef], OF OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined[OF isdef]]) 

(* 80 ************************************ 530 + 16 *)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsKindOf(Person)))"
by(rule OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsKindOf(Person)))"
by(rule OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsKindOf(Person)))"
by(rule OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(Person)))"
by(rule OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsKindOf(Planet)))"
by(rule OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsKindOf(Planet)))"
by(rule OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(Planet)))"
by(rule OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsKindOf(Planet)))"
by(rule OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsKindOf(Galaxy)))"
by(rule OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(Galaxy)))"
by(rule OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsKindOf(Galaxy)))"
by(rule OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsKindOf(Galaxy)))"
by(rule OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(OclAny)))"
by(rule OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Person) .oclIsKindOf(OclAny)))"
by(rule OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Planet) .oclIsKindOf(OclAny)))"
by(rule OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .oclIsKindOf(OclAny)))"
by(rule OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy_defined[OF isdef[THEN foundation20]]) 

(* 81 ************************************ 546 + 1 *)
subsection{* Up Down Casting *}

(* 82 ************************************ 547 + 4 *)
lemma actual_eq_static\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Person) .oclIsKindOf(Person))"
  apply(simp only: OclValid_def, insert isdef)
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person)
  apply(auto simp: foundation16 bot_option_def split: option.split type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split)
by((simp_all add: false_def true_def OclOr_def OclAnd_def OclNot_def)?) 
lemma actual_eq_static\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Planet) .oclIsKindOf(Planet))"
  apply(simp only: OclValid_def, insert isdef)
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet, subst (1) cp_OclOr, simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
  apply(auto simp: cp_OclOr[symmetric ] foundation16 bot_option_def OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet split: option.split type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split)
by((simp_all add: false_def true_def OclOr_def OclAnd_def OclNot_def)?) 
lemma actual_eq_static\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Galaxy) .oclIsKindOf(Galaxy))"
  apply(simp only: OclValid_def, insert isdef)
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy, subst (1) cp_OclOr, simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy, subst (2 1) cp_OclOr, simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
  apply(auto simp: cp_OclOr[symmetric ] foundation16 bot_option_def OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy split: option.split type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split)
by((simp_all add: false_def true_def OclOr_def OclAnd_def OclNot_def)?) 
lemma actual_eq_static\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(OclAny))"
  apply(simp only: OclValid_def, insert isdef)
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny, subst (1) cp_OclOr, simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny, subst (2 1) cp_OclOr, simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny, subst (3 2 1) cp_OclOr, simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
  apply(auto simp: cp_OclOr[symmetric ] foundation16 bot_option_def OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny split: option.split type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split type\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split typeoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t.split type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split typeoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y.split)
by((simp_all add: false_def true_def OclOr_def OclAnd_def OclNot_def)?) 

(* 83 ************************************ 551 + 6 *)
lemma actualKind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticKind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Person) .oclIsKindOf(Planet))"
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
by(rule foundation25', rule actual_eq_static\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n[OF isdef]) 
lemma actualKind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticKind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Person) .oclIsKindOf(Galaxy))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
by(rule foundation25', rule actualKind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticKind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t[OF isdef]) 
lemma actualKind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Person) .oclIsKindOf(OclAny))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
by(rule foundation25', rule actualKind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticKind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y[OF isdef]) 
lemma actualKind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_larger_staticKind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Planet) .oclIsKindOf(Galaxy))"
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
by(rule foundation25', rule actual_eq_static\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t[OF isdef]) 
lemma actualKind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Planet) .oclIsKindOf(OclAny))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
by(rule foundation25', rule actualKind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_larger_staticKind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y[OF isdef]) 
lemma actualKind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Galaxy) .oclIsKindOf(OclAny))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
by(rule foundation25', rule actual_eq_static\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y[OF isdef]) 

(* 84 ************************************ 557 + 6 *)
lemma not_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_then_Planet_OclIsTypeOf_others_unfold : 
assumes isdef: "(\<tau> \<Turnstile> (\<delta> (X)))"
assumes iskin: "(\<tau> \<Turnstile> ((X::Planet) .oclIsKindOf(Person)))"
shows "(\<tau> \<Turnstile> ((X::Planet) .oclIsTypeOf(Person)))"
  using iskin
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet)
done 
lemma not_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_then_Galaxy_OclIsTypeOf_others_unfold : 
assumes isdef: "(\<tau> \<Turnstile> (\<delta> (X)))"
assumes iskin: "(\<tau> \<Turnstile> ((X::Galaxy) .oclIsKindOf(Person)))"
shows "(\<tau> \<Turnstile> ((X::Galaxy) .oclIsTypeOf(Person)))"
  using iskin
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy)
done 
lemma not_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_then_OclAny_OclIsTypeOf_others_unfold : 
assumes isdef: "(\<tau> \<Turnstile> (\<delta> (X)))"
assumes iskin: "(\<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Person)))"
shows "(\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Person)))"
  using iskin
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
done 
lemma not_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_then_Galaxy_OclIsTypeOf_others_unfold : 
assumes isdef: "(\<tau> \<Turnstile> (\<delta> (X)))"
assumes iskin: "(\<tau> \<Turnstile> ((X::Galaxy) .oclIsKindOf(Planet)))"
shows "((\<tau> \<Turnstile> ((X::Galaxy) .oclIsTypeOf(Planet))) \<or> (\<tau> \<Turnstile> ((X::Galaxy) .oclIsTypeOf(Person))))"
  using iskin
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined'[OF isdef]])
  apply(simp)
  apply(drule not_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_then_Galaxy_OclIsTypeOf_others_unfold[OF isdef], blast)
done 
lemma not_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_then_OclAny_OclIsTypeOf_others_unfold : 
assumes isdef: "(\<tau> \<Turnstile> (\<delta> (X)))"
assumes iskin: "(\<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Planet)))"
shows "((\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Planet))) \<or> (\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Person))))"
  using iskin
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined'[OF isdef]])
  apply(simp)
  apply(drule not_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_then_OclAny_OclIsTypeOf_others_unfold[OF isdef], blast)
done 
lemma not_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_then_OclAny_OclIsTypeOf_others_unfold : 
assumes isdef: "(\<tau> \<Turnstile> (\<delta> (X)))"
assumes iskin: "(\<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Galaxy)))"
shows "((\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Galaxy))) \<or> ((\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Person))) \<or> (\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Planet)))))"
  using iskin
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined'[OF isdef]])
  apply(simp)
  apply(drule not_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_then_OclAny_OclIsTypeOf_others_unfold[OF isdef], blast)
done 

(* 85 ************************************ 563 + 6 *)
lemma not_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_then_Planet_OclIsTypeOf_others : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::Planet) .oclIsKindOf(Person))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Planet) .oclIsTypeOf(Planet))"
  using actual_eq_static\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet_defined'[OF isdef]])
  apply(simp)
  apply(simp add: iskin)
done 
lemma not_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_then_Galaxy_OclIsTypeOf_others : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::Galaxy) .oclIsKindOf(Person))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "(\<tau> \<Turnstile> ((X::Galaxy) .oclIsTypeOf(Galaxy)) \<or> \<tau> \<Turnstile> ((X::Galaxy) .oclIsTypeOf(Planet)))"
  using actual_eq_static\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined'[OF isdef]])
  apply(simp)
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy_defined'[OF isdef]])
  apply(simp)
  apply(simp add: iskin)
done 
lemma not_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_then_OclAny_OclIsTypeOf_others : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Person))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "(\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(OclAny)) \<or> (\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Galaxy)) \<or> \<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Planet))))"
  using actual_eq_static\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined'[OF isdef]])
  apply(simp)
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined'[OF isdef]])
  apply(simp)
  apply(simp only: OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_defined'[OF isdef]])
  apply(simp)
  apply(simp add: iskin)
done 
lemma not_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_then_Galaxy_OclIsTypeOf_others : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::Galaxy) .oclIsKindOf(Planet))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Galaxy) .oclIsTypeOf(Galaxy))"
  using actual_eq_static\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy_defined'[OF isdef]])
  apply(simp)
  apply(simp add: iskin)
done 
lemma not_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_then_OclAny_OclIsTypeOf_others : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Planet))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "(\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(OclAny)) \<or> \<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Galaxy)))"
  using actual_eq_static\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined'[OF isdef]])
  apply(simp)
  apply(simp only: OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny_defined'[OF isdef]])
  apply(simp)
  apply(simp add: iskin)
done 
lemma not_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_then_OclAny_OclIsTypeOf_others : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Galaxy))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(OclAny))"
  using actual_eq_static\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply(erule foundation26[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny_defined'[OF isdef]])
  apply(simp)
  apply(simp add: iskin)
done 

(* 86 ************************************ 569 + 10 *)
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
lemma down_cast_kind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_from_Galaxy_to_Person : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::Galaxy) .oclIsKindOf(Planet))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_then_Galaxy_OclIsTypeOf_others[OF iskin, OF isdef])
  apply(rule down_cast_type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_Galaxy_to_Person, simp only: , simp only: isdef)
done 
lemma down_cast_kind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_from_OclAny_to_Planet : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Planet))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Planet)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_then_OclAny_OclIsTypeOf_others[OF iskin, OF isdef], elim disjE)
  apply(rule down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Planet, simp only: , simp only: isdef)
  apply(rule down_cast_type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_OclAny_to_Planet, simp only: , simp only: isdef)
done 
lemma down_cast_kind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_from_OclAny_to_Person : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Planet))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_then_OclAny_OclIsTypeOf_others[OF iskin, OF isdef], elim disjE)
  apply(rule down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Person, simp only: , simp only: isdef)
  apply(rule down_cast_type\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_OclAny_to_Person, simp only: , simp only: isdef)
done 
lemma down_cast_kind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_from_OclAny_to_Galaxy : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Galaxy))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Galaxy)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_then_OclAny_OclIsTypeOf_others[OF iskin, OF isdef])
  apply(rule down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Galaxy, simp only: , simp only: isdef)
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

(* 87 ************************************ 579 + 1 *)
section{* OclAllInstances *}

(* 88 ************************************ 580 + 1 *)
text{* 
   To denote OCL-types occuring in OCL expressions syntactically---as, for example,  as
``argument'' of \inlineisar{oclAllInstances()}---we use the inverses of the injection
functions into the object universes; we show that this is sufficient ``characterization.''  *}

(* 89 ************************************ 581 + 4 *)
definition "Person = OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>"
definition "Planet = OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA>"
definition "Galaxy = OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA>"
definition "OclAny = OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>"

(* 90 ************************************ 585 + 1 *)
lemmas[simp,code_unfold] = Person_def
                            Planet_def
                            Galaxy_def
                            OclAny_def

(* 91 ************************************ 586 + 1 *)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_some : "(OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> (x)) \<noteq> None"
by(simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def)

(* 92 ************************************ 587 + 3 *)
lemma OclAllInstances_generic\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_exec : 
shows "(OclAllInstances_generic (pre_post) (OclAny)) = (\<lambda>\<tau>. (Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (\<lfloor>\<lfloor>Some ` OclAny ` (ran ((heap ((pre_post (\<tau>))))))\<rfloor>\<rfloor>)))"
  proof - let ?S1 = "(\<lambda>\<tau>. OclAny ` (ran ((heap ((pre_post (\<tau>)))))))" show ?thesis
  proof - let ?S2 = "(\<lambda>\<tau>. ((?S1) (\<tau>)) - {None})" show ?thesis
  proof - have B: "(\<And>\<tau>. ((?S2) (\<tau>)) \<subseteq> ((?S1) (\<tau>)))" by(auto) show ?thesis
  proof - have C: "(\<And>\<tau>. ((?S1) (\<tau>)) \<subseteq> ((?S2) (\<tau>)))" by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_some) show ?thesis
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
by(insert equalityI[OF B, OF C], simp) qed qed qed qed
lemma OclAllInstances_at_post\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_exec : 
shows "(OclAllInstances_at_post (OclAny)) = (\<lambda>\<tau>. (Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (\<lfloor>\<lfloor>Some ` OclAny ` (ran ((heap ((snd (\<tau>))))))\<rfloor>\<rfloor>)))"
  unfolding OclAllInstances_at_post_def
by(rule OclAllInstances_generic\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_exec) 
lemma OclAllInstances_at_pre\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_exec : 
shows "(OclAllInstances_at_pre (OclAny)) = (\<lambda>\<tau>. (Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (\<lfloor>\<lfloor>Some ` OclAny ` (ran ((heap ((fst (\<tau>))))))\<rfloor>\<rfloor>)))"
  unfolding OclAllInstances_at_pre_def
by(rule OclAllInstances_generic\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_exec) 

(* 93 ************************************ 590 + 1 *)
subsection{* OclIsTypeOf *}

(* 94 ************************************ 591 + 2 *)
lemma ex_ssubst : "(\<forall>x \<in> B. (s (x)) = (t (x))) \<Longrightarrow> (\<exists>x \<in> B. (P ((s (x))))) = (\<exists>x \<in> B. (P ((t (x)))))"
by(simp)
lemma ex_def : "x \<in> \<lceil>\<lceil>\<lfloor>\<lfloor>Some ` (X - {None})\<rfloor>\<rfloor>\<rceil>\<rceil> \<Longrightarrow> (\<exists>y. x = \<lfloor>\<lfloor>y\<rfloor>\<rfloor>)"
by(auto)

(* 95 ************************************ 593 + 21 *)
lemma Person_OclAllInstances_generic_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Person))) (OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsTypeOf(Person)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actual_eq_static\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n[simplified OclValid_def, simplified OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Person_OclAllInstances_at_post_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Person))) (OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))"
  unfolding OclAllInstances_at_post_def
by(rule Person_OclAllInstances_generic_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n) 
lemma Person_OclAllInstances_at_pre_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Person))) (OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))"
  unfolding OclAllInstances_at_pre_def
by(rule Person_OclAllInstances_generic_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n) 
lemma Planet_OclAllInstances_generic_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t1 : 
assumes [simp]: "(\<And>x. (pre_post ((x , x))) = x)"
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Planet))) (OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t)))"
  apply(rule exI[where x = "\<tau>\<^sub>0"], simp add: \<tau>\<^sub>0_def OclValid_def del: OclAllInstances_generic_def)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
by(simp) 
lemma Planet_OclAllInstances_at_post_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t1 : 
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Planet))) (OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t)))"
  unfolding OclAllInstances_at_post_def
by(rule Planet_OclAllInstances_generic_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t1, simp) 
lemma Planet_OclAllInstances_at_pre_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t1 : 
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Planet))) (OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t)))"
  unfolding OclAllInstances_at_pre_def
by(rule Planet_OclAllInstances_generic_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t1, simp) 
lemma Planet_OclAllInstances_generic_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t2 : 
assumes [simp]: "(\<And>x. (pre_post ((x , x))) = x)"
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (not ((UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Planet))) (OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t)))))"
  proof - fix oid a show ?thesis
  proof - let ?t0 = "(state.make ((Map.empty (oid \<mapsto> (in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (a))) (None) (None))))))) (Map.empty))" show ?thesis
  apply(rule exI[where x = "(?t0 , ?t0)"], simp add: OclValid_def del: OclAllInstances_generic_def)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA>_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
by(simp add: state.make_def OclNot_def) qed qed
lemma Planet_OclAllInstances_at_post_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t2 : 
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (not ((UML_Set.OclForall ((OclAllInstances_at_post (Planet))) (OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t)))))"
  unfolding OclAllInstances_at_post_def
by(rule Planet_OclAllInstances_generic_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t2, simp) 
lemma Planet_OclAllInstances_at_pre_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t2 : 
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (not ((UML_Set.OclForall ((OclAllInstances_at_pre (Planet))) (OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t)))))"
  unfolding OclAllInstances_at_pre_def
by(rule Planet_OclAllInstances_generic_OclIsTypeOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t2, simp) 
lemma Galaxy_OclAllInstances_generic_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y1 : 
assumes [simp]: "(\<And>x. (pre_post ((x , x))) = x)"
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Galaxy))) (OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y)))"
  apply(rule exI[where x = "\<tau>\<^sub>0"], simp add: \<tau>\<^sub>0_def OclValid_def del: OclAllInstances_generic_def)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
by(simp) 
lemma Galaxy_OclAllInstances_at_post_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y1 : 
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Galaxy))) (OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y)))"
  unfolding OclAllInstances_at_post_def
by(rule Galaxy_OclAllInstances_generic_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y1, simp) 
lemma Galaxy_OclAllInstances_at_pre_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y1 : 
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Galaxy))) (OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y)))"
  unfolding OclAllInstances_at_pre_def
by(rule Galaxy_OclAllInstances_generic_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y1, simp) 
lemma Galaxy_OclAllInstances_generic_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y2 : 
assumes [simp]: "(\<And>x. (pre_post ((x , x))) = x)"
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (not ((UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Galaxy))) (OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y)))))"
  proof - fix oid a show ?thesis
  proof - let ?t0 = "(state.make ((Map.empty (oid \<mapsto> (in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y ((mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (a))) (None) (None))))))) (Map.empty))" show ?thesis
  apply(rule exI[where x = "(?t0 , ?t0)"], simp add: OclValid_def del: OclAllInstances_generic_def)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA>_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
by(simp add: state.make_def OclNot_def) qed qed
lemma Galaxy_OclAllInstances_at_post_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y2 : 
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (not ((UML_Set.OclForall ((OclAllInstances_at_post (Galaxy))) (OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y)))))"
  unfolding OclAllInstances_at_post_def
by(rule Galaxy_OclAllInstances_generic_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y2, simp) 
lemma Galaxy_OclAllInstances_at_pre_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y2 : 
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (not ((UML_Set.OclForall ((OclAllInstances_at_pre (Galaxy))) (OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y)))))"
  unfolding OclAllInstances_at_pre_def
by(rule Galaxy_OclAllInstances_generic_OclIsTypeOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y2, simp) 
lemma OclAny_OclAllInstances_generic_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y1 : 
assumes [simp]: "(\<And>x. (pre_post ((x , x))) = x)"
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (OclAny))) (OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y)))"
  apply(rule exI[where x = "\<tau>\<^sub>0"], simp add: \<tau>\<^sub>0_def OclValid_def del: OclAllInstances_generic_def)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
by(simp) 
lemma OclAny_OclAllInstances_at_post_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y1 : 
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (OclAny))) (OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y)))"
  unfolding OclAllInstances_at_post_def
by(rule OclAny_OclAllInstances_generic_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y1, simp) 
lemma OclAny_OclAllInstances_at_pre_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y1 : 
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (OclAny))) (OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y)))"
  unfolding OclAllInstances_at_pre_def
by(rule OclAny_OclAllInstances_generic_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y1, simp) 
lemma OclAny_OclAllInstances_generic_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y2 : 
assumes [simp]: "(\<And>x. (pre_post ((x , x))) = x)"
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (not ((UML_Set.OclForall ((OclAllInstances_generic (pre_post) (OclAny))) (OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y)))))"
  proof - fix oid a show ?thesis
  proof - let ?t0 = "(state.make ((Map.empty (oid \<mapsto> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (a))))))))) (Map.empty))" show ?thesis
  apply(rule exI[where x = "(?t0 , ?t0)"], simp add: OclValid_def del: OclAllInstances_generic_def)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
by(simp add: state.make_def OclNot_def) qed qed
lemma OclAny_OclAllInstances_at_post_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y2 : 
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (not ((UML_Set.OclForall ((OclAllInstances_at_post (OclAny))) (OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y)))))"
  unfolding OclAllInstances_at_post_def
by(rule OclAny_OclAllInstances_generic_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y2, simp) 
lemma OclAny_OclAllInstances_at_pre_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y2 : 
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (not ((UML_Set.OclForall ((OclAllInstances_at_pre (OclAny))) (OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y)))))"
  unfolding OclAllInstances_at_pre_def
by(rule OclAny_OclAllInstances_generic_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y2, simp) 

(* 96 ************************************ 614 + 1 *)
subsection{* OclIsKindOf *}

(* 97 ************************************ 615 + 12 *)
lemma Person_OclAllInstances_generic_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Person))) (OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(Person)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actual_eq_static\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Person_OclAllInstances_at_post_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Person))) (OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))"
  unfolding OclAllInstances_at_post_def
by(rule Person_OclAllInstances_generic_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n) 
lemma Person_OclAllInstances_at_pre_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Person))) (OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))"
  unfolding OclAllInstances_at_pre_def
by(rule Person_OclAllInstances_generic_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n) 
lemma Planet_OclAllInstances_generic_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Planet))) (OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Planet)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(Planet)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actual_eq_static\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Planet_OclAllInstances_at_post_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Planet))) (OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t))"
  unfolding OclAllInstances_at_post_def
by(rule Planet_OclAllInstances_generic_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t) 
lemma Planet_OclAllInstances_at_pre_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Planet))) (OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t))"
  unfolding OclAllInstances_at_pre_def
by(rule Planet_OclAllInstances_generic_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t) 
lemma Galaxy_OclAllInstances_generic_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Galaxy))) (OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Galaxy)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(Galaxy)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actual_eq_static\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Galaxy_OclAllInstances_at_post_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Galaxy))) (OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y))"
  unfolding OclAllInstances_at_post_def
by(rule Galaxy_OclAllInstances_generic_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y) 
lemma Galaxy_OclAllInstances_at_pre_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Galaxy))) (OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y))"
  unfolding OclAllInstances_at_pre_def
by(rule Galaxy_OclAllInstances_generic_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y) 
lemma OclAny_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (OclAny))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(OclAny)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actual_eq_static\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma OclAny_OclAllInstances_at_post_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (OclAny))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_post_def
by(rule OclAny_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y) 
lemma OclAny_OclAllInstances_at_pre_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (OclAny))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_pre_def
by(rule OclAny_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y) 

(* 98 ************************************ 627 + 18 *)
lemma Person_OclAllInstances_generic_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Person))) (OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(Planet)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actualKind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticKind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Person_OclAllInstances_at_post_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Person))) (OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t))"
  unfolding OclAllInstances_at_post_def
by(rule Person_OclAllInstances_generic_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t) 
lemma Person_OclAllInstances_at_pre_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Person))) (OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t))"
  unfolding OclAllInstances_at_pre_def
by(rule Person_OclAllInstances_generic_OclIsKindOf\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t) 
lemma Person_OclAllInstances_generic_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Person))) (OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(Galaxy)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actualKind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticKind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Person_OclAllInstances_at_post_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Person))) (OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y))"
  unfolding OclAllInstances_at_post_def
by(rule Person_OclAllInstances_generic_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y) 
lemma Person_OclAllInstances_at_pre_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Person))) (OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y))"
  unfolding OclAllInstances_at_pre_def
by(rule Person_OclAllInstances_generic_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y) 
lemma Person_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Person))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(OclAny)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actualKind\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Person_OclAllInstances_at_post_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Person))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_post_def
by(rule Person_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y) 
lemma Person_OclAllInstances_at_pre_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Person))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_pre_def
by(rule Person_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y) 
lemma Planet_OclAllInstances_generic_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Planet))) (OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(Galaxy)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actualKind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_larger_staticKind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Planet_OclAllInstances_at_post_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Planet))) (OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y))"
  unfolding OclAllInstances_at_post_def
by(rule Planet_OclAllInstances_generic_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y) 
lemma Planet_OclAllInstances_at_pre_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Planet))) (OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y))"
  unfolding OclAllInstances_at_pre_def
by(rule Planet_OclAllInstances_generic_OclIsKindOf\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y) 
lemma Planet_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Planet))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(OclAny)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actualKind\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Planet_OclAllInstances_at_post_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Planet))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_post_def
by(rule Planet_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y) 
lemma Planet_OclAllInstances_at_pre_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Planet))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_pre_def
by(rule Planet_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y) 
lemma Galaxy_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Galaxy))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(OclAny)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actualKind\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Galaxy_OclAllInstances_at_post_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Galaxy))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_post_def
by(rule Galaxy_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y) 
lemma Galaxy_OclAllInstances_at_pre_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Galaxy))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_pre_def
by(rule Galaxy_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y) 

(* 99 ************************************ 645 + 1 *)
section{* The Accessors *}

(* 100 ************************************ 646 + 1 *)
text{* 
  \label{sec:edm-accessors} *}

(* 101 ************************************ 647 + 1 *)
text{*  *}

(* 102 ************************************ 648 + 1 *)
subsection{* Definition *}

(* 103 ************************************ 649 + 1 *)
text{*  *}

(* 104 ************************************ 650 + 1 *)
ML{* val oidPerson_0_boss = 0 *}

(* 105 ************************************ 651 + 1 *)
definition "oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S> = 0"

(* 106 ************************************ 652 + 1 *)
text{*  *}

(* 107 ************************************ 653 + 4 *)
definition "eval_extract x f = (\<lambda>\<tau>. (case x \<tau> of \<lfloor>\<lfloor>obj\<rfloor>\<rfloor> \<Rightarrow> (f ((oid_of (obj))) (\<tau>))
    | _ \<Rightarrow> invalid \<tau>))"
definition "in_pre_state = fst"
definition "in_post_state = snd"
definition "reconst_basetype = id"

(* 108 ************************************ 657 + 1 *)
text{*  *}

(* 109 ************************************ 658 + 2 *)
ML{* val switch2_01 = (fn [x0 , x1] => (x0 , x1)) *}
ML{* val switch2_10 = (fn [x0 , x1] => (x1 , x0)) *}

(* 110 ************************************ 660 + 4 *)
definition "switch\<^sub>2_01 = (\<lambda> [x0 , x1] \<Rightarrow> (x0 , x1))"
definition "switch\<^sub>2_10 = (\<lambda> [x0 , x1] \<Rightarrow> (x1 , x0))"
definition "List_flatten = (\<lambda>l. (foldl ((\<lambda>acc. (\<lambda>l. (foldl ((\<lambda>acc. (\<lambda>l. (Cons (l) (acc))))) (acc) ((rev (l))))))) (Nil) ((rev (l)))))"
definition "deref_assocs pre_post to_from assoc_oid f oid = (\<lambda>\<tau>. (case (assocs ((pre_post (\<tau>))) (assoc_oid)) of \<lfloor>S\<rfloor> \<Rightarrow> (f ((deref_assocs_list (to_from) (oid) (S))) (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"

(* 111 ************************************ 664 + 4 *)
definition "deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"
definition "deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"
definition "deref_oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"
definition "deref_oid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"

(* 112 ************************************ 668 + 0 *)

(* 113 ************************************ 668 + 1 *)
text{* 
   pointer undefined in state or not referencing a type conform object representation  *}

(* 114 ************************************ 669 + 12 *)
definition "select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S> f = (\<lambda> (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (\<bottom>) (_)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (\<lfloor>\<B>\<O>\<S>\<S>\<rfloor>) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (\<B>\<O>\<S>\<S>)))"
definition "select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y> f = (\<lambda> (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (\<bottom>)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (\<lfloor>\<S>\<A>\<L>\<A>\<R>\<Y>\<rfloor>)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (\<S>\<A>\<L>\<A>\<R>\<Y>)))"
definition "select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E> f = (\<lambda> (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (\<bottom>) (_)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (\<lfloor>\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>\<rfloor>) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>)))"
definition "select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T> f = (\<lambda> (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (_) (\<bottom>)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (_) (\<lfloor>\<W>\<E>\<I>\<G>\<H>\<T>\<rfloor>)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (\<W>\<E>\<I>\<G>\<H>\<T>)))"
definition "select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D> f = (\<lambda> (mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_) (\<bottom>) (_)) \<Rightarrow> null
    | (mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_) (\<lfloor>\<S>\<O>\<U>\<N>\<D>\<rfloor>) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (\<S>\<O>\<U>\<N>\<D>)))"
definition "select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G> f = (\<lambda> (mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_) (_) (\<bottom>)) \<Rightarrow> null
    | (mkoid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (_) (_) (\<lfloor>\<M>\<O>\<V>\<I>\<N>\<G>\<rfloor>)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (\<M>\<O>\<V>\<I>\<N>\<G>)))"
definition "select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E> f = (\<lambda> (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (\<bottom>) (_) (_) (_))) (_) (_)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (\<lfloor>\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>\<rfloor>) (_) (_) (_))) (_) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>)))"
definition "select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T> f = (\<lambda> (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (\<bottom>) (_) (_))) (_) (_)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (\<lfloor>\<W>\<E>\<I>\<G>\<H>\<T>\<rfloor>) (_) (_))) (_) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (\<W>\<E>\<I>\<G>\<H>\<T>)))"
definition "select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D> f = (\<lambda> (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (_) (\<bottom>) (_))) (_) (_)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (_) (\<lfloor>\<S>\<O>\<U>\<N>\<D>\<rfloor>) (_))) (_) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (\<S>\<O>\<U>\<N>\<D>)))"
definition "select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G> f = (\<lambda> (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (_) (_) (\<bottom>))) (_) (_)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (_) (_) (_) (_) (\<lfloor>\<M>\<O>\<V>\<I>\<N>\<G>\<rfloor>))) (_) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (\<M>\<O>\<V>\<I>\<N>\<G>)))"
definition "select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D> f = (\<lambda> (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (\<bottom>) (_))) (_) (_)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (\<lfloor>\<S>\<O>\<U>\<N>\<D>\<rfloor>) (_))) (_) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (\<S>\<O>\<U>\<N>\<D>))
    | (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (person))) (_) (_)) \<Rightarrow> (select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D> (f) (person)))"
definition "select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G> f = (\<lambda> (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (_) (\<bottom>))) (_) (_)) \<Rightarrow> null
    | (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (_) (_) (\<lfloor>\<M>\<O>\<V>\<I>\<N>\<G>\<rfloor>))) (_) (_)) \<Rightarrow> (f ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (\<M>\<O>\<V>\<I>\<N>\<G>))
    | (mkoid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t ((mk\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (person))) (_) (_)) \<Rightarrow> (select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G> (f) (person)))"

(* 115 ************************************ 681 + 0 *)

(* 116 ************************************ 681 + 12 *)
consts dot_0_\<B>\<O>\<S>\<S> :: "(\<AA>, '\<alpha>) val \<Rightarrow> Person" ("(_) .boss")
consts dot_0_\<B>\<O>\<S>\<S>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> Person" ("(_) .boss@pre")
consts dot\<S>\<A>\<L>\<A>\<R>\<Y> :: "(\<AA>, '\<alpha>) val \<Rightarrow> (\<AA>, int option option) val" ("(_) .salary")
consts dot\<S>\<A>\<L>\<A>\<R>\<Y>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> (\<AA>, int option option) val" ("(_) .salary@pre")
consts dot\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E> :: "(\<AA>, '\<alpha>) val \<Rightarrow> (\<AA>, nat option option) val" ("(_) .wormhole")
consts dot\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> (\<AA>, nat option option) val" ("(_) .wormhole@pre")
consts dot\<W>\<E>\<I>\<G>\<H>\<T> :: "(\<AA>, '\<alpha>) val \<Rightarrow> (\<AA>, int option option) val" ("(_) .weight")
consts dot\<W>\<E>\<I>\<G>\<H>\<T>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> (\<AA>, int option option) val" ("(_) .weight@pre")
consts dot\<S>\<O>\<U>\<N>\<D> :: "(\<AA>, '\<alpha>) val \<Rightarrow> (\<AA>, unit option option) val" ("(_) .sound")
consts dot\<S>\<O>\<U>\<N>\<D>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> (\<AA>, unit option option) val" ("(_) .sound@pre")
consts dot\<M>\<O>\<V>\<I>\<N>\<G> :: "(\<AA>, '\<alpha>) val \<Rightarrow> (\<AA>, bool option option) val" ("(_) .moving")
consts dot\<M>\<O>\<V>\<I>\<N>\<G>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> (\<AA>, bool option option) val" ("(_) .moving@pre")

(* 117 ************************************ 693 + 24 *)
defs(overloaded) dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S> : "(x::Person) .boss \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S> ((select_object_any\<^sub>S\<^sub>e\<^sub>t ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state))))))))))"
defs(overloaded) dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y> : "(x::Person) .salary \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>at_pre : "(x::Person) .boss@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S> ((select_object_any\<^sub>S\<^sub>e\<^sub>t ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state))))))))))"
defs(overloaded) dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>at_pre : "(x::Person) .salary@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E> : "(x::Planet) .wormhole \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_post_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T> : "(x::Planet) .weight \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_post_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>at_pre : "(x::Planet) .wormhole@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_pre_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>at_pre : "(x::Planet) .weight@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_pre_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D> : "(x::Galaxy) .sound \<equiv> (eval_extract (x) ((deref_oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (in_post_state) ((select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G> : "(x::Galaxy) .moving \<equiv> (eval_extract (x) ((deref_oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (in_post_state) ((select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>at_pre : "(x::Galaxy) .sound@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (in_pre_state) ((select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>at_pre : "(x::Galaxy) .moving@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y (in_pre_state) ((select\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E> : "(x::Person) .wormhole \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T> : "(x::Person) .weight \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D> : "(x::Person) .sound \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G> : "(x::Person) .moving \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>at_pre : "(x::Person) .wormhole@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>at_pre : "(x::Person) .weight@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>at_pre : "(x::Person) .sound@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>at_pre : "(x::Person) .moving@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) ((select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D> : "(x::Planet) .sound \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_post_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G> : "(x::Planet) .moving \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_post_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>at_pre : "(x::Planet) .sound@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_pre_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>at_pre : "(x::Planet) .moving@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t (in_pre_state) ((select\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G> (reconst_basetype))))))"

(* 118 ************************************ 717 + 1 *)
lemmas dot_accessor = dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>
                            dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>
                            dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>at_pre
                            dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>at_pre
                            dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>
                            dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>
                            dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>at_pre
                            dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>at_pre
                            dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>
                            dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>
                            dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>at_pre
                            dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>at_pre
                            dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>
                            dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>
                            dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>
                            dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>
                            dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>at_pre
                            dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>at_pre
                            dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>at_pre
                            dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>at_pre
                            dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>
                            dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>
                            dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>at_pre
                            dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>at_pre

(* 119 ************************************ 718 + 1 *)
subsection{* Context Passing *}

(* 120 ************************************ 719 + 1 *)
lemmas[simp,code_unfold] = eval_extract_def

(* 121 ************************************ 720 + 24 *)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S> : "(cp ((\<lambda>X. (X::Person) .boss)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y> : "(cp ((\<lambda>X. (X::Person) .salary)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>at_pre : "(cp ((\<lambda>X. (X::Person) .boss@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>at_pre : "(cp ((\<lambda>X. (X::Person) .salary@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E> : "(cp ((\<lambda>X. (X::Planet) .wormhole)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T> : "(cp ((\<lambda>X. (X::Planet) .weight)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>at_pre : "(cp ((\<lambda>X. (X::Planet) .wormhole@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>at_pre : "(cp ((\<lambda>X. (X::Planet) .weight@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D> : "(cp ((\<lambda>X. (X::Galaxy) .sound)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G> : "(cp ((\<lambda>X. (X::Galaxy) .moving)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>at_pre : "(cp ((\<lambda>X. (X::Galaxy) .sound@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>at_pre : "(cp ((\<lambda>X. (X::Galaxy) .moving@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E> : "(cp ((\<lambda>X. (X::Person) .wormhole)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T> : "(cp ((\<lambda>X. (X::Person) .weight)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D> : "(cp ((\<lambda>X. (X::Person) .sound)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G> : "(cp ((\<lambda>X. (X::Person) .moving)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>at_pre : "(cp ((\<lambda>X. (X::Person) .wormhole@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>at_pre : "(cp ((\<lambda>X. (X::Person) .weight@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>at_pre : "(cp ((\<lambda>X. (X::Person) .sound@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>at_pre : "(cp ((\<lambda>X. (X::Person) .moving@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D> : "(cp ((\<lambda>X. (X::Planet) .sound)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G> : "(cp ((\<lambda>X. (X::Planet) .moving)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>at_pre : "(cp ((\<lambda>X. (X::Planet) .sound@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>at_pre : "(cp ((\<lambda>X. (X::Planet) .moving@pre)))"
by(auto simp: dot_accessor cp_def)

(* 122 ************************************ 744 + 1 *)
lemmas[simp,code_unfold] = cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>
                            cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>
                            cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>at_pre
                            cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>at_pre
                            cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>
                            cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>
                            cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>at_pre
                            cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>at_pre
                            cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>
                            cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>
                            cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>at_pre
                            cp_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>at_pre
                            cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>
                            cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>
                            cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>
                            cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>
                            cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>at_pre
                            cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>at_pre
                            cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>at_pre
                            cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>at_pre
                            cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>
                            cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>
                            cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>at_pre
                            cp_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>at_pre

(* 123 ************************************ 745 + 1 *)
subsection{* Execution with Invalid or Null as Argument *}

(* 124 ************************************ 746 + 48 *)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>_invalid : "(invalid::Person) .boss = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>_null : "(null::Person) .boss = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_invalid : "(invalid::Person) .salary = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_null : "(null::Person) .salary = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>at_pre_invalid : "(invalid::Person) .boss@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>at_pre_null : "(null::Person) .boss@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>at_pre_invalid : "(invalid::Person) .salary@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>at_pre_null : "(null::Person) .salary@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>_invalid : "(invalid::Planet) .wormhole = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>_null : "(null::Planet) .wormhole = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>_invalid : "(invalid::Planet) .weight = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>_null : "(null::Planet) .weight = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>at_pre_invalid : "(invalid::Planet) .wormhole@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>at_pre_null : "(null::Planet) .wormhole@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>at_pre_invalid : "(invalid::Planet) .weight@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>at_pre_null : "(null::Planet) .weight@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>_invalid : "(invalid::Galaxy) .sound = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>_null : "(null::Galaxy) .sound = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>_invalid : "(invalid::Galaxy) .moving = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>_null : "(null::Galaxy) .moving = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>at_pre_invalid : "(invalid::Galaxy) .sound@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>at_pre_null : "(null::Galaxy) .sound@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>at_pre_invalid : "(invalid::Galaxy) .moving@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>at_pre_null : "(null::Galaxy) .moving@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>_invalid : "(invalid::Person) .wormhole = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>_null : "(null::Person) .wormhole = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>_invalid : "(invalid::Person) .weight = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>_null : "(null::Person) .weight = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>_invalid : "(invalid::Person) .sound = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>_null : "(null::Person) .sound = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>_invalid : "(invalid::Person) .moving = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>_null : "(null::Person) .moving = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>at_pre_invalid : "(invalid::Person) .wormhole@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>at_pre_null : "(null::Person) .wormhole@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>at_pre_invalid : "(invalid::Person) .weight@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>at_pre_null : "(null::Person) .weight@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>at_pre_invalid : "(invalid::Person) .sound@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>at_pre_null : "(null::Person) .sound@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>at_pre_invalid : "(invalid::Person) .moving@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>at_pre_null : "(null::Person) .moving@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>_invalid : "(invalid::Planet) .sound = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>_null : "(null::Planet) .sound = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>_invalid : "(invalid::Planet) .moving = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>_null : "(null::Planet) .moving = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>at_pre_invalid : "(invalid::Planet) .sound@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>at_pre_null : "(null::Planet) .sound@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>at_pre_invalid : "(invalid::Planet) .moving@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>at_pre_null : "(null::Planet) .moving@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)

(* 125 ************************************ 794 + 1 *)
subsection{* Representation in States *}

(* 126 ************************************ 795 + 24 *)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S> : "\<tau> \<Turnstile> (\<delta> ((X::Person) .boss)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .boss)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .boss)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y> : "\<tau> \<Turnstile> (\<delta> ((X::Person) .salary)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .salary)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .salary)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Person) .boss@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .boss@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .boss@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Person) .salary@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .salary@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .salary@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E> : "\<tau> \<Turnstile> (\<delta> ((X::Planet) .wormhole)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .wormhole)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .wormhole)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T> : "\<tau> \<Turnstile> (\<delta> ((X::Planet) .weight)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .weight)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .weight)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Planet) .wormhole@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .wormhole@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .wormhole@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Planet) .weight@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .weight@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .weight@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<W>\<E>\<I>\<G>\<H>\<T>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D> : "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .sound)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .sound)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .sound)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G> : "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .moving)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .moving)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .moving)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .sound@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .sound@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .sound@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<S>\<O>\<U>\<N>\<D>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Galaxy) .moving@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .moving@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .moving@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<M>\<O>\<V>\<I>\<N>\<G>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E> : "\<tau> \<Turnstile> (\<delta> ((X::Person) .wormhole)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .wormhole)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .wormhole)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T> : "\<tau> \<Turnstile> (\<delta> ((X::Person) .weight)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .weight)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .weight)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D> : "\<tau> \<Turnstile> (\<delta> ((X::Person) .sound)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .sound)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .sound)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G> : "\<tau> \<Turnstile> (\<delta> ((X::Person) .moving)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .moving)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .moving)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Person) .wormhole@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .wormhole@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .wormhole@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Person) .weight@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .weight@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .weight@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<W>\<E>\<I>\<G>\<H>\<T>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Person) .sound@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .sound@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .sound@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<O>\<U>\<N>\<D>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Person) .moving@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .moving@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .moving@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<M>\<O>\<V>\<I>\<N>\<G>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D> : "\<tau> \<Turnstile> (\<delta> ((X::Planet) .sound)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .sound)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .sound)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G> : "\<tau> \<Turnstile> (\<delta> ((X::Planet) .moving)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .moving)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .moving)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Planet) .sound@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .sound@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .sound@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<S>\<O>\<U>\<N>\<D>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Planet) .moving@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .moving@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .moving@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t\<M>\<O>\<V>\<I>\<N>\<G>at_pre_null)
by(simp add: defined_split)

(* 127 ************************************ 819 + 2 *)
lemma is_repr_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S> : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::Person) .boss))"
shows "(is_represented_in_state (in_post_state) (X .boss) (Person) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_post_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S> is_represented_in_state_def select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_def deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def in_post_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_post_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S> is_represented_in_state_def deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  proof - fix r typeoid          let ?t = "(Some ((Some (r)))) \<in> (Some o OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>) ` (ran ((heap ((in_post_state (\<tau>))))))"
          let ?sel_any = "(select_object_any\<^sub>S\<^sub>e\<^sub>t ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state))))"
          let ?sel = "((?sel_any) ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)))" show "(select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S> (?sel_any) (typeoid) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  apply(case_tac "typeoid", simp add: select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_def)
  proof - fix opt show "(((case opt of None \<Rightarrow> null
    | (Some (x)) \<Rightarrow> ((?sel) (x)))) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  apply(case_tac "opt", auto simp: null_fun_def null_option_def bot_option_def)
  proof - fix aa show "\<tau> \<Turnstile> (\<delta> (((?sel) (aa)))) \<Longrightarrow> ((?sel) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  apply(drule select_object_any_exec\<^sub>S\<^sub>e\<^sub>t[simplified foundation22], erule exE)
  proof - fix e show "((?sel) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ((?sel) (aa) (\<tau>)) = (deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_post_state) ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (e) (\<tau>)) \<Longrightarrow> ?t"
  apply(simp add: deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)
  apply(case_tac "(heap ((in_post_state (\<tau>))) (e))", simp add: invalid_def bot_option_def, simp)
  proof - fix aaa show "(case aaa of (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (obj)) \<Rightarrow> (Some ((Some (obj))))
    | _ \<Rightarrow> (invalid (\<tau>))) = (Some ((Some (r)))) \<Longrightarrow> (heap ((in_post_state (\<tau>))) (e)) = (Some (aaa)) \<Longrightarrow> ?t"
  apply(case_tac "aaa", auto simp: invalid_def bot_option_def image_def ran_def)
  apply(rule exI[where x = "(in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (r))"], simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def Let_def split: split_if_asm)
by(rule) qed 
  apply_end((blast)+)
 qed 
  apply_end(simp_all only: )
  apply_end(simp add: foundation16 bot_option_def null_option_def)
 qed qed qed qed qed 
  apply_end(simp_all)
 qed
lemma is_repr_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>at_pre : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::Person) .boss@pre))"
shows "(is_represented_in_state (in_pre_state) (X .boss@pre) (Person) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>at_pre[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_pre_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>at_pre is_represented_in_state_def select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_def deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def in_pre_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_pre_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>at_pre is_represented_in_state_def deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  proof - fix r typeoid          let ?t = "(Some ((Some (r)))) \<in> (Some o OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>) ` (ran ((heap ((in_pre_state (\<tau>))))))"
          let ?sel_any = "(select_object_any\<^sub>S\<^sub>e\<^sub>t ((deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state))))"
          let ?sel = "((?sel_any) ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)))" show "(select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S> (?sel_any) (typeoid) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  apply(case_tac "typeoid", simp add: select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_def)
  proof - fix opt show "(((case opt of None \<Rightarrow> null
    | (Some (x)) \<Rightarrow> ((?sel) (x)))) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  apply(case_tac "opt", auto simp: null_fun_def null_option_def bot_option_def)
  proof - fix aa show "\<tau> \<Turnstile> (\<delta> (((?sel) (aa)))) \<Longrightarrow> ((?sel) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  apply(drule select_object_any_exec\<^sub>S\<^sub>e\<^sub>t[simplified foundation22], erule exE)
  proof - fix e show "((?sel) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ((?sel) (aa) (\<tau>)) = (deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (in_pre_state) ((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (e) (\<tau>)) \<Longrightarrow> ?t"
  apply(simp add: deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)
  apply(case_tac "(heap ((in_pre_state (\<tau>))) (e))", simp add: invalid_def bot_option_def, simp)
  proof - fix aaa show "(case aaa of (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (obj)) \<Rightarrow> (Some ((Some (obj))))
    | _ \<Rightarrow> (invalid (\<tau>))) = (Some ((Some (r)))) \<Longrightarrow> (heap ((in_pre_state (\<tau>))) (e)) = (Some (aaa)) \<Longrightarrow> ?t"
  apply(case_tac "aaa", auto simp: invalid_def bot_option_def image_def ran_def)
  apply(rule exI[where x = "(in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (r))"], simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def Let_def split: split_if_asm)
by(rule) qed 
  apply_end((blast)+)
 qed 
  apply_end(simp_all only: )
  apply_end(simp add: foundation16 bot_option_def null_option_def)
 qed qed qed qed qed 
  apply_end(simp_all)
 qed

(* 128 ************************************ 821 + 1 *)
section{* A Little Infra-structure on Example States *}

(* 129 ************************************ 822 + 1 *)
text{* 

The example we are defining in this section comes from the figure~\ref{fig:edm1_system-states}.
\begin{figure}
\includegraphics[width=\textwidth]{figures/pre-post.pdf}
\caption{(a) pre-state $\sigma_1$ and
  (b) post-state $\sigma_1'$.}
\label{fig:edm1_system-states}
\end{figure}
 *}

(* 130 ************************************ 823 + 1 *)
text{*  *}

(* 131 ************************************ 824 + 1 *)
lemmas [simp,code_unfold] = state.defs
                            const_ss

(* 132 ************************************ 825 + 1 *)
lemmas[simp,code_unfold] = OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Planet
                            OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Galaxy
                            OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny
                            OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Galaxy
                            OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_OclAny
                            OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_Person
                            OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_OclAny
                            OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Person
                            OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_Planet
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Planet
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Galaxy

(* 133 ************************************ 826 + 10 *)
definition "oid1 = 1"
definition "oid2 = 2"
definition "oid3 = 3"
definition "oid4 = 4"
definition "oid5 = 5"
definition "oid6 = 6"
definition "oid7 = 7"
definition "oid8 = 8"
definition "oid9 = 9"
definition "inst_assoc1 = (\<lambda>oid_class to_from oid. ((case (deref_assocs_list ((to_from::oid list list \<Rightarrow> oid list \<times> oid list)) ((oid::oid)) ((drop ((((map_of_list ([(oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S> , (List.map ((\<lambda>(x , y). [x , y]) o switch\<^sub>2_01) ([[[oid7] , [oid7]] , [[oid6] , [oid7]] , [[oid2] , [oid2]] , [[oid1] , [oid2]]])))]))) ((oid_class::oid))))))) of Nil \<Rightarrow> None
    | l \<Rightarrow> (Some (l)))::oid list option))"

(* 134 ************************************ 836 + 18 *)
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n inst_assoc = (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid1) (None) (None) (None) (None))) (((inst_assoc) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid1))) (\<lfloor>1300\<rfloor>))"
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n inst_assoc = (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid2) (None) (None) (None) (None))) (((inst_assoc) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid2))) (\<lfloor>1800\<rfloor>))"
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n inst_assoc = (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid3) (None) (None) (None) (None))) (((inst_assoc) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid3))) (None))"
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n inst_assoc = (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid4) (None) (None) (None) (None))) (((inst_assoc) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid4))) (\<lfloor>2900\<rfloor>))"
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n inst_assoc = (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid5) (None) (None) (None) (None))) (((inst_assoc) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid5))) (\<lfloor>3500\<rfloor>))"
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n inst_assoc = (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid6) (None) (None) (None) (None))) (((inst_assoc) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid6))) (\<lfloor>2500\<rfloor>))"
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y inst_assoc = (mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid7) (None) (None) (None) (None))) (((inst_assoc) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid7))) (\<lfloor>3200\<rfloor>))))))"
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y inst_assoc = (mkoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (oid8))))"
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n inst_assoc = (mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid9) (None) (None) (None) (None))) (((inst_assoc) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid9))) (\<lfloor>0\<rfloor>))"
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1::Person) = (\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc1))\<rfloor>\<rfloor>)"
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2::Person) = (\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc1))\<rfloor>\<rfloor>)"
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3::Person) = (\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc1))\<rfloor>\<rfloor>)"
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4::Person) = (\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc1))\<rfloor>\<rfloor>)"
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5::Person) = (\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc1))\<rfloor>\<rfloor>)"
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6::Person) = (\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc1))\<rfloor>\<rfloor>)"
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7::OclAny) = (\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (inst_assoc1))\<rfloor>\<rfloor>)"
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8::OclAny) = (\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (inst_assoc1))\<rfloor>\<rfloor>)"
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9::Person) = (\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc1))\<rfloor>\<rfloor>)"

(* 135 ************************************ 854 + 1 *)
ML{* (Ty'.check ([(OCL.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .boss = Set{ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 }") , (OCL.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 /* unnamed attribute */ = Set{}") , (OCL.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 .boss = Set{ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 }") , (OCL.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 /* unnamed attribute */ = Set{ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 }") , (OCL.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 .boss = Set{}") , (OCL.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 /* unnamed attribute */ = Set{}") , (OCL.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4 .boss = Set{}") , (OCL.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4 /* unnamed attribute */ = Set{}") , (OCL.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5 .boss = Set{}") , (OCL.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5 /* unnamed attribute */ = Set{}") , (OCL.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 .boss = Set{ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 }") , (OCL.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 /* unnamed attribute */ = Set{}") , (OCL.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 .boss = Set{ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 }") , (OCL.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 /* unnamed attribute */ = Set{ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 }") , (OCL.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 .boss = Set{}") , (OCL.Writeln , "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 /* unnamed attribute */ = Set{}")]) (" error(s) in multiplicity constraints")) *}

(* 136 ************************************ 855 + 1 *)
definition "inst_assoc\<sigma>\<^sub>1 = (\<lambda>oid_class to_from oid. ((case (deref_assocs_list ((to_from::oid list list \<Rightarrow> oid list \<times> oid list)) ((oid::oid)) ((drop ((((map_of_list ([(oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S> , (List.map ((\<lambda>(x , y). [x , y]) o switch\<^sub>2_01) ([[[oid6] , [oid4]] , [[oid4] , [oid5]] , [[oid1] , [oid2]]])))]))) ((oid_class::oid))))))) of Nil \<Rightarrow> None
    | l \<Rightarrow> (Some (l)))::oid list option))"

(* 137 ************************************ 856 + 1 *)
definition "\<sigma>\<^sub>1 = (state.make ((Map.empty (oid1 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid1) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid1))) (\<lfloor>1000\<rfloor>))))) (oid2 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid2) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid2))) (\<lfloor>1200\<rfloor>))))) (oid4 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid4) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid4))) (\<lfloor>2600\<rfloor>))))) (oid5 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc\<sigma>\<^sub>1))))) (oid6 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid6) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid6))) (\<lfloor>2300\<rfloor>))))) (oid9 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc\<sigma>\<^sub>1))))))) (Map.empty))"

(* 138 ************************************ 857 + 2 *)
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<sigma>\<^sub>1::Person) = (\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc\<sigma>\<^sub>1))\<rfloor>\<rfloor>)"
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1::Person) = (\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc\<sigma>\<^sub>1))\<rfloor>\<rfloor>)"

(* 139 ************************************ 859 + 1 *)
lemma dom_\<sigma>\<^sub>1 : "(dom ((heap (\<sigma>\<^sub>1)))) = {oid1 , oid2 , oid4 , oid5 , oid6 , oid9}"
by(auto simp: \<sigma>\<^sub>1_def)

(* 140 ************************************ 860 + 1 *)
lemmas[simp,code_unfold] = dom_\<sigma>\<^sub>1

(* 141 ************************************ 861 + 1 *)
lemma perm_\<sigma>\<^sub>1 : "\<sigma>\<^sub>1 = (state.make ((Map.empty (oid9 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc\<sigma>\<^sub>1))))) (oid6 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid6) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid6))) (\<lfloor>2300\<rfloor>))))) (oid5 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc\<sigma>\<^sub>1))))) (oid4 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid4) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid4))) (\<lfloor>2600\<rfloor>))))) (oid2 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid2) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid2))) (\<lfloor>1200\<rfloor>))))) (oid1 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid1) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid1))) (\<lfloor>1000\<rfloor>))))))) ((assocs (\<sigma>\<^sub>1))))"
  apply(simp add: \<sigma>\<^sub>1_def oid1_def oid2_def oid4_def oid5_def oid6_def oid9_def)
  apply(subst (1) fun_upd_twist, simp)
  apply(subst (2) fun_upd_twist, simp)
  apply(subst (1) fun_upd_twist, simp)
  apply(subst (3) fun_upd_twist, simp)
  apply(subst (2) fun_upd_twist, simp)
  apply(subst (1) fun_upd_twist, simp)
  apply(subst (4) fun_upd_twist, simp)
  apply(subst (3) fun_upd_twist, simp)
  apply(subst (2) fun_upd_twist, simp)
  apply(subst (1) fun_upd_twist, simp)
  apply(subst (5) fun_upd_twist, simp)
  apply(subst (4) fun_upd_twist, simp)
  apply(subst (3) fun_upd_twist, simp)
  apply(subst (2) fun_upd_twist, simp)
  apply(subst (1) fun_upd_twist, simp)
by(simp)

(* 142 ************************************ 862 + 12 *)
lemma \<sigma>\<^sub>1_OclAllInstances_generic_exec_Person : 
assumes [simp]: "(\<And>a. (pre_post ((mk (a)))) = a)"
shows "(mk (\<sigma>\<^sub>1)) \<Turnstile> (OclAllInstances_generic (pre_post) (Person)) \<doteq> Set{(\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid1) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid1))) (\<lfloor>1000\<rfloor>))\<rfloor>\<rfloor>) , (\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid2) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid2))) (\<lfloor>1200\<rfloor>))\<rfloor>\<rfloor>) , (\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid4) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid4))) (\<lfloor>2600\<rfloor>))\<rfloor>\<rfloor>) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<sigma>\<^sub>1 , (\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid6) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid6))) (\<lfloor>2300\<rfloor>))\<rfloor>\<rfloor>) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1}"
  apply(subst perm_\<sigma>\<^sub>1)
  apply(simp only: state.make_def oid1_def oid2_def oid4_def oid5_def oid6_def oid9_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<sigma>\<^sub>1_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1_def)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(rule state_update_vs_allInstances_generic_empty)
by(simp_all add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def) 
lemma \<sigma>\<^sub>1_OclAllInstances_at_post_exec_Person : 
shows "(st , \<sigma>\<^sub>1) \<Turnstile> (OclAllInstances_at_post (Person)) \<doteq> Set{(\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid1) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid1))) (\<lfloor>1000\<rfloor>))\<rfloor>\<rfloor>) , (\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid2) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid2))) (\<lfloor>1200\<rfloor>))\<rfloor>\<rfloor>) , (\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid4) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid4))) (\<lfloor>2600\<rfloor>))\<rfloor>\<rfloor>) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<sigma>\<^sub>1 , (\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid6) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid6))) (\<lfloor>2300\<rfloor>))\<rfloor>\<rfloor>) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1}"
  unfolding OclAllInstances_at_post_def
by(rule \<sigma>\<^sub>1_OclAllInstances_generic_exec_Person, simp) 
lemma \<sigma>\<^sub>1_OclAllInstances_at_pre_exec_Person : 
shows "(\<sigma>\<^sub>1 , st) \<Turnstile> (OclAllInstances_at_pre (Person)) \<doteq> Set{(\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid1) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid1))) (\<lfloor>1000\<rfloor>))\<rfloor>\<rfloor>) , (\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid2) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid2))) (\<lfloor>1200\<rfloor>))\<rfloor>\<rfloor>) , (\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid4) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid4))) (\<lfloor>2600\<rfloor>))\<rfloor>\<rfloor>) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<sigma>\<^sub>1 , (\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid6) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid6))) (\<lfloor>2300\<rfloor>))\<rfloor>\<rfloor>) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1}"
  unfolding OclAllInstances_at_pre_def
by(rule \<sigma>\<^sub>1_OclAllInstances_generic_exec_Person, simp) 
lemma \<sigma>\<^sub>1_OclAllInstances_generic_exec_Planet : 
assumes [simp]: "(\<And>a. (pre_post ((mk (a)))) = a)"
shows "(mk (\<sigma>\<^sub>1)) \<Turnstile> (OclAllInstances_generic (pre_post) (Planet)) \<doteq> Set{((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid1) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid1))) (\<lfloor>1000\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(Planet) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid2) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid2))) (\<lfloor>1200\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(Planet) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid4) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid4))) (\<lfloor>2600\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(Planet) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<sigma>\<^sub>1 .oclAsType(Planet) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid6) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid6))) (\<lfloor>2300\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(Planet) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1 .oclAsType(Planet)}"
  apply(subst perm_\<sigma>\<^sub>1)
  apply(simp only: state.make_def oid1_def oid2_def oid4_def oid5_def oid6_def oid9_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<sigma>\<^sub>1_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(rule state_update_vs_allInstances_generic_empty)
by(simp_all add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA>_def) 
lemma \<sigma>\<^sub>1_OclAllInstances_at_post_exec_Planet : 
shows "(st , \<sigma>\<^sub>1) \<Turnstile> (OclAllInstances_at_post (Planet)) \<doteq> Set{((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid1) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid1))) (\<lfloor>1000\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(Planet) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid2) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid2))) (\<lfloor>1200\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(Planet) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid4) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid4))) (\<lfloor>2600\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(Planet) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<sigma>\<^sub>1 .oclAsType(Planet) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid6) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid6))) (\<lfloor>2300\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(Planet) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1 .oclAsType(Planet)}"
  unfolding OclAllInstances_at_post_def
by(rule \<sigma>\<^sub>1_OclAllInstances_generic_exec_Planet, simp) 
lemma \<sigma>\<^sub>1_OclAllInstances_at_pre_exec_Planet : 
shows "(\<sigma>\<^sub>1 , st) \<Turnstile> (OclAllInstances_at_pre (Planet)) \<doteq> Set{((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid1) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid1))) (\<lfloor>1000\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(Planet) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid2) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid2))) (\<lfloor>1200\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(Planet) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid4) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid4))) (\<lfloor>2600\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(Planet) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<sigma>\<^sub>1 .oclAsType(Planet) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid6) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid6))) (\<lfloor>2300\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(Planet) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1 .oclAsType(Planet)}"
  unfolding OclAllInstances_at_pre_def
by(rule \<sigma>\<^sub>1_OclAllInstances_generic_exec_Planet, simp) 
lemma \<sigma>\<^sub>1_OclAllInstances_generic_exec_Galaxy : 
assumes [simp]: "(\<And>a. (pre_post ((mk (a)))) = a)"
shows "(mk (\<sigma>\<^sub>1)) \<Turnstile> (OclAllInstances_generic (pre_post) (Galaxy)) \<doteq> Set{((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid1) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid1))) (\<lfloor>1000\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(Galaxy) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid2) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid2))) (\<lfloor>1200\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(Galaxy) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid4) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid4))) (\<lfloor>2600\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(Galaxy) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<sigma>\<^sub>1 .oclAsType(Galaxy) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid6) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid6))) (\<lfloor>2300\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(Galaxy) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1 .oclAsType(Galaxy)}"
  apply(subst perm_\<sigma>\<^sub>1)
  apply(simp only: state.make_def oid1_def oid2_def oid4_def oid5_def oid6_def oid9_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<sigma>\<^sub>1_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(rule state_update_vs_allInstances_generic_empty)
by(simp_all add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA>_def) 
lemma \<sigma>\<^sub>1_OclAllInstances_at_post_exec_Galaxy : 
shows "(st , \<sigma>\<^sub>1) \<Turnstile> (OclAllInstances_at_post (Galaxy)) \<doteq> Set{((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid1) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid1))) (\<lfloor>1000\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(Galaxy) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid2) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid2))) (\<lfloor>1200\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(Galaxy) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid4) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid4))) (\<lfloor>2600\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(Galaxy) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<sigma>\<^sub>1 .oclAsType(Galaxy) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid6) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid6))) (\<lfloor>2300\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(Galaxy) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1 .oclAsType(Galaxy)}"
  unfolding OclAllInstances_at_post_def
by(rule \<sigma>\<^sub>1_OclAllInstances_generic_exec_Galaxy, simp) 
lemma \<sigma>\<^sub>1_OclAllInstances_at_pre_exec_Galaxy : 
shows "(\<sigma>\<^sub>1 , st) \<Turnstile> (OclAllInstances_at_pre (Galaxy)) \<doteq> Set{((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid1) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid1))) (\<lfloor>1000\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(Galaxy) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid2) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid2))) (\<lfloor>1200\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(Galaxy) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid4) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid4))) (\<lfloor>2600\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(Galaxy) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<sigma>\<^sub>1 .oclAsType(Galaxy) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid6) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid6))) (\<lfloor>2300\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(Galaxy) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1 .oclAsType(Galaxy)}"
  unfolding OclAllInstances_at_pre_def
by(rule \<sigma>\<^sub>1_OclAllInstances_generic_exec_Galaxy, simp) 
lemma \<sigma>\<^sub>1_OclAllInstances_generic_exec_OclAny : 
assumes [simp]: "(\<And>a. (pre_post ((mk (a)))) = a)"
shows "(mk (\<sigma>\<^sub>1)) \<Turnstile> (OclAllInstances_generic (pre_post) (OclAny)) \<doteq> Set{((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid1) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid1))) (\<lfloor>1000\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(OclAny) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid2) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid2))) (\<lfloor>1200\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(OclAny) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid4) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid4))) (\<lfloor>2600\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(OclAny) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<sigma>\<^sub>1 .oclAsType(OclAny) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid6) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid6))) (\<lfloor>2300\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(OclAny) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1 .oclAsType(OclAny)}"
  apply(subst perm_\<sigma>\<^sub>1)
  apply(simp only: state.make_def oid1_def oid2_def oid4_def oid5_def oid6_def oid9_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<sigma>\<^sub>1_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(rule state_update_vs_allInstances_generic_empty)
by(simp_all add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def) 
lemma \<sigma>\<^sub>1_OclAllInstances_at_post_exec_OclAny : 
shows "(st , \<sigma>\<^sub>1) \<Turnstile> (OclAllInstances_at_post (OclAny)) \<doteq> Set{((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid1) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid1))) (\<lfloor>1000\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(OclAny) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid2) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid2))) (\<lfloor>1200\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(OclAny) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid4) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid4))) (\<lfloor>2600\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(OclAny) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<sigma>\<^sub>1 .oclAsType(OclAny) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid6) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid6))) (\<lfloor>2300\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(OclAny) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1 .oclAsType(OclAny)}"
  unfolding OclAllInstances_at_post_def
by(rule \<sigma>\<^sub>1_OclAllInstances_generic_exec_OclAny, simp) 
lemma \<sigma>\<^sub>1_OclAllInstances_at_pre_exec_OclAny : 
shows "(\<sigma>\<^sub>1 , st) \<Turnstile> (OclAllInstances_at_pre (OclAny)) \<doteq> Set{((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid1) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid1))) (\<lfloor>1000\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(OclAny) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid2) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid2))) (\<lfloor>1200\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(OclAny) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid4) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid4))) (\<lfloor>2600\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(OclAny) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<sigma>\<^sub>1 .oclAsType(OclAny) , ((\<lambda>_. \<lfloor>\<lfloor>(mkoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (oid6) (None) (None) (None) (None))) (((inst_assoc\<sigma>\<^sub>1) (oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S>) (switch\<^sub>2_01) (oid6))) (\<lfloor>2300\<rfloor>))\<rfloor>\<rfloor>)::Person) .oclAsType(OclAny) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1 .oclAsType(OclAny)}"
  unfolding OclAllInstances_at_pre_def
by(rule \<sigma>\<^sub>1_OclAllInstances_generic_exec_OclAny, simp) 

(* 143 ************************************ 874 + 1 *)
definition "inst_assoc\<sigma>\<^sub>1' = (\<lambda>oid_class to_from oid. ((case (deref_assocs_list ((to_from::oid list list \<Rightarrow> oid list \<times> oid list)) ((oid::oid)) ((drop ((((map_of_list ([(oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0_\<B>\<O>\<S>\<S> , (List.map ((\<lambda>(x , y). [x , y]) o switch\<^sub>2_01) ([[[oid7] , [oid7]] , [[oid6] , [oid7]] , [[oid2] , [oid2]] , [[oid1] , [oid2]]])))]))) ((oid_class::oid))))))) of Nil \<Rightarrow> None
    | l \<Rightarrow> (Some (l)))::oid list option))"

(* 144 ************************************ 875 + 1 *)
definition "\<sigma>\<^sub>1' = (state.make ((Map.empty (oid1 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc\<sigma>\<^sub>1'))))) (oid2 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc\<sigma>\<^sub>1'))))) (oid3 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc\<sigma>\<^sub>1'))))) (oid4 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc\<sigma>\<^sub>1'))))) (oid6 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc\<sigma>\<^sub>1'))))) (oid7 \<mapsto> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (inst_assoc\<sigma>\<^sub>1'))))) (oid8 \<mapsto> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (inst_assoc\<sigma>\<^sub>1'))))) (oid9 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc\<sigma>\<^sub>1'))))))) (Map.empty))"

(* 145 ************************************ 876 + 8 *)
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<sigma>\<^sub>1'::Person) = (\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc\<sigma>\<^sub>1'))\<rfloor>\<rfloor>)"
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<sigma>\<^sub>1'::Person) = (\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc\<sigma>\<^sub>1'))\<rfloor>\<rfloor>)"
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<sigma>\<^sub>1'::Person) = (\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc\<sigma>\<^sub>1'))\<rfloor>\<rfloor>)"
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<sigma>\<^sub>1'::Person) = (\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc\<sigma>\<^sub>1'))\<rfloor>\<rfloor>)"
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<sigma>\<^sub>1'::Person) = (\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc\<sigma>\<^sub>1'))\<rfloor>\<rfloor>)"
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7\<sigma>\<^sub>1'::OclAny) = (\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (inst_assoc\<sigma>\<^sub>1'))\<rfloor>\<rfloor>)"
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8\<sigma>\<^sub>1'::OclAny) = (\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (inst_assoc\<sigma>\<^sub>1'))\<rfloor>\<rfloor>)"
definition "(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1'::Person) = (\<lambda>_. \<lfloor>\<lfloor>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc\<sigma>\<^sub>1'))\<rfloor>\<rfloor>)"

(* 146 ************************************ 884 + 1 *)
lemma dom_\<sigma>\<^sub>1' : "(dom ((heap (\<sigma>\<^sub>1')))) = {oid1 , oid2 , oid3 , oid4 , oid6 , oid7 , oid8 , oid9}"
by(auto simp: \<sigma>\<^sub>1'_def)

(* 147 ************************************ 885 + 1 *)
lemmas[simp,code_unfold] = dom_\<sigma>\<^sub>1'

(* 148 ************************************ 886 + 1 *)
lemma perm_\<sigma>\<^sub>1' : "\<sigma>\<^sub>1' = (state.make ((Map.empty (oid9 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc\<sigma>\<^sub>1'))))) (oid8 \<mapsto> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (inst_assoc\<sigma>\<^sub>1'))))) (oid7 \<mapsto> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (inst_assoc\<sigma>\<^sub>1'))))) (oid6 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc\<sigma>\<^sub>1'))))) (oid4 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc\<sigma>\<^sub>1'))))) (oid3 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc\<sigma>\<^sub>1'))))) (oid2 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc\<sigma>\<^sub>1'))))) (oid1 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (inst_assoc\<sigma>\<^sub>1'))))))) ((assocs (\<sigma>\<^sub>1'))))"
  apply(simp add: \<sigma>\<^sub>1'_def oid1_def oid2_def oid3_def oid4_def oid6_def oid7_def oid8_def oid9_def)
  apply(subst (1) fun_upd_twist, simp)
  apply(subst (2) fun_upd_twist, simp)
  apply(subst (1) fun_upd_twist, simp)
  apply(subst (3) fun_upd_twist, simp)
  apply(subst (2) fun_upd_twist, simp)
  apply(subst (1) fun_upd_twist, simp)
  apply(subst (4) fun_upd_twist, simp)
  apply(subst (3) fun_upd_twist, simp)
  apply(subst (2) fun_upd_twist, simp)
  apply(subst (1) fun_upd_twist, simp)
  apply(subst (5) fun_upd_twist, simp)
  apply(subst (4) fun_upd_twist, simp)
  apply(subst (3) fun_upd_twist, simp)
  apply(subst (2) fun_upd_twist, simp)
  apply(subst (1) fun_upd_twist, simp)
  apply(subst (6) fun_upd_twist, simp)
  apply(subst (5) fun_upd_twist, simp)
  apply(subst (4) fun_upd_twist, simp)
  apply(subst (3) fun_upd_twist, simp)
  apply(subst (2) fun_upd_twist, simp)
  apply(subst (1) fun_upd_twist, simp)
  apply(subst (7) fun_upd_twist, simp)
  apply(subst (6) fun_upd_twist, simp)
  apply(subst (5) fun_upd_twist, simp)
  apply(subst (4) fun_upd_twist, simp)
  apply(subst (3) fun_upd_twist, simp)
  apply(subst (2) fun_upd_twist, simp)
  apply(subst (1) fun_upd_twist, simp)
by(simp)

(* 149 ************************************ 887 + 12 *)
lemma \<sigma>\<^sub>1'_OclAllInstances_generic_exec_Person : 
assumes [simp]: "(\<And>a. (pre_post ((mk (a)))) = a)"
shows "(mk (\<sigma>\<^sub>1')) \<Turnstile> (OclAllInstances_generic (pre_post) (Person)) \<doteq> Set{X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<sigma>\<^sub>1' , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<sigma>\<^sub>1' , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<sigma>\<^sub>1' , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<sigma>\<^sub>1' , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<sigma>\<^sub>1' , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7\<sigma>\<^sub>1' .oclAsType(Person) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1'}"
  apply(subst perm_\<sigma>\<^sub>1')
  apply(simp only: state.make_def oid1_def oid2_def oid3_def oid4_def oid6_def oid7_def oid8_def oid9_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_ntc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(rule state_update_vs_allInstances_generic_empty)
by(simp_all add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def) 
lemma \<sigma>\<^sub>1'_OclAllInstances_at_post_exec_Person : 
shows "(st , \<sigma>\<^sub>1') \<Turnstile> (OclAllInstances_at_post (Person)) \<doteq> Set{X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<sigma>\<^sub>1' , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<sigma>\<^sub>1' , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<sigma>\<^sub>1' , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<sigma>\<^sub>1' , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<sigma>\<^sub>1' , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7\<sigma>\<^sub>1' .oclAsType(Person) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1'}"
  unfolding OclAllInstances_at_post_def
by(rule \<sigma>\<^sub>1'_OclAllInstances_generic_exec_Person, simp) 
lemma \<sigma>\<^sub>1'_OclAllInstances_at_pre_exec_Person : 
shows "(\<sigma>\<^sub>1' , st) \<Turnstile> (OclAllInstances_at_pre (Person)) \<doteq> Set{X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<sigma>\<^sub>1' , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<sigma>\<^sub>1' , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<sigma>\<^sub>1' , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<sigma>\<^sub>1' , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<sigma>\<^sub>1' , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7\<sigma>\<^sub>1' .oclAsType(Person) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1'}"
  unfolding OclAllInstances_at_pre_def
by(rule \<sigma>\<^sub>1'_OclAllInstances_generic_exec_Person, simp) 
lemma \<sigma>\<^sub>1'_OclAllInstances_generic_exec_Planet : 
assumes [simp]: "(\<And>a. (pre_post ((mk (a)))) = a)"
shows "(mk (\<sigma>\<^sub>1')) \<Turnstile> (OclAllInstances_generic (pre_post) (Planet)) \<doteq> Set{X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<sigma>\<^sub>1' .oclAsType(Planet) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<sigma>\<^sub>1' .oclAsType(Planet) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<sigma>\<^sub>1' .oclAsType(Planet) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<sigma>\<^sub>1' .oclAsType(Planet) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<sigma>\<^sub>1' .oclAsType(Planet) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1' .oclAsType(Planet)}"
  apply(subst perm_\<sigma>\<^sub>1')
  apply(simp only: state.make_def oid1_def oid2_def oid3_def oid4_def oid6_def oid7_def oid8_def oid9_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_ntc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA>_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp)
  apply(subst state_update_vs_allInstances_generic_ntc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA>_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(rule state_update_vs_allInstances_generic_empty)
by(simp_all add: OclAsType\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>e\<^sub>t_\<AA>_def) 
lemma \<sigma>\<^sub>1'_OclAllInstances_at_post_exec_Planet : 
shows "(st , \<sigma>\<^sub>1') \<Turnstile> (OclAllInstances_at_post (Planet)) \<doteq> Set{X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<sigma>\<^sub>1' .oclAsType(Planet) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<sigma>\<^sub>1' .oclAsType(Planet) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<sigma>\<^sub>1' .oclAsType(Planet) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<sigma>\<^sub>1' .oclAsType(Planet) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<sigma>\<^sub>1' .oclAsType(Planet) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1' .oclAsType(Planet)}"
  unfolding OclAllInstances_at_post_def
by(rule \<sigma>\<^sub>1'_OclAllInstances_generic_exec_Planet, simp) 
lemma \<sigma>\<^sub>1'_OclAllInstances_at_pre_exec_Planet : 
shows "(\<sigma>\<^sub>1' , st) \<Turnstile> (OclAllInstances_at_pre (Planet)) \<doteq> Set{X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<sigma>\<^sub>1' .oclAsType(Planet) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<sigma>\<^sub>1' .oclAsType(Planet) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<sigma>\<^sub>1' .oclAsType(Planet) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<sigma>\<^sub>1' .oclAsType(Planet) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<sigma>\<^sub>1' .oclAsType(Planet) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1' .oclAsType(Planet)}"
  unfolding OclAllInstances_at_pre_def
by(rule \<sigma>\<^sub>1'_OclAllInstances_generic_exec_Planet, simp) 
lemma \<sigma>\<^sub>1'_OclAllInstances_generic_exec_Galaxy : 
assumes [simp]: "(\<And>a. (pre_post ((mk (a)))) = a)"
shows "(mk (\<sigma>\<^sub>1')) \<Turnstile> (OclAllInstances_generic (pre_post) (Galaxy)) \<doteq> Set{X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<sigma>\<^sub>1' .oclAsType(Galaxy) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<sigma>\<^sub>1' .oclAsType(Galaxy) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<sigma>\<^sub>1' .oclAsType(Galaxy) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<sigma>\<^sub>1' .oclAsType(Galaxy) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<sigma>\<^sub>1' .oclAsType(Galaxy) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1' .oclAsType(Galaxy)}"
  apply(subst perm_\<sigma>\<^sub>1')
  apply(simp only: state.make_def oid1_def oid2_def oid3_def oid4_def oid6_def oid7_def oid8_def oid9_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_ntc, simp, simp, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA>_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp)
  apply(subst state_update_vs_allInstances_generic_ntc, simp, simp, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA>_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(rule state_update_vs_allInstances_generic_empty)
by(simp_all add: OclAsType\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<AA>_def) 
lemma \<sigma>\<^sub>1'_OclAllInstances_at_post_exec_Galaxy : 
shows "(st , \<sigma>\<^sub>1') \<Turnstile> (OclAllInstances_at_post (Galaxy)) \<doteq> Set{X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<sigma>\<^sub>1' .oclAsType(Galaxy) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<sigma>\<^sub>1' .oclAsType(Galaxy) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<sigma>\<^sub>1' .oclAsType(Galaxy) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<sigma>\<^sub>1' .oclAsType(Galaxy) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<sigma>\<^sub>1' .oclAsType(Galaxy) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1' .oclAsType(Galaxy)}"
  unfolding OclAllInstances_at_post_def
by(rule \<sigma>\<^sub>1'_OclAllInstances_generic_exec_Galaxy, simp) 
lemma \<sigma>\<^sub>1'_OclAllInstances_at_pre_exec_Galaxy : 
shows "(\<sigma>\<^sub>1' , st) \<Turnstile> (OclAllInstances_at_pre (Galaxy)) \<doteq> Set{X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<sigma>\<^sub>1' .oclAsType(Galaxy) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<sigma>\<^sub>1' .oclAsType(Galaxy) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<sigma>\<^sub>1' .oclAsType(Galaxy) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<sigma>\<^sub>1' .oclAsType(Galaxy) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<sigma>\<^sub>1' .oclAsType(Galaxy) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1' .oclAsType(Galaxy)}"
  unfolding OclAllInstances_at_pre_def
by(rule \<sigma>\<^sub>1'_OclAllInstances_generic_exec_Galaxy, simp) 
lemma \<sigma>\<^sub>1'_OclAllInstances_generic_exec_OclAny : 
assumes [simp]: "(\<And>a. (pre_post ((mk (a)))) = a)"
shows "(mk (\<sigma>\<^sub>1')) \<Turnstile> (OclAllInstances_generic (pre_post) (OclAny)) \<doteq> Set{X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<sigma>\<^sub>1' .oclAsType(OclAny) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<sigma>\<^sub>1' .oclAsType(OclAny) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<sigma>\<^sub>1' .oclAsType(OclAny) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<sigma>\<^sub>1' .oclAsType(OclAny) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<sigma>\<^sub>1' .oclAsType(OclAny) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7\<sigma>\<^sub>1' , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8\<sigma>\<^sub>1' , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1' .oclAsType(OclAny)}"
  apply(subst perm_\<sigma>\<^sub>1')
  apply(simp only: state.make_def oid1_def oid2_def oid3_def oid4_def oid6_def oid7_def oid8_def oid9_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_generic_tc, simp, simp, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(rule state_update_vs_allInstances_generic_empty)
by(simp_all add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def) 
lemma \<sigma>\<^sub>1'_OclAllInstances_at_post_exec_OclAny : 
shows "(st , \<sigma>\<^sub>1') \<Turnstile> (OclAllInstances_at_post (OclAny)) \<doteq> Set{X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<sigma>\<^sub>1' .oclAsType(OclAny) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<sigma>\<^sub>1' .oclAsType(OclAny) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<sigma>\<^sub>1' .oclAsType(OclAny) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<sigma>\<^sub>1' .oclAsType(OclAny) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<sigma>\<^sub>1' .oclAsType(OclAny) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7\<sigma>\<^sub>1' , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8\<sigma>\<^sub>1' , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1' .oclAsType(OclAny)}"
  unfolding OclAllInstances_at_post_def
by(rule \<sigma>\<^sub>1'_OclAllInstances_generic_exec_OclAny, simp) 
lemma \<sigma>\<^sub>1'_OclAllInstances_at_pre_exec_OclAny : 
shows "(\<sigma>\<^sub>1' , st) \<Turnstile> (OclAllInstances_at_pre (OclAny)) \<doteq> Set{X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<sigma>\<^sub>1' .oclAsType(OclAny) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<sigma>\<^sub>1' .oclAsType(OclAny) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<sigma>\<^sub>1' .oclAsType(OclAny) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<sigma>\<^sub>1' .oclAsType(OclAny) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<sigma>\<^sub>1' .oclAsType(OclAny) , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7\<sigma>\<^sub>1' , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8\<sigma>\<^sub>1' , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1' .oclAsType(OclAny)}"
  unfolding OclAllInstances_at_pre_def
by(rule \<sigma>\<^sub>1'_OclAllInstances_generic_exec_OclAny, simp) 

(* 150 ************************************ 899 + 1 *)
lemma basic_\<sigma>\<^sub>1_\<sigma>\<^sub>1'_wff : "(WFF ((\<sigma>\<^sub>1 , \<sigma>\<^sub>1')))"
by(simp add: WFF_def \<sigma>\<^sub>1_def \<sigma>\<^sub>1'_def oid_of_\<AA>_def oid1_def oid2_def oid3_def oid4_def oid5_def oid6_def oid7_def oid8_def oid9_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def oid_of_typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def oid_of_typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)

(* 151 ************************************ 900 + 10 *)
lemma oid1\<sigma>\<^sub>1\<sigma>\<^sub>1'_\<sigma>\<^sub>1'_OclIsMaintained : "(\<sigma>\<^sub>1 , \<sigma>\<^sub>1') \<Turnstile> (OclIsMaintained (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<sigma>\<^sub>1'))"
by(simp add: X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def OclIsMaintained_def OclValid_def \<sigma>\<^sub>1_def \<sigma>\<^sub>1'_def oid_of_option_def oid1_def oid2_def oid3_def oid4_def oid5_def oid6_def oid7_def oid8_def oid9_def oid_of_typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def oid_of_typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)
lemma oid2\<sigma>\<^sub>1\<sigma>\<^sub>1'_\<sigma>\<^sub>1'_OclIsMaintained : "(\<sigma>\<^sub>1 , \<sigma>\<^sub>1') \<Turnstile> (OclIsMaintained (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<sigma>\<^sub>1'))"
by(simp add: X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def OclIsMaintained_def OclValid_def \<sigma>\<^sub>1_def \<sigma>\<^sub>1'_def oid_of_option_def oid1_def oid2_def oid3_def oid4_def oid5_def oid6_def oid7_def oid8_def oid9_def oid_of_typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def oid_of_typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)
lemma oid3\<sigma>\<^sub>1\<sigma>\<^sub>1'_\<sigma>\<^sub>1'_OclIsNew : "(\<sigma>\<^sub>1 , \<sigma>\<^sub>1') \<Turnstile> (OclIsNew (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<sigma>\<^sub>1'))"
by(simp add: X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def OclIsNew_def OclValid_def \<sigma>\<^sub>1_def \<sigma>\<^sub>1'_def oid_of_option_def oid1_def oid2_def oid3_def oid4_def oid5_def oid6_def oid7_def oid8_def oid9_def oid_of_typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def oid_of_typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)
lemma oid4\<sigma>\<^sub>1\<sigma>\<^sub>1'_\<sigma>\<^sub>1'_OclIsMaintained : "(\<sigma>\<^sub>1 , \<sigma>\<^sub>1') \<Turnstile> (OclIsMaintained (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<sigma>\<^sub>1'))"
by(simp add: X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def OclIsMaintained_def OclValid_def \<sigma>\<^sub>1_def \<sigma>\<^sub>1'_def oid_of_option_def oid1_def oid2_def oid3_def oid4_def oid5_def oid6_def oid7_def oid8_def oid9_def oid_of_typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def oid_of_typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)
lemma oid5\<sigma>\<^sub>1\<sigma>\<^sub>1'_\<sigma>\<^sub>1_OclIsDeleted : "(\<sigma>\<^sub>1 , \<sigma>\<^sub>1') \<Turnstile> (OclIsDeleted (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<sigma>\<^sub>1))"
by(simp add: X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<sigma>\<^sub>1_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def OclIsDeleted_def OclValid_def \<sigma>\<^sub>1_def \<sigma>\<^sub>1'_def oid_of_option_def oid1_def oid2_def oid3_def oid4_def oid5_def oid6_def oid7_def oid8_def oid9_def oid_of_typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def oid_of_typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)
lemma oid6\<sigma>\<^sub>1\<sigma>\<^sub>1'_\<sigma>\<^sub>1'_OclIsMaintained : "(\<sigma>\<^sub>1 , \<sigma>\<^sub>1') \<Turnstile> (OclIsMaintained (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<sigma>\<^sub>1'))"
by(simp add: X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def OclIsMaintained_def OclValid_def \<sigma>\<^sub>1_def \<sigma>\<^sub>1'_def oid_of_option_def oid1_def oid2_def oid3_def oid4_def oid5_def oid6_def oid7_def oid8_def oid9_def oid_of_typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def oid_of_typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)
lemma oid7\<sigma>\<^sub>1\<sigma>\<^sub>1'_\<sigma>\<^sub>1'_OclIsNew : "(\<sigma>\<^sub>1 , \<sigma>\<^sub>1') \<Turnstile> (OclIsNew (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7\<sigma>\<^sub>1'))"
by(simp add: X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def OclIsNew_def OclValid_def \<sigma>\<^sub>1_def \<sigma>\<^sub>1'_def oid_of_option_def oid1_def oid2_def oid3_def oid4_def oid5_def oid6_def oid7_def oid8_def oid9_def oid_of_typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def oid_of_typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)
lemma oid8\<sigma>\<^sub>1\<sigma>\<^sub>1'_\<sigma>\<^sub>1'_OclIsNew : "(\<sigma>\<^sub>1 , \<sigma>\<^sub>1') \<Turnstile> (OclIsNew (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8\<sigma>\<^sub>1'))"
by(simp add: X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def OclIsNew_def OclValid_def \<sigma>\<^sub>1_def \<sigma>\<^sub>1'_def oid_of_option_def oid1_def oid2_def oid3_def oid4_def oid5_def oid6_def oid7_def oid8_def oid9_def oid_of_typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def oid_of_typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)
lemma oid9\<sigma>\<^sub>1\<sigma>\<^sub>1'_\<sigma>\<^sub>1_OclIsMaintained : "(\<sigma>\<^sub>1 , \<sigma>\<^sub>1') \<Turnstile> (OclIsMaintained (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1))"
by(simp add: X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def OclIsMaintained_def OclValid_def \<sigma>\<^sub>1_def \<sigma>\<^sub>1'_def oid_of_option_def oid1_def oid2_def oid3_def oid4_def oid5_def oid6_def oid7_def oid8_def oid9_def oid_of_typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def oid_of_typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)
lemma oid9\<sigma>\<^sub>1\<sigma>\<^sub>1'_\<sigma>\<^sub>1'_OclIsMaintained : "(\<sigma>\<^sub>1 , \<sigma>\<^sub>1') \<Turnstile> (OclIsMaintained (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1'))"
by(simp add: X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def OclIsMaintained_def OclValid_def \<sigma>\<^sub>1_def \<sigma>\<^sub>1'_def oid_of_option_def oid1_def oid2_def oid3_def oid4_def oid5_def oid6_def oid7_def oid8_def oid9_def oid_of_typeoid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def oid_of_typeoid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)

(* 152 ************************************ 910 + 7 *)
generation_syntax [ shallow (generation_semantics [ design ]) ]
setup{* (Generation_mode.update_compiler_config ((K (let open OCL in Ocl_compiler_config_ext (true, NONE, Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 1), (Code_Numeral.Nat 10)), I ((Code_Numeral.Nat 0), (Code_Numeral.Nat 0)), Gen_only_design, SOME (OclClass ((String.explode "OclAny"), nil, uncurry cons (OclClass ((String.explode "Galaxy"), uncurry cons (I ((String.explode "sound"), OclTy_base_void), uncurry cons (I ((String.explode "moving"), OclTy_base_boolean), nil)), uncurry cons (OclClass ((String.explode "Planet"), uncurry cons (I ((String.explode "wormhole"), OclTy_base_unlimitednatural), uncurry cons (I ((String.explode "weight"), OclTy_base_integer), nil)), uncurry cons (OclClass ((String.explode "Person"), uncurry cons (I ((String.explode "boss"), OclTy_class (Ocl_ty_class_ext ((String.explode "oid"), (Code_Numeral.Nat 0), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), OclMult (uncurry cons (I (Mult_star, NONE), nil), Set), NONE, (String.explode "Person"), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), OclMult (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 0)), SOME (Mult_nat ((Code_Numeral.Nat 1)))), nil), Set), SOME ((String.explode "boss")), (String.explode "Person"), ()), ()))), uncurry cons (I ((String.explode "salary"), OclTy_base_integer), nil)), nil), nil)), nil)), nil))), uncurry cons (OclAstDefPrePost (OclDefPP ((String.explode "\<sigma>\<^sub>1"), (String.explode "\<sigma>\<^sub>1'"))), uncurry cons (OclAstDefState (OclDefSt ((String.explode "\<sigma>\<^sub>1'"), uncurry cons (OclDefCoreBinding ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1")), uncurry cons (OclDefCoreBinding ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2")), uncurry cons (OclDefCoreBinding ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3")), uncurry cons (OclDefCoreBinding ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4")), uncurry cons (OclDefCoreSkip, uncurry cons (OclDefCoreBinding ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6")), uncurry cons (OclDefCoreBinding ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7")), uncurry cons (OclDefCoreBinding ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8")), uncurry cons (OclDefCoreBinding ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9")), nil))))))))))), uncurry cons (OclAstDefState (OclDefSt ((String.explode "\<sigma>\<^sub>1"), uncurry cons (OclDefCoreAdd (Ocl_instance_single_ext ((String.explode ""), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "1000"))))), uncurry cons (I ((String.explode "boss"), Shall_base (ShallB_self (Oid ((Code_Numeral.Nat 1))))), nil))), ())), uncurry cons (OclDefCoreAdd (Ocl_instance_single_ext ((String.explode ""), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "1200"))))), nil)), ())), uncurry cons (OclDefCoreSkip, uncurry cons (OclDefCoreAdd (Ocl_instance_single_ext ((String.explode ""), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "2600"))))), uncurry cons (I ((String.explode "boss"), Shall_base (ShallB_self (Oid ((Code_Numeral.Nat 4))))), nil))), ())), uncurry cons (OclDefCoreBinding ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5")), uncurry cons (OclDefCoreAdd (Ocl_instance_single_ext ((String.explode ""), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "2300"))))), uncurry cons (I ((String.explode "boss"), Shall_base (ShallB_self (Oid ((Code_Numeral.Nat 3))))), nil))), ())), uncurry cons (OclDefCoreSkip, uncurry cons (OclDefCoreSkip, uncurry cons (OclDefCoreBinding ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9")), nil))))))))))), uncurry cons (OclAstInstance (OclInstance (uncurry cons (Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1"), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "1300"))))), uncurry cons (I ((String.explode "boss"), Shall_base (ShallB_str ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2")))), nil))), ()), uncurry cons (Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2"), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "1800"))))), uncurry cons (I ((String.explode "boss"), Shall_base (ShallB_str ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2")))), nil))), ()), uncurry cons (Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3"), (String.explode "Person"), OclAttrNoCast (nil), ()), uncurry cons (Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4"), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "2900"))))), nil)), ()), uncurry cons (Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5"), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "3500"))))), nil)), ()), uncurry cons (Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6"), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "2500"))))), uncurry cons (I ((String.explode "boss"), Shall_base (ShallB_str ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7")))), nil))), ()), uncurry cons (Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7"), (String.explode "OclAny"), OclAttrCast ((String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "3200"))))), uncurry cons (I ((String.explode "boss"), Shall_base (ShallB_str ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7")))), nil))), nil), ()), uncurry cons (Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8"), (String.explode "OclAny"), OclAttrNoCast (nil), ()), uncurry cons (Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9"), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "0"))))), nil)), ()), nil))))))))))), uncurry cons (OclAstClassRaw (Floor1, Ocl_class_raw_ext ((String.explode "Galaxy"), uncurry cons (I ((String.explode "sound"), OclTy_base_void), uncurry cons (I ((String.explode "moving"), OclTy_base_boolean), nil)), nil, nil, NONE, ())), uncurry cons (OclAstClassRaw (Floor1, Ocl_class_raw_ext ((String.explode "Planet"), uncurry cons (I ((String.explode "wormhole"), OclTy_base_unlimitednatural), uncurry cons (I ((String.explode "weight"), OclTy_base_integer), nil)), nil, nil, SOME ((String.explode "Galaxy")), ())), uncurry cons (OclAstAssociation (Ocl_association_ext (OclAssTy_association, uncurry cons (I ((String.explode "Person"), I (OclMult (uncurry cons (I (Mult_star, NONE), nil), Set), NONE)), uncurry cons (I ((String.explode "Person"), I (OclMult (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 0)), SOME (Mult_nat ((Code_Numeral.Nat 1)))), nil), Set), SOME ((String.explode "boss")))), nil)), ())), uncurry cons (OclAstClassRaw (Floor1, Ocl_class_raw_ext ((String.explode "Person"), uncurry cons (I ((String.explode "salary"), OclTy_base_integer), nil), nil, nil, SOME ((String.explode "Planet")), ())), nil)))))))), uncurry cons (I ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9"), I (Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9"), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "0"))))), nil)), ()), Oid ((Code_Numeral.Nat 9)))), uncurry cons (I ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8"), I (Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8"), (String.explode "OclAny"), OclAttrNoCast (nil), ()), Oid ((Code_Numeral.Nat 8)))), uncurry cons (I ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7"), I (Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7"), (String.explode "OclAny"), OclAttrCast ((String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "3200"))))), uncurry cons (I ((String.explode "boss"), Shall_base (ShallB_str ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7")))), nil))), nil), ()), Oid ((Code_Numeral.Nat 7)))), uncurry cons (I ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6"), I (Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6"), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "2500"))))), uncurry cons (I ((String.explode "boss"), Shall_base (ShallB_str ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7")))), nil))), ()), Oid ((Code_Numeral.Nat 6)))), uncurry cons (I ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5"), I (Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5"), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "3500"))))), nil)), ()), Oid ((Code_Numeral.Nat 5)))), uncurry cons (I ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4"), I (Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4"), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "2900"))))), nil)), ()), Oid ((Code_Numeral.Nat 4)))), uncurry cons (I ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3"), I (Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3"), (String.explode "Person"), OclAttrNoCast (nil), ()), Oid ((Code_Numeral.Nat 3)))), uncurry cons (I ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2"), I (Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2"), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "1800"))))), uncurry cons (I ((String.explode "boss"), Shall_base (ShallB_str ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2")))), nil))), ()), Oid ((Code_Numeral.Nat 2)))), uncurry cons (I ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1"), I (Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1"), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "1300"))))), uncurry cons (I ((String.explode "boss"), Shall_base (ShallB_str ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2")))), nil))), ()), Oid ((Code_Numeral.Nat 1)))), nil))))))))), uncurry cons (I ((String.explode "\<sigma>\<^sub>1'"), uncurry cons (I (Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 1), (Code_Numeral.Nat 1)), OclDefCoreBinding (I ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1"), Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1"), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "1300"))))), uncurry cons (I ((String.explode "boss"), Shall_base (ShallB_str ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2")))), nil))), ())))), uncurry cons (I (Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 1), (Code_Numeral.Nat 2)), OclDefCoreBinding (I ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2"), Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2"), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "1800"))))), uncurry cons (I ((String.explode "boss"), Shall_base (ShallB_str ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2")))), nil))), ())))), uncurry cons (I (Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 1), (Code_Numeral.Nat 3)), OclDefCoreBinding (I ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3"), Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3"), (String.explode "Person"), OclAttrNoCast (nil), ())))), uncurry cons (I (Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 1), (Code_Numeral.Nat 4)), OclDefCoreBinding (I ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4"), Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4"), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "2900"))))), nil)), ())))), uncurry cons (I (Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 1), (Code_Numeral.Nat 6)), OclDefCoreBinding (I ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6"), Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6"), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "2500"))))), uncurry cons (I ((String.explode "boss"), Shall_base (ShallB_str ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7")))), nil))), ())))), uncurry cons (I (Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 1), (Code_Numeral.Nat 7)), OclDefCoreBinding (I ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7"), Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7"), (String.explode "OclAny"), OclAttrCast ((String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "3200"))))), uncurry cons (I ((String.explode "boss"), Shall_base (ShallB_str ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7")))), nil))), nil), ())))), uncurry cons (I (Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 1), (Code_Numeral.Nat 8)), OclDefCoreBinding (I ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8"), Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8"), (String.explode "OclAny"), OclAttrNoCast (nil), ())))), uncurry cons (I (Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 1), (Code_Numeral.Nat 9)), OclDefCoreBinding (I ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9"), Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9"), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "0"))))), nil)), ())))), nil))))))))), uncurry cons (I ((String.explode "\<sigma>\<^sub>1"), uncurry cons (I (Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 1), (Code_Numeral.Nat 1)), OclDefCoreAdd (Ocl_instance_single_ext ((String.explode ""), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "1000"))))), uncurry cons (I ((String.explode "boss"), Shall_base (ShallB_self (Oid ((Code_Numeral.Nat 1))))), nil))), ()))), uncurry cons (I (Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 1), (Code_Numeral.Nat 2)), OclDefCoreAdd (Ocl_instance_single_ext ((String.explode ""), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "1200"))))), nil)), ()))), uncurry cons (I (Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 1), (Code_Numeral.Nat 4)), OclDefCoreAdd (Ocl_instance_single_ext ((String.explode ""), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "2600"))))), uncurry cons (I ((String.explode "boss"), Shall_base (ShallB_self (Oid ((Code_Numeral.Nat 4))))), nil))), ()))), uncurry cons (I (Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 1), (Code_Numeral.Nat 5)), OclDefCoreBinding (I ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5"), Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5"), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "3500"))))), nil)), ())))), uncurry cons (I (Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 1), (Code_Numeral.Nat 6)), OclDefCoreAdd (Ocl_instance_single_ext ((String.explode ""), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "2300"))))), uncurry cons (I ((String.explode "boss"), Shall_base (ShallB_self (Oid ((Code_Numeral.Nat 3))))), nil))), ()))), uncurry cons (I (Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 1), (Code_Numeral.Nat 9)), OclDefCoreBinding (I ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9"), Ocl_instance_single_ext ((String.explode "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9"), (String.explode "Person"), OclAttrNoCast (uncurry cons (I ((String.explode "salary"), Shall_base (ShallB_term (OclDefInteger ((String.explode "0"))))), nil)), ())))), nil))))))), nil)), true, false, I (uncurry cons ((String.explode "dot\<C>\<O>\<N>\<T>\<E>\<N>\<T>\<S>at_pre"), uncurry cons ((String.explode "dot\<M>\<O>\<V>\<I>\<N>\<G>at_pre"), uncurry cons ((String.explode "dot\<S>\<O>\<U>\<N>\<D>at_pre"), uncurry cons ((String.explode "dot\<W>\<E>\<I>\<G>\<H>\<T>at_pre"), uncurry cons ((String.explode "dot\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>at_pre"), uncurry cons ((String.explode "dot\<S>\<A>\<L>\<A>\<R>\<Y>at_pre"), uncurry cons ((String.explode "dot_0_\<B>\<O>\<S>\<S>at_pre"), nil))))))), uncurry cons ((String.explode "dot\<C>\<O>\<N>\<T>\<E>\<N>\<T>\<S>"), uncurry cons ((String.explode "dot\<M>\<O>\<V>\<I>\<N>\<G>"), uncurry cons ((String.explode "dot\<S>\<O>\<U>\<N>\<D>"), uncurry cons ((String.explode "dot\<W>\<E>\<I>\<G>\<H>\<T>"), uncurry cons ((String.explode "dot\<W>\<O>\<R>\<M>\<H>\<O>\<L>\<E>"), uncurry cons ((String.explode "dot\<S>\<A>\<L>\<A>\<R>\<Y>"), uncurry cons ((String.explode "dot_0_\<B>\<O>\<S>\<S>"), nil)))))))), uncurry cons (I ((String.explode "Set_Integer"), OclTy_collection (Set, OclTy_base_integer)), nil), false, ()) end)))) *}
type_synonym Set_Integer = "(\<AA>, int option option) Set"
consts dot\<C>\<O>\<N>\<T>\<E>\<N>\<T>\<S> :: "Person \<Rightarrow> Set_Integer" ("(_) .contents'(')")
consts dot\<C>\<O>\<N>\<T>\<E>\<N>\<T>\<S>at_pre :: "Person \<Rightarrow> Set_Integer" ("(_) .contents@pre'(')")
Context[shallow] Person :: contents () : Set(Integer)
  Post : "(\<lambda> self result. (result \<triangleq> if (self .boss \<doteq> null)
                   then (Set{}->including\<^sub>S\<^sub>e\<^sub>t(self .salary))
                   else (self .boss .contents()->including\<^sub>S\<^sub>e\<^sub>t(self .salary))
                   endif))"
  Post : "(\<lambda> self result. (true))"
  Pre : "(\<lambda> self. (false))"
thm dot\<C>\<O>\<N>\<T>\<E>\<N>\<T>\<S>_def

(* 153 ************************************ 917 + 2 *)
Context[shallow] Person
  Inv a : "(\<lambda> self. (self .boss <> null implies (self .salary  \<triangleq>  ((self .boss) .salary))))"
thm Person_aat_pre_def Person_a_def

(* 154 ************************************ 919 + 2 *)
Context[shallow] Planet
  Inv A : "(\<lambda> self. (true and (self .weight \<le>\<^sub>i\<^sub>n\<^sub>t \<zero>)))"
thm Planet_Aat_pre_def Planet_A_def

end
