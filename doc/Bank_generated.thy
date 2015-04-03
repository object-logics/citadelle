theory Bank_generated imports "../src/UML_Main"   "../src/compiler/OCL_compiler_static"   "../src/compiler/OCL_compiler_generator_dynamic" begin

(* 1 ************************************ 0 + 1 *)
type_synonym Currency = "real"

(* 2 ************************************ 1 + 1 *)
text{*  *}

(* 3 ************************************ 2 + 1 *)
text{* 
   \label{ex:employee-analysis:uml}  *}

(* 4 ************************************ 3 + 1 *)
section{* Introduction *}

(* 5 ************************************ 4 + 1 *)
text{* 

  For certain concepts like classes and class-types, only a generic
  definition for its resulting semantics can be given. Generic means,
  there is a function outside HOL that ``compiles'' a concrete,
  closed-world class diagram into a ``theory'' of this data model,
  consisting of a bunch of definitions for classes, accessors, method,
  casts, and tests for actual types, as well as proofs for the
  fundamental properties of these operations in this concrete data
  model.  *}

(* 6 ************************************ 5 + 1 *)
text{* 
   Such generic function or ``compiler'' can be implemented in
  Isabelle on the ML level.  This has been done, for a semantics
  following the open-world assumption, for UML 2.0
  in~\cite{brucker.ea:extensible:2008-b, brucker:interactive:2007}. In
  this paper, we follow another approach for UML 2.4: we define the
  concepts of the compilation informally, and present a concrete
  example which is verified in Isabelle/HOL.  *}

(* 7 ************************************ 6 + 1 *)
subsection{* Outlining the Example *}

(* 8 ************************************ 7 + 1 *)
text{*  *}

(* 9 ************************************ 8 + 1 *)
text{* 
   We are presenting here an ``analysis-model'' of the (slightly
modified) example Figure 7.3, page 20 of
the OCL standard~\cite{omg:ocl:2012}.
Here, analysis model means that associations
were really represented as relation on objects on the state---as is
intended by the standard---rather by pointers between objects as is
done in our ``design model'' (see \autoref{ex:employee-design:uml}).
To be precise, this theory contains the formalization of the data-part
covered by the UML class model (see \autoref{fig:person-ana}): *}

(* 10 ************************************ 9 + 1 *)
text{*  *}

(* 11 ************************************ 10 + 1 *)
text{* 

\begin{figure}
  \centering\scalebox{.3}{\includegraphics{figures/person.png}}%
  \caption{A simple UML class model drawn from Figure 7.3,
  page 20 of~\cite{omg:ocl:2012}. \label{fig:person-ana}}
\end{figure}
 *}

(* 12 ************************************ 11 + 1 *)
text{* 
   This means that the association (attached to the association class
\inlineocl{EmployeeRanking}) with the association ends \inlineocl+boss+ and \inlineocl+employees+ is implemented
by the attribute  \inlineocl+boss+ and the operation \inlineocl+employees+ (to be discussed in the OCL part
captured by the subsequent theory).
 *}

(* 13 ************************************ 12 + 1 *)
section{* Example Data-Universe and its Infrastructure *}

(* 14 ************************************ 13 + 1 *)
text{* 
   Our data universe  consists in the concrete class diagram just of node's,
and implicitly of the class object. Each class implies the existence of a class
type defined for the corresponding object representations as follows:  *}

(* 15 ************************************ 14 + 12 *)
datatype ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t = mk\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t "oid" "int option" "Currency option"
datatype ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t = mk\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t "ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t" "Currency option"
datatype ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s = mk\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s "oid" "int option" "Currency option"
datatype ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s = mk\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s "ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s" "Currency option"
datatype ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t = mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s "ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s"
                        | mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t "ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t"
                        | mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t "oid"
datatype ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t = mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t "ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t" "int option" "Currency option"
datatype ty\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k = mk\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k "oid"
datatype ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k = mk\<^sub>B\<^sub>a\<^sub>n\<^sub>k "ty\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k" "string option"
datatype ty\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t = mk\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t "oid"
datatype ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t = mk\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t "ty\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t" "string option" "string option" "int option"
datatype ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t "ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t"
                        | mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>B\<^sub>a\<^sub>n\<^sub>k "ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k"
                        | mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t "ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t"
                        | mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s "ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s"
                        | mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t "ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t"
                        | mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y "oid"
datatype ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y "ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y"

(* 16 ************************************ 26 + 1 *)
text{* 
   Now, we construct a concrete ``universe of OclAny types'' by injection into a
sum type containing the class types. This type of OclAny will be used as instance
for all respective type-variables.  *}

(* 17 ************************************ 27 + 1 *)
datatype \<AA> = in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t "ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t"
                        | in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s "ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s"
                        | in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t "ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t"
                        | in\<^sub>B\<^sub>a\<^sub>n\<^sub>k "ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k"
                        | in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t "ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t"
                        | in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y "ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y"

(* 18 ************************************ 28 + 1 *)
text{* 
   Having fixed the object universe, we can introduce type synonyms that exactly correspond
to OCL types. Again, we exploit that our representation of OCL is a ``shallow embedding'' with a
one-to-one correspondance of OCL-types to types of the meta-language HOL.  *}

(* 19 ************************************ 29 + 11 *)
type_synonym Void = "\<AA> Void"
type_synonym Boolean = "\<AA> Boolean"
type_synonym Integer = "\<AA> Integer"
type_synonym Real = "\<AA> Real"
type_synonym String = "\<AA> String"
type_synonym Current = "(\<AA>, ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t option option) val"
type_synonym Savings = "(\<AA>, ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s option option) val"
type_synonym Account = "(\<AA>, ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t option option) val"
type_synonym Bank = "(\<AA>, ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k option option) val"
type_synonym Client = "(\<AA>, ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t option option) val"
type_synonym OclAny = "(\<AA>, ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y option option) val"

(* 20 ************************************ 40 + 6 *)
type_synonym Sequence_Client = "(\<AA>, ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t option option Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"
type_synonym Set_Client = "(\<AA>, ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t option option Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"
type_synonym Sequence_Bank = "(\<AA>, ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k option option Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"
type_synonym Set_Bank = "(\<AA>, ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k option option Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"
type_synonym Sequence_Account = "(\<AA>, ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t option option Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"
type_synonym Set_Account = "(\<AA>, ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t option option Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"

(* 21 ************************************ 46 + 1 *)
text{* 
   To reuse key-elements of the library like referential equality, we have
to show that the object universe belongs to the type class ``oclany,'' \ie,
 each class type has to provide a function @{term oid_of} yielding the object id (oid) of the object.  *}

(* 22 ************************************ 47 + 6 *)
instantiation ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t :: object
begin
  definition oid_of_ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_def : "oid_of = (\<lambda> mk\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t t _ \<Rightarrow> (case t of (mk\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (t) (_) (_)) \<Rightarrow> t))"
  instance ..
end
instantiation ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s :: object
begin
  definition oid_of_ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_def : "oid_of = (\<lambda> mk\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s t _ \<Rightarrow> (case t of (mk\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (t) (_) (_)) \<Rightarrow> t))"
  instance ..
end
instantiation ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t :: object
begin
  definition oid_of_ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_def : "oid_of = (\<lambda> mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t t _ _ \<Rightarrow> (case t of (mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (t)) \<Rightarrow> t
    | (mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (t)) \<Rightarrow> (oid_of (t))
    | (mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (t)) \<Rightarrow> (oid_of (t))))"
  instance ..
end
instantiation ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k :: object
begin
  definition oid_of_ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k_def : "oid_of = (\<lambda> mk\<^sub>B\<^sub>a\<^sub>n\<^sub>k t _ \<Rightarrow> (case t of (mk\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k (t)) \<Rightarrow> t))"
  instance ..
end
instantiation ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t :: object
begin
  definition oid_of_ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def : "oid_of = (\<lambda> mk\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t t _ _ _ \<Rightarrow> (case t of (mk\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (t)) \<Rightarrow> t))"
  instance ..
end
instantiation ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: object
begin
  definition oid_of_ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def : "oid_of = (\<lambda> mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y t \<Rightarrow> (case t of (mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (t)) \<Rightarrow> t
    | (mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (t)) \<Rightarrow> (oid_of (t))
    | (mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (t)) \<Rightarrow> (oid_of (t))
    | (mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (t)) \<Rightarrow> (oid_of (t))
    | (mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>B\<^sub>a\<^sub>n\<^sub>k (t)) \<Rightarrow> (oid_of (t))
    | (mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (t)) \<Rightarrow> (oid_of (t))))"
  instance ..
end

(* 23 ************************************ 53 + 1 *)
instantiation \<AA> :: object
begin
  definition oid_of_\<AA>_def : "oid_of = (\<lambda> in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t Current \<Rightarrow> oid_of Current
    | in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s Savings \<Rightarrow> oid_of Savings
    | in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t Account \<Rightarrow> oid_of Account
    | in\<^sub>B\<^sub>a\<^sub>n\<^sub>k Bank \<Rightarrow> oid_of Bank
    | in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t Client \<Rightarrow> oid_of Client
    | in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y OclAny \<Rightarrow> oid_of OclAny)"
  instance ..
end

(* 24 ************************************ 54 + 1 *)
section{* Instantiation of the Generic Strict Equality *}

(* 25 ************************************ 55 + 1 *)
text{* 
   We instantiate the referential equality
on @{text "Person"} and @{text "OclAny"}  *}

(* 26 ************************************ 56 + 6 *)
defs(overloaded) StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t : "(x::Current) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
defs(overloaded) StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s : "(x::Savings) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
defs(overloaded) StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : "(x::Account) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
defs(overloaded) StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>B\<^sub>a\<^sub>n\<^sub>k : "(x::Bank) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
defs(overloaded) StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t : "(x::Client) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
defs(overloaded) StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : "(x::OclAny) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"

(* 27 ************************************ 62 + 1 *)
lemmas[simp,code_unfold] = StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t
                            StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s
                            StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t
                            StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>B\<^sub>a\<^sub>n\<^sub>k
                            StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t
                            StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y

(* 28 ************************************ 63 + 1 *)
text{* 
   For each Class \emph{C}, we will have a casting operation \inlineocl{.oclAsType($C$)},
   a test on the actual type \inlineocl{.oclIsTypeOf($C$)} as well as its relaxed form
   \inlineocl{.oclIsKindOf($C$)} (corresponding exactly to Java's \verb+instanceof+-operator.
 *}

(* 29 ************************************ 64 + 1 *)
text{* 
   Thus, since we have two class-types in our concrete class hierarchy, we have
two operations to declare and to provide two overloading definitions for the two static types.
 *}

(* 30 ************************************ 65 + 1 *)
section{* OclAsType *}

(* 31 ************************************ 66 + 1 *)
subsection{* Definition *}

(* 32 ************************************ 67 + 6 *)
consts OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t :: "'\<alpha> \<Rightarrow> Current" ("(_) .oclAsType'(Current')")
consts OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s :: "'\<alpha> \<Rightarrow> Savings" ("(_) .oclAsType'(Savings')")
consts OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t :: "'\<alpha> \<Rightarrow> Account" ("(_) .oclAsType'(Account')")
consts OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k :: "'\<alpha> \<Rightarrow> Bank" ("(_) .oclAsType'(Bank')")
consts OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t :: "'\<alpha> \<Rightarrow> Client" ("(_) .oclAsType'(Client')")
consts OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: "'\<alpha> \<Rightarrow> OclAny" ("(_) .oclAsType'(OclAny')")

(* 33 ************************************ 73 + 36 *)
defs(overloaded) OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current : "(x::Current) .oclAsType(Current) \<equiv> x"
defs(overloaded) OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account : "(x::Account) .oclAsType(Current) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Current\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny : "(x::OclAny) .oclAsType(Current) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Current\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings : "(x::Savings) .oclAsType(Current) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank : "(x::Bank) .oclAsType(Current) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client : "(x::Client) .oclAsType(Current) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings : "(x::Savings) .oclAsType(Savings) \<equiv> x"
defs(overloaded) OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account : "(x::Account) .oclAsType(Savings) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Savings\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny : "(x::OclAny) .oclAsType(Savings) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Savings\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current : "(x::Current) .oclAsType(Savings) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank : "(x::Bank) .oclAsType(Savings) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client : "(x::Client) .oclAsType(Savings) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account : "(x::Account) .oclAsType(Account) \<equiv> x"
defs(overloaded) OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny : "(x::OclAny) .oclAsType(Account) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Account\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current : "(x::Current) .oclAsType(Account) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Current\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current))) (None) (None))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings : "(x::Savings) .oclAsType(Account) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Savings\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings))) (None) (None))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank : "(x::Bank) .oclAsType(Account) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client : "(x::Client) .oclAsType(Account) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank : "(x::Bank) .oclAsType(Bank) \<equiv> x"
defs(overloaded) OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny : "(x::OclAny) .oclAsType(Bank) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Bank\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client : "(x::Client) .oclAsType(Bank) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings : "(x::Savings) .oclAsType(Bank) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account : "(x::Account) .oclAsType(Bank) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current : "(x::Current) .oclAsType(Bank) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client : "(x::Client) .oclAsType(Client) \<equiv> x"
defs(overloaded) OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny : "(x::OclAny) .oclAsType(Client) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Client\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank : "(x::Bank) .oclAsType(Client) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings : "(x::Savings) .oclAsType(Client) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account : "(x::Account) .oclAsType(Client) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current : "(x::Current) .oclAsType(Client) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny : "(x::OclAny) .oclAsType(OclAny) \<equiv> x"
defs(overloaded) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current : "(x::Current) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Current\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current))))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings : "(x::Savings) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Savings\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings))))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account : "(x::Account) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Account\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account))))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank : "(x::Bank) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Bank\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank))))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client : "(x::Client) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Client\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client))))\<rfloor>\<rfloor>))"

(* 34 ************************************ 109 + 6 *)
definition "OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_\<AA> = (\<lambda> (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> \<lfloor>Current\<rfloor>
    | (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current))) (_) (_)))) \<Rightarrow> \<lfloor>Current\<rfloor>
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)))))) \<Rightarrow> \<lfloor>Current\<rfloor>
    | _ \<Rightarrow> None)"
definition "OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_\<AA> = (\<lambda> (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> \<lfloor>Savings\<rfloor>
    | (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings))) (_) (_)))) \<Rightarrow> \<lfloor>Savings\<rfloor>
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)))))) \<Rightarrow> \<lfloor>Savings\<rfloor>
    | _ \<Rightarrow> None)"
definition "OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<AA> = (\<lambda> (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> \<lfloor>Account\<rfloor>
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)))))) \<Rightarrow> \<lfloor>Account\<rfloor>
    | (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> \<lfloor>(mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current))) (None) (None))\<rfloor>
    | (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> \<lfloor>(mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings))) (None) (None))\<rfloor>
    | _ \<Rightarrow> None)"
definition "OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_\<AA> = (\<lambda> (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> \<lfloor>Bank\<rfloor>
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)))))) \<Rightarrow> \<lfloor>Bank\<rfloor>
    | _ \<Rightarrow> None)"
definition "OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_\<AA> = (\<lambda> (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> \<lfloor>Client\<rfloor>
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)))))) \<Rightarrow> \<lfloor>Client\<rfloor>
    | _ \<Rightarrow> None)"
definition "OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> = Some o (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> OclAny
    | (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current))))
    | (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings))))
    | (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account))))
    | (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank))))
    | (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)))))"

(* 35 ************************************ 115 + 1 *)
lemmas[simp,code_unfold] = OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current
                            OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings
                            OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account
                            OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank
                            OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny

(* 36 ************************************ 116 + 1 *)
subsection{* Context Passing *}

(* 37 ************************************ 117 + 216 *)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Savings) .oclAsType(Savings)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Savings) .oclAsType(Savings)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Savings) .oclAsType(Savings)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Savings) .oclAsType(Savings)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Savings) .oclAsType(Savings)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Savings) .oclAsType(Savings)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Account) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Account) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Account) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Account) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Account) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Account) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Client) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Client) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Client) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Client) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Client) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Client) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::OclAny) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::OclAny) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::OclAny) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::OclAny) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::OclAny) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Bank) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Bank) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Bank) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Bank) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Bank) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Bank) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Current) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Current) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Current) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Current) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Current) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Current) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Savings) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Savings) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Savings) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Savings) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Savings) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Savings) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Account) .oclAsType(Account)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Account) .oclAsType(Account)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Account) .oclAsType(Account)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Account) .oclAsType(Account)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Account) .oclAsType(Account)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Account) .oclAsType(Account)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Client) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Client) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Client) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Client) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Client) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Client) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::OclAny) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::OclAny) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::OclAny) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::OclAny) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::OclAny) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Bank) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Bank) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Bank) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Bank) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Bank) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Bank) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Current) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Current) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Current) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Current) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Current) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Current) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Savings) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Savings) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Savings) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Savings) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Savings) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Savings) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Account) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Account) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Account) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Account) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Account) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Account) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Client) .oclAsType(Client)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Client) .oclAsType(Client)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Client) .oclAsType(Client)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Client) .oclAsType(Client)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Client) .oclAsType(Client)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Client) .oclAsType(Client)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::OclAny) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::OclAny) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::OclAny) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::OclAny) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::OclAny) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Bank) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Bank) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Bank) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Bank) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Bank) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Bank) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Current) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Current) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Current) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Current) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Current) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Current) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Savings) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Savings) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Savings) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Savings) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Savings) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Savings) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Account) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Account) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Account) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Account) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Account) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Account) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Client) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Client) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Client) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Client) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Client) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Client) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Bank) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Bank) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Bank) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Bank) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Bank) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Bank) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Current) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Current) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Current) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Current) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Current) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Current) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Savings) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Savings) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Savings) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Savings) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Savings) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Savings) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Account) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Account) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Account) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Account) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Account) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Account) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Client) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Client) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Client) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Client) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Client) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Client) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::OclAny) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::OclAny) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::OclAny) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::OclAny) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::OclAny) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Bank) .oclAsType(Bank)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Bank) .oclAsType(Bank)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Bank) .oclAsType(Bank)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Bank) .oclAsType(Bank)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Bank) .oclAsType(Bank)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Bank) .oclAsType(Bank)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Current) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Current) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Current) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Current) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Current) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Current) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Savings) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Savings) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Savings) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Savings) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Savings) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Savings) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Account) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Account) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Account) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Account) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Account) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Account) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Client) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Client) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Client) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Client) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Client) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Client) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::OclAny) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::OclAny) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::OclAny) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::OclAny) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::OclAny) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Bank) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Bank) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Bank) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Bank) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Bank) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Bank) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Current) .oclAsType(Current)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Current) .oclAsType(Current)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Current) .oclAsType(Current)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Current) .oclAsType(Current)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Current) .oclAsType(Current)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Current) .oclAsType(Current)))))"
by(rule cpI1, simp)

(* 38 ************************************ 333 + 1 *)
lemmas[simp,code_unfold] = cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Savings
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Savings
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Savings
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Savings
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Savings
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Savings
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Account
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Account
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Account
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Account
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Account
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Account
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Client
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Client
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Client
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Client
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Client
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Client
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_OclAny
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_OclAny
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_OclAny
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_OclAny
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_OclAny
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_OclAny
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Bank
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Bank
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Bank
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Bank
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Bank
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Bank
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Current
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Current
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Current
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Current
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Current
                            cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Current
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Savings
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Savings
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Savings
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Savings
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Savings
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Savings
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Account
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Account
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Account
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Account
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Account
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Account
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Client
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Client
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Client
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Client
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Client
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Client
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_OclAny
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_OclAny
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_OclAny
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_OclAny
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_OclAny
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_OclAny
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Bank
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Bank
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Bank
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Bank
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Bank
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Bank
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Current
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Current
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Current
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Current
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Current
                            cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Current
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Savings
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Savings
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Savings
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Savings
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Savings
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Account
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Account
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Account
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Account
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Account
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Account
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Client
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Client
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Client
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Client
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Client
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Client
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_OclAny
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_OclAny
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_OclAny
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Bank
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Bank
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Bank
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Bank
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Bank
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Current
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Current
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Current
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Current
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Current
                            cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Current
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Savings
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Savings
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Savings
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Savings
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Savings
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Savings
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Account
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Account
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Account
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Account
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Account
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Account
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Client
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Client
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Client
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Client
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Client
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Client
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_OclAny
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_OclAny
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_OclAny
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_OclAny
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_OclAny
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Bank
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Bank
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Bank
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Bank
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Bank
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Bank
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Current
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Current
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Current
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Current
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Current
                            cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Current
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Savings
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Savings
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Savings
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Savings
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Savings
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Savings
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Account
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Account
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Account
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Account
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Account
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Account
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Client
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Client
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Client
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Client
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Client
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Client
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_OclAny
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_OclAny
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_OclAny
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_OclAny
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_OclAny
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_OclAny
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Bank
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Bank
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Bank
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Bank
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Bank
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Bank
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Current
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Current
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Current
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Current
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Current
                            cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Current
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Savings
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Savings
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Savings
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Savings
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Savings
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Account
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Account
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Account
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Account
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Account
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Account
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Client
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Client
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Client
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Client
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Client
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Client
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_OclAny
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_OclAny
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_OclAny
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Bank
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Bank
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Bank
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Bank
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Bank
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Current
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Current
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Current
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Current
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Current
                            cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Current

(* 39 ************************************ 334 + 1 *)
subsection{* Execution with Invalid or Null as Argument *}

(* 40 ************************************ 335 + 72 *)
lemma OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_invalid : "((invalid::Savings) .oclAsType(Savings)) = invalid"
by(simp)
lemma OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_invalid : "((invalid::Account) .oclAsType(Savings)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account bot_option_def invalid_def)
lemma OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_invalid : "((invalid::Client) .oclAsType(Savings)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client bot_option_def invalid_def)
lemma OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_invalid : "((invalid::OclAny) .oclAsType(Savings)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny bot_option_def invalid_def)
lemma OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_invalid : "((invalid::Bank) .oclAsType(Savings)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank bot_option_def invalid_def)
lemma OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_invalid : "((invalid::Current) .oclAsType(Savings)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current bot_option_def invalid_def)
lemma OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_null : "((null::Savings) .oclAsType(Savings)) = null"
by(simp)
lemma OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_null : "((null::Account) .oclAsType(Savings)) = null"
by(rule ext, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_null : "((null::Client) .oclAsType(Savings)) = null"
by(rule ext, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_null : "((null::OclAny) .oclAsType(Savings)) = null"
by(rule ext, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_null : "((null::Bank) .oclAsType(Savings)) = null"
by(rule ext, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_null : "((null::Current) .oclAsType(Savings)) = null"
by(rule ext, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_invalid : "((invalid::Savings) .oclAsType(Account)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings bot_option_def invalid_def)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_invalid : "((invalid::Account) .oclAsType(Account)) = invalid"
by(simp)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_invalid : "((invalid::Client) .oclAsType(Account)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client bot_option_def invalid_def)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_invalid : "((invalid::OclAny) .oclAsType(Account)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny bot_option_def invalid_def)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_invalid : "((invalid::Bank) .oclAsType(Account)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank bot_option_def invalid_def)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_invalid : "((invalid::Current) .oclAsType(Account)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current bot_option_def invalid_def)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_null : "((null::Savings) .oclAsType(Account)) = null"
by(rule ext, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_null : "((null::Account) .oclAsType(Account)) = null"
by(simp)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_null : "((null::Client) .oclAsType(Account)) = null"
by(rule ext, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_null : "((null::OclAny) .oclAsType(Account)) = null"
by(rule ext, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_null : "((null::Bank) .oclAsType(Account)) = null"
by(rule ext, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_null : "((null::Current) .oclAsType(Account)) = null"
by(rule ext, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_invalid : "((invalid::Savings) .oclAsType(Client)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings bot_option_def invalid_def)
lemma OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_invalid : "((invalid::Account) .oclAsType(Client)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account bot_option_def invalid_def)
lemma OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_invalid : "((invalid::Client) .oclAsType(Client)) = invalid"
by(simp)
lemma OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid : "((invalid::OclAny) .oclAsType(Client)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny bot_option_def invalid_def)
lemma OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_invalid : "((invalid::Bank) .oclAsType(Client)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank bot_option_def invalid_def)
lemma OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_invalid : "((invalid::Current) .oclAsType(Client)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current bot_option_def invalid_def)
lemma OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_null : "((null::Savings) .oclAsType(Client)) = null"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_null : "((null::Account) .oclAsType(Client)) = null"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_null : "((null::Client) .oclAsType(Client)) = null"
by(simp)
lemma OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_null : "((null::OclAny) .oclAsType(Client)) = null"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_null : "((null::Bank) .oclAsType(Client)) = null"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_null : "((null::Current) .oclAsType(Client)) = null"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_invalid : "((invalid::Savings) .oclAsType(OclAny)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings bot_option_def invalid_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_invalid : "((invalid::Account) .oclAsType(OclAny)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account bot_option_def invalid_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_invalid : "((invalid::Client) .oclAsType(OclAny)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client bot_option_def invalid_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid : "((invalid::OclAny) .oclAsType(OclAny)) = invalid"
by(simp)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_invalid : "((invalid::Bank) .oclAsType(OclAny)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank bot_option_def invalid_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_invalid : "((invalid::Current) .oclAsType(OclAny)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current bot_option_def invalid_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_null : "((null::Savings) .oclAsType(OclAny)) = null"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_null : "((null::Account) .oclAsType(OclAny)) = null"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_null : "((null::Client) .oclAsType(OclAny)) = null"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null : "((null::OclAny) .oclAsType(OclAny)) = null"
by(simp)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_null : "((null::Bank) .oclAsType(OclAny)) = null"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_null : "((null::Current) .oclAsType(OclAny)) = null"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_invalid : "((invalid::Savings) .oclAsType(Bank)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings bot_option_def invalid_def)
lemma OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_invalid : "((invalid::Account) .oclAsType(Bank)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account bot_option_def invalid_def)
lemma OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_invalid : "((invalid::Client) .oclAsType(Bank)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client bot_option_def invalid_def)
lemma OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_invalid : "((invalid::OclAny) .oclAsType(Bank)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny bot_option_def invalid_def)
lemma OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_invalid : "((invalid::Bank) .oclAsType(Bank)) = invalid"
by(simp)
lemma OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_invalid : "((invalid::Current) .oclAsType(Bank)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current bot_option_def invalid_def)
lemma OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_null : "((null::Savings) .oclAsType(Bank)) = null"
by(rule ext, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_null : "((null::Account) .oclAsType(Bank)) = null"
by(rule ext, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_null : "((null::Client) .oclAsType(Bank)) = null"
by(rule ext, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_null : "((null::OclAny) .oclAsType(Bank)) = null"
by(rule ext, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_null : "((null::Bank) .oclAsType(Bank)) = null"
by(simp)
lemma OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_null : "((null::Current) .oclAsType(Bank)) = null"
by(rule ext, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_invalid : "((invalid::Savings) .oclAsType(Current)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings bot_option_def invalid_def)
lemma OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_invalid : "((invalid::Account) .oclAsType(Current)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account bot_option_def invalid_def)
lemma OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_invalid : "((invalid::Client) .oclAsType(Current)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client bot_option_def invalid_def)
lemma OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid : "((invalid::OclAny) .oclAsType(Current)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny bot_option_def invalid_def)
lemma OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_invalid : "((invalid::Bank) .oclAsType(Current)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank bot_option_def invalid_def)
lemma OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_invalid : "((invalid::Current) .oclAsType(Current)) = invalid"
by(simp)
lemma OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_null : "((null::Savings) .oclAsType(Current)) = null"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_null : "((null::Account) .oclAsType(Current)) = null"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_null : "((null::Client) .oclAsType(Current)) = null"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_null : "((null::OclAny) .oclAsType(Current)) = null"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_null : "((null::Bank) .oclAsType(Current)) = null"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_null : "((null::Current) .oclAsType(Current)) = null"
by(simp)

(* 41 ************************************ 407 + 1 *)
lemmas[simp,code_unfold] = OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_invalid
                            OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_invalid
                            OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_invalid
                            OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_invalid
                            OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_invalid
                            OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_invalid
                            OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_null
                            OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_null
                            OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_null
                            OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_null
                            OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_null
                            OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_null
                            OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_invalid
                            OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_invalid
                            OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_invalid
                            OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_invalid
                            OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_invalid
                            OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_invalid
                            OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_null
                            OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_null
                            OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_null
                            OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_null
                            OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_null
                            OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_null
                            OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_invalid
                            OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_invalid
                            OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_invalid
                            OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid
                            OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_invalid
                            OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_invalid
                            OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_null
                            OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_null
                            OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_null
                            OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_null
                            OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_null
                            OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_null
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_invalid
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_invalid
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_invalid
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_invalid
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_invalid
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_null
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_null
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_null
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_null
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_null
                            OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_invalid
                            OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_invalid
                            OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_invalid
                            OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_invalid
                            OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_invalid
                            OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_invalid
                            OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_null
                            OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_null
                            OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_null
                            OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_null
                            OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_null
                            OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_null
                            OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_invalid
                            OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_invalid
                            OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_invalid
                            OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid
                            OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_invalid
                            OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_invalid
                            OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_null
                            OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_null
                            OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_null
                            OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_null
                            OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_null
                            OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_null

(* 42 ************************************ 408 + 1 *)
subsection{* Validity and Definedness Properties *}

(* 43 ************************************ 409 + 7 *)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclAsType(Account)))"
  using isdef
by(auto simp: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current foundation16 null_option_def bot_option_def) 
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclAsType(Account)))"
  using isdef
by(auto simp: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings foundation16 null_option_def bot_option_def) 
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclAsType(OclAny)))"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current foundation16 null_option_def bot_option_def) 
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclAsType(OclAny)))"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings foundation16 null_option_def bot_option_def) 
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Account) .oclAsType(OclAny)))"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account foundation16 null_option_def bot_option_def) 
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Bank) .oclAsType(OclAny)))"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank foundation16 null_option_def bot_option_def) 
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Client) .oclAsType(OclAny)))"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client foundation16 null_option_def bot_option_def) 

(* 44 ************************************ 416 + 1 *)
subsection{* Up Down Casting *}

(* 45 ************************************ 417 + 7 *)
lemma up\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_down\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_cast0 : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::Current) .oclAsType(Account)) .oclAsType(Current)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split) 
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_cast0 : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::Current) .oclAsType(OclAny)) .oclAsType(Current)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split) 
lemma up\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_down\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_cast0 : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::Savings) .oclAsType(Account)) .oclAsType(Savings)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split) 
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_cast0 : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::Savings) .oclAsType(OclAny)) .oclAsType(Savings)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split) 
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_cast0 : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::Account) .oclAsType(OclAny)) .oclAsType(Account)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split) 
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>B\<^sub>a\<^sub>n\<^sub>k_cast0 : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::Bank) .oclAsType(OclAny)) .oclAsType(Bank)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split) 
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_cast0 : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::Client) .oclAsType(OclAny)) .oclAsType(Client)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split) 

(* 46 ************************************ 424 + 7 *)
lemma up\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_down\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_cast : 
shows "(((X::Current) .oclAsType(Account)) .oclAsType(Current)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_down\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done 
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_cast : 
shows "(((X::Current) .oclAsType(OclAny)) .oclAsType(Current)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done 
lemma up\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_down\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_cast : 
shows "(((X::Savings) .oclAsType(Account)) .oclAsType(Savings)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_down\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done 
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_cast : 
shows "(((X::Savings) .oclAsType(OclAny)) .oclAsType(Savings)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done 
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_cast : 
shows "(((X::Account) .oclAsType(OclAny)) .oclAsType(Account)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done 
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>B\<^sub>a\<^sub>n\<^sub>k_cast : 
shows "(((X::Bank) .oclAsType(OclAny)) .oclAsType(Bank)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>B\<^sub>a\<^sub>n\<^sub>k_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done 
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_cast : 
shows "(((X::Client) .oclAsType(OclAny)) .oclAsType(Client)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done 

(* 47 ************************************ 431 + 7 *)
lemma down\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_up\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_cast : 
assumes def_X: "X = ((Y::Current) .oclAsType(Account))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Current)) .oclAsType(Account)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_down\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym) 
lemma down\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_cast : 
assumes def_X: "X = ((Y::Current) .oclAsType(OclAny))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Current)) .oclAsType(OclAny)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym) 
lemma down\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_up\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_cast : 
assumes def_X: "X = ((Y::Savings) .oclAsType(Account))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Savings)) .oclAsType(Account)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_down\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym) 
lemma down\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_cast : 
assumes def_X: "X = ((Y::Savings) .oclAsType(OclAny))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Savings)) .oclAsType(OclAny)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym) 
lemma down\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_cast : 
assumes def_X: "X = ((Y::Account) .oclAsType(OclAny))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Account)) .oclAsType(OclAny)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym) 
lemma down\<^sub>B\<^sub>a\<^sub>n\<^sub>k_up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_cast : 
assumes def_X: "X = ((Y::Bank) .oclAsType(OclAny))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Bank)) .oclAsType(OclAny)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>B\<^sub>a\<^sub>n\<^sub>k_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym) 
lemma down\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_cast : 
assumes def_X: "X = ((Y::Client) .oclAsType(OclAny))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Client)) .oclAsType(OclAny)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym) 

(* 48 ************************************ 438 + 1 *)
section{* OclIsTypeOf *}

(* 49 ************************************ 439 + 1 *)
subsection{* Definition *}

(* 50 ************************************ 440 + 6 *)
consts OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Current')")
consts OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Savings')")
consts OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Account')")
consts OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Bank')")
consts OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Client')")
consts OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(OclAny')")

(* 51 ************************************ 446 + 36 *)
defs(overloaded) OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current : "(x::Current) .oclIsTypeOf(Current) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (_) (_) (_))) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account : "(x::Account) .oclIsTypeOf(Current) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny : "(x::OclAny) .oclIsTypeOf(Current) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings : "(x::Savings) .oclIsTypeOf(Current) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank : "(x::Bank) .oclIsTypeOf(Current) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client : "(x::Client) .oclIsTypeOf(Current) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings : "(x::Savings) .oclIsTypeOf(Savings) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s ((mk\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (_) (_) (_))) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account : "(x::Account) .oclIsTypeOf(Savings) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny : "(x::OclAny) .oclIsTypeOf(Savings) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current : "(x::Current) .oclIsTypeOf(Savings) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank : "(x::Bank) .oclIsTypeOf(Savings) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client : "(x::Client) .oclIsTypeOf(Savings) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account : "(x::Account) .oclIsTypeOf(Account) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny : "(x::OclAny) .oclIsTypeOf(Account) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current : "(x::Current) .oclIsTypeOf(Account) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings : "(x::Savings) .oclIsTypeOf(Account) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank : "(x::Bank) .oclIsTypeOf(Account) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client : "(x::Client) .oclIsTypeOf(Account) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank : "(x::Bank) .oclIsTypeOf(Bank) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>B\<^sub>a\<^sub>n\<^sub>k ((mk\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k (_))) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny : "(x::OclAny) .oclIsTypeOf(Bank) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>B\<^sub>a\<^sub>n\<^sub>k (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client : "(x::Client) .oclIsTypeOf(Bank) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings : "(x::Savings) .oclIsTypeOf(Bank) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account : "(x::Account) .oclIsTypeOf(Bank) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current : "(x::Current) .oclIsTypeOf(Bank) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client : "(x::Client) .oclIsTypeOf(Client) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (_))) (_) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny : "(x::OclAny) .oclIsTypeOf(Client) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank : "(x::Bank) .oclIsTypeOf(Client) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings : "(x::Savings) .oclIsTypeOf(Client) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account : "(x::Account) .oclIsTypeOf(Client) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current : "(x::Current) .oclIsTypeOf(Client) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny : "(x::OclAny) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current : "(x::Current) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings : "(x::Savings) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account : "(x::Account) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank : "(x::Bank) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client : "(x::Client) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"

(* 52 ************************************ 482 + 6 *)
definition "OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_\<AA> = (\<lambda> (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Current))::Current) .oclIsTypeOf(Current))
    | (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Account))::Account) .oclIsTypeOf(Current))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsTypeOf(Current))
    | (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Savings))::Savings) .oclIsTypeOf(Current))
    | (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Bank))::Bank) .oclIsTypeOf(Current))
    | (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Client))::Client) .oclIsTypeOf(Current)))"
definition "OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_\<AA> = (\<lambda> (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Savings))::Savings) .oclIsTypeOf(Savings))
    | (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Account))::Account) .oclIsTypeOf(Savings))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsTypeOf(Savings))
    | (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Current))::Current) .oclIsTypeOf(Savings))
    | (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Bank))::Bank) .oclIsTypeOf(Savings))
    | (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Client))::Client) .oclIsTypeOf(Savings)))"
definition "OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<AA> = (\<lambda> (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Account))::Account) .oclIsTypeOf(Account))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsTypeOf(Account))
    | (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Current))::Current) .oclIsTypeOf(Account))
    | (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Savings))::Savings) .oclIsTypeOf(Account))
    | (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Bank))::Bank) .oclIsTypeOf(Account))
    | (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Client))::Client) .oclIsTypeOf(Account)))"
definition "OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_\<AA> = (\<lambda> (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Bank))::Bank) .oclIsTypeOf(Bank))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsTypeOf(Bank))
    | (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Client))::Client) .oclIsTypeOf(Bank))
    | (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Savings))::Savings) .oclIsTypeOf(Bank))
    | (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Account))::Account) .oclIsTypeOf(Bank))
    | (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Current))::Current) .oclIsTypeOf(Bank)))"
definition "OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_\<AA> = (\<lambda> (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Client))::Client) .oclIsTypeOf(Client))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsTypeOf(Client))
    | (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Bank))::Bank) .oclIsTypeOf(Client))
    | (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Savings))::Savings) .oclIsTypeOf(Client))
    | (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Account))::Account) .oclIsTypeOf(Client))
    | (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Current))::Current) .oclIsTypeOf(Client)))"
definition "OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsTypeOf(OclAny))
    | (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Current))::Current) .oclIsTypeOf(OclAny))
    | (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Savings))::Savings) .oclIsTypeOf(OclAny))
    | (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Account))::Account) .oclIsTypeOf(OclAny))
    | (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Bank))::Bank) .oclIsTypeOf(OclAny))
    | (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Client))::Client) .oclIsTypeOf(OclAny)))"

(* 53 ************************************ 488 + 1 *)
lemmas[simp,code_unfold] = OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current
                            OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings
                            OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account
                            OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank
                            OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client
                            OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny

(* 54 ************************************ 489 + 1 *)
subsection{* Context Passing *}

(* 55 ************************************ 490 + 216 *)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Savings) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Savings) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Savings) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Savings) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Savings) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Savings) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Account) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Account) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Account) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Account) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Account) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Account) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Client) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Client) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Client) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Client) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Client) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Client) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::OclAny) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::OclAny) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::OclAny) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::OclAny) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::OclAny) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Bank) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Bank) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Bank) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Bank) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Bank) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Bank) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Current) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Current) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Current) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Current) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Current) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Current) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Savings) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Savings) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Savings) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Savings) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Savings) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Savings) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Account) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Account) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Account) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Account) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Account) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Account) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Client) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Client) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Client) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Client) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Client) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Client) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::OclAny) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::OclAny) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::OclAny) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::OclAny) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::OclAny) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Bank) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Bank) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Bank) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Bank) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Bank) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Bank) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Current) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Current) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Current) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Current) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Current) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Current) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Savings) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Savings) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Savings) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Savings) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Savings) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Savings) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Account) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Account) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Account) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Account) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Account) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Account) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Client) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Client) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Client) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Client) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Client) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Client) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::OclAny) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::OclAny) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::OclAny) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::OclAny) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::OclAny) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Bank) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Bank) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Bank) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Bank) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Bank) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Bank) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Current) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Current) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Current) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Current) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Current) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Current) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Savings) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Savings) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Savings) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Savings) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Savings) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Savings) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Account) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Account) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Account) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Account) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Account) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Account) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Client) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Client) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Client) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Client) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Client) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Client) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Bank) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Bank) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Bank) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Bank) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Bank) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Bank) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Current) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Current) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Current) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Current) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Current) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Current) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Savings) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Savings) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Savings) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Savings) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Savings) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Savings) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Account) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Account) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Account) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Account) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Account) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Account) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Client) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Client) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Client) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Client) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Client) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Client) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::OclAny) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::OclAny) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::OclAny) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::OclAny) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::OclAny) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Bank) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Bank) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Bank) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Bank) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Bank) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Bank) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Current) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Current) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Current) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Current) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Current) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Current) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Savings) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Savings) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Savings) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Savings) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Savings) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Savings) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Account) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Account) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Account) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Account) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Account) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Account) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Client) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Client) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Client) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Client) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Client) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Client) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::OclAny) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::OclAny) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::OclAny) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::OclAny) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::OclAny) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Bank) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Bank) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Bank) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Bank) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Bank) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Bank) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Current) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Current) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Current) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Current) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Current) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Current) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp)

(* 56 ************************************ 706 + 1 *)
lemmas[simp,code_unfold] = cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Savings
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Savings
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Savings
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Savings
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Savings
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Savings
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Account
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Account
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Account
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Account
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Account
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Account
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Client
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Client
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Client
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Client
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Client
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Client
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_OclAny
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_OclAny
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_OclAny
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_OclAny
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_OclAny
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_OclAny
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Bank
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Bank
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Bank
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Bank
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Bank
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Bank
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Current
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Current
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Current
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Current
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Current
                            cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Current
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Savings
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Savings
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Savings
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Savings
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Savings
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Savings
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Account
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Account
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Account
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Account
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Account
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Account
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Client
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Client
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Client
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Client
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Client
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Client
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_OclAny
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_OclAny
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_OclAny
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_OclAny
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_OclAny
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_OclAny
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Bank
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Bank
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Bank
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Bank
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Bank
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Bank
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Current
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Current
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Current
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Current
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Current
                            cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Current
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Savings
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Savings
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Savings
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Savings
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Savings
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Account
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Account
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Account
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Account
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Account
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Account
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Client
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Client
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Client
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Client
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Client
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Client
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_OclAny
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_OclAny
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_OclAny
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Bank
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Bank
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Bank
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Bank
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Bank
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Current
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Current
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Current
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Current
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Current
                            cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Current
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Savings
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Savings
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Savings
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Savings
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Savings
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Savings
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Account
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Account
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Account
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Account
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Account
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Account
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Client
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Client
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Client
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Client
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Client
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Client
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_OclAny
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_OclAny
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_OclAny
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_OclAny
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_OclAny
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Bank
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Bank
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Bank
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Bank
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Bank
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Bank
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Current
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Current
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Current
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Current
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Current
                            cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Current
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Savings
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Savings
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Savings
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Savings
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Savings
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Savings
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Account
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Account
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Account
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Account
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Account
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Account
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Client
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Client
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Client
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Client
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Client
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Client
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_OclAny
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_OclAny
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_OclAny
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_OclAny
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_OclAny
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_OclAny
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Bank
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Bank
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Bank
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Bank
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Bank
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Bank
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Current
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Current
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Current
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Current
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Current
                            cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Current
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Savings
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Savings
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Savings
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Savings
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Savings
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Account
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Account
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Account
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Account
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Account
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Account
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Client
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Client
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Client
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Client
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Client
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Client
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_OclAny
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_OclAny
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_OclAny
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Bank
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Bank
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Bank
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Bank
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Bank
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Current
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Current
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Current
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Current
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Current
                            cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Current

(* 57 ************************************ 707 + 1 *)
subsection{* Execution with Invalid or Null as Argument *}

(* 58 ************************************ 708 + 72 *)
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_invalid : "((invalid::Savings) .oclIsTypeOf(Savings)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_invalid : "((invalid::Account) .oclIsTypeOf(Savings)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_invalid : "((invalid::Client) .oclIsTypeOf(Savings)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_invalid : "((invalid::OclAny) .oclIsTypeOf(Savings)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_invalid : "((invalid::Bank) .oclIsTypeOf(Savings)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_invalid : "((invalid::Current) .oclIsTypeOf(Savings)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_null : "((null::Savings) .oclIsTypeOf(Savings)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_null : "((null::Account) .oclIsTypeOf(Savings)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_null : "((null::Client) .oclIsTypeOf(Savings)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_null : "((null::OclAny) .oclIsTypeOf(Savings)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_null : "((null::Bank) .oclIsTypeOf(Savings)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_null : "((null::Current) .oclIsTypeOf(Savings)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_invalid : "((invalid::Savings) .oclIsTypeOf(Account)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_invalid : "((invalid::Account) .oclIsTypeOf(Account)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_invalid : "((invalid::Client) .oclIsTypeOf(Account)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_invalid : "((invalid::OclAny) .oclIsTypeOf(Account)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_invalid : "((invalid::Bank) .oclIsTypeOf(Account)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_invalid : "((invalid::Current) .oclIsTypeOf(Account)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_null : "((null::Savings) .oclIsTypeOf(Account)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_null : "((null::Account) .oclIsTypeOf(Account)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_null : "((null::Client) .oclIsTypeOf(Account)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_null : "((null::OclAny) .oclIsTypeOf(Account)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_null : "((null::Bank) .oclIsTypeOf(Account)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_null : "((null::Current) .oclIsTypeOf(Account)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_invalid : "((invalid::Savings) .oclIsTypeOf(Client)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_invalid : "((invalid::Account) .oclIsTypeOf(Client)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_invalid : "((invalid::Client) .oclIsTypeOf(Client)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid : "((invalid::OclAny) .oclIsTypeOf(Client)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_invalid : "((invalid::Bank) .oclIsTypeOf(Client)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_invalid : "((invalid::Current) .oclIsTypeOf(Client)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_null : "((null::Savings) .oclIsTypeOf(Client)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_null : "((null::Account) .oclIsTypeOf(Client)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_null : "((null::Client) .oclIsTypeOf(Client)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_null : "((null::OclAny) .oclIsTypeOf(Client)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_null : "((null::Bank) .oclIsTypeOf(Client)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_null : "((null::Current) .oclIsTypeOf(Client)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_invalid : "((invalid::Savings) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_invalid : "((invalid::Account) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_invalid : "((invalid::Client) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid : "((invalid::OclAny) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_invalid : "((invalid::Bank) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_invalid : "((invalid::Current) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_null : "((null::Savings) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_null : "((null::Account) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_null : "((null::Client) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null : "((null::OclAny) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_null : "((null::Bank) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_null : "((null::Current) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_invalid : "((invalid::Savings) .oclIsTypeOf(Bank)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_invalid : "((invalid::Account) .oclIsTypeOf(Bank)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_invalid : "((invalid::Client) .oclIsTypeOf(Bank)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_invalid : "((invalid::OclAny) .oclIsTypeOf(Bank)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_invalid : "((invalid::Bank) .oclIsTypeOf(Bank)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_invalid : "((invalid::Current) .oclIsTypeOf(Bank)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_null : "((null::Savings) .oclIsTypeOf(Bank)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_null : "((null::Account) .oclIsTypeOf(Bank)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_null : "((null::Client) .oclIsTypeOf(Bank)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_null : "((null::OclAny) .oclIsTypeOf(Bank)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_null : "((null::Bank) .oclIsTypeOf(Bank)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_null : "((null::Current) .oclIsTypeOf(Bank)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_invalid : "((invalid::Savings) .oclIsTypeOf(Current)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_invalid : "((invalid::Account) .oclIsTypeOf(Current)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_invalid : "((invalid::Client) .oclIsTypeOf(Current)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid : "((invalid::OclAny) .oclIsTypeOf(Current)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_invalid : "((invalid::Bank) .oclIsTypeOf(Current)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_invalid : "((invalid::Current) .oclIsTypeOf(Current)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_null : "((null::Savings) .oclIsTypeOf(Current)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_null : "((null::Account) .oclIsTypeOf(Current)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_null : "((null::Client) .oclIsTypeOf(Current)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_null : "((null::OclAny) .oclIsTypeOf(Current)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_null : "((null::Bank) .oclIsTypeOf(Current)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_null : "((null::Current) .oclIsTypeOf(Current)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)

(* 59 ************************************ 780 + 1 *)
lemmas[simp,code_unfold] = OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_invalid
                            OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_invalid
                            OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_invalid
                            OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_invalid
                            OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_invalid
                            OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_invalid
                            OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_null
                            OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_null
                            OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_null
                            OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_null
                            OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_null
                            OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_null
                            OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_invalid
                            OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_invalid
                            OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_invalid
                            OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_invalid
                            OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_invalid
                            OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_invalid
                            OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_null
                            OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_null
                            OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_null
                            OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_null
                            OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_null
                            OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_null
                            OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_invalid
                            OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_invalid
                            OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_invalid
                            OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid
                            OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_invalid
                            OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_invalid
                            OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_null
                            OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_null
                            OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_null
                            OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_null
                            OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_null
                            OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_null
                            OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_invalid
                            OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_invalid
                            OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_invalid
                            OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid
                            OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_invalid
                            OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_invalid
                            OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_null
                            OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_null
                            OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_null
                            OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null
                            OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_null
                            OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_null
                            OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_invalid
                            OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_invalid
                            OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_invalid
                            OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_invalid
                            OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_invalid
                            OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_invalid
                            OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_null
                            OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_null
                            OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_null
                            OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_null
                            OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_null
                            OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_null
                            OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_invalid
                            OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_invalid
                            OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_invalid
                            OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid
                            OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_invalid
                            OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_invalid
                            OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_null
                            OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_null
                            OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_null
                            OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_null
                            OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_null
                            OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_null

(* 60 ************************************ 781 + 1 *)
subsection{* Validity and Definedness Properties *}

(* 61 ************************************ 782 + 36 *)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclIsTypeOf(Current)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Account) .oclIsTypeOf(Current)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account split: option.split ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(Current)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny split: option.split ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split) 
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclIsTypeOf(Current)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings split: option.split ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split) 
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Bank) .oclIsTypeOf(Current)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank split: option.split ty\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split) 
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Client) .oclIsTypeOf(Current)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclIsTypeOf(Savings)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings split: option.split ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split) 
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Account) .oclIsTypeOf(Savings)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account split: option.split ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(Savings)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny split: option.split ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split) 
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclIsTypeOf(Savings)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Bank) .oclIsTypeOf(Savings)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank split: option.split ty\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split) 
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Client) .oclIsTypeOf(Savings)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Account) .oclIsTypeOf(Account)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account split: option.split ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(Account)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny split: option.split ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split) 
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclIsTypeOf(Account)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclIsTypeOf(Account)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings split: option.split ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split) 
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Bank) .oclIsTypeOf(Account)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank split: option.split ty\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split) 
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Client) .oclIsTypeOf(Account)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Bank) .oclIsTypeOf(Bank)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank split: option.split ty\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split) 
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(Bank)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny split: option.split ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split) 
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Client) .oclIsTypeOf(Bank)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclIsTypeOf(Bank)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings split: option.split ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split) 
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Account) .oclIsTypeOf(Bank)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account split: option.split ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclIsTypeOf(Bank)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Client) .oclIsTypeOf(Client)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(Client)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny split: option.split ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split) 
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Bank) .oclIsTypeOf(Client)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank split: option.split ty\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split) 
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclIsTypeOf(Client)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings split: option.split ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split) 
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Account) .oclIsTypeOf(Client)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account split: option.split ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclIsTypeOf(Client)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(OclAny)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny split: option.split ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclIsTypeOf(OclAny)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclIsTypeOf(OclAny)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings split: option.split ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Account) .oclIsTypeOf(OclAny)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account split: option.split ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Bank) .oclIsTypeOf(OclAny)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank split: option.split ty\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Client) .oclIsTypeOf(OclAny)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split) 

(* 62 ************************************ 818 + 36 *)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclIsTypeOf(Current)))"
by(rule OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Account) .oclIsTypeOf(Current)))"
by(rule OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(Current)))"
by(rule OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclIsTypeOf(Current)))"
by(rule OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Bank) .oclIsTypeOf(Current)))"
by(rule OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Client) .oclIsTypeOf(Current)))"
by(rule OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclIsTypeOf(Savings)))"
by(rule OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Account) .oclIsTypeOf(Savings)))"
by(rule OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(Savings)))"
by(rule OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclIsTypeOf(Savings)))"
by(rule OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Bank) .oclIsTypeOf(Savings)))"
by(rule OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Client) .oclIsTypeOf(Savings)))"
by(rule OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Account) .oclIsTypeOf(Account)))"
by(rule OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(Account)))"
by(rule OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclIsTypeOf(Account)))"
by(rule OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclIsTypeOf(Account)))"
by(rule OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Bank) .oclIsTypeOf(Account)))"
by(rule OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Client) .oclIsTypeOf(Account)))"
by(rule OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Bank) .oclIsTypeOf(Bank)))"
by(rule OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(Bank)))"
by(rule OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Client) .oclIsTypeOf(Bank)))"
by(rule OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclIsTypeOf(Bank)))"
by(rule OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Account) .oclIsTypeOf(Bank)))"
by(rule OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclIsTypeOf(Bank)))"
by(rule OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Client) .oclIsTypeOf(Client)))"
by(rule OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(Client)))"
by(rule OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Bank) .oclIsTypeOf(Client)))"
by(rule OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclIsTypeOf(Client)))"
by(rule OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Account) .oclIsTypeOf(Client)))"
by(rule OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclIsTypeOf(Client)))"
by(rule OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsTypeOf(OclAny)))"
by(rule OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclIsTypeOf(OclAny)))"
by(rule OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclIsTypeOf(OclAny)))"
by(rule OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Account) .oclIsTypeOf(OclAny)))"
by(rule OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Bank) .oclIsTypeOf(OclAny)))"
by(rule OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Client) .oclIsTypeOf(OclAny)))"
by(rule OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_defined[OF isdef[THEN foundation20]]) 

(* 63 ************************************ 854 + 1 *)
subsection{* Up Down Casting *}

(* 64 ************************************ 855 + 23 *)
lemma actualType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_larger_staticType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Current) .oclIsTypeOf(Account)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_larger_staticType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Current) .oclIsTypeOf(OclAny)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_larger_staticType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Current) .oclIsTypeOf(Savings)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_larger_staticType\<^sub>B\<^sub>a\<^sub>n\<^sub>k : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Current) .oclIsTypeOf(Bank)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_larger_staticType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Current) .oclIsTypeOf(Client)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_larger_staticType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Savings) .oclIsTypeOf(Account)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_larger_staticType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Savings) .oclIsTypeOf(OclAny)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_larger_staticType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Savings) .oclIsTypeOf(Current)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_larger_staticType\<^sub>B\<^sub>a\<^sub>n\<^sub>k : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Savings) .oclIsTypeOf(Bank)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_larger_staticType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Savings) .oclIsTypeOf(Client)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_larger_staticType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Account) .oclIsTypeOf(OclAny)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_larger_staticType\<^sub>B\<^sub>a\<^sub>n\<^sub>k : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Account) .oclIsTypeOf(Bank)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_larger_staticType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Account) .oclIsTypeOf(Client)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_larger_staticType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Bank) .oclIsTypeOf(OclAny)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_larger_staticType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Bank) .oclIsTypeOf(Client)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_larger_staticType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Bank) .oclIsTypeOf(Savings)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_larger_staticType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Bank) .oclIsTypeOf(Account)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_larger_staticType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Bank) .oclIsTypeOf(Current)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_larger_staticType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Client) .oclIsTypeOf(OclAny)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_larger_staticType\<^sub>B\<^sub>a\<^sub>n\<^sub>k : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Client) .oclIsTypeOf(Bank)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_larger_staticType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Client) .oclIsTypeOf(Savings)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_larger_staticType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Client) .oclIsTypeOf(Account)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_larger_staticType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Client) .oclIsTypeOf(Current)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client foundation22 foundation16 null_option_def bot_option_def) 

(* 65 ************************************ 878 + 31 *)
lemma down_cast_type\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_from_Account_to_Current : 
assumes istyp: "\<tau> \<Turnstile> ((X::Account) .oclIsTypeOf(Account))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Current)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split)
by(simp add: OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Current : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(OclAny))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Current)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_from_OclAny_to_Current : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Account))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Current)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_from_Account_to_Current : 
assumes istyp: "\<tau> \<Turnstile> ((X::Account) .oclIsTypeOf(Savings))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Current)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split)
by(simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>B\<^sub>a\<^sub>n\<^sub>k_from_Account_to_Current : 
assumes istyp: "\<tau> \<Turnstile> ((X::Account) .oclIsTypeOf(Bank))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Current)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split)
by(simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_from_Account_to_Current : 
assumes istyp: "\<tau> \<Turnstile> ((X::Account) .oclIsTypeOf(Client))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Current)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split)
by(simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_from_OclAny_to_Current : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Savings))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Current)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>B\<^sub>a\<^sub>n\<^sub>k_from_OclAny_to_Current : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Bank))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Current)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Current : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Client))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Current)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_from_Account_to_Savings : 
assumes istyp: "\<tau> \<Turnstile> ((X::Account) .oclIsTypeOf(Account))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Savings)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split)
by(simp add: OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Savings : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(OclAny))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Savings)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_from_OclAny_to_Savings : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Account))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Savings)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_from_Account_to_Savings : 
assumes istyp: "\<tau> \<Turnstile> ((X::Account) .oclIsTypeOf(Current))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Savings)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split)
by(simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>B\<^sub>a\<^sub>n\<^sub>k_from_Account_to_Savings : 
assumes istyp: "\<tau> \<Turnstile> ((X::Account) .oclIsTypeOf(Bank))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Savings)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split)
by(simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_from_Account_to_Savings : 
assumes istyp: "\<tau> \<Turnstile> ((X::Account) .oclIsTypeOf(Client))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Savings)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split)
by(simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Savings : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Current))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Savings)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>B\<^sub>a\<^sub>n\<^sub>k_from_OclAny_to_Savings : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Bank))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Savings)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Savings : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Client))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Savings)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Account : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(OclAny))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Account)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>B\<^sub>a\<^sub>n\<^sub>k_from_OclAny_to_Account : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Bank))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Account)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Account : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Client))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Account)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Bank : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(OclAny))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Bank)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Bank : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Client))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Bank)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_from_OclAny_to_Bank : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Savings))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Bank)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_from_OclAny_to_Bank : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Account))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Bank)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Bank : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Current))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Bank)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Client : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(OclAny))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Client)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>B\<^sub>a\<^sub>n\<^sub>k_from_OclAny_to_Client : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Bank))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Client)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_from_OclAny_to_Client : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Savings))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Client)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_from_OclAny_to_Client : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Account))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Client)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Client : 
assumes istyp: "\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Current))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Client)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny OclValid_def false_def true_def) 

(* 66 ************************************ 909 + 1 *)
section{* OclIsKindOf *}

(* 67 ************************************ 910 + 1 *)
subsection{* Definition *}

(* 68 ************************************ 911 + 6 *)
consts OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Current')")
consts OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Savings')")
consts OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Account')")
consts OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Bank')")
consts OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Client')")
consts OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(OclAny')")

(* 69 ************************************ 917 + 36 *)
defs(overloaded) OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current : "(x::Current) .oclIsKindOf(Current) \<equiv> (x .oclIsTypeOf(Current))"
defs(overloaded) OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account : "(x::Account) .oclIsKindOf(Current) \<equiv> (x .oclIsTypeOf(Current))"
defs(overloaded) OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny : "(x::OclAny) .oclIsKindOf(Current) \<equiv> (x .oclIsTypeOf(Current))"
defs(overloaded) OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings : "(x::Savings) .oclIsKindOf(Current) \<equiv> (x .oclIsTypeOf(Current))"
defs(overloaded) OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank : "(x::Bank) .oclIsKindOf(Current) \<equiv> (x .oclIsTypeOf(Current))"
defs(overloaded) OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client : "(x::Client) .oclIsKindOf(Current) \<equiv> (x .oclIsTypeOf(Current))"
defs(overloaded) OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings : "(x::Savings) .oclIsKindOf(Savings) \<equiv> (x .oclIsTypeOf(Savings))"
defs(overloaded) OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account : "(x::Account) .oclIsKindOf(Savings) \<equiv> (x .oclIsTypeOf(Savings))"
defs(overloaded) OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny : "(x::OclAny) .oclIsKindOf(Savings) \<equiv> (x .oclIsTypeOf(Savings))"
defs(overloaded) OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current : "(x::Current) .oclIsKindOf(Savings) \<equiv> (x .oclIsTypeOf(Savings))"
defs(overloaded) OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank : "(x::Bank) .oclIsKindOf(Savings) \<equiv> (x .oclIsTypeOf(Savings))"
defs(overloaded) OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client : "(x::Client) .oclIsKindOf(Savings) \<equiv> (x .oclIsTypeOf(Savings))"
defs(overloaded) OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account : "(x::Account) .oclIsKindOf(Account) \<equiv> (x .oclIsTypeOf(Account)) or (x .oclIsKindOf(Savings)) or (x .oclIsKindOf(Current))"
defs(overloaded) OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny : "(x::OclAny) .oclIsKindOf(Account) \<equiv> (x .oclIsTypeOf(Account)) or (x .oclIsKindOf(Savings)) or (x .oclIsKindOf(Current))"
defs(overloaded) OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current : "(x::Current) .oclIsKindOf(Account) \<equiv> (x .oclIsTypeOf(Account)) or (x .oclIsKindOf(Savings)) or (x .oclIsKindOf(Current))"
defs(overloaded) OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings : "(x::Savings) .oclIsKindOf(Account) \<equiv> (x .oclIsTypeOf(Account)) or (x .oclIsKindOf(Savings)) or (x .oclIsKindOf(Current))"
defs(overloaded) OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank : "(x::Bank) .oclIsKindOf(Account) \<equiv> (x .oclIsTypeOf(Account)) or (x .oclIsKindOf(Savings)) or (x .oclIsKindOf(Current))"
defs(overloaded) OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client : "(x::Client) .oclIsKindOf(Account) \<equiv> (x .oclIsTypeOf(Account)) or (x .oclIsKindOf(Savings)) or (x .oclIsKindOf(Current))"
defs(overloaded) OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank : "(x::Bank) .oclIsKindOf(Bank) \<equiv> (x .oclIsTypeOf(Bank))"
defs(overloaded) OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny : "(x::OclAny) .oclIsKindOf(Bank) \<equiv> (x .oclIsTypeOf(Bank))"
defs(overloaded) OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client : "(x::Client) .oclIsKindOf(Bank) \<equiv> (x .oclIsTypeOf(Bank))"
defs(overloaded) OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings : "(x::Savings) .oclIsKindOf(Bank) \<equiv> (x .oclIsTypeOf(Bank))"
defs(overloaded) OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account : "(x::Account) .oclIsKindOf(Bank) \<equiv> (x .oclIsTypeOf(Bank))"
defs(overloaded) OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current : "(x::Current) .oclIsKindOf(Bank) \<equiv> (x .oclIsTypeOf(Bank))"
defs(overloaded) OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client : "(x::Client) .oclIsKindOf(Client) \<equiv> (x .oclIsTypeOf(Client))"
defs(overloaded) OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny : "(x::OclAny) .oclIsKindOf(Client) \<equiv> (x .oclIsTypeOf(Client))"
defs(overloaded) OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank : "(x::Bank) .oclIsKindOf(Client) \<equiv> (x .oclIsTypeOf(Client))"
defs(overloaded) OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings : "(x::Savings) .oclIsKindOf(Client) \<equiv> (x .oclIsTypeOf(Client))"
defs(overloaded) OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account : "(x::Account) .oclIsKindOf(Client) \<equiv> (x .oclIsTypeOf(Client))"
defs(overloaded) OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current : "(x::Current) .oclIsKindOf(Client) \<equiv> (x .oclIsTypeOf(Client))"
defs(overloaded) OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny : "(x::OclAny) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Client)) or (x .oclIsKindOf(Bank)) or (x .oclIsKindOf(Account))"
defs(overloaded) OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current : "(x::Current) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Client)) or (x .oclIsKindOf(Bank)) or (x .oclIsKindOf(Account))"
defs(overloaded) OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings : "(x::Savings) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Client)) or (x .oclIsKindOf(Bank)) or (x .oclIsKindOf(Account))"
defs(overloaded) OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account : "(x::Account) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Client)) or (x .oclIsKindOf(Bank)) or (x .oclIsKindOf(Account))"
defs(overloaded) OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank : "(x::Bank) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Client)) or (x .oclIsKindOf(Bank)) or (x .oclIsKindOf(Account))"
defs(overloaded) OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client : "(x::Client) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Client)) or (x .oclIsKindOf(Bank)) or (x .oclIsKindOf(Account))"

(* 70 ************************************ 953 + 6 *)
definition "OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_\<AA> = (\<lambda> (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Current))::Current) .oclIsKindOf(Current))
    | (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Account))::Account) .oclIsKindOf(Current))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsKindOf(Current))
    | (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Savings))::Savings) .oclIsKindOf(Current))
    | (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Bank))::Bank) .oclIsKindOf(Current))
    | (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Client))::Client) .oclIsKindOf(Current)))"
definition "OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_\<AA> = (\<lambda> (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Savings))::Savings) .oclIsKindOf(Savings))
    | (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Account))::Account) .oclIsKindOf(Savings))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsKindOf(Savings))
    | (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Current))::Current) .oclIsKindOf(Savings))
    | (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Bank))::Bank) .oclIsKindOf(Savings))
    | (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Client))::Client) .oclIsKindOf(Savings)))"
definition "OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<AA> = (\<lambda> (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Account))::Account) .oclIsKindOf(Account))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsKindOf(Account))
    | (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Current))::Current) .oclIsKindOf(Account))
    | (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Savings))::Savings) .oclIsKindOf(Account))
    | (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Bank))::Bank) .oclIsKindOf(Account))
    | (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Client))::Client) .oclIsKindOf(Account)))"
definition "OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_\<AA> = (\<lambda> (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Bank))::Bank) .oclIsKindOf(Bank))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsKindOf(Bank))
    | (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Client))::Client) .oclIsKindOf(Bank))
    | (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Savings))::Savings) .oclIsKindOf(Bank))
    | (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Account))::Account) .oclIsKindOf(Bank))
    | (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Current))::Current) .oclIsKindOf(Bank)))"
definition "OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_\<AA> = (\<lambda> (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Client))::Client) .oclIsKindOf(Client))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsKindOf(Client))
    | (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Bank))::Bank) .oclIsKindOf(Client))
    | (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Savings))::Savings) .oclIsKindOf(Client))
    | (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Account))::Account) .oclIsKindOf(Client))
    | (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Current))::Current) .oclIsKindOf(Client)))"
definition "OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::OclAny) .oclIsKindOf(OclAny))
    | (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Current))::Current) .oclIsKindOf(OclAny))
    | (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Savings))::Savings) .oclIsKindOf(OclAny))
    | (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Account))::Account) .oclIsKindOf(OclAny))
    | (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Bank))::Bank) .oclIsKindOf(OclAny))
    | (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Client))::Client) .oclIsKindOf(OclAny)))"

(* 71 ************************************ 959 + 1 *)
lemmas[simp,code_unfold] = OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current
                            OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings
                            OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account
                            OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank
                            OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client
                            OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny

(* 72 ************************************ 960 + 1 *)
subsection{* Context Passing *}

(* 73 ************************************ 961 + 216 *)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Current) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Current)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Current) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Current)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Current) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Current)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Current) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Current)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Current) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Current)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Current) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Current)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Account) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Account)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Account) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Account)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Account) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Account)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Account) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Account)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Account) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Account)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Account) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Account)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::OclAny) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_OclAny)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::OclAny) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_OclAny)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::OclAny) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::OclAny) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::OclAny) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_OclAny)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Savings) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Savings)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Savings) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Savings)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Savings) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Savings) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Savings)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Savings) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Savings)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Savings) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Savings)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Bank) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Bank)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Bank) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Bank)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Bank) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Bank) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Bank)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Bank) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Bank)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Bank) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Bank)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Client) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Client)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Client) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Client)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Client) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Client)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Client) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Client)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Client) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Client)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Client) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Client)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Savings) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Savings)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Savings) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Savings)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Savings) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Savings)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Savings) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Savings)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Savings) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Savings)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Savings) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Savings)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Account) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Account)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Account) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Account)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Account) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Account)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Account) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Account)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Account) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Account)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Account) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Account)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::OclAny) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_OclAny)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::OclAny) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_OclAny)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::OclAny) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_OclAny)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::OclAny) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_OclAny)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::OclAny) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_OclAny)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Current) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Current)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Current) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Current)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Current) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Current)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Current) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Current)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Current) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Current)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Current) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Current)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Bank) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Bank)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Bank) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Bank)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Bank) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Bank)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Bank) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Bank)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Bank) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Bank)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Bank) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Bank)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Client) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Client)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Client) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Client)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Client) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Client)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Client) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Client)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Client) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Client)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Client) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Client)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Account) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Account)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Account, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Account)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Account) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Account)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Account, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Account)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Account) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Account)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Account, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Account)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Account) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Account)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Account, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Account)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Account) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Account)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Account, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Account)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Account) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Account)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Account, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Account)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::OclAny) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_OclAny, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_OclAny)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_OclAny, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::OclAny) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_OclAny, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_OclAny)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::OclAny) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_OclAny, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::OclAny) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_OclAny, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::OclAny) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_OclAny, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_OclAny)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Current) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Current)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Current, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Current)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Current) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Current)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Current, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Current)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Current) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Current)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Current, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Current)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Current) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Current)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Current, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Current)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Current) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Current)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Current, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Current)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Current) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Current)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Current, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Current)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Savings) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Savings)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Savings, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Savings)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Savings) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Savings)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Savings, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Savings) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Savings)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Savings, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Savings)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Savings) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Savings)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Savings, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Savings)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Savings) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Savings)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Savings, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Savings)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Savings) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Savings)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Savings, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Savings)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Bank) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Bank)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Bank, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Bank)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Bank) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Bank)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Bank, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Bank) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Bank)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Bank, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Bank)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Bank) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Bank)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Bank, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Bank)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Bank) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Bank)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Bank, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Bank)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Bank) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Bank)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Bank, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Bank)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Client) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Client)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Client, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Client)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Client) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Client)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Client, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Client)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Client) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Client)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Client, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Client)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Client) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Client)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Client, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Client)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Client) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Client)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Client, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Client)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Client) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Client)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Client, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Client)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Bank) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Bank)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Bank) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Bank)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Bank) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Bank)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Bank) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Bank)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Bank) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Bank)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Bank) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Bank)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::OclAny) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_OclAny)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::OclAny) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_OclAny)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::OclAny) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_OclAny)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::OclAny) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_OclAny)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::OclAny) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_OclAny)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Client) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Client)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Client) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Client)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Client) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Client)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Client) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Client)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Client) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Client)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Client) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Client)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Savings) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Savings)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Savings) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Savings)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Savings) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Savings)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Savings) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Savings)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Savings) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Savings)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Savings) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Savings)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Account) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Account)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Account) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Account)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Account) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Account)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Account) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Account)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Account) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Account)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Account) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Account)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Current) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Current)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Current) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Current)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Current) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Current)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Current) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Current)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Current) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Current)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Current) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Current)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Client) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Client)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Client) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Client)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Client) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Client)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Client) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Client)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Client) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Client)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Client) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Client)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::OclAny) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_OclAny)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::OclAny) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::OclAny) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::OclAny) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_OclAny)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::OclAny) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_OclAny)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Bank) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Bank)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Bank) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Bank) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Bank)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Bank) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Bank)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Bank) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Bank)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Bank) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Bank)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Savings) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Savings)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Savings) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Savings) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Savings)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Savings) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Savings)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Savings) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Savings)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Savings) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Savings)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Account) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Account)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Account) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Account)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Account) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Account)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Account) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Account)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Account) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Account)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Account) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Account)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Current) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Current)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Current) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Current)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Current) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Current)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Current) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Current)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Current) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Current)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Current) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Current)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_OclAny, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_OclAny, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_OclAny, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_OclAny, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_OclAny, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_OclAny, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_OclAny, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_OclAny, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_OclAny, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Current) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Current)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Current, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Current, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Current)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Current) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Current)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Current, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Current, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Current)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Current) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Current)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Current, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Current, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Current)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Current) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Current)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Current, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Current, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Current)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Current) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Current)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Current, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Current, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Current)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Current) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Current)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Current, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Current, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Current)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Savings) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Savings)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Savings, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Savings)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Savings) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Savings)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Savings, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Savings, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Savings)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Savings) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Savings)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Savings, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Savings, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Savings)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Savings) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Savings)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Savings, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Savings, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Savings)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Savings) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Savings)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Savings, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Savings, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Savings)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Savings) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Savings)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Savings, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Savings, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Savings)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Account) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Account)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Account, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Account, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Account)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Account) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Account)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Account, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Account, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Account)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Account) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Account)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Account, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Account, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Account)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Account) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Account)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Account, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Account, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Account)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Account) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Account)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Account, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Account, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Account)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Account) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Account)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Account, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Account, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Account)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Bank) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Bank)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Bank, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Bank)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Bank) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Bank)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Bank, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Bank, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Bank)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Bank) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Bank)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Bank, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Bank, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Bank)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Bank) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Bank)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Bank, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Bank, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Bank)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Bank) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Bank)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Bank, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Bank, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Bank)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Bank) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Bank)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Bank, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Bank, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Bank)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::OclAny)))::Client) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Client)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Client, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Client, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Client)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Current)))::Client) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Client)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Client, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Client, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Client)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Savings)))::Client) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Client)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Client, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Client, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Client)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Account)))::Client) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Client)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Client, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Client, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Client)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Bank)))::Client) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Client)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Client, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Client, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Client)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::Client)))::Client) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Client)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Client, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Client, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Client)

(* 74 ************************************ 1177 + 1 *)
lemmas[simp,code_unfold] = cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Savings
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Savings
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Savings
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Savings
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Savings
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Savings
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Account
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Account
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Account
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Account
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Account
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Account
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Client
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Client
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Client
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Client
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Client
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Client
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_OclAny
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_OclAny
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_OclAny
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_OclAny
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_OclAny
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_OclAny
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Bank
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Bank
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Bank
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Bank
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Bank
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Bank
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Current
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Current
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Current
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Current
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Current
                            cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Current
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Savings
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Savings
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Savings
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Savings
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Savings
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Savings
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Account
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Account
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Account
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Account
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Account
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Account
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Client
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Client
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Client
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Client
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Client
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Client
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_OclAny
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_OclAny
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_OclAny
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_OclAny
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_OclAny
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_OclAny
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Bank
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Bank
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Bank
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Bank
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Bank
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Bank
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Current
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Current
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Current
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Current
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Current
                            cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Current
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Savings
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Savings
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Savings
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Savings
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Savings
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Account
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Account
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Account
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Account
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Account
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Account
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Client
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Client
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Client
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Client
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Client
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Client
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_OclAny
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_OclAny
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_OclAny
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Bank
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Bank
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Bank
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Bank
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Bank
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Current
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Current
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Current
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Current
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Current
                            cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Current
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Savings
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Savings
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Savings
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Savings
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Savings
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Savings
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Account
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Account
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Account
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Account
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Account
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Account
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Client
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Client
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Client
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Client
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Client
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Client
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_OclAny
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_OclAny
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_OclAny
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_OclAny
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_OclAny
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Bank
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Bank
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Bank
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Bank
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Bank
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Bank
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Current
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Current
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Current
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Current
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Current
                            cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Current
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Savings
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Savings
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Savings
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Savings
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Savings
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Savings
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Account
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Account
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Account
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Account
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Account
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Account
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Client
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Client
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Client
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Client
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Client
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Client
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_OclAny
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_OclAny
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_OclAny
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_OclAny
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_OclAny
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_OclAny
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Bank
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Bank
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Bank
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Bank
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Bank
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Bank
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Current
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Current
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Current
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Current
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Current
                            cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Current
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Savings
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Savings
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Savings
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Savings
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Savings
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Account
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Account
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Account
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Account
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Account
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Account
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Client
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Client
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Client
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Client
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Client
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Client
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_OclAny
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_OclAny
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_OclAny
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Bank
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Bank
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Bank
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Bank
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Bank
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Current
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Current
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Current
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Current
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Current
                            cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Current

(* 75 ************************************ 1178 + 1 *)
subsection{* Execution with Invalid or Null as Argument *}

(* 76 ************************************ 1179 + 72 *)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_invalid : "((invalid::Current) .oclIsKindOf(Current)) = invalid"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_invalid)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_null : "((null::Current) .oclIsKindOf(Current)) = true"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_null)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_invalid : "((invalid::Account) .oclIsKindOf(Current)) = invalid"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_invalid)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_null : "((null::Account) .oclIsKindOf(Current)) = true"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_null)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid : "((invalid::OclAny) .oclIsKindOf(Current)) = invalid"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_null : "((null::OclAny) .oclIsKindOf(Current)) = true"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_null)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_invalid : "((invalid::Savings) .oclIsKindOf(Current)) = invalid"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_invalid)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_null : "((null::Savings) .oclIsKindOf(Current)) = true"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_null)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_invalid : "((invalid::Bank) .oclIsKindOf(Current)) = invalid"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_invalid)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_null : "((null::Bank) .oclIsKindOf(Current)) = true"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_null)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_invalid : "((invalid::Client) .oclIsKindOf(Current)) = invalid"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_invalid)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_null : "((null::Client) .oclIsKindOf(Current)) = true"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_null)
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_invalid : "((invalid::Savings) .oclIsKindOf(Savings)) = invalid"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_invalid)
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_null : "((null::Savings) .oclIsKindOf(Savings)) = true"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_null)
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_invalid : "((invalid::Account) .oclIsKindOf(Savings)) = invalid"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_invalid)
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_null : "((null::Account) .oclIsKindOf(Savings)) = true"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_null)
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_invalid : "((invalid::OclAny) .oclIsKindOf(Savings)) = invalid"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_invalid)
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_null : "((null::OclAny) .oclIsKindOf(Savings)) = true"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_null)
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_invalid : "((invalid::Current) .oclIsKindOf(Savings)) = invalid"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_invalid)
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_null : "((null::Current) .oclIsKindOf(Savings)) = true"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_null)
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_invalid : "((invalid::Bank) .oclIsKindOf(Savings)) = invalid"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_invalid)
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_null : "((null::Bank) .oclIsKindOf(Savings)) = true"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_null)
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_invalid : "((invalid::Client) .oclIsKindOf(Savings)) = invalid"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_invalid)
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_null : "((null::Client) .oclIsKindOf(Savings)) = true"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_null)
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_invalid : "((invalid::Account) .oclIsKindOf(Account)) = invalid"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_invalid OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_invalid OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_invalid, simp)
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_null : "((null::Account) .oclIsKindOf(Account)) = true"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_null OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_null OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_null, simp)
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_invalid : "((invalid::OclAny) .oclIsKindOf(Account)) = invalid"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_invalid OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_invalid OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid, simp)
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_null : "((null::OclAny) .oclIsKindOf(Account)) = true"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_null OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_null OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_null, simp)
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_invalid : "((invalid::Current) .oclIsKindOf(Account)) = invalid"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_invalid OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_invalid OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_invalid, simp)
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_null : "((null::Current) .oclIsKindOf(Account)) = true"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_null OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_null OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_null, simp)
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_invalid : "((invalid::Savings) .oclIsKindOf(Account)) = invalid"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_invalid OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_invalid OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_invalid, simp)
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_null : "((null::Savings) .oclIsKindOf(Account)) = true"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_null OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_null OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_null, simp)
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_invalid : "((invalid::Bank) .oclIsKindOf(Account)) = invalid"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_invalid OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_invalid OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_invalid, simp)
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_null : "((null::Bank) .oclIsKindOf(Account)) = true"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_null OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_null OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_null, simp)
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_invalid : "((invalid::Client) .oclIsKindOf(Account)) = invalid"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_invalid OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_invalid OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_invalid, simp)
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_null : "((null::Client) .oclIsKindOf(Account)) = true"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_null OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_null OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_null, simp)
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_invalid : "((invalid::Bank) .oclIsKindOf(Bank)) = invalid"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_invalid)
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_null : "((null::Bank) .oclIsKindOf(Bank)) = true"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_null)
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_invalid : "((invalid::OclAny) .oclIsKindOf(Bank)) = invalid"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_invalid)
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_null : "((null::OclAny) .oclIsKindOf(Bank)) = true"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_null)
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_invalid : "((invalid::Client) .oclIsKindOf(Bank)) = invalid"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_invalid)
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_null : "((null::Client) .oclIsKindOf(Bank)) = true"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_null)
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_invalid : "((invalid::Savings) .oclIsKindOf(Bank)) = invalid"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_invalid)
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_null : "((null::Savings) .oclIsKindOf(Bank)) = true"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_null)
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_invalid : "((invalid::Account) .oclIsKindOf(Bank)) = invalid"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_invalid)
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_null : "((null::Account) .oclIsKindOf(Bank)) = true"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_null)
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_invalid : "((invalid::Current) .oclIsKindOf(Bank)) = invalid"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_invalid)
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_null : "((null::Current) .oclIsKindOf(Bank)) = true"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_null)
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_invalid : "((invalid::Client) .oclIsKindOf(Client)) = invalid"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_invalid)
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_null : "((null::Client) .oclIsKindOf(Client)) = true"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_null)
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid : "((invalid::OclAny) .oclIsKindOf(Client)) = invalid"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid)
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_null : "((null::OclAny) .oclIsKindOf(Client)) = true"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_null)
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_invalid : "((invalid::Bank) .oclIsKindOf(Client)) = invalid"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_invalid)
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_null : "((null::Bank) .oclIsKindOf(Client)) = true"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_null)
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_invalid : "((invalid::Savings) .oclIsKindOf(Client)) = invalid"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_invalid)
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_null : "((null::Savings) .oclIsKindOf(Client)) = true"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_null)
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_invalid : "((invalid::Account) .oclIsKindOf(Client)) = invalid"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_invalid)
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_null : "((null::Account) .oclIsKindOf(Client)) = true"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_null)
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_invalid : "((invalid::Current) .oclIsKindOf(Client)) = invalid"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_invalid)
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_null : "((null::Current) .oclIsKindOf(Client)) = true"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_null)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid : "((invalid::OclAny) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_invalid OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null : "((null::OclAny) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_null OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_null OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_invalid : "((invalid::Current) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_invalid OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_invalid OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_invalid OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_null : "((null::Current) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_null OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_null OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_null OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_invalid : "((invalid::Savings) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_invalid OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_invalid OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_invalid OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_null : "((null::Savings) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_null OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_null OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_null OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_invalid : "((invalid::Account) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_invalid OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_invalid OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_invalid OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_null : "((null::Account) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_null OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_null OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_null OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_invalid : "((invalid::Bank) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_invalid OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_invalid OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_invalid OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_null : "((null::Bank) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_null OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_null OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_null OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_invalid : "((invalid::Client) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_invalid OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_invalid OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_invalid OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_null : "((null::Client) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_null OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_null OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_null OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_null, simp)

(* 77 ************************************ 1251 + 1 *)
lemmas[simp,code_unfold] = OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_invalid
                            OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_invalid
                            OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_invalid
                            OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_invalid
                            OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_invalid
                            OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_invalid
                            OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_null
                            OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_null
                            OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_null
                            OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_null
                            OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_null
                            OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_null
                            OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_invalid
                            OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_invalid
                            OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_invalid
                            OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_invalid
                            OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_invalid
                            OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_invalid
                            OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_null
                            OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_null
                            OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_null
                            OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_null
                            OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_null
                            OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_null
                            OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_invalid
                            OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_invalid
                            OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_invalid
                            OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid
                            OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_invalid
                            OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_invalid
                            OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_null
                            OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_null
                            OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_null
                            OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_null
                            OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_null
                            OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_null
                            OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_invalid
                            OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_invalid
                            OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_invalid
                            OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid
                            OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_invalid
                            OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_invalid
                            OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_null
                            OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_null
                            OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_null
                            OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null
                            OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_null
                            OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_null
                            OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_invalid
                            OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_invalid
                            OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_invalid
                            OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_invalid
                            OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_invalid
                            OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_invalid
                            OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_null
                            OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_null
                            OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_null
                            OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_null
                            OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_null
                            OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_null
                            OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_invalid
                            OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_invalid
                            OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_invalid
                            OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid
                            OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_invalid
                            OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_invalid
                            OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_null
                            OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_null
                            OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_null
                            OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_null
                            OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_null
                            OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_null

(* 78 ************************************ 1252 + 1 *)
subsection{* Validity and Definedness Properties *}

(* 79 ************************************ 1253 + 36 *)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclIsKindOf(Current)))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current, rule OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Account) .oclIsKindOf(Current)))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account, rule OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(Current)))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny, rule OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclIsKindOf(Current)))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings, rule OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Bank) .oclIsKindOf(Current)))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank, rule OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Client) .oclIsKindOf(Current)))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client, rule OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclIsKindOf(Savings)))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings, rule OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Account) .oclIsKindOf(Savings)))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account, rule OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(Savings)))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny, rule OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclIsKindOf(Savings)))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current, rule OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Bank) .oclIsKindOf(Savings)))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank, rule OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Client) .oclIsKindOf(Savings)))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client, rule OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Account) .oclIsKindOf(Account)))"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account, rule defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_defined[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_defined[OF isdef]], OF OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(Account)))"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny, rule defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_defined[OF isdef]], OF OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclIsKindOf(Account)))"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current, rule defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_defined[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_defined[OF isdef]], OF OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclIsKindOf(Account)))"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings, rule defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_defined[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_defined[OF isdef]], OF OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Bank) .oclIsKindOf(Account)))"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank, rule defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_defined[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_defined[OF isdef]], OF OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Client) .oclIsKindOf(Account)))"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client, rule defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_defined[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_defined[OF isdef]], OF OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Bank) .oclIsKindOf(Bank)))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank, rule OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(Bank)))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny, rule OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Client) .oclIsKindOf(Bank)))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client, rule OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclIsKindOf(Bank)))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings, rule OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Account) .oclIsKindOf(Bank)))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account, rule OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclIsKindOf(Bank)))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current, rule OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Client) .oclIsKindOf(Client)))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client, rule OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(Client)))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny, rule OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Bank) .oclIsKindOf(Client)))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank, rule OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclIsKindOf(Client)))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings, rule OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Account) .oclIsKindOf(Client)))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account, rule OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclIsKindOf(Client)))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current, rule OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(OclAny)))"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny, rule defined_or_I[OF defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined[OF isdef]], OF OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined[OF isdef]], OF OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclIsKindOf(OclAny)))"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current, rule defined_or_I[OF defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_defined[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_defined[OF isdef]], OF OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_defined[OF isdef]], OF OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclIsKindOf(OclAny)))"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings, rule defined_or_I[OF defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_defined[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_defined[OF isdef]], OF OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_defined[OF isdef]], OF OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Account) .oclIsKindOf(OclAny)))"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account, rule defined_or_I[OF defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_defined[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_defined[OF isdef]], OF OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_defined[OF isdef]], OF OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Bank) .oclIsKindOf(OclAny)))"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank, rule defined_or_I[OF defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_defined[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_defined[OF isdef]], OF OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_defined[OF isdef]], OF OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Client) .oclIsKindOf(OclAny)))"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client, rule defined_or_I[OF defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_defined[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_defined[OF isdef]], OF OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_defined[OF isdef]], OF OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_defined[OF isdef]]) 

(* 80 ************************************ 1289 + 36 *)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclIsKindOf(Current)))"
by(rule OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Account) .oclIsKindOf(Current)))"
by(rule OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(Current)))"
by(rule OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclIsKindOf(Current)))"
by(rule OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Bank) .oclIsKindOf(Current)))"
by(rule OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Client) .oclIsKindOf(Current)))"
by(rule OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclIsKindOf(Savings)))"
by(rule OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Account) .oclIsKindOf(Savings)))"
by(rule OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(Savings)))"
by(rule OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclIsKindOf(Savings)))"
by(rule OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Bank) .oclIsKindOf(Savings)))"
by(rule OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Client) .oclIsKindOf(Savings)))"
by(rule OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Account) .oclIsKindOf(Account)))"
by(rule OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(Account)))"
by(rule OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclIsKindOf(Account)))"
by(rule OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclIsKindOf(Account)))"
by(rule OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Bank) .oclIsKindOf(Account)))"
by(rule OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Client) .oclIsKindOf(Account)))"
by(rule OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Bank) .oclIsKindOf(Bank)))"
by(rule OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(Bank)))"
by(rule OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Client) .oclIsKindOf(Bank)))"
by(rule OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclIsKindOf(Bank)))"
by(rule OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Account) .oclIsKindOf(Bank)))"
by(rule OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclIsKindOf(Bank)))"
by(rule OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Client) .oclIsKindOf(Client)))"
by(rule OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(Client)))"
by(rule OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Bank) .oclIsKindOf(Client)))"
by(rule OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclIsKindOf(Client)))"
by(rule OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Account) .oclIsKindOf(Client)))"
by(rule OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclIsKindOf(Client)))"
by(rule OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::OclAny) .oclIsKindOf(OclAny)))"
by(rule OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Current) .oclIsKindOf(OclAny)))"
by(rule OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Savings) .oclIsKindOf(OclAny)))"
by(rule OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Account) .oclIsKindOf(OclAny)))"
by(rule OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Bank) .oclIsKindOf(OclAny)))"
by(rule OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::Client) .oclIsKindOf(OclAny)))"
by(rule OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_defined[OF isdef[THEN foundation20]]) 

(* 81 ************************************ 1325 + 1 *)
subsection{* Up Down Casting *}

(* 82 ************************************ 1326 + 6 *)
lemma actual_eq_static\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Current) .oclIsKindOf(Current))"
  apply(simp only: OclValid_def, insert isdef)
  apply(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current)
  apply(auto simp: foundation16 bot_option_def split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split)
by((simp_all add: false_def true_def OclOr_def OclAnd_def OclNot_def)?) 
lemma actual_eq_static\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Savings) .oclIsKindOf(Savings))"
  apply(simp only: OclValid_def, insert isdef)
  apply(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings)
  apply(auto simp: foundation16 bot_option_def split: option.split ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split)
by((simp_all add: false_def true_def OclOr_def OclAnd_def OclNot_def)?) 
lemma actual_eq_static\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Account) .oclIsKindOf(Account))"
  apply(simp only: OclValid_def, insert isdef)
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account, subst (1) cp_OclOr, subst (2 1) cp_OclOr, simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account, simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
  apply(auto simp: cp_OclOr[symmetric ] foundation16 bot_option_def OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account split: option.split ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split)
by((simp_all add: false_def true_def OclOr_def OclAnd_def OclNot_def)?) 
lemma actual_eq_static\<^sub>B\<^sub>a\<^sub>n\<^sub>k : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Bank) .oclIsKindOf(Bank))"
  apply(simp only: OclValid_def, insert isdef)
  apply(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank)
  apply(auto simp: foundation16 bot_option_def split: option.split ty\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split)
by((simp_all add: false_def true_def OclOr_def OclAnd_def OclNot_def)?) 
lemma actual_eq_static\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Client) .oclIsKindOf(Client))"
  apply(simp only: OclValid_def, insert isdef)
  apply(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client)
  apply(auto simp: foundation16 bot_option_def split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split)
by((simp_all add: false_def true_def OclOr_def OclAnd_def OclNot_def)?) 
lemma actual_eq_static\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(OclAny))"
  apply(simp only: OclValid_def, insert isdef)
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny, subst (1) cp_OclOr, subst (2 1) cp_OclOr, subst (3 2 1) cp_OclOr, simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny, simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny, subst (4 3 2 1) cp_OclOr, subst (5 4 3 2 1) cp_OclOr, simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny, simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
  apply(auto simp: cp_OclOr[symmetric ] foundation16 bot_option_def OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny split: option.split ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split ty\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split)
by((simp_all add: false_def true_def OclOr_def OclAnd_def OclNot_def)?) 

(* 83 ************************************ 1332 + 7 *)
lemma actualKind\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_larger_staticKind\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Current) .oclIsKindOf(Account))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
by(rule foundation25', rule actual_eq_static\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t[OF isdef]) 
lemma actualKind\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Current) .oclIsKindOf(OclAny))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
by(rule foundation25', rule actualKind\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_larger_staticKind\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t[OF isdef]) 
lemma actualKind\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_larger_staticKind\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Savings) .oclIsKindOf(Account))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
by(rule foundation25, rule foundation25', rule actual_eq_static\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s[OF isdef]) 
lemma actualKind\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Savings) .oclIsKindOf(OclAny))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
by(rule foundation25', rule actualKind\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_larger_staticKind\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t[OF isdef]) 
lemma actualKind\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Account) .oclIsKindOf(OclAny))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
by(rule foundation25', rule actual_eq_static\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t[OF isdef]) 
lemma actualKind\<^sub>B\<^sub>a\<^sub>n\<^sub>k_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Bank) .oclIsKindOf(OclAny))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
by(rule foundation25, rule foundation25', rule actual_eq_static\<^sub>B\<^sub>a\<^sub>n\<^sub>k[OF isdef]) 
lemma actualKind\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::Client) .oclIsKindOf(OclAny))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
by(rule foundation25, rule foundation25, rule foundation25', rule actual_eq_static\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t[OF isdef]) 

(* 84 ************************************ 1339 + 7 *)
lemma not_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_then_Account_OclIsTypeOf_others_unfold : 
assumes isdef: "(\<tau> \<Turnstile> (\<delta> (X)))"
assumes iskin: "(\<tau> \<Turnstile> ((X::Account) .oclIsKindOf(Current)))"
shows "(\<tau> \<Turnstile> ((X::Account) .oclIsTypeOf(Current)))"
  using iskin
  apply(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
done 
lemma not_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others_unfold : 
assumes isdef: "(\<tau> \<Turnstile> (\<delta> (X)))"
assumes iskin: "(\<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Current)))"
shows "(\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Current)))"
  using iskin
  apply(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
done 
lemma not_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_then_Account_OclIsTypeOf_others_unfold : 
assumes isdef: "(\<tau> \<Turnstile> (\<delta> (X)))"
assumes iskin: "(\<tau> \<Turnstile> ((X::Account) .oclIsKindOf(Savings)))"
shows "(\<tau> \<Turnstile> ((X::Account) .oclIsTypeOf(Savings)))"
  using iskin
  apply(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
done 
lemma not_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_then_OclAny_OclIsTypeOf_others_unfold : 
assumes isdef: "(\<tau> \<Turnstile> (\<delta> (X)))"
assumes iskin: "(\<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Savings)))"
shows "(\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Savings)))"
  using iskin
  apply(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
done 
lemma not_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others_unfold : 
assumes isdef: "(\<tau> \<Turnstile> (\<delta> (X)))"
assumes iskin: "(\<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Account)))"
shows "((\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Account))) \<or> ((\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Current))) \<or> (\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Savings)))))"
  using iskin
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
  apply(erule foundation26[OF defined_or_I[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_defined'[OF isdef]], OF OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_defined'[OF isdef]])
  apply(erule foundation26[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_defined'[OF isdef]])
  apply(simp)
  apply(drule not_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_then_OclAny_OclIsTypeOf_others_unfold[OF isdef], blast)
  apply(drule not_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others_unfold[OF isdef], blast)
done 
lemma not_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_then_OclAny_OclIsTypeOf_others_unfold : 
assumes isdef: "(\<tau> \<Turnstile> (\<delta> (X)))"
assumes iskin: "(\<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Bank)))"
shows "(\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Bank)))"
  using iskin
  apply(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
done 
lemma not_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others_unfold : 
assumes isdef: "(\<tau> \<Turnstile> (\<delta> (X)))"
assumes iskin: "(\<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Client)))"
shows "(\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Client)))"
  using iskin
  apply(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
done 

(* 85 ************************************ 1346 + 7 *)
lemma not_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_then_Account_OclIsTypeOf_others : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::Account) .oclIsKindOf(Current))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "(\<tau> \<Turnstile> ((X::Account) .oclIsTypeOf(Account)) \<or> \<tau> \<Turnstile> ((X::Account) .oclIsKindOf(Savings)))"
  using actual_eq_static\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account)
  apply(erule foundation26[OF defined_or_I[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_defined'[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_defined'[OF isdef]], OF OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_defined'[OF isdef]])
  apply(erule foundation26[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_defined'[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_defined'[OF isdef]])
  apply(simp)
  apply(simp)
  apply(simp add: iskin)
done 
lemma not_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Current))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "(\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(OclAny)) \<or> (\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Account)) \<or> (\<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Bank)) \<or> (\<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Client)) \<or> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Savings))))))"
  using actual_eq_static\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply(erule foundation26[OF defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined'[OF isdef]], OF OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined'[OF isdef]], OF OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined'[OF isdef]])
  apply(erule foundation26[OF defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined'[OF isdef]], OF OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined'[OF isdef]])
  apply(erule foundation26[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined'[OF isdef]])
  apply(simp)
  apply(simp)
  apply(simp)
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
  apply(erule foundation26[OF defined_or_I[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_defined'[OF isdef]], OF OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_defined'[OF isdef]])
  apply(erule foundation26[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_defined'[OF isdef]])
  apply(simp)
  apply(simp)
  apply(simp add: iskin)
done 
lemma not_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_then_Account_OclIsTypeOf_others : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::Account) .oclIsKindOf(Savings))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "(\<tau> \<Turnstile> ((X::Account) .oclIsTypeOf(Account)) \<or> \<tau> \<Turnstile> ((X::Account) .oclIsKindOf(Current)))"
  using actual_eq_static\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account)
  apply(erule foundation26[OF defined_or_I[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_defined'[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_defined'[OF isdef]], OF OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_defined'[OF isdef]])
  apply(erule foundation26[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_defined'[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_defined'[OF isdef]])
  apply(simp)
  apply(simp add: iskin)
  apply(simp)
done 
lemma not_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_then_OclAny_OclIsTypeOf_others : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Savings))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "(\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(OclAny)) \<or> (\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(Account)) \<or> (\<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Bank)) \<or> (\<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Client)) \<or> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Current))))))"
  using actual_eq_static\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply(erule foundation26[OF defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined'[OF isdef]], OF OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined'[OF isdef]], OF OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined'[OF isdef]])
  apply(erule foundation26[OF defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined'[OF isdef]], OF OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined'[OF isdef]])
  apply(erule foundation26[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined'[OF isdef]])
  apply(simp)
  apply(simp)
  apply(simp)
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
  apply(erule foundation26[OF defined_or_I[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_defined'[OF isdef]], OF OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_defined'[OF isdef]])
  apply(erule foundation26[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_defined'[OF isdef]])
  apply(simp)
  apply(simp add: iskin)
  apply(simp)
done 
lemma not_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Account))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "(\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(OclAny)) \<or> (\<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Bank)) \<or> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Client))))"
  using actual_eq_static\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply(erule foundation26[OF defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined'[OF isdef]], OF OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined'[OF isdef]], OF OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined'[OF isdef]])
  apply(erule foundation26[OF defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined'[OF isdef]], OF OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined'[OF isdef]])
  apply(erule foundation26[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined'[OF isdef]])
  apply(simp)
  apply(simp)
  apply(simp)
  apply(simp add: iskin)
done 
lemma not_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_then_OclAny_OclIsTypeOf_others : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Bank))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "(\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(OclAny)) \<or> (\<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Client)) \<or> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Account))))"
  using actual_eq_static\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply(erule foundation26[OF defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined'[OF isdef]], OF OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined'[OF isdef]], OF OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined'[OF isdef]])
  apply(erule foundation26[OF defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined'[OF isdef]], OF OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined'[OF isdef]])
  apply(erule foundation26[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined'[OF isdef]])
  apply(simp)
  apply(simp)
  apply(simp add: iskin)
  apply(simp)
done 
lemma not_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Client))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "(\<tau> \<Turnstile> ((X::OclAny) .oclIsTypeOf(OclAny)) \<or> (\<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Bank)) \<or> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Account))))"
  using actual_eq_static\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply(erule foundation26[OF defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined'[OF isdef]], OF OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined'[OF isdef]], OF OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined'[OF isdef]])
  apply(erule foundation26[OF defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined'[OF isdef]], OF OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined'[OF isdef]])
  apply(erule foundation26[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined'[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined'[OF isdef]])
  apply(simp)
  apply(simp add: iskin)
  apply(simp)
  apply(simp)
done 

(* 86 ************************************ 1353 + 9 *)
lemma down_cast_kind\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_from_Account_to_Current : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::Account) .oclIsKindOf(Current))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Current)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_then_Account_OclIsTypeOf_others[OF iskin, OF isdef], elim disjE)
  apply(rule down_cast_type\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_from_Account_to_Current, simp only: , simp only: isdef)
  apply(drule not_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_then_Account_OclIsTypeOf_others_unfold[OF isdef])
  apply(rule down_cast_type\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_from_Account_to_Current, simp only: , simp only: isdef)
done 
lemma down_cast_kind\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Current : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Current))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Current)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others[OF iskin, OF isdef], elim disjE)
  apply(rule down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Current, simp only: , simp only: isdef)
  apply(rule down_cast_type\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_from_OclAny_to_Current, simp only: , simp only: isdef)
  apply(drule not_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_then_OclAny_OclIsTypeOf_others_unfold[OF isdef])
  apply(rule down_cast_type\<^sub>B\<^sub>a\<^sub>n\<^sub>k_from_OclAny_to_Current, simp only: , simp only: isdef)
  apply(drule not_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others_unfold[OF isdef])
  apply(rule down_cast_type\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Current, simp only: , simp only: isdef)
  apply(drule not_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_then_OclAny_OclIsTypeOf_others_unfold[OF isdef])
  apply(rule down_cast_type\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_from_OclAny_to_Current, simp only: , simp only: isdef)
done 
lemma down_cast_kind\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_from_Account_to_Savings : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::Account) .oclIsKindOf(Savings))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Savings)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_then_Account_OclIsTypeOf_others[OF iskin, OF isdef], elim disjE)
  apply(rule down_cast_type\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_from_Account_to_Savings, simp only: , simp only: isdef)
  apply(drule not_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_then_Account_OclIsTypeOf_others_unfold[OF isdef])
  apply(rule down_cast_type\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_from_Account_to_Savings, simp only: , simp only: isdef)
done 
lemma down_cast_kind\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_from_OclAny_to_Savings : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Savings))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Savings)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_then_OclAny_OclIsTypeOf_others[OF iskin, OF isdef], elim disjE)
  apply(rule down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Savings, simp only: , simp only: isdef)
  apply(rule down_cast_type\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_from_OclAny_to_Savings, simp only: , simp only: isdef)
  apply(drule not_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_then_OclAny_OclIsTypeOf_others_unfold[OF isdef])
  apply(rule down_cast_type\<^sub>B\<^sub>a\<^sub>n\<^sub>k_from_OclAny_to_Savings, simp only: , simp only: isdef)
  apply(drule not_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others_unfold[OF isdef])
  apply(rule down_cast_type\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Savings, simp only: , simp only: isdef)
  apply(drule not_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others_unfold[OF isdef])
  apply(rule down_cast_type\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Savings, simp only: , simp only: isdef)
done 
lemma down_cast_kind\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_from_OclAny_to_Account : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Account))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Account)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others[OF iskin, OF isdef], elim disjE)
  apply(rule down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Account, simp only: , simp only: isdef)
  apply(drule not_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_then_OclAny_OclIsTypeOf_others_unfold[OF isdef])
  apply(rule down_cast_type\<^sub>B\<^sub>a\<^sub>n\<^sub>k_from_OclAny_to_Account, simp only: , simp only: isdef)
  apply(drule not_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others_unfold[OF isdef])
  apply(rule down_cast_type\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Account, simp only: , simp only: isdef)
done 
lemma down_cast_kind\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_from_OclAny_to_Current : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Account))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Current)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others[OF iskin, OF isdef], elim disjE)
  apply(rule down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Current, simp only: , simp only: isdef)
  apply(drule not_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_then_OclAny_OclIsTypeOf_others_unfold[OF isdef])
  apply(rule down_cast_type\<^sub>B\<^sub>a\<^sub>n\<^sub>k_from_OclAny_to_Current, simp only: , simp only: isdef)
  apply(drule not_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others_unfold[OF isdef])
  apply(rule down_cast_type\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Current, simp only: , simp only: isdef)
done 
lemma down_cast_kind\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_from_OclAny_to_Savings : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Account))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Savings)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others[OF iskin, OF isdef], elim disjE)
  apply(rule down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Savings, simp only: , simp only: isdef)
  apply(drule not_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_then_OclAny_OclIsTypeOf_others_unfold[OF isdef])
  apply(rule down_cast_type\<^sub>B\<^sub>a\<^sub>n\<^sub>k_from_OclAny_to_Savings, simp only: , simp only: isdef)
  apply(drule not_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others_unfold[OF isdef])
  apply(rule down_cast_type\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Savings, simp only: , simp only: isdef)
done 
lemma down_cast_kind\<^sub>B\<^sub>a\<^sub>n\<^sub>k_from_OclAny_to_Bank : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Bank))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Bank)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_then_OclAny_OclIsTypeOf_others[OF iskin, OF isdef], elim disjE)
  apply(rule down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Bank, simp only: , simp only: isdef)
  apply(drule not_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others_unfold[OF isdef])
  apply(rule down_cast_type\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Bank, simp only: , simp only: isdef)
  apply(drule not_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others_unfold[OF isdef])
  apply(auto simp: isdef down_cast_type\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_from_OclAny_to_Bank down_cast_type\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_from_OclAny_to_Bank down_cast_type\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Bank)
done 
lemma down_cast_kind\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Client : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::OclAny) .oclIsKindOf(Client))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Client)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others[OF iskin, OF isdef], elim disjE)
  apply(rule down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Client, simp only: , simp only: isdef)
  apply(drule not_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_then_OclAny_OclIsTypeOf_others_unfold[OF isdef])
  apply(rule down_cast_type\<^sub>B\<^sub>a\<^sub>n\<^sub>k_from_OclAny_to_Client, simp only: , simp only: isdef)
  apply(drule not_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others_unfold[OF isdef])
  apply(auto simp: isdef down_cast_type\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_from_OclAny_to_Client down_cast_type\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_from_OclAny_to_Client down_cast_type\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Client)
done 

(* 87 ************************************ 1362 + 1 *)
section{* OclAllInstances *}

(* 88 ************************************ 1363 + 1 *)
text{* 
   To denote OCL-types occuring in OCL expressions syntactically---as, for example,  as
``argument'' of \inlineisar{oclAllInstances()}---we use the inverses of the injection
functions into the object universes; we show that this is sufficient ``characterization.''  *}

(* 89 ************************************ 1364 + 6 *)
definition "Current = OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_\<AA>"
definition "Savings = OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_\<AA>"
definition "Account = OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<AA>"
definition "Bank = OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_\<AA>"
definition "Client = OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_\<AA>"
definition "OclAny = OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>"

(* 90 ************************************ 1370 + 1 *)
lemmas[simp,code_unfold] = Current_def
                            Savings_def
                            Account_def
                            Bank_def
                            Client_def
                            OclAny_def

(* 91 ************************************ 1371 + 1 *)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_some : "(OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> (x)) \<noteq> None"
by(simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def)

(* 92 ************************************ 1372 + 3 *)
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

(* 93 ************************************ 1375 + 1 *)
subsection{* OclIsTypeOf *}

(* 94 ************************************ 1376 + 2 *)
lemma ex_ssubst : "(\<forall>x \<in> B. (s (x)) = (t (x))) \<Longrightarrow> (\<exists>x \<in> B. (P ((s (x))))) = (\<exists>x \<in> B. (P ((t (x)))))"
by(simp)
lemma ex_def : "x \<in> \<lceil>\<lceil>\<lfloor>\<lfloor>Some ` (X - {None})\<rfloor>\<rfloor>\<rceil>\<rceil> \<Longrightarrow> (\<exists>y. x = \<lfloor>\<lfloor>y\<rfloor>\<rfloor>)"
by(auto)

(* 95 ************************************ 1378 + 24 *)
lemma Current_OclAllInstances_generic_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Current))) (OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsTypeOf(Current)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actual_eq_static\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t[simplified OclValid_def, simplified OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Current_OclAllInstances_at_post_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Current))) (OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t))"
  unfolding OclAllInstances_at_post_def
by(rule Current_OclAllInstances_generic_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t) 
lemma Current_OclAllInstances_at_pre_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Current))) (OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t))"
  unfolding OclAllInstances_at_pre_def
by(rule Current_OclAllInstances_generic_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t) 
lemma Savings_OclAllInstances_generic_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Savings))) (OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsTypeOf(Savings)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actual_eq_static\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s[simplified OclValid_def, simplified OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Savings_OclAllInstances_at_post_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Savings))) (OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s))"
  unfolding OclAllInstances_at_post_def
by(rule Savings_OclAllInstances_generic_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s) 
lemma Savings_OclAllInstances_at_pre_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Savings))) (OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s))"
  unfolding OclAllInstances_at_pre_def
by(rule Savings_OclAllInstances_generic_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s) 
lemma Account_OclAllInstances_generic_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t1 : 
assumes [simp]: "(\<And>x. (pre_post ((x , x))) = x)"
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Account))) (OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t)))"
  apply(rule exI[where x = "\<tau>\<^sub>0"], simp add: \<tau>\<^sub>0_def OclValid_def del: OclAllInstances_generic_def)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
by(simp) 
lemma Account_OclAllInstances_at_post_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t1 : 
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Account))) (OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t)))"
  unfolding OclAllInstances_at_post_def
by(rule Account_OclAllInstances_generic_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t1, simp) 
lemma Account_OclAllInstances_at_pre_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t1 : 
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Account))) (OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t)))"
  unfolding OclAllInstances_at_pre_def
by(rule Account_OclAllInstances_generic_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t1, simp) 
lemma Account_OclAllInstances_generic_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t2 : 
assumes [simp]: "(\<And>x. (pre_post ((x , x))) = x)"
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (not ((UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Account))) (OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t)))))"
  proof - fix oid a show ?thesis
  proof - let ?t0 = "(state.make ((Map.empty (oid \<mapsto> (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (a))) (None) (None))))))) (Map.empty))" show ?thesis
  apply(rule exI[where x = "(?t0 , ?t0)"], simp add: OclValid_def del: OclAllInstances_generic_def)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<AA>_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
by(simp add: state.make_def OclNot_def) qed qed
lemma Account_OclAllInstances_at_post_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t2 : 
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (not ((UML_Set.OclForall ((OclAllInstances_at_post (Account))) (OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t)))))"
  unfolding OclAllInstances_at_post_def
by(rule Account_OclAllInstances_generic_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t2, simp) 
lemma Account_OclAllInstances_at_pre_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t2 : 
shows "(\<exists>\<tau>. \<tau> \<Turnstile> (not ((UML_Set.OclForall ((OclAllInstances_at_pre (Account))) (OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t)))))"
  unfolding OclAllInstances_at_pre_def
by(rule Account_OclAllInstances_generic_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t2, simp) 
lemma Bank_OclAllInstances_generic_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Bank))) (OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsTypeOf(Bank)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actual_eq_static\<^sub>B\<^sub>a\<^sub>n\<^sub>k[simplified OclValid_def, simplified OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Bank_OclAllInstances_at_post_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Bank))) (OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k))"
  unfolding OclAllInstances_at_post_def
by(rule Bank_OclAllInstances_generic_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k) 
lemma Bank_OclAllInstances_at_pre_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Bank))) (OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k))"
  unfolding OclAllInstances_at_pre_def
by(rule Bank_OclAllInstances_generic_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k) 
lemma Client_OclAllInstances_generic_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Client))) (OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsTypeOf(Client)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actual_eq_static\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t[simplified OclValid_def, simplified OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Client_OclAllInstances_at_post_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Client))) (OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t))"
  unfolding OclAllInstances_at_post_def
by(rule Client_OclAllInstances_generic_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t) 
lemma Client_OclAllInstances_at_pre_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Client))) (OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t))"
  unfolding OclAllInstances_at_pre_def
by(rule Client_OclAllInstances_generic_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t) 
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
  proof - let ?t0 = "(state.make ((Map.empty (oid \<mapsto> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (a))))))))) (Map.empty))" show ?thesis
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

(* 96 ************************************ 1402 + 1 *)
subsection{* OclIsKindOf *}

(* 97 ************************************ 1403 + 18 *)
lemma Current_OclAllInstances_generic_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Current))) (OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(Current)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actual_eq_static\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Current_OclAllInstances_at_post_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Current))) (OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t))"
  unfolding OclAllInstances_at_post_def
by(rule Current_OclAllInstances_generic_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t) 
lemma Current_OclAllInstances_at_pre_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Current))) (OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t))"
  unfolding OclAllInstances_at_pre_def
by(rule Current_OclAllInstances_generic_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t) 
lemma Savings_OclAllInstances_generic_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Savings))) (OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(Savings)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actual_eq_static\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Savings_OclAllInstances_at_post_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Savings))) (OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s))"
  unfolding OclAllInstances_at_post_def
by(rule Savings_OclAllInstances_generic_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s) 
lemma Savings_OclAllInstances_at_pre_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Savings))) (OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s))"
  unfolding OclAllInstances_at_pre_def
by(rule Savings_OclAllInstances_generic_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s) 
lemma Account_OclAllInstances_generic_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Account))) (OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(Account)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actual_eq_static\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Account_OclAllInstances_at_post_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Account))) (OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t))"
  unfolding OclAllInstances_at_post_def
by(rule Account_OclAllInstances_generic_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t) 
lemma Account_OclAllInstances_at_pre_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Account))) (OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t))"
  unfolding OclAllInstances_at_pre_def
by(rule Account_OclAllInstances_generic_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t) 
lemma Bank_OclAllInstances_generic_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Bank))) (OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(Bank)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actual_eq_static\<^sub>B\<^sub>a\<^sub>n\<^sub>k[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Bank_OclAllInstances_at_post_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Bank))) (OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k))"
  unfolding OclAllInstances_at_post_def
by(rule Bank_OclAllInstances_generic_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k) 
lemma Bank_OclAllInstances_at_pre_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Bank))) (OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k))"
  unfolding OclAllInstances_at_pre_def
by(rule Bank_OclAllInstances_generic_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k) 
lemma Client_OclAllInstances_generic_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Client))) (OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(Client)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actual_eq_static\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Client_OclAllInstances_at_post_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Client))) (OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t))"
  unfolding OclAllInstances_at_post_def
by(rule Client_OclAllInstances_generic_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t) 
lemma Client_OclAllInstances_at_pre_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Client))) (OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t))"
  unfolding OclAllInstances_at_pre_def
by(rule Client_OclAllInstances_generic_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t) 
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

(* 98 ************************************ 1421 + 21 *)
lemma Current_OclAllInstances_generic_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Current))) (OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(Account)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actualKind\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_larger_staticKind\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Current_OclAllInstances_at_post_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Current))) (OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t))"
  unfolding OclAllInstances_at_post_def
by(rule Current_OclAllInstances_generic_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t) 
lemma Current_OclAllInstances_at_pre_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Current))) (OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t))"
  unfolding OclAllInstances_at_pre_def
by(rule Current_OclAllInstances_generic_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t) 
lemma Current_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Current))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(OclAny)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actualKind\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Current_OclAllInstances_at_post_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Current))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_post_def
by(rule Current_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y) 
lemma Current_OclAllInstances_at_pre_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Current))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_pre_def
by(rule Current_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y) 
lemma Savings_OclAllInstances_generic_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Savings))) (OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(Account)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actualKind\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_larger_staticKind\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Savings_OclAllInstances_at_post_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Savings))) (OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t))"
  unfolding OclAllInstances_at_post_def
by(rule Savings_OclAllInstances_generic_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t) 
lemma Savings_OclAllInstances_at_pre_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Savings))) (OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t))"
  unfolding OclAllInstances_at_pre_def
by(rule Savings_OclAllInstances_generic_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t) 
lemma Savings_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Savings))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(OclAny)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actualKind\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Savings_OclAllInstances_at_post_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Savings))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_post_def
by(rule Savings_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y) 
lemma Savings_OclAllInstances_at_pre_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Savings))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_pre_def
by(rule Savings_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y) 
lemma Account_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Account))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(OclAny)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actualKind\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Account_OclAllInstances_at_post_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Account))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_post_def
by(rule Account_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y) 
lemma Account_OclAllInstances_at_pre_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Account))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_pre_def
by(rule Account_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y) 
lemma Bank_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Bank))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(OclAny)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actualKind\<^sub>B\<^sub>a\<^sub>n\<^sub>k_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Bank_OclAllInstances_at_post_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Bank))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_post_def
by(rule Bank_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y) 
lemma Bank_OclAllInstances_at_pre_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Bank))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_pre_def
by(rule Bank_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y) 
lemma Client_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (Client))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  apply(simp add: OclValid_def del: OclAllInstances_generic_def OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
  apply(simp only: UML_Set.OclForall_def refl if_True OclAllInstances_generic_defined[simplified OclValid_def])
  apply(simp only: OclAllInstances_generic_def)
  apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
  apply(subst (1 2 3) ex_ssubst[where s = "(\<lambda>x. (((\<lambda>_. x) .oclIsKindOf(OclAny)) (\<tau>)))" and t = "(\<lambda>_. (true (\<tau>)))"])
  apply(intro ballI actualKind\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y[simplified OclValid_def])
  apply(drule ex_def, erule exE, simp)
by(simp)
lemma Client_OclAllInstances_at_post_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (Client))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_post_def
by(rule Client_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y) 
lemma Client_OclAllInstances_at_pre_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (Client))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
  unfolding OclAllInstances_at_pre_def
by(rule Client_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y) 

(* 99 ************************************ 1442 + 1 *)
section{* The Accessors *}

(* 100 ************************************ 1443 + 1 *)
text{*  *}

(* 101 ************************************ 1444 + 1 *)
text{* 
  \label{sec:eam-accessors} *}

(* 102 ************************************ 1445 + 1 *)
subsection{* Definition *}

(* 103 ************************************ 1446 + 1 *)
text{* 
   We start with a oid for the association; this oid can be used
in presence of association classes to represent the association inside an object,
pretty much similar to the \inlineisar+Employee_DesignModel_UMLPart+, where we stored
an \verb+oid+ inside the class as ``pointer.''  *}

(* 104 ************************************ 1447 + 10 *)
ML{* val oidCurrent_0_bank = 2 *}
ML{* val oidCurrent_0_owner = 0 *}
ML{* val oidSavings_0_bank = 2 *}
ML{* val oidSavings_0_owner = 0 *}
ML{* val oidAccount_0_bank = 2 *}
ML{* val oidAccount_0_owner = 0 *}
ML{* val oidBank_1_b_accounts = 2 *}
ML{* val oidBank_0_clients = 1 *}
ML{* val oidClient_1_c_accounts = 0 *}
ML{* val oidClient_1_banks = 1 *}

(* 105 ************************************ 1457 + 10 *)
definition "oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K> = 2"
definition "oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R> = 0"
definition "oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K> = 2"
definition "oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R> = 0"
definition "oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K> = 2"
definition "oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R> = 0"
definition "oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S> = 2"
definition "oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S> = 1"
definition "oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S> = 0"
definition "oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<B>\<A>\<N>\<K>\<S> = 1"

(* 106 ************************************ 1467 + 1 *)
text{* 
   From there on, we can already define an empty state which must contain
for $\mathit{oid}_{Person}\mathcal{BOSS}$ the empty relation (encoded as association list, since there are
associations with a Sequence-like structure). *}

(* 107 ************************************ 1468 + 5 *)
definition "eval_extract x f = (\<lambda>\<tau>. (case x \<tau> of \<lfloor>\<lfloor>obj\<rfloor>\<rfloor> \<Rightarrow> (f ((oid_of (obj))) (\<tau>))
    | _ \<Rightarrow> invalid \<tau>))"
definition "in_pre_state = fst"
definition "in_post_state = snd"
definition "reconst_basetype = (\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)"
definition "reconst_basetype\<^sub>V\<^sub>o\<^sub>i\<^sub>d x = Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e o (reconst_basetype (x))"

(* 108 ************************************ 1473 + 1 *)
text{* 
   The @{text pre_post}-parameter is configured with @{text fst} or
@{text snd}, the @{text to_from}-parameter either with the identity @{term id} or
the following combinator @{text switch}:  *}

(* 109 ************************************ 1474 + 2 *)
ML{* val switch2_01 = (fn [x0 , x1] => (x0 , x1)) *}
ML{* val switch2_10 = (fn [x0 , x1] => (x1 , x0)) *}

(* 110 ************************************ 1476 + 3 *)
definition "switch\<^sub>2_01 = (\<lambda> [x0 , x1] \<Rightarrow> (x0 , x1))"
definition "switch\<^sub>2_10 = (\<lambda> [x0 , x1] \<Rightarrow> (x1 , x0))"
definition "deref_assocs pre_post to_from assoc_oid f oid = (\<lambda>\<tau>. (case (assocs ((pre_post (\<tau>))) (assoc_oid)) of \<lfloor>S\<rfloor> \<Rightarrow> (f ((deref_assocs_list (to_from) (oid) (S))) (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"

(* 111 ************************************ 1479 + 6 *)
definition "deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"
definition "deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"
definition "deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"
definition "deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^sub>B\<^sub>a\<^sub>n\<^sub>k obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"
definition "deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"
definition "deref_oid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"

(* 112 ************************************ 1485 + 10 *)
definition "deref_assocs\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K> fst_snd f = (deref_assocs (fst_snd) (switch\<^sub>2_01) (oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>) (f)) \<circ> oid_of"
definition "deref_assocs\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R> fst_snd f = (deref_assocs (fst_snd) (switch\<^sub>2_01) (oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>) (f)) \<circ> oid_of"
definition "deref_assocs\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K> fst_snd f = (deref_assocs (fst_snd) (switch\<^sub>2_01) (oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K>) (f)) \<circ> oid_of"
definition "deref_assocs\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R> fst_snd f = (deref_assocs (fst_snd) (switch\<^sub>2_01) (oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R>) (f)) \<circ> oid_of"
definition "deref_assocs\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K> fst_snd f = (deref_assocs (fst_snd) (switch\<^sub>2_01) (oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>) (f)) \<circ> oid_of"
definition "deref_assocs\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R> fst_snd f = (deref_assocs (fst_snd) (switch\<^sub>2_01) (oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>) (f)) \<circ> oid_of"
definition "deref_assocs\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S> fst_snd f = (deref_assocs (fst_snd) (switch\<^sub>2_10) (oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>) (f)) \<circ> oid_of"
definition "deref_assocs\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S> fst_snd f = (deref_assocs (fst_snd) (switch\<^sub>2_01) (oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S>) (f)) \<circ> oid_of"
definition "deref_assocs\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S> fst_snd f = (deref_assocs (fst_snd) (switch\<^sub>2_10) (oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>) (f)) \<circ> oid_of"
definition "deref_assocs\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<B>\<A>\<N>\<K>\<S> fst_snd f = (deref_assocs (fst_snd) (switch\<^sub>2_10) (oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<B>\<A>\<N>\<K>\<S>) (f)) \<circ> oid_of"

(* 113 ************************************ 1495 + 1 *)
text{* 
   pointer undefined in state or not referencing a type conform object representation  *}

(* 114 ************************************ 1496 + 12 *)
definition "select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T> f = (\<lambda> (mk\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (_) (\<bottom>)) \<Rightarrow> null
    | (mk\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (_) (\<lfloor>\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T>\<rfloor>)) \<Rightarrow> (f (\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T>)))"
definition "select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<M>\<A>\<X> f = (\<lambda> (mk\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (_) (\<bottom>)) \<Rightarrow> null
    | (mk\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (_) (\<lfloor>\<M>\<A>\<X>\<rfloor>)) \<Rightarrow> (f (\<M>\<A>\<X>)))"
definition "select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<I>\<D> f = (\<lambda> (mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (_) (\<bottom>) (_)) \<Rightarrow> null
    | (mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (_) (\<lfloor>\<I>\<D>\<rfloor>) (_)) \<Rightarrow> (f (\<I>\<D>)))"
definition "select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E> f = (\<lambda> (mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (_) (_) (\<bottom>)) \<Rightarrow> null
    | (mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (_) (_) (\<lfloor>\<B>\<A>\<L>\<A>\<N>\<C>\<E>\<rfloor>)) \<Rightarrow> (f (\<B>\<A>\<L>\<A>\<N>\<C>\<E>)))"
definition "select\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<N>\<A>\<M>\<E> f = (\<lambda> (mk\<^sub>B\<^sub>a\<^sub>n\<^sub>k (_) (\<bottom>)) \<Rightarrow> null
    | (mk\<^sub>B\<^sub>a\<^sub>n\<^sub>k (_) (\<lfloor>\<N>\<A>\<M>\<E>\<rfloor>)) \<Rightarrow> (f (\<N>\<A>\<M>\<E>)))"
definition "select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E> f = (\<lambda> (mk\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (_) (\<bottom>) (_) (_)) \<Rightarrow> null
    | (mk\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (_) (\<lfloor>\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E>\<rfloor>) (_) (_)) \<Rightarrow> (f (\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E>)))"
definition "select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<D>\<D>\<R>\<E>\<S>\<S> f = (\<lambda> (mk\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (_) (_) (\<bottom>) (_)) \<Rightarrow> null
    | (mk\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (_) (_) (\<lfloor>\<A>\<D>\<D>\<R>\<E>\<S>\<S>\<rfloor>) (_)) \<Rightarrow> (f (\<A>\<D>\<D>\<R>\<E>\<S>\<S>)))"
definition "select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<G>\<E> f = (\<lambda> (mk\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (_) (_) (_) (\<bottom>)) \<Rightarrow> null
    | (mk\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (_) (_) (_) (\<lfloor>\<A>\<G>\<E>\<rfloor>)) \<Rightarrow> (f (\<A>\<G>\<E>)))"
definition "select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<I>\<D> f = (\<lambda> (mk\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (_) (\<bottom>) (_))) (_)) \<Rightarrow> null
    | (mk\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (_) (\<lfloor>\<I>\<D>\<rfloor>) (_))) (_)) \<Rightarrow> (f (\<I>\<D>)))"
definition "select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E> f = (\<lambda> (mk\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (_) (_) (\<bottom>))) (_)) \<Rightarrow> null
    | (mk\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (_) (_) (\<lfloor>\<B>\<A>\<L>\<A>\<N>\<C>\<E>\<rfloor>))) (_)) \<Rightarrow> (f (\<B>\<A>\<L>\<A>\<N>\<C>\<E>)))"
definition "select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<I>\<D> f = (\<lambda> (mk\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s ((mk\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (_) (\<bottom>) (_))) (_)) \<Rightarrow> null
    | (mk\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s ((mk\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (_) (\<lfloor>\<I>\<D>\<rfloor>) (_))) (_)) \<Rightarrow> (f (\<I>\<D>)))"
definition "select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<L>\<A>\<N>\<C>\<E> f = (\<lambda> (mk\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s ((mk\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (_) (_) (\<bottom>))) (_)) \<Rightarrow> null
    | (mk\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s ((mk\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (_) (_) (\<lfloor>\<B>\<A>\<L>\<A>\<N>\<C>\<E>\<rfloor>))) (_)) \<Rightarrow> (f (\<B>\<A>\<L>\<A>\<N>\<C>\<E>)))"

(* 115 ************************************ 1508 + 10 *)
definition "select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<N>\<K> = select_object_any\<^sub>S\<^sub>e\<^sub>t"
definition "select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<W>\<N>\<E>\<R> = select_object_any\<^sub>S\<^sub>e\<^sub>t"
definition "select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<N>\<K> = select_object_any\<^sub>S\<^sub>e\<^sub>t"
definition "select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<O>\<W>\<N>\<E>\<R> = select_object_any\<^sub>S\<^sub>e\<^sub>t"
definition "select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<N>\<K> = select_object_any\<^sub>S\<^sub>e\<^sub>t"
definition "select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<O>\<W>\<N>\<E>\<R> = select_object_any\<^sub>S\<^sub>e\<^sub>t"
definition "select\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S> = select_object\<^sub>S\<^sub>e\<^sub>t"
definition "select\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<C>\<L>\<I>\<E>\<N>\<T>\<S> = select_object\<^sub>S\<^sub>e\<^sub>t"
definition "select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S> = select_object\<^sub>S\<^sub>e\<^sub>t"
definition "select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<N>\<K>\<S> = select_object\<^sub>S\<^sub>e\<^sub>t"

(* 116 ************************************ 1518 + 28 *)
consts dot\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T> :: "(\<AA>, '\<alpha>) val \<Rightarrow> (\<AA>, Currency option option) val" ("(_) .overdraft")
consts dot\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> (\<AA>, Currency option option) val" ("(_) .overdraft@pre")
consts dot\<M>\<A>\<X> :: "(\<AA>, '\<alpha>) val \<Rightarrow> (\<AA>, Currency option option) val" ("(_) .max")
consts dot\<M>\<A>\<X>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> (\<AA>, Currency option option) val" ("(_) .max@pre")
consts dot_0_\<B>\<A>\<N>\<K> :: "(\<AA>, '\<alpha>) val \<Rightarrow> Bank" ("(_) .bank")
consts dot_0_\<B>\<A>\<N>\<K>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> Bank" ("(_) .bank@pre")
consts dot_0_\<O>\<W>\<N>\<E>\<R> :: "(\<AA>, '\<alpha>) val \<Rightarrow> Client" ("(_) .owner")
consts dot_0_\<O>\<W>\<N>\<E>\<R>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> Client" ("(_) .owner@pre")
consts dot\<I>\<D> :: "(\<AA>, '\<alpha>) val \<Rightarrow> Integer" ("(_) .id")
consts dot\<I>\<D>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> Integer" ("(_) .id@pre")
consts dot\<B>\<A>\<L>\<A>\<N>\<C>\<E> :: "(\<AA>, '\<alpha>) val \<Rightarrow> (\<AA>, Currency option option) val" ("(_) .balance")
consts dot\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> (\<AA>, Currency option option) val" ("(_) .balance@pre")
consts dot_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S> :: "(\<AA>, '\<alpha>) val \<Rightarrow> Set_Account" ("(_) .b'_accounts")
consts dot_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> Set_Account" ("(_) .b'_accounts@pre")
consts dot_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S> :: "(\<AA>, '\<alpha>) val \<Rightarrow> Set_Client" ("(_) .clients")
consts dot_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> Set_Client" ("(_) .clients@pre")
consts dot\<N>\<A>\<M>\<E> :: "(\<AA>, '\<alpha>) val \<Rightarrow> String" ("(_) .name")
consts dot\<N>\<A>\<M>\<E>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> String" ("(_) .name@pre")
consts dot_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S> :: "(\<AA>, '\<alpha>) val \<Rightarrow> Set_Account" ("(_) .c'_accounts")
consts dot_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> Set_Account" ("(_) .c'_accounts@pre")
consts dot_1_\<B>\<A>\<N>\<K>\<S> :: "(\<AA>, '\<alpha>) val \<Rightarrow> Set_Bank" ("(_) .banks")
consts dot_1_\<B>\<A>\<N>\<K>\<S>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> Set_Bank" ("(_) .banks@pre")
consts dot\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E> :: "(\<AA>, '\<alpha>) val \<Rightarrow> String" ("(_) .clientname")
consts dot\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> String" ("(_) .clientname@pre")
consts dot\<A>\<D>\<D>\<R>\<E>\<S>\<S> :: "(\<AA>, '\<alpha>) val \<Rightarrow> String" ("(_) .address")
consts dot\<A>\<D>\<D>\<R>\<E>\<S>\<S>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> String" ("(_) .address@pre")
consts dot\<A>\<G>\<E> :: "(\<AA>, '\<alpha>) val \<Rightarrow> Integer" ("(_) .age")
consts dot\<A>\<G>\<E>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> Integer" ("(_) .age@pre")

(* 117 ************************************ 1546 + 44 *)
defs(overloaded) dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T> : "(x::Current) .overdraft \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (in_post_state) ((select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T>at_pre : "(x::Current) .overdraft@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (in_pre_state) ((select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<M>\<A>\<X> : "(x::Savings) .max \<equiv> (eval_extract (x) ((deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (in_post_state) ((select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<M>\<A>\<X> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<M>\<A>\<X>at_pre : "(x::Savings) .max@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (in_pre_state) ((select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<M>\<A>\<X> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K> : "(x::Account) .bank \<equiv> (eval_extract (x) ((deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (in_post_state) ((deref_assocs\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K> (in_post_state) ((select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<N>\<K> ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_post_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R> : "(x::Account) .owner \<equiv> (eval_extract (x) ((deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (in_post_state) ((deref_assocs\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R> (in_post_state) ((select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<O>\<W>\<N>\<E>\<R> ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_post_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<I>\<D> : "(x::Account) .id \<equiv> (eval_extract (x) ((deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (in_post_state) ((select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<I>\<D> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E> : "(x::Account) .balance \<equiv> (eval_extract (x) ((deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (in_post_state) ((select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre : "(x::Account) .bank@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (in_pre_state) ((deref_assocs\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K> (in_pre_state) ((select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<N>\<K> ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_pre_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre : "(x::Account) .owner@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (in_pre_state) ((deref_assocs\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R> (in_pre_state) ((select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<O>\<W>\<N>\<E>\<R> ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_pre_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<I>\<D>at_pre : "(x::Account) .id@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (in_pre_state) ((select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<I>\<D> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre : "(x::Account) .balance@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (in_pre_state) ((select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S> : "(x::Bank) .b_accounts \<equiv> (eval_extract (x) ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_post_state) ((deref_assocs\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S> (in_post_state) ((select\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S> ((deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (in_post_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S> : "(x::Bank) .clients \<equiv> (eval_extract (x) ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_post_state) ((deref_assocs\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S> (in_post_state) ((select\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<C>\<L>\<I>\<E>\<N>\<T>\<S> ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_post_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<N>\<A>\<M>\<E> : "(x::Bank) .name \<equiv> (eval_extract (x) ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_post_state) ((select\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<N>\<A>\<M>\<E> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>at_pre : "(x::Bank) .b_accounts@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_pre_state) ((deref_assocs\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S> (in_pre_state) ((select\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S> ((deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (in_pre_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S>at_pre : "(x::Bank) .clients@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_pre_state) ((deref_assocs\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S> (in_pre_state) ((select\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<C>\<L>\<I>\<E>\<N>\<T>\<S> ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_pre_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<N>\<A>\<M>\<E>at_pre : "(x::Bank) .name@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_pre_state) ((select\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<N>\<A>\<M>\<E> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S> : "(x::Client) .c_accounts \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_post_state) ((deref_assocs\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S> (in_post_state) ((select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S> ((deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (in_post_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<B>\<A>\<N>\<K>\<S> : "(x::Client) .banks \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_post_state) ((deref_assocs\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<B>\<A>\<N>\<K>\<S> (in_post_state) ((select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<N>\<K>\<S> ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_post_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E> : "(x::Client) .clientname \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_post_state) ((select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<D>\<D>\<R>\<E>\<S>\<S> : "(x::Client) .address \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_post_state) ((select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<D>\<D>\<R>\<E>\<S>\<S> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<G>\<E> : "(x::Client) .age \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_post_state) ((select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<G>\<E> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>at_pre : "(x::Client) .c_accounts@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_pre_state) ((deref_assocs\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S> (in_pre_state) ((select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S> ((deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (in_pre_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<B>\<A>\<N>\<K>\<S>at_pre : "(x::Client) .banks@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_pre_state) ((deref_assocs\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<B>\<A>\<N>\<K>\<S> (in_pre_state) ((select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<N>\<K>\<S> ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_pre_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E>at_pre : "(x::Client) .clientname@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_pre_state) ((select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<D>\<D>\<R>\<E>\<S>\<S>at_pre : "(x::Client) .address@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_pre_state) ((select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<D>\<D>\<R>\<E>\<S>\<S> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<G>\<E>at_pre : "(x::Client) .age@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_pre_state) ((select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<G>\<E> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K> : "(x::Current) .bank \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (in_post_state) ((deref_assocs\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K> (in_post_state) ((select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<N>\<K> ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_post_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R> : "(x::Current) .owner \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (in_post_state) ((deref_assocs\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R> (in_post_state) ((select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<W>\<N>\<E>\<R> ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_post_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<I>\<D> : "(x::Current) .id \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (in_post_state) ((select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<I>\<D> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E> : "(x::Current) .balance \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (in_post_state) ((select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre : "(x::Current) .bank@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (in_pre_state) ((deref_assocs\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K> (in_pre_state) ((select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<N>\<K> ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_pre_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre : "(x::Current) .owner@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (in_pre_state) ((deref_assocs\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R> (in_pre_state) ((select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<W>\<N>\<E>\<R> ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_pre_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<I>\<D>at_pre : "(x::Current) .id@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (in_pre_state) ((select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<I>\<D> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre : "(x::Current) .balance@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (in_pre_state) ((select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K> : "(x::Savings) .bank \<equiv> (eval_extract (x) ((deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (in_post_state) ((deref_assocs\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K> (in_post_state) ((select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<N>\<K> ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_post_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R> : "(x::Savings) .owner \<equiv> (eval_extract (x) ((deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (in_post_state) ((deref_assocs\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R> (in_post_state) ((select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<O>\<W>\<N>\<E>\<R> ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_post_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<I>\<D> : "(x::Savings) .id \<equiv> (eval_extract (x) ((deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (in_post_state) ((select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<I>\<D> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<L>\<A>\<N>\<C>\<E> : "(x::Savings) .balance \<equiv> (eval_extract (x) ((deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (in_post_state) ((select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<L>\<A>\<N>\<C>\<E> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K>at_pre : "(x::Savings) .bank@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (in_pre_state) ((deref_assocs\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K> (in_pre_state) ((select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<N>\<K> ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_pre_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R>at_pre : "(x::Savings) .owner@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (in_pre_state) ((deref_assocs\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R> (in_pre_state) ((select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<O>\<W>\<N>\<E>\<R> ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_pre_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<I>\<D>at_pre : "(x::Savings) .id@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (in_pre_state) ((select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<I>\<D> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre : "(x::Savings) .balance@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (in_pre_state) ((select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<L>\<A>\<N>\<C>\<E> (reconst_basetype))))))"

(* 118 ************************************ 1590 + 1 *)
lemmas dot_accessor = dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T>
                            dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T>at_pre
                            dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<M>\<A>\<X>
                            dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<M>\<A>\<X>at_pre
                            dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>
                            dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>
                            dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<I>\<D>
                            dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>
                            dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre
                            dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre
                            dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<I>\<D>at_pre
                            dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre
                            dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>
                            dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S>
                            dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<N>\<A>\<M>\<E>
                            dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>at_pre
                            dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S>at_pre
                            dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<N>\<A>\<M>\<E>at_pre
                            dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>
                            dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<B>\<A>\<N>\<K>\<S>
                            dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E>
                            dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<D>\<D>\<R>\<E>\<S>\<S>
                            dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<G>\<E>
                            dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>at_pre
                            dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<B>\<A>\<N>\<K>\<S>at_pre
                            dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E>at_pre
                            dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<D>\<D>\<R>\<E>\<S>\<S>at_pre
                            dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<G>\<E>at_pre
                            dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>
                            dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>
                            dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<I>\<D>
                            dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>
                            dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre
                            dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre
                            dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<I>\<D>at_pre
                            dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre
                            dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K>
                            dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R>
                            dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<I>\<D>
                            dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<L>\<A>\<N>\<C>\<E>
                            dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K>at_pre
                            dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R>at_pre
                            dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<I>\<D>at_pre
                            dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre

(* 119 ************************************ 1591 + 1 *)
subsection{* Context Passing *}

(* 120 ************************************ 1592 + 1 *)
lemmas[simp,code_unfold] = eval_extract_def

(* 121 ************************************ 1593 + 44 *)
lemma cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T> : "(cp ((\<lambda>X. (X::Current) .overdraft)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T>at_pre : "(cp ((\<lambda>X. (X::Current) .overdraft@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<M>\<A>\<X> : "(cp ((\<lambda>X. (X::Savings) .max)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<M>\<A>\<X>at_pre : "(cp ((\<lambda>X. (X::Savings) .max@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K> : "(cp ((\<lambda>X. (X::Account) .bank)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R> : "(cp ((\<lambda>X. (X::Account) .owner)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<I>\<D> : "(cp ((\<lambda>X. (X::Account) .id)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E> : "(cp ((\<lambda>X. (X::Account) .balance)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre : "(cp ((\<lambda>X. (X::Account) .bank@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre : "(cp ((\<lambda>X. (X::Account) .owner@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<I>\<D>at_pre : "(cp ((\<lambda>X. (X::Account) .id@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre : "(cp ((\<lambda>X. (X::Account) .balance@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S> : "(cp ((\<lambda>X. (X::Bank) .b_accounts)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S> : "(cp ((\<lambda>X. (X::Bank) .clients)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<N>\<A>\<M>\<E> : "(cp ((\<lambda>X. (X::Bank) .name)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>at_pre : "(cp ((\<lambda>X. (X::Bank) .b_accounts@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S>at_pre : "(cp ((\<lambda>X. (X::Bank) .clients@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<N>\<A>\<M>\<E>at_pre : "(cp ((\<lambda>X. (X::Bank) .name@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S> : "(cp ((\<lambda>X. (X::Client) .c_accounts)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<B>\<A>\<N>\<K>\<S> : "(cp ((\<lambda>X. (X::Client) .banks)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E> : "(cp ((\<lambda>X. (X::Client) .clientname)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<D>\<D>\<R>\<E>\<S>\<S> : "(cp ((\<lambda>X. (X::Client) .address)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<G>\<E> : "(cp ((\<lambda>X. (X::Client) .age)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>at_pre : "(cp ((\<lambda>X. (X::Client) .c_accounts@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<B>\<A>\<N>\<K>\<S>at_pre : "(cp ((\<lambda>X. (X::Client) .banks@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E>at_pre : "(cp ((\<lambda>X. (X::Client) .clientname@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<D>\<D>\<R>\<E>\<S>\<S>at_pre : "(cp ((\<lambda>X. (X::Client) .address@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<G>\<E>at_pre : "(cp ((\<lambda>X. (X::Client) .age@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K> : "(cp ((\<lambda>X. (X::Current) .bank)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R> : "(cp ((\<lambda>X. (X::Current) .owner)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<I>\<D> : "(cp ((\<lambda>X. (X::Current) .id)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E> : "(cp ((\<lambda>X. (X::Current) .balance)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre : "(cp ((\<lambda>X. (X::Current) .bank@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre : "(cp ((\<lambda>X. (X::Current) .owner@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<I>\<D>at_pre : "(cp ((\<lambda>X. (X::Current) .id@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre : "(cp ((\<lambda>X. (X::Current) .balance@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K> : "(cp ((\<lambda>X. (X::Savings) .bank)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R> : "(cp ((\<lambda>X. (X::Savings) .owner)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<I>\<D> : "(cp ((\<lambda>X. (X::Savings) .id)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<L>\<A>\<N>\<C>\<E> : "(cp ((\<lambda>X. (X::Savings) .balance)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K>at_pre : "(cp ((\<lambda>X. (X::Savings) .bank@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R>at_pre : "(cp ((\<lambda>X. (X::Savings) .owner@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<I>\<D>at_pre : "(cp ((\<lambda>X. (X::Savings) .id@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre : "(cp ((\<lambda>X. (X::Savings) .balance@pre)))"
by(auto simp: dot_accessor cp_def)

(* 122 ************************************ 1637 + 1 *)
lemmas[simp,code_unfold] = cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T>
                            cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T>at_pre
                            cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<M>\<A>\<X>
                            cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<M>\<A>\<X>at_pre
                            cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>
                            cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>
                            cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<I>\<D>
                            cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>
                            cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre
                            cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre
                            cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<I>\<D>at_pre
                            cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre
                            cp_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>
                            cp_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S>
                            cp_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<N>\<A>\<M>\<E>
                            cp_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>at_pre
                            cp_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S>at_pre
                            cp_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<N>\<A>\<M>\<E>at_pre
                            cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>
                            cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<B>\<A>\<N>\<K>\<S>
                            cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E>
                            cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<D>\<D>\<R>\<E>\<S>\<S>
                            cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<G>\<E>
                            cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>at_pre
                            cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<B>\<A>\<N>\<K>\<S>at_pre
                            cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E>at_pre
                            cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<D>\<D>\<R>\<E>\<S>\<S>at_pre
                            cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<G>\<E>at_pre
                            cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>
                            cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>
                            cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<I>\<D>
                            cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>
                            cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre
                            cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre
                            cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<I>\<D>at_pre
                            cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre
                            cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K>
                            cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R>
                            cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<I>\<D>
                            cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<L>\<A>\<N>\<C>\<E>
                            cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K>at_pre
                            cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R>at_pre
                            cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<I>\<D>at_pre
                            cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre

(* 123 ************************************ 1638 + 1 *)
subsection{* Execution with Invalid or Null as Argument *}

(* 124 ************************************ 1639 + 88 *)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T>_invalid : "(invalid::Current) .overdraft = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T>_null : "(null::Current) .overdraft = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T>at_pre_invalid : "(invalid::Current) .overdraft@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T>at_pre_null : "(null::Current) .overdraft@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<M>\<A>\<X>_invalid : "(invalid::Savings) .max = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<M>\<A>\<X>_null : "(null::Savings) .max = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<M>\<A>\<X>at_pre_invalid : "(invalid::Savings) .max@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<M>\<A>\<X>at_pre_null : "(null::Savings) .max@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>_invalid : "(invalid::Account) .bank = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>_null : "(null::Account) .bank = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>_invalid : "(invalid::Account) .owner = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>_null : "(null::Account) .owner = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<I>\<D>_invalid : "(invalid::Account) .id = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<I>\<D>_null : "(null::Account) .id = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>_invalid : "(invalid::Account) .balance = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>_null : "(null::Account) .balance = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre_invalid : "(invalid::Account) .bank@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre_null : "(null::Account) .bank@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre_invalid : "(invalid::Account) .owner@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre_null : "(null::Account) .owner@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<I>\<D>at_pre_invalid : "(invalid::Account) .id@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<I>\<D>at_pre_null : "(null::Account) .id@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre_invalid : "(invalid::Account) .balance@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre_null : "(null::Account) .balance@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>_invalid : "(invalid::Bank) .b_accounts = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>_null : "(null::Bank) .b_accounts = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S>_invalid : "(invalid::Bank) .clients = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S>_null : "(null::Bank) .clients = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<N>\<A>\<M>\<E>_invalid : "(invalid::Bank) .name = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<N>\<A>\<M>\<E>_null : "(null::Bank) .name = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>at_pre_invalid : "(invalid::Bank) .b_accounts@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>at_pre_null : "(null::Bank) .b_accounts@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S>at_pre_invalid : "(invalid::Bank) .clients@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S>at_pre_null : "(null::Bank) .clients@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<N>\<A>\<M>\<E>at_pre_invalid : "(invalid::Bank) .name@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<N>\<A>\<M>\<E>at_pre_null : "(null::Bank) .name@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>_invalid : "(invalid::Client) .c_accounts = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>_null : "(null::Client) .c_accounts = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<B>\<A>\<N>\<K>\<S>_invalid : "(invalid::Client) .banks = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<B>\<A>\<N>\<K>\<S>_null : "(null::Client) .banks = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E>_invalid : "(invalid::Client) .clientname = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E>_null : "(null::Client) .clientname = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<D>\<D>\<R>\<E>\<S>\<S>_invalid : "(invalid::Client) .address = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<D>\<D>\<R>\<E>\<S>\<S>_null : "(null::Client) .address = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<G>\<E>_invalid : "(invalid::Client) .age = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<G>\<E>_null : "(null::Client) .age = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>at_pre_invalid : "(invalid::Client) .c_accounts@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>at_pre_null : "(null::Client) .c_accounts@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<B>\<A>\<N>\<K>\<S>at_pre_invalid : "(invalid::Client) .banks@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<B>\<A>\<N>\<K>\<S>at_pre_null : "(null::Client) .banks@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E>at_pre_invalid : "(invalid::Client) .clientname@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E>at_pre_null : "(null::Client) .clientname@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<D>\<D>\<R>\<E>\<S>\<S>at_pre_invalid : "(invalid::Client) .address@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<D>\<D>\<R>\<E>\<S>\<S>at_pre_null : "(null::Client) .address@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<G>\<E>at_pre_invalid : "(invalid::Client) .age@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<G>\<E>at_pre_null : "(null::Client) .age@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>_invalid : "(invalid::Current) .bank = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>_null : "(null::Current) .bank = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>_invalid : "(invalid::Current) .owner = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>_null : "(null::Current) .owner = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<I>\<D>_invalid : "(invalid::Current) .id = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<I>\<D>_null : "(null::Current) .id = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>_invalid : "(invalid::Current) .balance = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>_null : "(null::Current) .balance = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre_invalid : "(invalid::Current) .bank@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre_null : "(null::Current) .bank@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre_invalid : "(invalid::Current) .owner@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre_null : "(null::Current) .owner@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<I>\<D>at_pre_invalid : "(invalid::Current) .id@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<I>\<D>at_pre_null : "(null::Current) .id@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre_invalid : "(invalid::Current) .balance@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre_null : "(null::Current) .balance@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K>_invalid : "(invalid::Savings) .bank = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K>_null : "(null::Savings) .bank = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R>_invalid : "(invalid::Savings) .owner = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R>_null : "(null::Savings) .owner = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<I>\<D>_invalid : "(invalid::Savings) .id = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<I>\<D>_null : "(null::Savings) .id = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<L>\<A>\<N>\<C>\<E>_invalid : "(invalid::Savings) .balance = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<L>\<A>\<N>\<C>\<E>_null : "(null::Savings) .balance = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K>at_pre_invalid : "(invalid::Savings) .bank@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K>at_pre_null : "(null::Savings) .bank@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R>at_pre_invalid : "(invalid::Savings) .owner@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R>at_pre_null : "(null::Savings) .owner@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<I>\<D>at_pre_invalid : "(invalid::Savings) .id@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<I>\<D>at_pre_null : "(null::Savings) .id@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre_invalid : "(invalid::Savings) .balance@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre_null : "(null::Savings) .balance@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)

(* 125 ************************************ 1727 + 1 *)
subsection{* Representation in States *}

(* 126 ************************************ 1728 + 44 *)
lemma defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T> : "\<tau> \<Turnstile> (\<delta> ((X::Current) .overdraft)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .overdraft)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .overdraft)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Current) .overdraft@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .overdraft@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .overdraft@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<M>\<A>\<X> : "\<tau> \<Turnstile> (\<delta> ((X::Savings) .max)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .max)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<M>\<A>\<X>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .max)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<M>\<A>\<X>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<M>\<A>\<X>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Savings) .max@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .max@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<M>\<A>\<X>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .max@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<M>\<A>\<X>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K> : "\<tau> \<Turnstile> (\<delta> ((X::Account) .bank)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .bank)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .bank)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R> : "\<tau> \<Turnstile> (\<delta> ((X::Account) .owner)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .owner)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .owner)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<I>\<D> : "\<tau> \<Turnstile> (\<delta> ((X::Account) .id)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .id)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<I>\<D>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .id)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<I>\<D>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E> : "\<tau> \<Turnstile> (\<delta> ((X::Account) .balance)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .balance)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .balance)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Account) .bank@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .bank@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .bank@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Account) .owner@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .owner@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .owner@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<I>\<D>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Account) .id@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .id@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<I>\<D>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .id@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<I>\<D>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Account) .balance@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .balance@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .balance@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S> : "\<tau> \<Turnstile> (\<delta> ((X::Bank) .b_accounts)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .b_accounts)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .b_accounts)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S> : "\<tau> \<Turnstile> (\<delta> ((X::Bank) .clients)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .clients)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .clients)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<N>\<A>\<M>\<E> : "\<tau> \<Turnstile> (\<delta> ((X::Bank) .name)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .name)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<N>\<A>\<M>\<E>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .name)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<N>\<A>\<M>\<E>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Bank) .b_accounts@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .b_accounts@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .b_accounts@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Bank) .clients@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .clients@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .clients@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<N>\<A>\<M>\<E>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Bank) .name@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .name@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<N>\<A>\<M>\<E>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .name@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<N>\<A>\<M>\<E>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S> : "\<tau> \<Turnstile> (\<delta> ((X::Client) .c_accounts)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .c_accounts)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .c_accounts)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<B>\<A>\<N>\<K>\<S> : "\<tau> \<Turnstile> (\<delta> ((X::Client) .banks)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .banks)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<B>\<A>\<N>\<K>\<S>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .banks)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<B>\<A>\<N>\<K>\<S>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E> : "\<tau> \<Turnstile> (\<delta> ((X::Client) .clientname)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .clientname)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .clientname)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<D>\<D>\<R>\<E>\<S>\<S> : "\<tau> \<Turnstile> (\<delta> ((X::Client) .address)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .address)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<D>\<D>\<R>\<E>\<S>\<S>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .address)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<D>\<D>\<R>\<E>\<S>\<S>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<G>\<E> : "\<tau> \<Turnstile> (\<delta> ((X::Client) .age)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .age)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<G>\<E>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .age)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<G>\<E>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Client) .c_accounts@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .c_accounts@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .c_accounts@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<B>\<A>\<N>\<K>\<S>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Client) .banks@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .banks@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<B>\<A>\<N>\<K>\<S>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .banks@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<B>\<A>\<N>\<K>\<S>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Client) .clientname@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .clientname@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .clientname@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<D>\<D>\<R>\<E>\<S>\<S>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Client) .address@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .address@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<D>\<D>\<R>\<E>\<S>\<S>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .address@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<D>\<D>\<R>\<E>\<S>\<S>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<G>\<E>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Client) .age@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .age@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<G>\<E>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .age@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<A>\<G>\<E>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K> : "\<tau> \<Turnstile> (\<delta> ((X::Current) .bank)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .bank)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .bank)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R> : "\<tau> \<Turnstile> (\<delta> ((X::Current) .owner)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .owner)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .owner)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<I>\<D> : "\<tau> \<Turnstile> (\<delta> ((X::Current) .id)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .id)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<I>\<D>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .id)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<I>\<D>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E> : "\<tau> \<Turnstile> (\<delta> ((X::Current) .balance)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .balance)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .balance)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Current) .bank@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .bank@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .bank@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Current) .owner@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .owner@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .owner@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<I>\<D>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Current) .id@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .id@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<I>\<D>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .id@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<I>\<D>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Current) .balance@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .balance@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .balance@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K> : "\<tau> \<Turnstile> (\<delta> ((X::Savings) .bank)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .bank)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .bank)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R> : "\<tau> \<Turnstile> (\<delta> ((X::Savings) .owner)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .owner)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .owner)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<I>\<D> : "\<tau> \<Turnstile> (\<delta> ((X::Savings) .id)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .id)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<I>\<D>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .id)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<I>\<D>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<L>\<A>\<N>\<C>\<E> : "\<tau> \<Turnstile> (\<delta> ((X::Savings) .balance)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .balance)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<L>\<A>\<N>\<C>\<E>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .balance)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<L>\<A>\<N>\<C>\<E>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Savings) .bank@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .bank@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .bank@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Savings) .owner@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .owner@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .owner@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<I>\<D>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Savings) .id@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .id@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<I>\<D>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .id@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<I>\<D>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::Savings) .balance@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .balance@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .balance@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre_null)
by(simp add: defined_split)

(* 127 ************************************ 1772 + 12 *)
lemma is_repr_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K> : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::Account) .bank))"
shows "(is_represented_in_state (in_post_state) (X .bank) (Bank) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_post_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K> is_represented_in_state_def select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<N>\<K>_def deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_def in_post_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_post_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K> is_represented_in_state_def deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  apply(simp add: deref_assocs\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>_def deref_assocs_def)
  apply(case_tac "(assocs ((in_post_state (\<tau>))) (oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>))", simp add: invalid_def bot_option_def, simp add: select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<N>\<K>_def)
  proof - fix r typeoid          let ?t = "(Some ((Some (r)))) \<in> (Some o OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_\<AA>) ` (ran ((heap ((in_post_state (\<tau>))))))"
          let ?sel_any = "(select_object_any\<^sub>S\<^sub>e\<^sub>t ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_post_state) (reconst_basetype))))" show "((?sel_any) (typeoid) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  proof - fix aa show "\<tau> \<Turnstile> (\<delta> (((?sel_any) (aa)))) \<Longrightarrow> ((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  apply(drule select_object_any_exec\<^sub>S\<^sub>e\<^sub>t[simplified foundation22], erule exE)
  proof - fix e show "((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ((?sel_any) (aa) (\<tau>)) = (deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_post_state) (reconst_basetype) (e) (\<tau>)) \<Longrightarrow> ?t"
  apply(simp add: deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k_def)
  apply(case_tac "(heap ((in_post_state (\<tau>))) (e))", simp add: invalid_def bot_option_def, simp)
  proof - fix aaa show "(case aaa of (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (obj)) \<Rightarrow> (reconst_basetype (obj) (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))) = (Some ((Some (r)))) \<Longrightarrow> (heap ((in_post_state (\<tau>))) (e)) = (Some (aaa)) \<Longrightarrow> ?t"
  apply(case_tac "aaa", auto simp: invalid_def bot_option_def image_def ran_def)
  apply(rule exI[where x = "(in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (r))"], simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_\<AA>_def Let_def reconst_basetype_def split: split_if_asm)
by(rule) qed 
  apply_end((blast)+)
 qed 
  apply_end(simp_all only: )
  apply_end(simp add: foundation16 bot_option_def null_option_def)
 qed qed qed qed 
  apply_end(simp_all)
 qed
lemma is_repr_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R> : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::Account) .owner))"
shows "(is_represented_in_state (in_post_state) (X .owner) (Client) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_post_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R> is_represented_in_state_def select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<O>\<W>\<N>\<E>\<R>_def deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_def in_post_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_post_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R> is_represented_in_state_def deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  apply(simp add: deref_assocs\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>_def deref_assocs_def)
  apply(case_tac "(assocs ((in_post_state (\<tau>))) (oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>))", simp add: invalid_def bot_option_def, simp add: select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<O>\<W>\<N>\<E>\<R>_def)
  proof - fix r typeoid          let ?t = "(Some ((Some (r)))) \<in> (Some o OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_\<AA>) ` (ran ((heap ((in_post_state (\<tau>))))))"
          let ?sel_any = "(select_object_any\<^sub>S\<^sub>e\<^sub>t ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_post_state) (reconst_basetype))))" show "((?sel_any) (typeoid) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  proof - fix aa show "\<tau> \<Turnstile> (\<delta> (((?sel_any) (aa)))) \<Longrightarrow> ((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  apply(drule select_object_any_exec\<^sub>S\<^sub>e\<^sub>t[simplified foundation22], erule exE)
  proof - fix e show "((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ((?sel_any) (aa) (\<tau>)) = (deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_post_state) (reconst_basetype) (e) (\<tau>)) \<Longrightarrow> ?t"
  apply(simp add: deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def)
  apply(case_tac "(heap ((in_post_state (\<tau>))) (e))", simp add: invalid_def bot_option_def, simp)
  proof - fix aaa show "(case aaa of (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (obj)) \<Rightarrow> (reconst_basetype (obj) (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))) = (Some ((Some (r)))) \<Longrightarrow> (heap ((in_post_state (\<tau>))) (e)) = (Some (aaa)) \<Longrightarrow> ?t"
  apply(case_tac "aaa", auto simp: invalid_def bot_option_def image_def ran_def)
  apply(rule exI[where x = "(in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (r))"], simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_\<AA>_def Let_def reconst_basetype_def split: split_if_asm)
by(rule) qed 
  apply_end((blast)+)
 qed 
  apply_end(simp_all only: )
  apply_end(simp add: foundation16 bot_option_def null_option_def)
 qed qed qed qed 
  apply_end(simp_all)
 qed
lemma is_repr_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::Account) .bank@pre))"
shows "(is_represented_in_state (in_pre_state) (X .bank@pre) (Bank) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_pre_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre is_represented_in_state_def select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<N>\<K>_def deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_def in_pre_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_pre_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre is_represented_in_state_def deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  apply(simp add: deref_assocs\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>_def deref_assocs_def)
  apply(case_tac "(assocs ((in_pre_state (\<tau>))) (oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>))", simp add: invalid_def bot_option_def, simp add: select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<B>\<A>\<N>\<K>_def)
  proof - fix r typeoid          let ?t = "(Some ((Some (r)))) \<in> (Some o OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_\<AA>) ` (ran ((heap ((in_pre_state (\<tau>))))))"
          let ?sel_any = "(select_object_any\<^sub>S\<^sub>e\<^sub>t ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_pre_state) (reconst_basetype))))" show "((?sel_any) (typeoid) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  proof - fix aa show "\<tau> \<Turnstile> (\<delta> (((?sel_any) (aa)))) \<Longrightarrow> ((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  apply(drule select_object_any_exec\<^sub>S\<^sub>e\<^sub>t[simplified foundation22], erule exE)
  proof - fix e show "((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ((?sel_any) (aa) (\<tau>)) = (deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_pre_state) (reconst_basetype) (e) (\<tau>)) \<Longrightarrow> ?t"
  apply(simp add: deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k_def)
  apply(case_tac "(heap ((in_pre_state (\<tau>))) (e))", simp add: invalid_def bot_option_def, simp)
  proof - fix aaa show "(case aaa of (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (obj)) \<Rightarrow> (reconst_basetype (obj) (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))) = (Some ((Some (r)))) \<Longrightarrow> (heap ((in_pre_state (\<tau>))) (e)) = (Some (aaa)) \<Longrightarrow> ?t"
  apply(case_tac "aaa", auto simp: invalid_def bot_option_def image_def ran_def)
  apply(rule exI[where x = "(in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (r))"], simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_\<AA>_def Let_def reconst_basetype_def split: split_if_asm)
by(rule) qed 
  apply_end((blast)+)
 qed 
  apply_end(simp_all only: )
  apply_end(simp add: foundation16 bot_option_def null_option_def)
 qed qed qed qed 
  apply_end(simp_all)
 qed
lemma is_repr_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::Account) .owner@pre))"
shows "(is_represented_in_state (in_pre_state) (X .owner@pre) (Client) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_pre_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre is_represented_in_state_def select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<O>\<W>\<N>\<E>\<R>_def deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_def in_pre_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_pre_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre is_represented_in_state_def deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  apply(simp add: deref_assocs\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>_def deref_assocs_def)
  apply(case_tac "(assocs ((in_pre_state (\<tau>))) (oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>))", simp add: invalid_def bot_option_def, simp add: select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<O>\<W>\<N>\<E>\<R>_def)
  proof - fix r typeoid          let ?t = "(Some ((Some (r)))) \<in> (Some o OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_\<AA>) ` (ran ((heap ((in_pre_state (\<tau>))))))"
          let ?sel_any = "(select_object_any\<^sub>S\<^sub>e\<^sub>t ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_pre_state) (reconst_basetype))))" show "((?sel_any) (typeoid) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  proof - fix aa show "\<tau> \<Turnstile> (\<delta> (((?sel_any) (aa)))) \<Longrightarrow> ((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  apply(drule select_object_any_exec\<^sub>S\<^sub>e\<^sub>t[simplified foundation22], erule exE)
  proof - fix e show "((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ((?sel_any) (aa) (\<tau>)) = (deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_pre_state) (reconst_basetype) (e) (\<tau>)) \<Longrightarrow> ?t"
  apply(simp add: deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def)
  apply(case_tac "(heap ((in_pre_state (\<tau>))) (e))", simp add: invalid_def bot_option_def, simp)
  proof - fix aaa show "(case aaa of (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (obj)) \<Rightarrow> (reconst_basetype (obj) (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))) = (Some ((Some (r)))) \<Longrightarrow> (heap ((in_pre_state (\<tau>))) (e)) = (Some (aaa)) \<Longrightarrow> ?t"
  apply(case_tac "aaa", auto simp: invalid_def bot_option_def image_def ran_def)
  apply(rule exI[where x = "(in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (r))"], simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_\<AA>_def Let_def reconst_basetype_def split: split_if_asm)
by(rule) qed 
  apply_end((blast)+)
 qed 
  apply_end(simp_all only: )
  apply_end(simp add: foundation16 bot_option_def null_option_def)
 qed qed qed qed 
  apply_end(simp_all)
 qed
lemma is_repr_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K> : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::Current) .bank))"
shows "(is_represented_in_state (in_post_state) (X .bank) (Bank) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_post_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K> is_represented_in_state_def select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<N>\<K>_def deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_def in_post_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_post_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K> is_represented_in_state_def deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  apply(simp add: deref_assocs\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>_def deref_assocs_def)
  apply(case_tac "(assocs ((in_post_state (\<tau>))) (oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>))", simp add: invalid_def bot_option_def, simp add: select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<N>\<K>_def)
  proof - fix r typeoid          let ?t = "(Some ((Some (r)))) \<in> (Some o OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_\<AA>) ` (ran ((heap ((in_post_state (\<tau>))))))"
          let ?sel_any = "(select_object_any\<^sub>S\<^sub>e\<^sub>t ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_post_state) (reconst_basetype))))" show "((?sel_any) (typeoid) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  proof - fix aa show "\<tau> \<Turnstile> (\<delta> (((?sel_any) (aa)))) \<Longrightarrow> ((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  apply(drule select_object_any_exec\<^sub>S\<^sub>e\<^sub>t[simplified foundation22], erule exE)
  proof - fix e show "((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ((?sel_any) (aa) (\<tau>)) = (deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_post_state) (reconst_basetype) (e) (\<tau>)) \<Longrightarrow> ?t"
  apply(simp add: deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k_def)
  apply(case_tac "(heap ((in_post_state (\<tau>))) (e))", simp add: invalid_def bot_option_def, simp)
  proof - fix aaa show "(case aaa of (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (obj)) \<Rightarrow> (reconst_basetype (obj) (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))) = (Some ((Some (r)))) \<Longrightarrow> (heap ((in_post_state (\<tau>))) (e)) = (Some (aaa)) \<Longrightarrow> ?t"
  apply(case_tac "aaa", auto simp: invalid_def bot_option_def image_def ran_def)
  apply(rule exI[where x = "(in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (r))"], simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_\<AA>_def Let_def reconst_basetype_def split: split_if_asm)
by(rule) qed 
  apply_end((blast)+)
 qed 
  apply_end(simp_all only: )
  apply_end(simp add: foundation16 bot_option_def null_option_def)
 qed qed qed qed 
  apply_end(simp_all)
 qed
lemma is_repr_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R> : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::Current) .owner))"
shows "(is_represented_in_state (in_post_state) (X .owner) (Client) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_post_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R> is_represented_in_state_def select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<W>\<N>\<E>\<R>_def deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_def in_post_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_post_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R> is_represented_in_state_def deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  apply(simp add: deref_assocs\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>_def deref_assocs_def)
  apply(case_tac "(assocs ((in_post_state (\<tau>))) (oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>))", simp add: invalid_def bot_option_def, simp add: select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<W>\<N>\<E>\<R>_def)
  proof - fix r typeoid          let ?t = "(Some ((Some (r)))) \<in> (Some o OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_\<AA>) ` (ran ((heap ((in_post_state (\<tau>))))))"
          let ?sel_any = "(select_object_any\<^sub>S\<^sub>e\<^sub>t ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_post_state) (reconst_basetype))))" show "((?sel_any) (typeoid) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  proof - fix aa show "\<tau> \<Turnstile> (\<delta> (((?sel_any) (aa)))) \<Longrightarrow> ((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  apply(drule select_object_any_exec\<^sub>S\<^sub>e\<^sub>t[simplified foundation22], erule exE)
  proof - fix e show "((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ((?sel_any) (aa) (\<tau>)) = (deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_post_state) (reconst_basetype) (e) (\<tau>)) \<Longrightarrow> ?t"
  apply(simp add: deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def)
  apply(case_tac "(heap ((in_post_state (\<tau>))) (e))", simp add: invalid_def bot_option_def, simp)
  proof - fix aaa show "(case aaa of (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (obj)) \<Rightarrow> (reconst_basetype (obj) (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))) = (Some ((Some (r)))) \<Longrightarrow> (heap ((in_post_state (\<tau>))) (e)) = (Some (aaa)) \<Longrightarrow> ?t"
  apply(case_tac "aaa", auto simp: invalid_def bot_option_def image_def ran_def)
  apply(rule exI[where x = "(in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (r))"], simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_\<AA>_def Let_def reconst_basetype_def split: split_if_asm)
by(rule) qed 
  apply_end((blast)+)
 qed 
  apply_end(simp_all only: )
  apply_end(simp add: foundation16 bot_option_def null_option_def)
 qed qed qed qed 
  apply_end(simp_all)
 qed
lemma is_repr_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::Current) .bank@pre))"
shows "(is_represented_in_state (in_pre_state) (X .bank@pre) (Bank) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_pre_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre is_represented_in_state_def select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<N>\<K>_def deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_def in_pre_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_pre_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>at_pre is_represented_in_state_def deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  apply(simp add: deref_assocs\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>_def deref_assocs_def)
  apply(case_tac "(assocs ((in_pre_state (\<tau>))) (oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<B>\<A>\<N>\<K>))", simp add: invalid_def bot_option_def, simp add: select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<B>\<A>\<N>\<K>_def)
  proof - fix r typeoid          let ?t = "(Some ((Some (r)))) \<in> (Some o OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_\<AA>) ` (ran ((heap ((in_pre_state (\<tau>))))))"
          let ?sel_any = "(select_object_any\<^sub>S\<^sub>e\<^sub>t ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_pre_state) (reconst_basetype))))" show "((?sel_any) (typeoid) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  proof - fix aa show "\<tau> \<Turnstile> (\<delta> (((?sel_any) (aa)))) \<Longrightarrow> ((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  apply(drule select_object_any_exec\<^sub>S\<^sub>e\<^sub>t[simplified foundation22], erule exE)
  proof - fix e show "((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ((?sel_any) (aa) (\<tau>)) = (deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_pre_state) (reconst_basetype) (e) (\<tau>)) \<Longrightarrow> ?t"
  apply(simp add: deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k_def)
  apply(case_tac "(heap ((in_pre_state (\<tau>))) (e))", simp add: invalid_def bot_option_def, simp)
  proof - fix aaa show "(case aaa of (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (obj)) \<Rightarrow> (reconst_basetype (obj) (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))) = (Some ((Some (r)))) \<Longrightarrow> (heap ((in_pre_state (\<tau>))) (e)) = (Some (aaa)) \<Longrightarrow> ?t"
  apply(case_tac "aaa", auto simp: invalid_def bot_option_def image_def ran_def)
  apply(rule exI[where x = "(in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (r))"], simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_\<AA>_def Let_def reconst_basetype_def split: split_if_asm)
by(rule) qed 
  apply_end((blast)+)
 qed 
  apply_end(simp_all only: )
  apply_end(simp add: foundation16 bot_option_def null_option_def)
 qed qed qed qed 
  apply_end(simp_all)
 qed
lemma is_repr_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::Current) .owner@pre))"
shows "(is_represented_in_state (in_pre_state) (X .owner@pre) (Client) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_pre_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre is_represented_in_state_def select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<W>\<N>\<E>\<R>_def deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_def in_pre_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_pre_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>at_pre is_represented_in_state_def deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  apply(simp add: deref_assocs\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>_def deref_assocs_def)
  apply(case_tac "(assocs ((in_pre_state (\<tau>))) (oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<O>\<W>\<N>\<E>\<R>))", simp add: invalid_def bot_option_def, simp add: select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<O>\<W>\<N>\<E>\<R>_def)
  proof - fix r typeoid          let ?t = "(Some ((Some (r)))) \<in> (Some o OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_\<AA>) ` (ran ((heap ((in_pre_state (\<tau>))))))"
          let ?sel_any = "(select_object_any\<^sub>S\<^sub>e\<^sub>t ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_pre_state) (reconst_basetype))))" show "((?sel_any) (typeoid) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  proof - fix aa show "\<tau> \<Turnstile> (\<delta> (((?sel_any) (aa)))) \<Longrightarrow> ((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  apply(drule select_object_any_exec\<^sub>S\<^sub>e\<^sub>t[simplified foundation22], erule exE)
  proof - fix e show "((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ((?sel_any) (aa) (\<tau>)) = (deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_pre_state) (reconst_basetype) (e) (\<tau>)) \<Longrightarrow> ?t"
  apply(simp add: deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def)
  apply(case_tac "(heap ((in_pre_state (\<tau>))) (e))", simp add: invalid_def bot_option_def, simp)
  proof - fix aaa show "(case aaa of (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (obj)) \<Rightarrow> (reconst_basetype (obj) (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))) = (Some ((Some (r)))) \<Longrightarrow> (heap ((in_pre_state (\<tau>))) (e)) = (Some (aaa)) \<Longrightarrow> ?t"
  apply(case_tac "aaa", auto simp: invalid_def bot_option_def image_def ran_def)
  apply(rule exI[where x = "(in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (r))"], simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_\<AA>_def Let_def reconst_basetype_def split: split_if_asm)
by(rule) qed 
  apply_end((blast)+)
 qed 
  apply_end(simp_all only: )
  apply_end(simp add: foundation16 bot_option_def null_option_def)
 qed qed qed qed 
  apply_end(simp_all)
 qed
lemma is_repr_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K> : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::Savings) .bank))"
shows "(is_represented_in_state (in_post_state) (X .bank) (Bank) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K>[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_post_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K> is_represented_in_state_def select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<N>\<K>_def deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_def in_post_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_post_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K> is_represented_in_state_def deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  apply(simp add: deref_assocs\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K>_def deref_assocs_def)
  apply(case_tac "(assocs ((in_post_state (\<tau>))) (oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K>))", simp add: invalid_def bot_option_def, simp add: select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<N>\<K>_def)
  proof - fix r typeoid          let ?t = "(Some ((Some (r)))) \<in> (Some o OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_\<AA>) ` (ran ((heap ((in_post_state (\<tau>))))))"
          let ?sel_any = "(select_object_any\<^sub>S\<^sub>e\<^sub>t ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_post_state) (reconst_basetype))))" show "((?sel_any) (typeoid) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  proof - fix aa show "\<tau> \<Turnstile> (\<delta> (((?sel_any) (aa)))) \<Longrightarrow> ((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  apply(drule select_object_any_exec\<^sub>S\<^sub>e\<^sub>t[simplified foundation22], erule exE)
  proof - fix e show "((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ((?sel_any) (aa) (\<tau>)) = (deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_post_state) (reconst_basetype) (e) (\<tau>)) \<Longrightarrow> ?t"
  apply(simp add: deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k_def)
  apply(case_tac "(heap ((in_post_state (\<tau>))) (e))", simp add: invalid_def bot_option_def, simp)
  proof - fix aaa show "(case aaa of (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (obj)) \<Rightarrow> (reconst_basetype (obj) (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))) = (Some ((Some (r)))) \<Longrightarrow> (heap ((in_post_state (\<tau>))) (e)) = (Some (aaa)) \<Longrightarrow> ?t"
  apply(case_tac "aaa", auto simp: invalid_def bot_option_def image_def ran_def)
  apply(rule exI[where x = "(in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (r))"], simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_\<AA>_def Let_def reconst_basetype_def split: split_if_asm)
by(rule) qed 
  apply_end((blast)+)
 qed 
  apply_end(simp_all only: )
  apply_end(simp add: foundation16 bot_option_def null_option_def)
 qed qed qed qed 
  apply_end(simp_all)
 qed
lemma is_repr_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R> : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::Savings) .owner))"
shows "(is_represented_in_state (in_post_state) (X .owner) (Client) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R>[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_post_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R> is_represented_in_state_def select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<O>\<W>\<N>\<E>\<R>_def deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_def in_post_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_post_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R> is_represented_in_state_def deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  apply(simp add: deref_assocs\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R>_def deref_assocs_def)
  apply(case_tac "(assocs ((in_post_state (\<tau>))) (oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R>))", simp add: invalid_def bot_option_def, simp add: select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<O>\<W>\<N>\<E>\<R>_def)
  proof - fix r typeoid          let ?t = "(Some ((Some (r)))) \<in> (Some o OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_\<AA>) ` (ran ((heap ((in_post_state (\<tau>))))))"
          let ?sel_any = "(select_object_any\<^sub>S\<^sub>e\<^sub>t ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_post_state) (reconst_basetype))))" show "((?sel_any) (typeoid) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  proof - fix aa show "\<tau> \<Turnstile> (\<delta> (((?sel_any) (aa)))) \<Longrightarrow> ((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  apply(drule select_object_any_exec\<^sub>S\<^sub>e\<^sub>t[simplified foundation22], erule exE)
  proof - fix e show "((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ((?sel_any) (aa) (\<tau>)) = (deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_post_state) (reconst_basetype) (e) (\<tau>)) \<Longrightarrow> ?t"
  apply(simp add: deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def)
  apply(case_tac "(heap ((in_post_state (\<tau>))) (e))", simp add: invalid_def bot_option_def, simp)
  proof - fix aaa show "(case aaa of (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (obj)) \<Rightarrow> (reconst_basetype (obj) (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))) = (Some ((Some (r)))) \<Longrightarrow> (heap ((in_post_state (\<tau>))) (e)) = (Some (aaa)) \<Longrightarrow> ?t"
  apply(case_tac "aaa", auto simp: invalid_def bot_option_def image_def ran_def)
  apply(rule exI[where x = "(in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (r))"], simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_\<AA>_def Let_def reconst_basetype_def split: split_if_asm)
by(rule) qed 
  apply_end((blast)+)
 qed 
  apply_end(simp_all only: )
  apply_end(simp add: foundation16 bot_option_def null_option_def)
 qed qed qed qed 
  apply_end(simp_all)
 qed
lemma is_repr_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K>at_pre : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::Savings) .bank@pre))"
shows "(is_represented_in_state (in_pre_state) (X .bank@pre) (Bank) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K>at_pre[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_pre_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K>at_pre is_represented_in_state_def select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<N>\<K>_def deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_def in_pre_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_pre_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K>at_pre is_represented_in_state_def deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  apply(simp add: deref_assocs\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K>_def deref_assocs_def)
  apply(case_tac "(assocs ((in_pre_state (\<tau>))) (oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<B>\<A>\<N>\<K>))", simp add: invalid_def bot_option_def, simp add: select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<B>\<A>\<N>\<K>_def)
  proof - fix r typeoid          let ?t = "(Some ((Some (r)))) \<in> (Some o OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_\<AA>) ` (ran ((heap ((in_pre_state (\<tau>))))))"
          let ?sel_any = "(select_object_any\<^sub>S\<^sub>e\<^sub>t ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_pre_state) (reconst_basetype))))" show "((?sel_any) (typeoid) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  proof - fix aa show "\<tau> \<Turnstile> (\<delta> (((?sel_any) (aa)))) \<Longrightarrow> ((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  apply(drule select_object_any_exec\<^sub>S\<^sub>e\<^sub>t[simplified foundation22], erule exE)
  proof - fix e show "((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ((?sel_any) (aa) (\<tau>)) = (deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_pre_state) (reconst_basetype) (e) (\<tau>)) \<Longrightarrow> ?t"
  apply(simp add: deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k_def)
  apply(case_tac "(heap ((in_pre_state (\<tau>))) (e))", simp add: invalid_def bot_option_def, simp)
  proof - fix aaa show "(case aaa of (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (obj)) \<Rightarrow> (reconst_basetype (obj) (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))) = (Some ((Some (r)))) \<Longrightarrow> (heap ((in_pre_state (\<tau>))) (e)) = (Some (aaa)) \<Longrightarrow> ?t"
  apply(case_tac "aaa", auto simp: invalid_def bot_option_def image_def ran_def)
  apply(rule exI[where x = "(in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (r))"], simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_\<AA>_def Let_def reconst_basetype_def split: split_if_asm)
by(rule) qed 
  apply_end((blast)+)
 qed 
  apply_end(simp_all only: )
  apply_end(simp add: foundation16 bot_option_def null_option_def)
 qed qed qed qed 
  apply_end(simp_all)
 qed
lemma is_repr_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R>at_pre : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::Savings) .owner@pre))"
shows "(is_represented_in_state (in_pre_state) (X .owner@pre) (Client) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R>at_pre[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_pre_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R>at_pre is_represented_in_state_def select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<O>\<W>\<N>\<E>\<R>_def deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_def in_pre_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_pre_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R>at_pre is_represented_in_state_def deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  apply(simp add: deref_assocs\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R>_def deref_assocs_def)
  apply(case_tac "(assocs ((in_pre_state (\<tau>))) (oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<O>\<W>\<N>\<E>\<R>))", simp add: invalid_def bot_option_def, simp add: select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<O>\<W>\<N>\<E>\<R>_def)
  proof - fix r typeoid          let ?t = "(Some ((Some (r)))) \<in> (Some o OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_\<AA>) ` (ran ((heap ((in_pre_state (\<tau>))))))"
          let ?sel_any = "(select_object_any\<^sub>S\<^sub>e\<^sub>t ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_pre_state) (reconst_basetype))))" show "((?sel_any) (typeoid) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  proof - fix aa show "\<tau> \<Turnstile> (\<delta> (((?sel_any) (aa)))) \<Longrightarrow> ((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ?t"
  apply(drule select_object_any_exec\<^sub>S\<^sub>e\<^sub>t[simplified foundation22], erule exE)
  proof - fix e show "((?sel_any) (aa) (\<tau>)) = (Some ((Some (r)))) \<Longrightarrow> ((?sel_any) (aa) (\<tau>)) = (deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_pre_state) (reconst_basetype) (e) (\<tau>)) \<Longrightarrow> ?t"
  apply(simp add: deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def)
  apply(case_tac "(heap ((in_pre_state (\<tau>))) (e))", simp add: invalid_def bot_option_def, simp)
  proof - fix aaa show "(case aaa of (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (obj)) \<Rightarrow> (reconst_basetype (obj) (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))) = (Some ((Some (r)))) \<Longrightarrow> (heap ((in_pre_state (\<tau>))) (e)) = (Some (aaa)) \<Longrightarrow> ?t"
  apply(case_tac "aaa", auto simp: invalid_def bot_option_def image_def ran_def)
  apply(rule exI[where x = "(in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (r))"], simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_\<AA>_def Let_def reconst_basetype_def split: split_if_asm)
by(rule) qed 
  apply_end((blast)+)
 qed 
  apply_end(simp_all only: )
  apply_end(simp add: foundation16 bot_option_def null_option_def)
 qed qed qed qed 
  apply_end(simp_all)
 qed

(* 128 ************************************ 1784 + 1 *)
section{* A Little Infra-structure on Example States *}

(* 129 ************************************ 1785 + 1 *)
text{*  *}

(* 130 ************************************ 1786 + 1 *)
text{* 

The example we are defining in this section comes from the figure~\ref{fig:eam1_system-states}.
\begin{figure}
\includegraphics[width=\textwidth]{figures/pre-post.pdf}
\caption{(a) pre-state $\sigma_1$ and
  (b) post-state $\sigma_1'$.}
\label{fig:eam1_system-states}
\end{figure}
 *}

(* 131 ************************************ 1787 + 1 *)
lemmas [simp,code_unfold] = state.defs
                            const_ss

(* 132 ************************************ 1788 + 1 *)
lemmas[simp,code_unfold] = OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account
                            OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny
                            OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings
                            OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank
                            OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client
                            OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account
                            OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny
                            OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current
                            OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank
                            OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client
                            OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny
                            OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current
                            OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings
                            OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank
                            OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client
                            OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny
                            OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client
                            OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings
                            OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account
                            OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current
                            OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny
                            OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank
                            OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings
                            OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account
                            OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client

(* 133 ************************************ 1789 + 4 *)
definition "oid3 = 3"
definition "oid4 = 4"
definition "oid5 = 5"
definition "oid6 = 6"

(* 134 ************************************ 1793 + 8 *)
definition "Saving1\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t = (mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s ((mk\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s ((mk\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (oid3) (None) (None))) (\<lfloor>2000\<rfloor>))))) (None) (None))"
definition "Client1\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t = (mk\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (oid4))) (None) (None) (None))"
definition "Account1\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t = (mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (oid5))) (\<lfloor>250\<rfloor>) (None))"
definition "Bank1\<^sub>B\<^sub>a\<^sub>n\<^sub>k = (mk\<^sub>B\<^sub>a\<^sub>n\<^sub>k ((mk\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k (oid6))) (\<lfloor>(let c = char_of_nat in c 092 # c 060 # CHR ''i'' # CHR ''n'' # CHR ''f'' # CHR ''i'' # CHR ''n'' # CHR ''i'' # CHR ''t'' # CHR ''y'' # c 062 # c 092 # c 060 # CHR ''h'' # CHR ''e'' # CHR ''a'' # CHR ''r'' # CHR ''t'' # CHR ''s'' # CHR ''u'' # CHR ''i'' # CHR ''t'' # c 062 # c 032 # c 092 # c 060 # CHR ''L'' # CHR ''o'' # CHR ''n'' # CHR ''g'' # CHR ''l'' # CHR ''e'' # CHR ''f'' # CHR ''t'' # CHR ''r'' # CHR ''i'' # CHR ''g'' # CHR ''h'' # CHR ''t'' # CHR ''a'' # CHR ''r'' # CHR ''r'' # CHR ''o'' # CHR ''w'' # c 062 # c 032 # c 092 # c 060 # CHR ''i'' # CHR ''n'' # CHR ''f'' # CHR ''i'' # CHR ''n'' # CHR ''i'' # CHR ''t'' # CHR ''y'' # c 062 # c 092 # c 060 # CHR ''e'' # CHR ''p'' # CHR ''s'' # CHR ''i'' # CHR ''l'' # CHR ''o'' # CHR ''n'' # c 062 # [])\<rfloor>))"
definition "(Saving1::Account) = (\<lambda>_. \<lfloor>\<lfloor>Saving1\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<rfloor>\<rfloor>)"
definition "(Client1::Client) = (\<lambda>_. \<lfloor>\<lfloor>Client1\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<rfloor>\<rfloor>)"
definition "(Account1::Account) = (\<lambda>_. \<lfloor>\<lfloor>Account1\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<rfloor>\<rfloor>)"
definition "(Bank1::Bank) = (\<lambda>_. \<lfloor>\<lfloor>Bank1\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<rfloor>\<rfloor>)"

(* 135 ************************************ 1801 + 1 *)
ML{* (Ty'.check ([(OCL.Writeln , "Saving1 .owner = Set{ Client1 }") , (OCL.Writeln , "Saving1 .bank = Set{ Bank1 }") , (OCL.Writeln , "Saving1 .balance = Set{}") , (OCL.Writeln , "Saving1 .max = Set{}") , (OCL.Writeln , "Client1 .banks = Set{ Bank1 }") , (OCL.Writeln , "Client1 .c_accounts = Set{ Saving1 , Account1 }") , (OCL.Writeln , "Account1 .owner = Set{ Client1 }") , (OCL.Writeln , "Account1 .bank = Set{ Bank1 }") , (OCL.Writeln , "Account1 .balance = Set{}") , (OCL.Writeln , "Bank1 .clients = Set{ Client1 }") , (OCL.Writeln , "Bank1 .b_accounts = Set{ Saving1 , Account1 }")]) (" error(s)")) *}

(* 136 ************************************ 1802 + 3 *)
generation_syntax [ shallow ]
setup{* (Generation_mode.update_compiler_config ((K (let open OCL in Ocl_compiler_config_ext (true, NONE, Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 3), (Code_Numeral.Nat 7)), I ((Code_Numeral.Nat 0), (Code_Numeral.Nat 0)), Gen_default, SOME (OclClass ((OCL.SS_base (OCL.ST "OclAny")), nil, uncurry cons (OclClass ((OCL.SS_base (OCL.ST "Client")), uncurry cons (I ((OCL.SS_base (OCL.ST "c_accounts")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((OCL.SS_base (OCL.ST "oid")), (Code_Numeral.Nat 1), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), NONE), nil), SOME ((OCL.SS_base (OCL.ST "owner"))), nil, ()), (OCL.SS_base (OCL.ST "Client")), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "c_accounts"))), nil, ()), (OCL.SS_base (OCL.ST "Account")), ()), ())), nil))), uncurry cons (I ((OCL.SS_base (OCL.ST "banks")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((OCL.SS_base (OCL.ST "oid")), (Code_Numeral.Nat 0), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "clients"))), nil, ()), (OCL.SS_base (OCL.ST "Client")), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "banks"))), nil, ()), (OCL.SS_base (OCL.ST "Bank")), ()), ())), nil))), uncurry cons (I ((OCL.SS_base (OCL.ST "clientname")), OclTy_base_string), uncurry cons (I ((OCL.SS_base (OCL.ST "address")), OclTy_base_string), uncurry cons (I ((OCL.SS_base (OCL.ST "age")), OclTy_base_integer), nil))))), nil), uncurry cons (OclClass ((OCL.SS_base (OCL.ST "Bank")), uncurry cons (I ((OCL.SS_base (OCL.ST "b_accounts")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((OCL.SS_base (OCL.ST "oid")), (Code_Numeral.Nat 2), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), NONE), nil), SOME ((OCL.SS_base (OCL.ST "bank"))), nil, ()), (OCL.SS_base (OCL.ST "Bank")), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "b_accounts"))), nil, ()), (OCL.SS_base (OCL.ST "Account")), ()), ())), nil))), uncurry cons (I ((OCL.SS_base (OCL.ST "clients")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((OCL.SS_base (OCL.ST "oid")), (Code_Numeral.Nat 0), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "banks"))), nil, ()), (OCL.SS_base (OCL.ST "Bank")), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "clients"))), nil, ()), (OCL.SS_base (OCL.ST "Client")), ()), ())), nil))), uncurry cons (I ((OCL.SS_base (OCL.ST "name")), OclTy_base_string), nil))), nil), uncurry cons (OclClass ((OCL.SS_base (OCL.ST "Account")), uncurry cons (I ((OCL.SS_base (OCL.ST "bank")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((OCL.SS_base (OCL.ST "oid")), (Code_Numeral.Nat 2), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "b_accounts"))), nil, ()), (OCL.SS_base (OCL.ST "Account")), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), NONE), nil), SOME ((OCL.SS_base (OCL.ST "bank"))), nil, ()), (OCL.SS_base (OCL.ST "Bank")), ()), ())), nil))), uncurry cons (I ((OCL.SS_base (OCL.ST "owner")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((OCL.SS_base (OCL.ST "oid")), (Code_Numeral.Nat 1), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "c_accounts"))), nil, ()), (OCL.SS_base (OCL.ST "Account")), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), NONE), nil), SOME ((OCL.SS_base (OCL.ST "owner"))), nil, ()), (OCL.SS_base (OCL.ST "Client")), ()), ())), nil))), uncurry cons (I ((OCL.SS_base (OCL.ST "id")), OclTy_base_integer), uncurry cons (I ((OCL.SS_base (OCL.ST "balance")), OclTy_raw ((OCL.SS_base (OCL.ST "Currency")))), nil)))), uncurry cons (OclClass ((OCL.SS_base (OCL.ST "Savings")), uncurry cons (I ((OCL.SS_base (OCL.ST "max")), OclTy_raw ((OCL.SS_base (OCL.ST "Currency")))), nil), nil), uncurry cons (OclClass ((OCL.SS_base (OCL.ST "Current")), uncurry cons (I ((OCL.SS_base (OCL.ST "overdraft")), OclTy_raw ((OCL.SS_base (OCL.ST "Currency")))), nil), nil), nil))), nil))))), uncurry cons (OclAstInstance (OclInstance (uncurry cons (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Saving1"))), (OCL.SS_base (OCL.ST "Account")), OclAttrCast ((OCL.SS_base (OCL.ST "Savings")), OclAttrNoCast (uncurry cons (I ((OCL.SS_base (OCL.ST "max")), ShallB_term (OclDefInteger ((OCL.SS_base (OCL.ST "2000"))))), nil)), nil), ()), uncurry cons (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Client1"))), (OCL.SS_base (OCL.ST "Client")), OclAttrNoCast (uncurry cons (I ((OCL.SS_base (OCL.ST "c_accounts")), ShallB_str ((OCL.SS_base (OCL.ST "Saving1")))), uncurry cons (I ((OCL.SS_base (OCL.ST "banks")), ShallB_str ((OCL.SS_base (OCL.ST "Bank1")))), nil))), ()), uncurry cons (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Account1"))), (OCL.SS_base (OCL.ST "Account")), OclAttrNoCast (uncurry cons (I ((OCL.SS_base (OCL.ST "id")), ShallB_term (OclDefInteger ((OCL.SS_base (OCL.ST "250"))))), uncurry cons (I ((OCL.SS_base (OCL.ST "owner")), ShallB_str ((OCL.SS_base (OCL.ST "Client1")))), nil))), ()), uncurry cons (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Bank1"))), (OCL.SS_base (OCL.ST "Bank")), OclAttrNoCast (uncurry cons (I ((OCL.SS_base (OCL.ST "b_accounts")), ShallB_list (uncurry cons (ShallB_str ((OCL.SS_base (OCL.ST "Saving1"))), uncurry cons (ShallB_str ((OCL.SS_base (OCL.ST "Account1"))), nil)))), uncurry cons (I ((OCL.SS_base (OCL.ST "name")), ShallB_term (OclDefString ((OCL.SS_base (OCL.ST "\<infinity>\<heartsuit> \<Longleftrightarrow> \<infinity>\<epsilon>"))))), nil))), ()), nil)))))), uncurry cons (OclAstEnum (OclEnumSynonym ((OCL.SS_base (OCL.ST "Currency")), OclTy_base_real)), uncurry cons (OclAstClassRaw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Current"))), uncurry cons (uncurry cons (OclTyCore_pre ((OCL.SS_base (OCL.ST "Account"))), nil), nil)), uncurry cons (I ((OCL.SS_base (OCL.ST "overdraft")), OclTy_object (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Currency"))), nil))), nil), nil, false, ())), uncurry cons (OclAstClassRaw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Savings"))), uncurry cons (uncurry cons (OclTyCore_pre ((OCL.SS_base (OCL.ST "Account"))), nil), nil)), uncurry cons (I ((OCL.SS_base (OCL.ST "max")), OclTy_object (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Currency"))), nil))), nil), nil, false, ())), uncurry cons (OclAstAssociation (Ocl_association_ext (OclAssTy_association, OclAssRel (uncurry cons (I (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Account"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "b_accounts"))), nil, ())), uncurry cons (I (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Bank"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), NONE), nil), SOME ((OCL.SS_base (OCL.ST "bank"))), nil, ())), nil))), ())), uncurry cons (OclAstAssociation (Ocl_association_ext (OclAssTy_association, OclAssRel (uncurry cons (I (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Account"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "c_accounts"))), nil, ())), uncurry cons (I (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Client"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), NONE), nil), SOME ((OCL.SS_base (OCL.ST "owner"))), nil, ())), nil))), ())), uncurry cons (OclAstAssociation (Ocl_association_ext (OclAssTy_association, OclAssRel (uncurry cons (I (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Bank"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "banks"))), nil, ())), uncurry cons (I (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Client"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "clients"))), nil, ())), nil))), ())), uncurry cons (OclAstClassRaw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Account"))), nil), uncurry cons (I ((OCL.SS_base (OCL.ST "id")), OclTy_base_integer), uncurry cons (I ((OCL.SS_base (OCL.ST "balance")), OclTy_object (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Currency"))), nil))), nil)), nil, false, ())), uncurry cons (OclAstClassRaw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Client"))), nil), uncurry cons (I ((OCL.SS_base (OCL.ST "clientname")), OclTy_base_string), uncurry cons (I ((OCL.SS_base (OCL.ST "address")), OclTy_base_string), uncurry cons (I ((OCL.SS_base (OCL.ST "age")), OclTy_base_integer), nil))), nil, false, ())), uncurry cons (OclAstClassRaw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Bank"))), nil), uncurry cons (I ((OCL.SS_base (OCL.ST "name")), OclTy_base_string), nil), nil, false, ())), nil)))))))))), uncurry cons (I ((OCL.ST "Bank1"), I (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Bank1"))), (OCL.SS_base (OCL.ST "Bank")), OclAttrNoCast (uncurry cons (I ((OCL.SS_base (OCL.ST "b_accounts")), ShallB_list (uncurry cons (ShallB_str ((OCL.SS_base (OCL.ST "Saving1"))), uncurry cons (ShallB_str ((OCL.SS_base (OCL.ST "Account1"))), nil)))), uncurry cons (I ((OCL.SS_base (OCL.ST "name")), ShallB_term (OclDefString ((OCL.SS_base (OCL.ST "\<infinity>\<heartsuit> \<Longleftrightarrow> \<infinity>\<epsilon>"))))), nil))), ()), Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 3), (Code_Numeral.Nat 6)))), uncurry cons (I ((OCL.ST "Account1"), I (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Account1"))), (OCL.SS_base (OCL.ST "Account")), OclAttrNoCast (uncurry cons (I ((OCL.SS_base (OCL.ST "id")), ShallB_term (OclDefInteger ((OCL.SS_base (OCL.ST "250"))))), uncurry cons (I ((OCL.SS_base (OCL.ST "owner")), ShallB_str ((OCL.SS_base (OCL.ST "Client1")))), nil))), ()), Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 3), (Code_Numeral.Nat 5)))), uncurry cons (I ((OCL.ST "Client1"), I (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Client1"))), (OCL.SS_base (OCL.ST "Client")), OclAttrNoCast (uncurry cons (I ((OCL.SS_base (OCL.ST "c_accounts")), ShallB_str ((OCL.SS_base (OCL.ST "Saving1")))), uncurry cons (I ((OCL.SS_base (OCL.ST "banks")), ShallB_str ((OCL.SS_base (OCL.ST "Bank1")))), nil))), ()), Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 3), (Code_Numeral.Nat 4)))), uncurry cons (I ((OCL.ST "Saving1"), I (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Saving1"))), (OCL.SS_base (OCL.ST "Account")), OclAttrCast ((OCL.SS_base (OCL.ST "Savings")), OclAttrNoCast (uncurry cons (I ((OCL.SS_base (OCL.ST "max")), ShallB_term (OclDefInteger ((OCL.SS_base (OCL.ST "2000"))))), nil)), nil), ()), Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 3), (Code_Numeral.Nat 3)))), nil)))), nil, true, false, I (uncurry cons ((OCL.ST "dot\<A>\<G>\<E>at_pre"), uncurry cons ((OCL.ST "dot\<A>\<D>\<D>\<R>\<E>\<S>\<S>at_pre"), uncurry cons ((OCL.ST "dot\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E>at_pre"), uncurry cons ((OCL.ST "dot_1_\<B>\<A>\<N>\<K>\<S>at_pre"), uncurry cons ((OCL.ST "dot_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>at_pre"), uncurry cons ((OCL.ST "dot\<N>\<A>\<M>\<E>at_pre"), uncurry cons ((OCL.ST "dot_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S>at_pre"), uncurry cons ((OCL.ST "dot_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>at_pre"), uncurry cons ((OCL.ST "dot\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre"), uncurry cons ((OCL.ST "dot\<I>\<D>at_pre"), uncurry cons ((OCL.ST "dot_0_\<O>\<W>\<N>\<E>\<R>at_pre"), uncurry cons ((OCL.ST "dot_0_\<B>\<A>\<N>\<K>at_pre"), uncurry cons ((OCL.ST "dot\<M>\<A>\<X>at_pre"), uncurry cons ((OCL.ST "dot\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T>at_pre"), nil)))))))))))))), uncurry cons ((OCL.ST "dot\<A>\<G>\<E>"), uncurry cons ((OCL.ST "dot\<A>\<D>\<D>\<R>\<E>\<S>\<S>"), uncurry cons ((OCL.ST "dot\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E>"), uncurry cons ((OCL.ST "dot_1_\<B>\<A>\<N>\<K>\<S>"), uncurry cons ((OCL.ST "dot_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>"), uncurry cons ((OCL.ST "dot\<N>\<A>\<M>\<E>"), uncurry cons ((OCL.ST "dot_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S>"), uncurry cons ((OCL.ST "dot_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>"), uncurry cons ((OCL.ST "dot\<B>\<A>\<L>\<A>\<N>\<C>\<E>"), uncurry cons ((OCL.ST "dot\<I>\<D>"), uncurry cons ((OCL.ST "dot_0_\<O>\<W>\<N>\<E>\<R>"), uncurry cons ((OCL.ST "dot_0_\<B>\<A>\<N>\<K>"), uncurry cons ((OCL.ST "dot\<M>\<A>\<X>"), uncurry cons ((OCL.ST "dot\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T>"), nil))))))))))))))), uncurry cons ((OCL.ST "Sequence_Client"), uncurry cons ((OCL.ST "Set_Client"), uncurry cons ((OCL.ST "Sequence_Bank"), uncurry cons ((OCL.ST "Set_Bank"), uncurry cons ((OCL.ST "Sequence_Account"), uncurry cons ((OCL.ST "Set_Account"), nil)))))), I (NONE, false), ()) end)))) *}
State[shallow] \<sigma>\<^sub>1' = [ Account1, Client1, Bank1, Saving1 ]

(* 137 ************************************ 1805 + 1 *)
State[shallow] ss = [  ]

(* 138 ************************************ 1806 + 1 *)
PrePost[shallow] ss \<sigma>\<^sub>1'

(* 139 ************************************ 1807 + 2 *)
definition OclInt25 ("\<two>\<five>")
  where "OclInt25 = (\<lambda>_. \<lfloor>\<lfloor>25\<rfloor>\<rfloor>)"
definition OclReal250_0 ("\<two>\<five>\<zero>.\<zero>")
  where "OclReal250_0 = (\<lambda>_. \<lfloor>\<lfloor>250\<rfloor>\<rfloor>)"

(* 140 ************************************ 1809 + 2 *)
setup{* (Generation_mode.update_compiler_config ((K (let open OCL in Ocl_compiler_config_ext (true, NONE, Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 3), (Code_Numeral.Nat 7)), I ((Code_Numeral.Nat 0), (Code_Numeral.Nat 0)), Gen_default, SOME (OclClass ((OCL.SS_base (OCL.ST "OclAny")), nil, uncurry cons (OclClass ((OCL.SS_base (OCL.ST "Client")), uncurry cons (I ((OCL.SS_base (OCL.ST "c_accounts")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((OCL.SS_base (OCL.ST "oid")), (Code_Numeral.Nat 1), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), NONE), nil), SOME ((OCL.SS_base (OCL.ST "owner"))), nil, ()), (OCL.SS_base (OCL.ST "Client")), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "c_accounts"))), nil, ()), (OCL.SS_base (OCL.ST "Account")), ()), ())), nil))), uncurry cons (I ((OCL.SS_base (OCL.ST "banks")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((OCL.SS_base (OCL.ST "oid")), (Code_Numeral.Nat 0), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "clients"))), nil, ()), (OCL.SS_base (OCL.ST "Client")), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "banks"))), nil, ()), (OCL.SS_base (OCL.ST "Bank")), ()), ())), nil))), uncurry cons (I ((OCL.SS_base (OCL.ST "clientname")), OclTy_base_string), uncurry cons (I ((OCL.SS_base (OCL.ST "address")), OclTy_base_string), uncurry cons (I ((OCL.SS_base (OCL.ST "age")), OclTy_base_integer), nil))))), nil), uncurry cons (OclClass ((OCL.SS_base (OCL.ST "Bank")), uncurry cons (I ((OCL.SS_base (OCL.ST "b_accounts")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((OCL.SS_base (OCL.ST "oid")), (Code_Numeral.Nat 2), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), NONE), nil), SOME ((OCL.SS_base (OCL.ST "bank"))), nil, ()), (OCL.SS_base (OCL.ST "Bank")), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "b_accounts"))), nil, ()), (OCL.SS_base (OCL.ST "Account")), ()), ())), nil))), uncurry cons (I ((OCL.SS_base (OCL.ST "clients")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((OCL.SS_base (OCL.ST "oid")), (Code_Numeral.Nat 0), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "banks"))), nil, ()), (OCL.SS_base (OCL.ST "Bank")), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "clients"))), nil, ()), (OCL.SS_base (OCL.ST "Client")), ()), ())), nil))), uncurry cons (I ((OCL.SS_base (OCL.ST "name")), OclTy_base_string), nil))), nil), uncurry cons (OclClass ((OCL.SS_base (OCL.ST "Account")), uncurry cons (I ((OCL.SS_base (OCL.ST "bank")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((OCL.SS_base (OCL.ST "oid")), (Code_Numeral.Nat 2), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "b_accounts"))), nil, ()), (OCL.SS_base (OCL.ST "Account")), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), NONE), nil), SOME ((OCL.SS_base (OCL.ST "bank"))), nil, ()), (OCL.SS_base (OCL.ST "Bank")), ()), ())), nil))), uncurry cons (I ((OCL.SS_base (OCL.ST "owner")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((OCL.SS_base (OCL.ST "oid")), (Code_Numeral.Nat 1), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "c_accounts"))), nil, ()), (OCL.SS_base (OCL.ST "Account")), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), NONE), nil), SOME ((OCL.SS_base (OCL.ST "owner"))), nil, ()), (OCL.SS_base (OCL.ST "Client")), ()), ())), nil))), uncurry cons (I ((OCL.SS_base (OCL.ST "id")), OclTy_base_integer), uncurry cons (I ((OCL.SS_base (OCL.ST "balance")), OclTy_raw ((OCL.SS_base (OCL.ST "Currency")))), nil)))), uncurry cons (OclClass ((OCL.SS_base (OCL.ST "Savings")), uncurry cons (I ((OCL.SS_base (OCL.ST "max")), OclTy_raw ((OCL.SS_base (OCL.ST "Currency")))), nil), nil), uncurry cons (OclClass ((OCL.SS_base (OCL.ST "Current")), uncurry cons (I ((OCL.SS_base (OCL.ST "overdraft")), OclTy_raw ((OCL.SS_base (OCL.ST "Currency")))), nil), nil), nil))), nil))))), uncurry cons (OclAstDefBaseL (OclDefBase (uncurry cons (OclDefInteger ((OCL.SS_base (OCL.ST "25"))), uncurry cons (OclDefReal (I ((OCL.SS_base (OCL.ST "250")), (OCL.SS_base (OCL.ST "0")))), nil)))), uncurry cons (OclAstDefPrePost (Floor1, OclDefPP (NONE, OclDefPPCoreBinding ((OCL.SS_base (OCL.ST "ss"))), SOME (OclDefPPCoreBinding ((OCL.SS_base (OCL.ST "\<sigma>\<^sub>1'")))))), uncurry cons (OclAstDefState (Floor1, OclDefSt ((OCL.SS_base (OCL.ST "ss")), nil)), uncurry cons (OclAstDefState (Floor1, OclDefSt ((OCL.SS_base (OCL.ST "\<sigma>\<^sub>1'")), uncurry cons (OclDefCoreBinding ((OCL.SS_base (OCL.ST "Account1"))), uncurry cons (OclDefCoreBinding ((OCL.SS_base (OCL.ST "Client1"))), uncurry cons (OclDefCoreBinding ((OCL.SS_base (OCL.ST "Bank1"))), uncurry cons (OclDefCoreBinding ((OCL.SS_base (OCL.ST "Saving1"))), nil)))))), uncurry cons (OclAstInstance (OclInstance (uncurry cons (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Saving1"))), (OCL.SS_base (OCL.ST "Account")), OclAttrCast ((OCL.SS_base (OCL.ST "Savings")), OclAttrNoCast (uncurry cons (I ((OCL.SS_base (OCL.ST "max")), ShallB_term (OclDefInteger ((OCL.SS_base (OCL.ST "2000"))))), nil)), nil), ()), uncurry cons (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Client1"))), (OCL.SS_base (OCL.ST "Client")), OclAttrNoCast (uncurry cons (I ((OCL.SS_base (OCL.ST "c_accounts")), ShallB_str ((OCL.SS_base (OCL.ST "Saving1")))), uncurry cons (I ((OCL.SS_base (OCL.ST "banks")), ShallB_str ((OCL.SS_base (OCL.ST "Bank1")))), nil))), ()), uncurry cons (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Account1"))), (OCL.SS_base (OCL.ST "Account")), OclAttrNoCast (uncurry cons (I ((OCL.SS_base (OCL.ST "id")), ShallB_term (OclDefInteger ((OCL.SS_base (OCL.ST "250"))))), uncurry cons (I ((OCL.SS_base (OCL.ST "owner")), ShallB_str ((OCL.SS_base (OCL.ST "Client1")))), nil))), ()), uncurry cons (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Bank1"))), (OCL.SS_base (OCL.ST "Bank")), OclAttrNoCast (uncurry cons (I ((OCL.SS_base (OCL.ST "b_accounts")), ShallB_list (uncurry cons (ShallB_str ((OCL.SS_base (OCL.ST "Saving1"))), uncurry cons (ShallB_str ((OCL.SS_base (OCL.ST "Account1"))), nil)))), uncurry cons (I ((OCL.SS_base (OCL.ST "name")), ShallB_term (OclDefString ((OCL.SS_base (OCL.ST "\<infinity>\<heartsuit> \<Longleftrightarrow> \<infinity>\<epsilon>"))))), nil))), ()), nil)))))), uncurry cons (OclAstEnum (OclEnumSynonym ((OCL.SS_base (OCL.ST "Currency")), OclTy_base_real)), uncurry cons (OclAstClassRaw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Current"))), uncurry cons (uncurry cons (OclTyCore_pre ((OCL.SS_base (OCL.ST "Account"))), nil), nil)), uncurry cons (I ((OCL.SS_base (OCL.ST "overdraft")), OclTy_object (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Currency"))), nil))), nil), nil, false, ())), uncurry cons (OclAstClassRaw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Savings"))), uncurry cons (uncurry cons (OclTyCore_pre ((OCL.SS_base (OCL.ST "Account"))), nil), nil)), uncurry cons (I ((OCL.SS_base (OCL.ST "max")), OclTy_object (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Currency"))), nil))), nil), nil, false, ())), uncurry cons (OclAstAssociation (Ocl_association_ext (OclAssTy_association, OclAssRel (uncurry cons (I (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Account"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "b_accounts"))), nil, ())), uncurry cons (I (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Bank"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), NONE), nil), SOME ((OCL.SS_base (OCL.ST "bank"))), nil, ())), nil))), ())), uncurry cons (OclAstAssociation (Ocl_association_ext (OclAssTy_association, OclAssRel (uncurry cons (I (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Account"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "c_accounts"))), nil, ())), uncurry cons (I (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Client"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), NONE), nil), SOME ((OCL.SS_base (OCL.ST "owner"))), nil, ())), nil))), ())), uncurry cons (OclAstAssociation (Ocl_association_ext (OclAssTy_association, OclAssRel (uncurry cons (I (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Bank"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "banks"))), nil, ())), uncurry cons (I (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Client"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "clients"))), nil, ())), nil))), ())), uncurry cons (OclAstClassRaw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Account"))), nil), uncurry cons (I ((OCL.SS_base (OCL.ST "id")), OclTy_base_integer), uncurry cons (I ((OCL.SS_base (OCL.ST "balance")), OclTy_object (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Currency"))), nil))), nil)), nil, false, ())), uncurry cons (OclAstClassRaw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Client"))), nil), uncurry cons (I ((OCL.SS_base (OCL.ST "clientname")), OclTy_base_string), uncurry cons (I ((OCL.SS_base (OCL.ST "address")), OclTy_base_string), uncurry cons (I ((OCL.SS_base (OCL.ST "age")), OclTy_base_integer), nil))), nil, false, ())), uncurry cons (OclAstClassRaw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Bank"))), nil), uncurry cons (I ((OCL.SS_base (OCL.ST "name")), OclTy_base_string), nil), nil, false, ())), nil)))))))))))))), uncurry cons (I ((OCL.ST "Bank1"), I (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Bank1"))), (OCL.SS_base (OCL.ST "Bank")), OclAttrNoCast (uncurry cons (I ((OCL.SS_base (OCL.ST "b_accounts")), ShallB_list (uncurry cons (ShallB_str ((OCL.SS_base (OCL.ST "Saving1"))), uncurry cons (ShallB_str ((OCL.SS_base (OCL.ST "Account1"))), nil)))), uncurry cons (I ((OCL.SS_base (OCL.ST "name")), ShallB_term (OclDefString ((OCL.SS_base (OCL.ST "\<infinity>\<heartsuit> \<Longleftrightarrow> \<infinity>\<epsilon>"))))), nil))), ()), Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 3), (Code_Numeral.Nat 6)))), uncurry cons (I ((OCL.ST "Account1"), I (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Account1"))), (OCL.SS_base (OCL.ST "Account")), OclAttrNoCast (uncurry cons (I ((OCL.SS_base (OCL.ST "id")), ShallB_term (OclDefInteger ((OCL.SS_base (OCL.ST "250"))))), uncurry cons (I ((OCL.SS_base (OCL.ST "owner")), ShallB_str ((OCL.SS_base (OCL.ST "Client1")))), nil))), ()), Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 3), (Code_Numeral.Nat 5)))), uncurry cons (I ((OCL.ST "Client1"), I (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Client1"))), (OCL.SS_base (OCL.ST "Client")), OclAttrNoCast (uncurry cons (I ((OCL.SS_base (OCL.ST "c_accounts")), ShallB_str ((OCL.SS_base (OCL.ST "Saving1")))), uncurry cons (I ((OCL.SS_base (OCL.ST "banks")), ShallB_str ((OCL.SS_base (OCL.ST "Bank1")))), nil))), ()), Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 3), (Code_Numeral.Nat 4)))), uncurry cons (I ((OCL.ST "Saving1"), I (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Saving1"))), (OCL.SS_base (OCL.ST "Account")), OclAttrCast ((OCL.SS_base (OCL.ST "Savings")), OclAttrNoCast (uncurry cons (I ((OCL.SS_base (OCL.ST "max")), ShallB_term (OclDefInteger ((OCL.SS_base (OCL.ST "2000"))))), nil)), nil), ()), Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 3), (Code_Numeral.Nat 3)))), nil)))), nil, true, true, I (uncurry cons ((OCL.ST "dot\<A>\<G>\<E>at_pre"), uncurry cons ((OCL.ST "dot\<A>\<D>\<D>\<R>\<E>\<S>\<S>at_pre"), uncurry cons ((OCL.ST "dot\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E>at_pre"), uncurry cons ((OCL.ST "dot_1_\<B>\<A>\<N>\<K>\<S>at_pre"), uncurry cons ((OCL.ST "dot_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>at_pre"), uncurry cons ((OCL.ST "dot\<N>\<A>\<M>\<E>at_pre"), uncurry cons ((OCL.ST "dot_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S>at_pre"), uncurry cons ((OCL.ST "dot_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>at_pre"), uncurry cons ((OCL.ST "dot\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre"), uncurry cons ((OCL.ST "dot\<I>\<D>at_pre"), uncurry cons ((OCL.ST "dot_0_\<O>\<W>\<N>\<E>\<R>at_pre"), uncurry cons ((OCL.ST "dot_0_\<B>\<A>\<N>\<K>at_pre"), uncurry cons ((OCL.ST "dot\<M>\<A>\<X>at_pre"), uncurry cons ((OCL.ST "dot\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T>at_pre"), nil)))))))))))))), uncurry cons ((OCL.ST "dot\<A>\<G>\<E>"), uncurry cons ((OCL.ST "dot\<A>\<D>\<D>\<R>\<E>\<S>\<S>"), uncurry cons ((OCL.ST "dot\<C>\<L>\<I>\<E>\<N>\<T>\<N>\<A>\<M>\<E>"), uncurry cons ((OCL.ST "dot_1_\<B>\<A>\<N>\<K>\<S>"), uncurry cons ((OCL.ST "dot_1_\<C>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>"), uncurry cons ((OCL.ST "dot\<N>\<A>\<M>\<E>"), uncurry cons ((OCL.ST "dot_0_\<C>\<L>\<I>\<E>\<N>\<T>\<S>"), uncurry cons ((OCL.ST "dot_1_\<B>095\<A>\<C>\<C>\<O>\<U>\<N>\<T>\<S>"), uncurry cons ((OCL.ST "dot\<B>\<A>\<L>\<A>\<N>\<C>\<E>"), uncurry cons ((OCL.ST "dot\<I>\<D>"), uncurry cons ((OCL.ST "dot_0_\<O>\<W>\<N>\<E>\<R>"), uncurry cons ((OCL.ST "dot_0_\<B>\<A>\<N>\<K>"), uncurry cons ((OCL.ST "dot\<M>\<A>\<X>"), uncurry cons ((OCL.ST "dot\<O>\<V>\<E>\<R>\<D>\<R>\<A>\<F>\<T>"), nil))))))))))))))), uncurry cons ((OCL.ST "Sequence_Client"), uncurry cons ((OCL.ST "Set_Client"), uncurry cons ((OCL.ST "Sequence_Bank"), uncurry cons ((OCL.ST "Set_Bank"), uncurry cons ((OCL.ST "Sequence_Account"), uncurry cons ((OCL.ST "Set_Account"), nil)))))), I (NONE, false), ()) end)))) *}
Context[shallow] c : Savings   Inv  : "(\<lambda> self c. (\<zero>.\<zero> <\<^sub>r\<^sub>e\<^sub>a\<^sub>l (c .max)))"
  Inv  : "(\<lambda> self c. (c .balance \<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l (c .max) and \<zero>.\<zero> \<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l (c .balance)))"

(* 141 ************************************ 1811 + 1 *)
Context[shallow] c : Current   Inv  : "(\<lambda> self c. (\<two>\<five> \<le>\<^sub>i\<^sub>n\<^sub>t (c .owner .age) implies (c .overdraft \<doteq> \<two>\<five>\<zero>.\<zero>)))"
  Inv  : "(\<lambda> self c. (c .owner .age <\<^sub>i\<^sub>n\<^sub>t \<two>\<five>   implies (c .overdraft \<doteq> \<zero>.\<zero>)))"

(* 142 ************************************ 1812 + 1 *)
Context[shallow] c : Client   Inv  : "(\<lambda> self c. (c .banks ->forAll\<^sub>S\<^sub>e\<^sub>t(b | b .b_accounts ->select\<^sub>S\<^sub>e\<^sub>t(a | (a .owner \<doteq> c) and
                                                                  (a .oclIsTypeOf(Current)))
                                             ->size\<^sub>S\<^sub>e\<^sub>t() \<le>\<^sub>i\<^sub>n\<^sub>t \<one>)))"

(* 143 ************************************ 1813 + 3 *)
consts dot\<C>\<R>\<E>\<A>\<T>\<E>095\<C>\<L>\<I>\<E>\<N>\<T> :: "Bank \<Rightarrow> String \<Rightarrow> Integer \<Rightarrow> Bank \<Rightarrow> Integer" ("(_) .create'_client'((_),(_),(_)')")
consts dot\<C>\<R>\<E>\<A>\<T>\<E>095\<C>\<L>\<I>\<E>\<N>\<T>at_pre :: "Bank \<Rightarrow> String \<Rightarrow> Integer \<Rightarrow> Bank \<Rightarrow> Integer" ("(_) .create'_client@pre'((_),(_),(_)')")
Context[shallow] Bank :: create_client (clientname : String, age : Integer, bank : Bank) : Integer
  Pre : "(\<lambda> bank age clientname self. (bank .clients ->forAll\<^sub>S\<^sub>e\<^sub>t(c | c .clientname <> clientname or (c .age <> age))))"
  Post : "(\<lambda> bank age clientname self result. (bank .clients ->exists\<^sub>S\<^sub>e\<^sub>t(c | c .clientname \<doteq> clientname and (c .age \<doteq> age))))"

(* 144 ************************************ 1816 + 3 *)
consts dot\<G>\<E>\<T>095\<B>\<A>\<L>\<A>\<N>\<C>\<E> :: "Account \<Rightarrow> String \<Rightarrow> Integer \<Rightarrow> Real" ("(_) .get'_balance'((_),(_)')")
consts dot\<G>\<E>\<T>095\<B>\<A>\<L>\<A>\<N>\<C>\<E>at_pre :: "Account \<Rightarrow> String \<Rightarrow> Integer \<Rightarrow> Real" ("(_) .get'_balance@pre'((_),(_)')")
Context[shallow] Account :: get_balance (c : String, no : Integer) : Real
  Pre : "(\<lambda> no c self. (self .id \<doteq> no and ((self .owner .clientname) \<doteq> c)))"
  Post : "(\<lambda> no c self result. (result \<doteq> (self .balance)))"

(* 145 ************************************ 1819 + 3 *)
consts dot\<D>\<E>\<P>\<O>\<S>\<I>\<T> :: "Account \<Rightarrow> String \<Rightarrow> Integer \<Rightarrow> Real \<Rightarrow> Real" ("(_) .deposit'((_),(_),(_)')")
consts dot\<D>\<E>\<P>\<O>\<S>\<I>\<T>at_pre :: "Account \<Rightarrow> String \<Rightarrow> Integer \<Rightarrow> Real \<Rightarrow> Real" ("(_) .deposit@pre'((_),(_),(_)')")
Context[shallow] Account :: deposit (c : String, no : Integer, amount : Real) : Real
  Pre : "(\<lambda> amount no c self. (self .id \<doteq> no and ((self .owner .clientname) \<doteq> c) and (\<zero>.\<zero>  \<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l amount)))"
  Post : "(\<lambda> amount no c self result. (self .balance \<doteq> (self .balance@pre +\<^sub>r\<^sub>e\<^sub>a\<^sub>l amount)))"

(* 146 ************************************ 1822 + 3 *)
consts dot\<W>\<I>\<T>\<H>\<D>\<R>\<A>\<W> :: "Account \<Rightarrow> String \<Rightarrow> Integer \<Rightarrow> Real \<Rightarrow> Real" ("(_) .withdraw'((_),(_),(_)')")
consts dot\<W>\<I>\<T>\<H>\<D>\<R>\<A>\<W>at_pre :: "Account \<Rightarrow> String \<Rightarrow> Integer \<Rightarrow> Real \<Rightarrow> Real" ("(_) .withdraw@pre'((_),(_),(_)')")
Context[shallow] Account :: withdraw (c : String, no : Integer, amount : Real) : Real
  Pre : "(\<lambda> amount no c self. (self .id \<doteq> no and ((self .owner .clientname) \<doteq> c) and (\<zero>.\<zero>  \<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l amount)))"
  Post : "(\<lambda> amount no c self result. (self .balance \<doteq> (self .balance@pre -\<^sub>r\<^sub>e\<^sub>a\<^sub>l amount)))"

end
