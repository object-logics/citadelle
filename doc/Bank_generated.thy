theory Bank_generated imports "../src/UML_Main"   "../src/compiler/OCL_compiler_static"   "../src/compiler/OCL_compiler_generator_dynamic" begin

(* 1 ************************************ 0 + 1 *)
type_synonym ty_syn\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>c\<^sub>y = "real"

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
datatype ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t = mk\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t "oid" "int option" "ty_syn\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>c\<^sub>y option"
datatype ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t = mk\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t "ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t" "ty_syn\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>c\<^sub>y option"
datatype ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s = mk\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s "oid" "int option" "ty_syn\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>c\<^sub>y option"
datatype ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s = mk\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s "ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s" "ty_syn\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>c\<^sub>y option"
datatype ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t = mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s "ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s"
                        | mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t "ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t"
                        | mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t "oid"
datatype ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t = mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t "ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t" "int option" "ty_syn\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>c\<^sub>y option"
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

(* 19 ************************************ 29 + 7 *)
type_synonym Void = "\<AA> Void"
type_synonym Boolean = "\<AA> Boolean"
type_synonym Integer = "\<AA> Integer"
type_synonym Real = "\<AA> Real"
type_synonym String = "\<AA> String"
type_synonym '\<alpha> val' = "(\<AA>, '\<alpha>) val"
type_notation val' ("\<cdot>(_)")

(* 20 ************************************ 36 + 6 *)
type_synonym Current = "\<langle>\<langle>ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>"
type_synonym Savings = "\<langle>\<langle>ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>"
type_synonym Account = "\<langle>\<langle>ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>"
type_synonym Bank = "\<langle>\<langle>ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>"
type_synonym Client = "\<langle>\<langle>ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>"
type_synonym OclAny = "\<langle>\<langle>ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>"

(* 21 ************************************ 42 + 6 *)
type_synonym Sequence_Client = "(\<AA>, ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t option option Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"
type_synonym Set_Client = "(\<AA>, ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t option option Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"
type_synonym Sequence_Bank = "(\<AA>, ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k option option Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"
type_synonym Set_Bank = "(\<AA>, ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k option option Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"
type_synonym Sequence_Account = "(\<AA>, ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t option option Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"
type_synonym Set_Account = "(\<AA>, ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t option option Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"

(* 22 ************************************ 48 + 1 *)
type_synonym Currency = "Real"

(* 23 ************************************ 49 + 1 *)
text{* 
   To reuse key-elements of the library like referential equality, we have
to show that the object universe belongs to the type class ``oclany,'' \ie,
 each class type has to provide a function @{term oid_of} yielding the object id (oid) of the object.  *}

(* 24 ************************************ 50 + 6 *)
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

(* 25 ************************************ 56 + 1 *)
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

(* 26 ************************************ 57 + 1 *)
section{* Instantiation of the Generic Strict Equality *}

(* 27 ************************************ 58 + 1 *)
text{* 
   We instantiate the referential equality
on @{text "Person"} and @{text "OclAny"}  *}

(* 28 ************************************ 59 + 6 *)
defs(overloaded) StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t : "(x::\<cdot>Current) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
defs(overloaded) StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s : "(x::\<cdot>Savings) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
defs(overloaded) StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : "(x::\<cdot>Account) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
defs(overloaded) StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>B\<^sub>a\<^sub>n\<^sub>k : "(x::\<cdot>Bank) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
defs(overloaded) StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t : "(x::\<cdot>Client) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
defs(overloaded) StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : "(x::\<cdot>OclAny) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"

(* 29 ************************************ 65 + 1 *)
lemmas[simp,code_unfold] = StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t
                            StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s
                            StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t
                            StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>B\<^sub>a\<^sub>n\<^sub>k
                            StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t
                            StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y

(* 30 ************************************ 66 + 1 *)
text{* 
   For each Class \emph{C}, we will have a casting operation \inlineocl{.oclAsType($C$)},
   a test on the actual type \inlineocl{.oclIsTypeOf($C$)} as well as its relaxed form
   \inlineocl{.oclIsKindOf($C$)} (corresponding exactly to Java's \verb+instanceof+-operator.
 *}

(* 31 ************************************ 67 + 1 *)
text{* 
   Thus, since we have two class-types in our concrete class hierarchy, we have
two operations to declare and to provide two overloading definitions for the two static types.
 *}

(* 32 ************************************ 68 + 1 *)
section{* OclAsType *}

(* 33 ************************************ 69 + 1 *)
subsection{* Definition *}

(* 34 ************************************ 70 + 6 *)
consts OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t :: "'\<alpha> \<Rightarrow> \<cdot>Current" ("(_) .oclAsType'(Current')")
consts OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s :: "'\<alpha> \<Rightarrow> \<cdot>Savings" ("(_) .oclAsType'(Savings')")
consts OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t :: "'\<alpha> \<Rightarrow> \<cdot>Account" ("(_) .oclAsType'(Account')")
consts OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k :: "'\<alpha> \<Rightarrow> \<cdot>Bank" ("(_) .oclAsType'(Bank')")
consts OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t :: "'\<alpha> \<Rightarrow> \<cdot>Client" ("(_) .oclAsType'(Client')")
consts OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: "'\<alpha> \<Rightarrow> \<cdot>OclAny" ("(_) .oclAsType'(OclAny')")

(* 35 ************************************ 76 + 36 *)
defs(overloaded) OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current : "(x::\<cdot>Current) .oclAsType(Current) \<equiv> x"
defs(overloaded) OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account : "(x::\<cdot>Account) .oclAsType(Current) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Current\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny : "(x::\<cdot>OclAny) .oclAsType(Current) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Current\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings : "(x::\<cdot>Savings) .oclAsType(Current) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank : "(x::\<cdot>Bank) .oclAsType(Current) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client : "(x::\<cdot>Client) .oclAsType(Current) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings : "(x::\<cdot>Savings) .oclAsType(Savings) \<equiv> x"
defs(overloaded) OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account : "(x::\<cdot>Account) .oclAsType(Savings) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Savings\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny : "(x::\<cdot>OclAny) .oclAsType(Savings) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Savings\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current : "(x::\<cdot>Current) .oclAsType(Savings) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank : "(x::\<cdot>Bank) .oclAsType(Savings) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client : "(x::\<cdot>Client) .oclAsType(Savings) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account : "(x::\<cdot>Account) .oclAsType(Account) \<equiv> x"
defs(overloaded) OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny : "(x::\<cdot>OclAny) .oclAsType(Account) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Account\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current : "(x::\<cdot>Current) .oclAsType(Account) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Current\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current))) (None) (None))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings : "(x::\<cdot>Savings) .oclAsType(Account) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Savings\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings))) (None) (None))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank : "(x::\<cdot>Bank) .oclAsType(Account) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client : "(x::\<cdot>Client) .oclAsType(Account) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank : "(x::\<cdot>Bank) .oclAsType(Bank) \<equiv> x"
defs(overloaded) OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny : "(x::\<cdot>OclAny) .oclAsType(Bank) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Bank\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client : "(x::\<cdot>Client) .oclAsType(Bank) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings : "(x::\<cdot>Savings) .oclAsType(Bank) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account : "(x::\<cdot>Account) .oclAsType(Bank) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current : "(x::\<cdot>Current) .oclAsType(Bank) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client : "(x::\<cdot>Client) .oclAsType(Client) \<equiv> x"
defs(overloaded) OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny : "(x::\<cdot>OclAny) .oclAsType(Client) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client))))\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>Client\<rfloor>\<rfloor>
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank : "(x::\<cdot>Bank) .oclAsType(Client) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings : "(x::\<cdot>Savings) .oclAsType(Client) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account : "(x::\<cdot>Account) .oclAsType(Client) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current : "(x::\<cdot>Current) .oclAsType(Client) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"
defs(overloaded) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny : "(x::\<cdot>OclAny) .oclAsType(OclAny) \<equiv> x"
defs(overloaded) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current : "(x::\<cdot>Current) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Current\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current))))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings : "(x::\<cdot>Savings) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Savings\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings))))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account : "(x::\<cdot>Account) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Account\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account))))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank : "(x::\<cdot>Bank) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Bank\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank))))\<rfloor>\<rfloor>))"
defs(overloaded) OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client : "(x::\<cdot>Client) .oclAsType(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (null (\<tau>))
    | \<lfloor>\<lfloor>Client\<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client))))\<rfloor>\<rfloor>))"

(* 36 ************************************ 112 + 6 *)
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

(* 37 ************************************ 118 + 1 *)
lemmas[simp,code_unfold] = OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current
                            OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings
                            OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account
                            OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank
                            OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny

(* 38 ************************************ 119 + 1 *)
subsection{* Context Passing *}

(* 39 ************************************ 120 + 216 *)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Savings) .oclAsType(Savings)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Savings) .oclAsType(Savings)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Savings) .oclAsType(Savings)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Savings) .oclAsType(Savings)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Savings) .oclAsType(Savings)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Savings) .oclAsType(Savings)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Account) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Account) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Account) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Account) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Account) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Account) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Client) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Client) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Client) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Client) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Client) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Client) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>OclAny) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>OclAny) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>OclAny) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>OclAny) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>OclAny) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Bank) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Bank) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Bank) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Bank) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Bank) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Bank) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Current) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Current) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Current) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Current) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Current) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current)
lemma cp_OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Current) .oclAsType(Savings)))))"
by(rule cpI1, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Savings) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Savings) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Savings) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Savings) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Savings) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Savings) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Account) .oclAsType(Account)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Account) .oclAsType(Account)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Account) .oclAsType(Account)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Account) .oclAsType(Account)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Account) .oclAsType(Account)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Account) .oclAsType(Account)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Client) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Client) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Client) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Client) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Client) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Client) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>OclAny) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>OclAny) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>OclAny) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>OclAny) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>OclAny) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Bank) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Bank) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Bank) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Bank) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Bank) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Bank) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Current) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Current) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Current) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Current) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Current) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
lemma cp_OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Current) .oclAsType(Account)))))"
by(rule cpI1, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Savings) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Savings) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Savings) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Savings) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Savings) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Savings) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Account) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Account) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Account) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Account) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Account) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Account) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Client) .oclAsType(Client)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Client) .oclAsType(Client)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Client) .oclAsType(Client)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Client) .oclAsType(Client)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Client) .oclAsType(Client)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Client) .oclAsType(Client)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>OclAny) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>OclAny) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>OclAny) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>OclAny) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>OclAny) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Bank) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Bank) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Bank) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Bank) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Bank) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Bank) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Current) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Current) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Current) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Current) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Current) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current)
lemma cp_OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Current) .oclAsType(Client)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Savings) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Savings) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Savings) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Savings) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Savings) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Savings) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Account) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Account) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Account) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Account) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Account) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Account) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Client) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Client) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Client) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Client) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Client) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Client) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>OclAny) .oclAsType(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Bank) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Bank) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Bank) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Bank) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Bank) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Bank) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Current) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Current) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Current) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Current) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Current) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Current) .oclAsType(OclAny)))))"
by(rule cpI1, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Savings) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Savings) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Savings) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Savings) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Savings) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Savings) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Account) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Account) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Account) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Account) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Account) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Account) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Client) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Client) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Client) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Client) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Client) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Client) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>OclAny) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>OclAny) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>OclAny) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>OclAny) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>OclAny) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Bank) .oclAsType(Bank)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Bank) .oclAsType(Bank)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Bank) .oclAsType(Bank)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Bank) .oclAsType(Bank)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Bank) .oclAsType(Bank)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Bank) .oclAsType(Bank)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Current) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Current) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Current) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Current) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Current) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current)
lemma cp_OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Current) .oclAsType(Bank)))))"
by(rule cpI1, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Savings) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Savings) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Savings) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Savings) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Savings) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Savings) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Account) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Account) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Account) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Account) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Account) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Account) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Client) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Client) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Client) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Client) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Client) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Client) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>OclAny) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>OclAny) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>OclAny) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>OclAny) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>OclAny) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Bank) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Bank) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Bank) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Bank) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Bank) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Bank) .oclAsType(Current)))))"
by(rule cpI1, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Current) .oclAsType(Current)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Current) .oclAsType(Current)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Current) .oclAsType(Current)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Current) .oclAsType(Current)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Current) .oclAsType(Current)))))"
by(rule cpI1, simp)
lemma cp_OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Current) .oclAsType(Current)))))"
by(rule cpI1, simp)

(* 40 ************************************ 336 + 1 *)
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

(* 41 ************************************ 337 + 1 *)
subsection{* Execution with Invalid or Null as Argument *}

(* 42 ************************************ 338 + 72 *)
lemma OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_invalid : "((invalid::\<cdot>Savings) .oclAsType(Savings)) = invalid"
by(simp)
lemma OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_invalid : "((invalid::\<cdot>Account) .oclAsType(Savings)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account bot_option_def invalid_def)
lemma OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_invalid : "((invalid::\<cdot>Client) .oclAsType(Savings)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client bot_option_def invalid_def)
lemma OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclAsType(Savings)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny bot_option_def invalid_def)
lemma OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_invalid : "((invalid::\<cdot>Bank) .oclAsType(Savings)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank bot_option_def invalid_def)
lemma OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_invalid : "((invalid::\<cdot>Current) .oclAsType(Savings)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current bot_option_def invalid_def)
lemma OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_null : "((null::\<cdot>Savings) .oclAsType(Savings)) = null"
by(simp)
lemma OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_null : "((null::\<cdot>Account) .oclAsType(Savings)) = null"
by(rule ext, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_null : "((null::\<cdot>Client) .oclAsType(Savings)) = null"
by(rule ext, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_null : "((null::\<cdot>OclAny) .oclAsType(Savings)) = null"
by(rule ext, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_null : "((null::\<cdot>Bank) .oclAsType(Savings)) = null"
by(rule ext, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_null : "((null::\<cdot>Current) .oclAsType(Savings)) = null"
by(rule ext, simp add: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_invalid : "((invalid::\<cdot>Savings) .oclAsType(Account)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings bot_option_def invalid_def)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_invalid : "((invalid::\<cdot>Account) .oclAsType(Account)) = invalid"
by(simp)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_invalid : "((invalid::\<cdot>Client) .oclAsType(Account)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client bot_option_def invalid_def)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclAsType(Account)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny bot_option_def invalid_def)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_invalid : "((invalid::\<cdot>Bank) .oclAsType(Account)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank bot_option_def invalid_def)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_invalid : "((invalid::\<cdot>Current) .oclAsType(Account)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current bot_option_def invalid_def)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_null : "((null::\<cdot>Savings) .oclAsType(Account)) = null"
by(rule ext, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_null : "((null::\<cdot>Account) .oclAsType(Account)) = null"
by(simp)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_null : "((null::\<cdot>Client) .oclAsType(Account)) = null"
by(rule ext, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_null : "((null::\<cdot>OclAny) .oclAsType(Account)) = null"
by(rule ext, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_null : "((null::\<cdot>Bank) .oclAsType(Account)) = null"
by(rule ext, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_null : "((null::\<cdot>Current) .oclAsType(Account)) = null"
by(rule ext, simp add: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_invalid : "((invalid::\<cdot>Savings) .oclAsType(Client)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings bot_option_def invalid_def)
lemma OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_invalid : "((invalid::\<cdot>Account) .oclAsType(Client)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account bot_option_def invalid_def)
lemma OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_invalid : "((invalid::\<cdot>Client) .oclAsType(Client)) = invalid"
by(simp)
lemma OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclAsType(Client)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny bot_option_def invalid_def)
lemma OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_invalid : "((invalid::\<cdot>Bank) .oclAsType(Client)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank bot_option_def invalid_def)
lemma OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_invalid : "((invalid::\<cdot>Current) .oclAsType(Client)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current bot_option_def invalid_def)
lemma OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_null : "((null::\<cdot>Savings) .oclAsType(Client)) = null"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_null : "((null::\<cdot>Account) .oclAsType(Client)) = null"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_null : "((null::\<cdot>Client) .oclAsType(Client)) = null"
by(simp)
lemma OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_null : "((null::\<cdot>OclAny) .oclAsType(Client)) = null"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_null : "((null::\<cdot>Bank) .oclAsType(Client)) = null"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_null : "((null::\<cdot>Current) .oclAsType(Client)) = null"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_invalid : "((invalid::\<cdot>Savings) .oclAsType(OclAny)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings bot_option_def invalid_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_invalid : "((invalid::\<cdot>Account) .oclAsType(OclAny)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account bot_option_def invalid_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_invalid : "((invalid::\<cdot>Client) .oclAsType(OclAny)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client bot_option_def invalid_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclAsType(OclAny)) = invalid"
by(simp)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_invalid : "((invalid::\<cdot>Bank) .oclAsType(OclAny)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank bot_option_def invalid_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_invalid : "((invalid::\<cdot>Current) .oclAsType(OclAny)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current bot_option_def invalid_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_null : "((null::\<cdot>Savings) .oclAsType(OclAny)) = null"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_null : "((null::\<cdot>Account) .oclAsType(OclAny)) = null"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_null : "((null::\<cdot>Client) .oclAsType(OclAny)) = null"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null : "((null::\<cdot>OclAny) .oclAsType(OclAny)) = null"
by(simp)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_null : "((null::\<cdot>Bank) .oclAsType(OclAny)) = null"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_null : "((null::\<cdot>Current) .oclAsType(OclAny)) = null"
by(rule ext, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_invalid : "((invalid::\<cdot>Savings) .oclAsType(Bank)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings bot_option_def invalid_def)
lemma OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_invalid : "((invalid::\<cdot>Account) .oclAsType(Bank)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account bot_option_def invalid_def)
lemma OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_invalid : "((invalid::\<cdot>Client) .oclAsType(Bank)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client bot_option_def invalid_def)
lemma OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclAsType(Bank)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny bot_option_def invalid_def)
lemma OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_invalid : "((invalid::\<cdot>Bank) .oclAsType(Bank)) = invalid"
by(simp)
lemma OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_invalid : "((invalid::\<cdot>Current) .oclAsType(Bank)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current bot_option_def invalid_def)
lemma OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_null : "((null::\<cdot>Savings) .oclAsType(Bank)) = null"
by(rule ext, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_null : "((null::\<cdot>Account) .oclAsType(Bank)) = null"
by(rule ext, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_null : "((null::\<cdot>Client) .oclAsType(Bank)) = null"
by(rule ext, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_null : "((null::\<cdot>OclAny) .oclAsType(Bank)) = null"
by(rule ext, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_null : "((null::\<cdot>Bank) .oclAsType(Bank)) = null"
by(simp)
lemma OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_null : "((null::\<cdot>Current) .oclAsType(Bank)) = null"
by(rule ext, simp add: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_invalid : "((invalid::\<cdot>Savings) .oclAsType(Current)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings bot_option_def invalid_def)
lemma OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_invalid : "((invalid::\<cdot>Account) .oclAsType(Current)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account bot_option_def invalid_def)
lemma OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_invalid : "((invalid::\<cdot>Client) .oclAsType(Current)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client bot_option_def invalid_def)
lemma OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclAsType(Current)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny bot_option_def invalid_def)
lemma OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_invalid : "((invalid::\<cdot>Bank) .oclAsType(Current)) = invalid"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank bot_option_def invalid_def)
lemma OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_invalid : "((invalid::\<cdot>Current) .oclAsType(Current)) = invalid"
by(simp)
lemma OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_null : "((null::\<cdot>Savings) .oclAsType(Current)) = null"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_null : "((null::\<cdot>Account) .oclAsType(Current)) = null"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_null : "((null::\<cdot>Client) .oclAsType(Current)) = null"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_null : "((null::\<cdot>OclAny) .oclAsType(Current)) = null"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_null : "((null::\<cdot>Bank) .oclAsType(Current)) = null"
by(rule ext, simp add: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank bot_option_def null_fun_def null_option_def)
lemma OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_null : "((null::\<cdot>Current) .oclAsType(Current)) = null"
by(simp)

(* 43 ************************************ 410 + 1 *)
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

(* 44 ************************************ 411 + 1 *)
subsection{* Validity and Definedness Properties *}

(* 45 ************************************ 412 + 7 *)
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclAsType(Account)))"
  using isdef
by(auto simp: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current foundation16 null_option_def bot_option_def) 
lemma OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclAsType(Account)))"
  using isdef
by(auto simp: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings foundation16 null_option_def bot_option_def) 
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclAsType(OclAny)))"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current foundation16 null_option_def bot_option_def) 
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclAsType(OclAny)))"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings foundation16 null_option_def bot_option_def) 
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .oclAsType(OclAny)))"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account foundation16 null_option_def bot_option_def) 
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .oclAsType(OclAny)))"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank foundation16 null_option_def bot_option_def) 
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .oclAsType(OclAny)))"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client foundation16 null_option_def bot_option_def) 

(* 46 ************************************ 419 + 1 *)
subsection{* Up Down Casting *}

(* 47 ************************************ 420 + 7 *)
lemma up\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_down\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_cast0 : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::\<cdot>Current) .oclAsType(Account)) .oclAsType(Current)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split) 
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_cast0 : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::\<cdot>Current) .oclAsType(OclAny)) .oclAsType(Current)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split) 
lemma up\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_down\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_cast0 : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::\<cdot>Savings) .oclAsType(Account)) .oclAsType(Savings)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split) 
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_cast0 : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::\<cdot>Savings) .oclAsType(OclAny)) .oclAsType(Savings)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split) 
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_cast0 : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::\<cdot>Account) .oclAsType(OclAny)) .oclAsType(Account)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split) 
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>B\<^sub>a\<^sub>n\<^sub>k_cast0 : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::\<cdot>Bank) .oclAsType(OclAny)) .oclAsType(Bank)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split) 
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_cast0 : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (((X::\<cdot>Client) .oclAsType(OclAny)) .oclAsType(Client)) \<triangleq> X"
  using isdef
by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split) 

(* 48 ************************************ 427 + 7 *)
lemma up\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_down\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_cast : 
shows "(((X::\<cdot>Current) .oclAsType(Account)) .oclAsType(Current)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_down\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done 
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_cast : 
shows "(((X::\<cdot>Current) .oclAsType(OclAny)) .oclAsType(Current)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done 
lemma up\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_down\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_cast : 
shows "(((X::\<cdot>Savings) .oclAsType(Account)) .oclAsType(Savings)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_down\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done 
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_cast : 
shows "(((X::\<cdot>Savings) .oclAsType(OclAny)) .oclAsType(Savings)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done 
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_cast : 
shows "(((X::\<cdot>Account) .oclAsType(OclAny)) .oclAsType(Account)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done 
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>B\<^sub>a\<^sub>n\<^sub>k_cast : 
shows "(((X::\<cdot>Bank) .oclAsType(OclAny)) .oclAsType(Bank)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>B\<^sub>a\<^sub>n\<^sub>k_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done 
lemma up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_cast : 
shows "(((X::\<cdot>Client) .oclAsType(OclAny)) .oclAsType(Client)) = X"
  apply(rule ext, rename_tac \<tau>)
  apply(rule foundation22[THEN iffD1])
  apply(case_tac "\<tau> \<Turnstile> (\<delta> (X))", simp add: up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_cast0)
  apply(simp add: defined_split, elim disjE)
  apply((erule StrongEq_L_subst2_rev, simp, simp)+)
done 

(* 49 ************************************ 434 + 7 *)
lemma down\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_up\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_cast : 
assumes def_X: "X = ((Y::\<cdot>Current) .oclAsType(Account))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Current)) .oclAsType(Account)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_down\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym) 
lemma down\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_cast : 
assumes def_X: "X = ((Y::\<cdot>Current) .oclAsType(OclAny))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Current)) .oclAsType(OclAny)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym) 
lemma down\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_up\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_cast : 
assumes def_X: "X = ((Y::\<cdot>Savings) .oclAsType(Account))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Savings)) .oclAsType(Account)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_down\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym) 
lemma down\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_cast : 
assumes def_X: "X = ((Y::\<cdot>Savings) .oclAsType(OclAny))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Savings)) .oclAsType(OclAny)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym) 
lemma down\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_cast : 
assumes def_X: "X = ((Y::\<cdot>Account) .oclAsType(OclAny))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Account)) .oclAsType(OclAny)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym) 
lemma down\<^sub>B\<^sub>a\<^sub>n\<^sub>k_up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_cast : 
assumes def_X: "X = ((Y::\<cdot>Bank) .oclAsType(OclAny))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Bank)) .oclAsType(OclAny)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>B\<^sub>a\<^sub>n\<^sub>k_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym) 
lemma down\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_cast : 
assumes def_X: "X = ((Y::\<cdot>Client) .oclAsType(OclAny))"
shows "(\<tau> \<Turnstile> ((not ((\<upsilon> (X)))) or ((X .oclAsType(Client)) .oclAsType(OclAny)) \<doteq> X))"
  apply(case_tac "(\<tau> \<Turnstile> ((not ((\<upsilon> (X))))))", rule foundation25, simp)
by(rule foundation25', simp add: def_X up\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_down\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_cast StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym) 

(* 50 ************************************ 441 + 1 *)
section{* OclIsTypeOf *}

(* 51 ************************************ 442 + 1 *)
subsection{* Definition *}

(* 52 ************************************ 443 + 6 *)
consts OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Current')")
consts OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Savings')")
consts OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Account')")
consts OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Bank')")
consts OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(Client')")
consts OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(OclAny')")

(* 53 ************************************ 449 + 36 *)
defs(overloaded) OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current : "(x::\<cdot>Current) .oclIsTypeOf(Current) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (_) (_) (_))) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account : "(x::\<cdot>Account) .oclIsTypeOf(Current) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny : "(x::\<cdot>OclAny) .oclIsTypeOf(Current) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings : "(x::\<cdot>Savings) .oclIsTypeOf(Current) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank : "(x::\<cdot>Bank) .oclIsTypeOf(Current) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client : "(x::\<cdot>Client) .oclIsTypeOf(Current) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings : "(x::\<cdot>Savings) .oclIsTypeOf(Savings) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s ((mk\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (_) (_) (_))) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account : "(x::\<cdot>Account) .oclIsTypeOf(Savings) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny : "(x::\<cdot>OclAny) .oclIsTypeOf(Savings) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current : "(x::\<cdot>Current) .oclIsTypeOf(Savings) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank : "(x::\<cdot>Bank) .oclIsTypeOf(Savings) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client : "(x::\<cdot>Client) .oclIsTypeOf(Savings) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account : "(x::\<cdot>Account) .oclIsTypeOf(Account) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (_))) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny : "(x::\<cdot>OclAny) .oclIsTypeOf(Account) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current : "(x::\<cdot>Current) .oclIsTypeOf(Account) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings : "(x::\<cdot>Savings) .oclIsTypeOf(Account) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank : "(x::\<cdot>Bank) .oclIsTypeOf(Account) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client : "(x::\<cdot>Client) .oclIsTypeOf(Account) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank : "(x::\<cdot>Bank) .oclIsTypeOf(Bank) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>B\<^sub>a\<^sub>n\<^sub>k ((mk\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k (_))) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny : "(x::\<cdot>OclAny) .oclIsTypeOf(Bank) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>B\<^sub>a\<^sub>n\<^sub>k (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client : "(x::\<cdot>Client) .oclIsTypeOf(Bank) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings : "(x::\<cdot>Savings) .oclIsTypeOf(Bank) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account : "(x::\<cdot>Account) .oclIsTypeOf(Bank) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current : "(x::\<cdot>Current) .oclIsTypeOf(Bank) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client : "(x::\<cdot>Client) .oclIsTypeOf(Client) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (_))) (_) (_) (_))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny : "(x::\<cdot>OclAny) .oclIsTypeOf(Client) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank : "(x::\<cdot>Bank) .oclIsTypeOf(Client) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings : "(x::\<cdot>Savings) .oclIsTypeOf(Client) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account : "(x::\<cdot>Account) .oclIsTypeOf(Client) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current : "(x::\<cdot>Current) .oclIsTypeOf(Client) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny : "(x::\<cdot>OclAny) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current : "(x::\<cdot>Current) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings : "(x::\<cdot>Savings) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account : "(x::\<cdot>Account) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank : "(x::\<cdot>Bank) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"
defs(overloaded) OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client : "(x::\<cdot>Client) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | _ \<Rightarrow> (false (\<tau>))))"

(* 54 ************************************ 485 + 6 *)
definition "OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_\<AA> = (\<lambda> (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Current))::\<cdot>Current) .oclIsTypeOf(Current))
    | (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Account))::\<cdot>Account) .oclIsTypeOf(Current))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::\<cdot>OclAny) .oclIsTypeOf(Current))
    | (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Savings))::\<cdot>Savings) .oclIsTypeOf(Current))
    | (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Bank))::\<cdot>Bank) .oclIsTypeOf(Current))
    | (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Client))::\<cdot>Client) .oclIsTypeOf(Current)))"
definition "OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_\<AA> = (\<lambda> (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Savings))::\<cdot>Savings) .oclIsTypeOf(Savings))
    | (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Account))::\<cdot>Account) .oclIsTypeOf(Savings))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::\<cdot>OclAny) .oclIsTypeOf(Savings))
    | (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Current))::\<cdot>Current) .oclIsTypeOf(Savings))
    | (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Bank))::\<cdot>Bank) .oclIsTypeOf(Savings))
    | (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Client))::\<cdot>Client) .oclIsTypeOf(Savings)))"
definition "OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<AA> = (\<lambda> (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Account))::\<cdot>Account) .oclIsTypeOf(Account))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::\<cdot>OclAny) .oclIsTypeOf(Account))
    | (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Current))::\<cdot>Current) .oclIsTypeOf(Account))
    | (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Savings))::\<cdot>Savings) .oclIsTypeOf(Account))
    | (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Bank))::\<cdot>Bank) .oclIsTypeOf(Account))
    | (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Client))::\<cdot>Client) .oclIsTypeOf(Account)))"
definition "OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_\<AA> = (\<lambda> (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Bank))::\<cdot>Bank) .oclIsTypeOf(Bank))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::\<cdot>OclAny) .oclIsTypeOf(Bank))
    | (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Client))::\<cdot>Client) .oclIsTypeOf(Bank))
    | (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Savings))::\<cdot>Savings) .oclIsTypeOf(Bank))
    | (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Account))::\<cdot>Account) .oclIsTypeOf(Bank))
    | (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Current))::\<cdot>Current) .oclIsTypeOf(Bank)))"
definition "OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_\<AA> = (\<lambda> (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Client))::\<cdot>Client) .oclIsTypeOf(Client))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::\<cdot>OclAny) .oclIsTypeOf(Client))
    | (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Bank))::\<cdot>Bank) .oclIsTypeOf(Client))
    | (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Savings))::\<cdot>Savings) .oclIsTypeOf(Client))
    | (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Account))::\<cdot>Account) .oclIsTypeOf(Client))
    | (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Current))::\<cdot>Current) .oclIsTypeOf(Client)))"
definition "OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::\<cdot>OclAny) .oclIsTypeOf(OclAny))
    | (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Current))::\<cdot>Current) .oclIsTypeOf(OclAny))
    | (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Savings))::\<cdot>Savings) .oclIsTypeOf(OclAny))
    | (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Account))::\<cdot>Account) .oclIsTypeOf(OclAny))
    | (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Bank))::\<cdot>Bank) .oclIsTypeOf(OclAny))
    | (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Client))::\<cdot>Client) .oclIsTypeOf(OclAny)))"

(* 55 ************************************ 491 + 1 *)
lemmas[simp,code_unfold] = OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current
                            OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings
                            OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account
                            OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank
                            OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client
                            OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny

(* 56 ************************************ 492 + 1 *)
subsection{* Context Passing *}

(* 57 ************************************ 493 + 216 *)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Savings) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Savings) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Savings) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Savings) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Savings) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Savings) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Account) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Account) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Account) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Account) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Account) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Account) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Client) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Client) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Client) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Client) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Client) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Client) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>OclAny) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>OclAny) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>OclAny) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>OclAny) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>OclAny) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Bank) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Bank) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Bank) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Bank) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Bank) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Bank) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Current) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Current) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Current) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Current) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Current) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current)
lemma cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Current) .oclIsTypeOf(Savings)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Savings) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Savings) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Savings) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Savings) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Savings) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Savings) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Account) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Account) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Account) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Account) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Account) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Account) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Client) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Client) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Client) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Client) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Client) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Client) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>OclAny) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>OclAny) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>OclAny) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>OclAny) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>OclAny) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Bank) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Bank) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Bank) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Bank) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Bank) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Bank) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Current) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Current) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Current) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Current) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Current) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
lemma cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Current) .oclIsTypeOf(Account)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Savings) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Savings) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Savings) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Savings) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Savings) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Savings) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Account) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Account) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Account) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Account) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Account) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Account) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Client) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Client) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Client) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Client) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Client) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Client) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>OclAny) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>OclAny) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>OclAny) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>OclAny) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>OclAny) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Bank) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Bank) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Bank) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Bank) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Bank) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Bank) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Current) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Current) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Current) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Current) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Current) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Current) .oclIsTypeOf(Client)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Savings) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Savings) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Savings) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Savings) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Savings) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Savings) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Account) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Account) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Account) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Account) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Account) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Account) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Client) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Client) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Client) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Client) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Client) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Client) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>OclAny) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Bank) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Bank) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Bank) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Bank) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Bank) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Bank) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Current) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Current) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Current) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Current) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Current) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Current) .oclIsTypeOf(OclAny)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Savings) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Savings) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Savings) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Savings) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Savings) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Savings) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Account) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Account) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Account) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Account) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Account) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Account) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Client) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Client) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Client) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Client) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Client) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Client) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>OclAny) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>OclAny) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>OclAny) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>OclAny) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>OclAny) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Bank) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Bank) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Bank) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Bank) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Bank) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Bank) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Current) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Current) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Current) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Current) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Current) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current)
lemma cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Current) .oclIsTypeOf(Bank)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Savings) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Savings) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Savings) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Savings) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Savings) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Savings) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Account) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Account) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Account) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Account) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Account) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Account) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Client) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Client) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Client) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Client) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Client) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Client) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>OclAny) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>OclAny) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>OclAny) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>OclAny) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>OclAny) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Bank) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Bank) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Bank) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Bank) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Bank) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Bank) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Current) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Current) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Current) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Current) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Current) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp)
lemma cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Current) .oclIsTypeOf(Current)))))"
by(rule cpI1, simp)

(* 58 ************************************ 709 + 1 *)
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

(* 59 ************************************ 710 + 1 *)
subsection{* Execution with Invalid or Null as Argument *}

(* 60 ************************************ 711 + 72 *)
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_invalid : "((invalid::\<cdot>Savings) .oclIsTypeOf(Savings)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_invalid : "((invalid::\<cdot>Account) .oclIsTypeOf(Savings)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_invalid : "((invalid::\<cdot>Client) .oclIsTypeOf(Savings)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclIsTypeOf(Savings)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_invalid : "((invalid::\<cdot>Bank) .oclIsTypeOf(Savings)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_invalid : "((invalid::\<cdot>Current) .oclIsTypeOf(Savings)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_null : "((null::\<cdot>Savings) .oclIsTypeOf(Savings)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_null : "((null::\<cdot>Account) .oclIsTypeOf(Savings)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_null : "((null::\<cdot>Client) .oclIsTypeOf(Savings)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_null : "((null::\<cdot>OclAny) .oclIsTypeOf(Savings)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_null : "((null::\<cdot>Bank) .oclIsTypeOf(Savings)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_null : "((null::\<cdot>Current) .oclIsTypeOf(Savings)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_invalid : "((invalid::\<cdot>Savings) .oclIsTypeOf(Account)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_invalid : "((invalid::\<cdot>Account) .oclIsTypeOf(Account)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_invalid : "((invalid::\<cdot>Client) .oclIsTypeOf(Account)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclIsTypeOf(Account)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_invalid : "((invalid::\<cdot>Bank) .oclIsTypeOf(Account)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_invalid : "((invalid::\<cdot>Current) .oclIsTypeOf(Account)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_null : "((null::\<cdot>Savings) .oclIsTypeOf(Account)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_null : "((null::\<cdot>Account) .oclIsTypeOf(Account)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_null : "((null::\<cdot>Client) .oclIsTypeOf(Account)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_null : "((null::\<cdot>OclAny) .oclIsTypeOf(Account)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_null : "((null::\<cdot>Bank) .oclIsTypeOf(Account)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_null : "((null::\<cdot>Current) .oclIsTypeOf(Account)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_invalid : "((invalid::\<cdot>Savings) .oclIsTypeOf(Client)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_invalid : "((invalid::\<cdot>Account) .oclIsTypeOf(Client)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_invalid : "((invalid::\<cdot>Client) .oclIsTypeOf(Client)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclIsTypeOf(Client)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_invalid : "((invalid::\<cdot>Bank) .oclIsTypeOf(Client)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_invalid : "((invalid::\<cdot>Current) .oclIsTypeOf(Client)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_null : "((null::\<cdot>Savings) .oclIsTypeOf(Client)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_null : "((null::\<cdot>Account) .oclIsTypeOf(Client)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_null : "((null::\<cdot>Client) .oclIsTypeOf(Client)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_null : "((null::\<cdot>OclAny) .oclIsTypeOf(Client)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_null : "((null::\<cdot>Bank) .oclIsTypeOf(Client)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_null : "((null::\<cdot>Current) .oclIsTypeOf(Client)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_invalid : "((invalid::\<cdot>Savings) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_invalid : "((invalid::\<cdot>Account) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_invalid : "((invalid::\<cdot>Client) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_invalid : "((invalid::\<cdot>Bank) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_invalid : "((invalid::\<cdot>Current) .oclIsTypeOf(OclAny)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_null : "((null::\<cdot>Savings) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_null : "((null::\<cdot>Account) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_null : "((null::\<cdot>Client) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null : "((null::\<cdot>OclAny) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_null : "((null::\<cdot>Bank) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_null : "((null::\<cdot>Current) .oclIsTypeOf(OclAny)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_invalid : "((invalid::\<cdot>Savings) .oclIsTypeOf(Bank)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_invalid : "((invalid::\<cdot>Account) .oclIsTypeOf(Bank)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_invalid : "((invalid::\<cdot>Client) .oclIsTypeOf(Bank)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclIsTypeOf(Bank)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_invalid : "((invalid::\<cdot>Bank) .oclIsTypeOf(Bank)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_invalid : "((invalid::\<cdot>Current) .oclIsTypeOf(Bank)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_null : "((null::\<cdot>Savings) .oclIsTypeOf(Bank)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_null : "((null::\<cdot>Account) .oclIsTypeOf(Bank)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_null : "((null::\<cdot>Client) .oclIsTypeOf(Bank)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_null : "((null::\<cdot>OclAny) .oclIsTypeOf(Bank)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_null : "((null::\<cdot>Bank) .oclIsTypeOf(Bank)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_null : "((null::\<cdot>Current) .oclIsTypeOf(Bank)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_invalid : "((invalid::\<cdot>Savings) .oclIsTypeOf(Current)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_invalid : "((invalid::\<cdot>Account) .oclIsTypeOf(Current)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_invalid : "((invalid::\<cdot>Client) .oclIsTypeOf(Current)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclIsTypeOf(Current)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_invalid : "((invalid::\<cdot>Bank) .oclIsTypeOf(Current)) = invalid"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_invalid : "((invalid::\<cdot>Current) .oclIsTypeOf(Current)) = invalid"
by(rule ext, simp add: bot_option_def invalid_def)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_null : "((null::\<cdot>Savings) .oclIsTypeOf(Current)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_null : "((null::\<cdot>Account) .oclIsTypeOf(Current)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_null : "((null::\<cdot>Client) .oclIsTypeOf(Current)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_null : "((null::\<cdot>OclAny) .oclIsTypeOf(Current)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_null : "((null::\<cdot>Bank) .oclIsTypeOf(Current)) = true"
by(rule ext, simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank bot_option_def null_fun_def null_option_def)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_null : "((null::\<cdot>Current) .oclIsTypeOf(Current)) = true"
by(rule ext, simp add: bot_option_def null_fun_def null_option_def)

(* 61 ************************************ 783 + 1 *)
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

(* 62 ************************************ 784 + 1 *)
subsection{* Validity and Definedness Properties *}

(* 63 ************************************ 785 + 36 *)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclIsTypeOf(Current)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .oclIsTypeOf(Current)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account split: option.split ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsTypeOf(Current)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny split: option.split ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split) 
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclIsTypeOf(Current)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings split: option.split ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split) 
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .oclIsTypeOf(Current)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank split: option.split ty\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split) 
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .oclIsTypeOf(Current)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclIsTypeOf(Savings)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings split: option.split ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split) 
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .oclIsTypeOf(Savings)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account split: option.split ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsTypeOf(Savings)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny split: option.split ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split) 
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclIsTypeOf(Savings)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .oclIsTypeOf(Savings)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank split: option.split ty\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split) 
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .oclIsTypeOf(Savings)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .oclIsTypeOf(Account)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account split: option.split ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsTypeOf(Account)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny split: option.split ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split) 
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclIsTypeOf(Account)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclIsTypeOf(Account)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings split: option.split ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split) 
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .oclIsTypeOf(Account)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank split: option.split ty\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split) 
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .oclIsTypeOf(Account)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .oclIsTypeOf(Bank)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank split: option.split ty\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split) 
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsTypeOf(Bank)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny split: option.split ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split) 
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .oclIsTypeOf(Bank)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclIsTypeOf(Bank)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings split: option.split ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split) 
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .oclIsTypeOf(Bank)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account split: option.split ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclIsTypeOf(Bank)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .oclIsTypeOf(Client)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsTypeOf(Client)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny split: option.split ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split) 
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .oclIsTypeOf(Client)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank split: option.split ty\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split) 
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclIsTypeOf(Client)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings split: option.split ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split) 
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .oclIsTypeOf(Client)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account split: option.split ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclIsTypeOf(Client)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsTypeOf(OclAny)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny split: option.split ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclIsTypeOf(OclAny)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclIsTypeOf(OclAny)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings split: option.split ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .oclIsTypeOf(OclAny)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account split: option.split ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .oclIsTypeOf(OclAny)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank split: option.split ty\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .oclIsTypeOf(OclAny)))"
  apply(insert isdef[simplified foundation18'], simp only: OclValid_def, subst cp_defined)
by(auto simp: cp_defined[symmetric ] bot_option_def OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split) 

(* 64 ************************************ 821 + 36 *)
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclIsTypeOf(Current)))"
by(rule OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .oclIsTypeOf(Current)))"
by(rule OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsTypeOf(Current)))"
by(rule OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclIsTypeOf(Current)))"
by(rule OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .oclIsTypeOf(Current)))"
by(rule OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .oclIsTypeOf(Current)))"
by(rule OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclIsTypeOf(Savings)))"
by(rule OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .oclIsTypeOf(Savings)))"
by(rule OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsTypeOf(Savings)))"
by(rule OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclIsTypeOf(Savings)))"
by(rule OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .oclIsTypeOf(Savings)))"
by(rule OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .oclIsTypeOf(Savings)))"
by(rule OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .oclIsTypeOf(Account)))"
by(rule OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsTypeOf(Account)))"
by(rule OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclIsTypeOf(Account)))"
by(rule OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclIsTypeOf(Account)))"
by(rule OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .oclIsTypeOf(Account)))"
by(rule OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .oclIsTypeOf(Account)))"
by(rule OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .oclIsTypeOf(Bank)))"
by(rule OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsTypeOf(Bank)))"
by(rule OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .oclIsTypeOf(Bank)))"
by(rule OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclIsTypeOf(Bank)))"
by(rule OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .oclIsTypeOf(Bank)))"
by(rule OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclIsTypeOf(Bank)))"
by(rule OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .oclIsTypeOf(Client)))"
by(rule OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsTypeOf(Client)))"
by(rule OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .oclIsTypeOf(Client)))"
by(rule OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclIsTypeOf(Client)))"
by(rule OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .oclIsTypeOf(Client)))"
by(rule OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclIsTypeOf(Client)))"
by(rule OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsTypeOf(OclAny)))"
by(rule OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclIsTypeOf(OclAny)))"
by(rule OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclIsTypeOf(OclAny)))"
by(rule OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .oclIsTypeOf(OclAny)))"
by(rule OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .oclIsTypeOf(OclAny)))"
by(rule OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_defined[OF isdef[THEN foundation20]]) 
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .oclIsTypeOf(OclAny)))"
by(rule OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_defined[OF isdef[THEN foundation20]]) 

(* 65 ************************************ 857 + 1 *)
subsection{* Up Down Casting *}

(* 66 ************************************ 858 + 23 *)
lemma actualType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_larger_staticType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Current) .oclIsTypeOf(Account)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_larger_staticType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Current) .oclIsTypeOf(OclAny)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_larger_staticType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Current) .oclIsTypeOf(Savings)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_larger_staticType\<^sub>B\<^sub>a\<^sub>n\<^sub>k : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Current) .oclIsTypeOf(Bank)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_larger_staticType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Current) .oclIsTypeOf(Client)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_larger_staticType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Savings) .oclIsTypeOf(Account)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_larger_staticType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Savings) .oclIsTypeOf(OclAny)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_larger_staticType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Savings) .oclIsTypeOf(Current)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_larger_staticType\<^sub>B\<^sub>a\<^sub>n\<^sub>k : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Savings) .oclIsTypeOf(Bank)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_larger_staticType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Savings) .oclIsTypeOf(Client)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_larger_staticType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Account) .oclIsTypeOf(OclAny)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_larger_staticType\<^sub>B\<^sub>a\<^sub>n\<^sub>k : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Account) .oclIsTypeOf(Bank)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_larger_staticType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Account) .oclIsTypeOf(Client)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_larger_staticType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Bank) .oclIsTypeOf(OclAny)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_larger_staticType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Bank) .oclIsTypeOf(Client)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_larger_staticType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Bank) .oclIsTypeOf(Savings)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_larger_staticType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Bank) .oclIsTypeOf(Account)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_larger_staticType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Bank) .oclIsTypeOf(Current)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_larger_staticType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Client) .oclIsTypeOf(OclAny)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_larger_staticType\<^sub>B\<^sub>a\<^sub>n\<^sub>k : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Client) .oclIsTypeOf(Bank)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_larger_staticType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Client) .oclIsTypeOf(Savings)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_larger_staticType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Client) .oclIsTypeOf(Account)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client foundation22 foundation16 null_option_def bot_option_def) 
lemma actualType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_larger_staticType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Client) .oclIsTypeOf(Current)) \<triangleq> false"
  using isdef
by(auto simp: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client foundation22 foundation16 null_option_def bot_option_def) 

(* 67 ************************************ 881 + 31 *)
lemma down_cast_type\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_from_Account_to_Current : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>Account) .oclIsTypeOf(Account))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Current)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split)
by(simp add: OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Current : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(OclAny))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Current)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_from_OclAny_to_Current : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Account))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Current)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_from_Account_to_Current : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>Account) .oclIsTypeOf(Savings))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Current)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split)
by(simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>B\<^sub>a\<^sub>n\<^sub>k_from_Account_to_Current : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>Account) .oclIsTypeOf(Bank))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Current)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split)
by(simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_from_Account_to_Current : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>Account) .oclIsTypeOf(Client))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Current)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split)
by(simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_from_OclAny_to_Current : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Savings))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Current)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>B\<^sub>a\<^sub>n\<^sub>k_from_OclAny_to_Current : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Bank))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Current)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Current : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Client))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Current)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_from_Account_to_Savings : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>Account) .oclIsTypeOf(Account))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Savings)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split)
by(simp add: OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Savings : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(OclAny))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Savings)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_from_OclAny_to_Savings : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Account))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Savings)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_from_Account_to_Savings : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>Account) .oclIsTypeOf(Current))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Savings)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split)
by(simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>B\<^sub>a\<^sub>n\<^sub>k_from_Account_to_Savings : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>Account) .oclIsTypeOf(Bank))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Savings)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split)
by(simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_from_Account_to_Savings : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>Account) .oclIsTypeOf(Client))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Savings)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split)
by(simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Savings : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Current))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Savings)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>B\<^sub>a\<^sub>n\<^sub>k_from_OclAny_to_Savings : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Bank))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Savings)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Savings : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Client))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Savings)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Account : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(OclAny))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Account)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>B\<^sub>a\<^sub>n\<^sub>k_from_OclAny_to_Account : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Bank))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Account)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Account : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Client))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Account)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Bank : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(OclAny))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Bank)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Bank : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Client))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Bank)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_from_OclAny_to_Bank : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Savings))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Bank)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_from_OclAny_to_Bank : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Account))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Bank)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Bank : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Current))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Bank)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Client : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(OclAny))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Client)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>B\<^sub>a\<^sub>n\<^sub>k_from_OclAny_to_Client : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Bank))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Client)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_from_OclAny_to_Client : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Savings))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Client)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_from_OclAny_to_Client : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Account))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Client)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny OclValid_def false_def true_def) 
lemma down_cast_type\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Client : 
assumes istyp: "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Current))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Client)) \<triangleq> invalid"
  using istyp isdef
  apply(auto simp: OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny foundation22 foundation16 null_option_def bot_option_def split: ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)
by(simp add: OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny OclValid_def false_def true_def) 

(* 68 ************************************ 912 + 1 *)
section{* OclIsKindOf *}

(* 69 ************************************ 913 + 1 *)
subsection{* Definition *}

(* 70 ************************************ 914 + 6 *)
consts OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Current')")
consts OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Savings')")
consts OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Account')")
consts OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Bank')")
consts OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(Client')")
consts OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(OclAny')")

(* 71 ************************************ 920 + 36 *)
defs(overloaded) OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current : "(x::\<cdot>Current) .oclIsKindOf(Current) \<equiv> (x .oclIsTypeOf(Current))"
defs(overloaded) OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account : "(x::\<cdot>Account) .oclIsKindOf(Current) \<equiv> (x .oclIsTypeOf(Current))"
defs(overloaded) OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny : "(x::\<cdot>OclAny) .oclIsKindOf(Current) \<equiv> (x .oclIsTypeOf(Current))"
defs(overloaded) OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings : "(x::\<cdot>Savings) .oclIsKindOf(Current) \<equiv> (x .oclIsTypeOf(Current))"
defs(overloaded) OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank : "(x::\<cdot>Bank) .oclIsKindOf(Current) \<equiv> (x .oclIsTypeOf(Current))"
defs(overloaded) OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client : "(x::\<cdot>Client) .oclIsKindOf(Current) \<equiv> (x .oclIsTypeOf(Current))"
defs(overloaded) OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings : "(x::\<cdot>Savings) .oclIsKindOf(Savings) \<equiv> (x .oclIsTypeOf(Savings))"
defs(overloaded) OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account : "(x::\<cdot>Account) .oclIsKindOf(Savings) \<equiv> (x .oclIsTypeOf(Savings))"
defs(overloaded) OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny : "(x::\<cdot>OclAny) .oclIsKindOf(Savings) \<equiv> (x .oclIsTypeOf(Savings))"
defs(overloaded) OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current : "(x::\<cdot>Current) .oclIsKindOf(Savings) \<equiv> (x .oclIsTypeOf(Savings))"
defs(overloaded) OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank : "(x::\<cdot>Bank) .oclIsKindOf(Savings) \<equiv> (x .oclIsTypeOf(Savings))"
defs(overloaded) OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client : "(x::\<cdot>Client) .oclIsKindOf(Savings) \<equiv> (x .oclIsTypeOf(Savings))"
defs(overloaded) OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account : "(x::\<cdot>Account) .oclIsKindOf(Account) \<equiv> (x .oclIsTypeOf(Account)) or (x .oclIsKindOf(Savings)) or (x .oclIsKindOf(Current))"
defs(overloaded) OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny : "(x::\<cdot>OclAny) .oclIsKindOf(Account) \<equiv> (x .oclIsTypeOf(Account)) or (x .oclIsKindOf(Savings)) or (x .oclIsKindOf(Current))"
defs(overloaded) OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current : "(x::\<cdot>Current) .oclIsKindOf(Account) \<equiv> (x .oclIsTypeOf(Account)) or (x .oclIsKindOf(Savings)) or (x .oclIsKindOf(Current))"
defs(overloaded) OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings : "(x::\<cdot>Savings) .oclIsKindOf(Account) \<equiv> (x .oclIsTypeOf(Account)) or (x .oclIsKindOf(Savings)) or (x .oclIsKindOf(Current))"
defs(overloaded) OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank : "(x::\<cdot>Bank) .oclIsKindOf(Account) \<equiv> (x .oclIsTypeOf(Account)) or (x .oclIsKindOf(Savings)) or (x .oclIsKindOf(Current))"
defs(overloaded) OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client : "(x::\<cdot>Client) .oclIsKindOf(Account) \<equiv> (x .oclIsTypeOf(Account)) or (x .oclIsKindOf(Savings)) or (x .oclIsKindOf(Current))"
defs(overloaded) OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank : "(x::\<cdot>Bank) .oclIsKindOf(Bank) \<equiv> (x .oclIsTypeOf(Bank))"
defs(overloaded) OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny : "(x::\<cdot>OclAny) .oclIsKindOf(Bank) \<equiv> (x .oclIsTypeOf(Bank))"
defs(overloaded) OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client : "(x::\<cdot>Client) .oclIsKindOf(Bank) \<equiv> (x .oclIsTypeOf(Bank))"
defs(overloaded) OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings : "(x::\<cdot>Savings) .oclIsKindOf(Bank) \<equiv> (x .oclIsTypeOf(Bank))"
defs(overloaded) OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account : "(x::\<cdot>Account) .oclIsKindOf(Bank) \<equiv> (x .oclIsTypeOf(Bank))"
defs(overloaded) OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current : "(x::\<cdot>Current) .oclIsKindOf(Bank) \<equiv> (x .oclIsTypeOf(Bank))"
defs(overloaded) OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client : "(x::\<cdot>Client) .oclIsKindOf(Client) \<equiv> (x .oclIsTypeOf(Client))"
defs(overloaded) OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny : "(x::\<cdot>OclAny) .oclIsKindOf(Client) \<equiv> (x .oclIsTypeOf(Client))"
defs(overloaded) OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank : "(x::\<cdot>Bank) .oclIsKindOf(Client) \<equiv> (x .oclIsTypeOf(Client))"
defs(overloaded) OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings : "(x::\<cdot>Savings) .oclIsKindOf(Client) \<equiv> (x .oclIsTypeOf(Client))"
defs(overloaded) OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account : "(x::\<cdot>Account) .oclIsKindOf(Client) \<equiv> (x .oclIsTypeOf(Client))"
defs(overloaded) OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current : "(x::\<cdot>Current) .oclIsKindOf(Client) \<equiv> (x .oclIsTypeOf(Client))"
defs(overloaded) OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny : "(x::\<cdot>OclAny) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Client)) or (x .oclIsKindOf(Bank)) or (x .oclIsKindOf(Account))"
defs(overloaded) OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current : "(x::\<cdot>Current) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Client)) or (x .oclIsKindOf(Bank)) or (x .oclIsKindOf(Account))"
defs(overloaded) OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings : "(x::\<cdot>Savings) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Client)) or (x .oclIsKindOf(Bank)) or (x .oclIsKindOf(Account))"
defs(overloaded) OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account : "(x::\<cdot>Account) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Client)) or (x .oclIsKindOf(Bank)) or (x .oclIsKindOf(Account))"
defs(overloaded) OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank : "(x::\<cdot>Bank) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Client)) or (x .oclIsKindOf(Bank)) or (x .oclIsKindOf(Account))"
defs(overloaded) OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client : "(x::\<cdot>Client) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny)) or (x .oclIsKindOf(Client)) or (x .oclIsKindOf(Bank)) or (x .oclIsKindOf(Account))"

(* 72 ************************************ 956 + 6 *)
definition "OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_\<AA> = (\<lambda> (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Current))::\<cdot>Current) .oclIsKindOf(Current))
    | (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Account))::\<cdot>Account) .oclIsKindOf(Current))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::\<cdot>OclAny) .oclIsKindOf(Current))
    | (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Savings))::\<cdot>Savings) .oclIsKindOf(Current))
    | (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Bank))::\<cdot>Bank) .oclIsKindOf(Current))
    | (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Client))::\<cdot>Client) .oclIsKindOf(Current)))"
definition "OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_\<AA> = (\<lambda> (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Savings))::\<cdot>Savings) .oclIsKindOf(Savings))
    | (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Account))::\<cdot>Account) .oclIsKindOf(Savings))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::\<cdot>OclAny) .oclIsKindOf(Savings))
    | (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Current))::\<cdot>Current) .oclIsKindOf(Savings))
    | (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Bank))::\<cdot>Bank) .oclIsKindOf(Savings))
    | (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Client))::\<cdot>Client) .oclIsKindOf(Savings)))"
definition "OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<AA> = (\<lambda> (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Account))::\<cdot>Account) .oclIsKindOf(Account))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::\<cdot>OclAny) .oclIsKindOf(Account))
    | (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Current))::\<cdot>Current) .oclIsKindOf(Account))
    | (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Savings))::\<cdot>Savings) .oclIsKindOf(Account))
    | (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Bank))::\<cdot>Bank) .oclIsKindOf(Account))
    | (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Client))::\<cdot>Client) .oclIsKindOf(Account)))"
definition "OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_\<AA> = (\<lambda> (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Bank))::\<cdot>Bank) .oclIsKindOf(Bank))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::\<cdot>OclAny) .oclIsKindOf(Bank))
    | (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Client))::\<cdot>Client) .oclIsKindOf(Bank))
    | (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Savings))::\<cdot>Savings) .oclIsKindOf(Bank))
    | (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Account))::\<cdot>Account) .oclIsKindOf(Bank))
    | (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Current))::\<cdot>Current) .oclIsKindOf(Bank)))"
definition "OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_\<AA> = (\<lambda> (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Client))::\<cdot>Client) .oclIsKindOf(Client))
    | (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::\<cdot>OclAny) .oclIsKindOf(Client))
    | (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Bank))::\<cdot>Bank) .oclIsKindOf(Client))
    | (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Savings))::\<cdot>Savings) .oclIsKindOf(Client))
    | (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Account))::\<cdot>Account) .oclIsKindOf(Client))
    | (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Current))::\<cdot>Current) .oclIsKindOf(Client)))"
definition "OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::\<cdot>OclAny) .oclIsKindOf(OclAny))
    | (in\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (Current)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Current))::\<cdot>Current) .oclIsKindOf(OclAny))
    | (in\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (Savings)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Savings))::\<cdot>Savings) .oclIsKindOf(OclAny))
    | (in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (Account)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Account))::\<cdot>Account) .oclIsKindOf(OclAny))
    | (in\<^sub>B\<^sub>a\<^sub>n\<^sub>k (Bank)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Bank))::\<cdot>Bank) .oclIsKindOf(OclAny))
    | (in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (Client)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (Client))::\<cdot>Client) .oclIsKindOf(OclAny)))"

(* 73 ************************************ 962 + 1 *)
lemmas[simp,code_unfold] = OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current
                            OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings
                            OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account
                            OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank
                            OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client
                            OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny

(* 74 ************************************ 963 + 1 *)
subsection{* Context Passing *}

(* 75 ************************************ 964 + 216 *)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Current) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Current)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Current) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Current)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Current) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Current)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Current) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Current)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Current) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Current)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Current) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Current)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Account) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Account)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Account) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Account)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Account) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Account)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Account) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Account)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Account) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Account)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Account) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Account)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>OclAny) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_OclAny)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>OclAny) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_OclAny)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>OclAny) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>OclAny) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>OclAny) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_OclAny)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Savings) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Savings)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Savings) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Savings)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Savings) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Savings) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Savings)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Savings) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Savings)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Savings) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Savings)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Bank) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Bank)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Bank) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Bank)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Bank) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Bank) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Bank)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Bank) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Bank)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Bank) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Bank)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Client) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Client)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Client) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Client)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Client) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Client)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Client) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Client)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Client) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Client)
lemma cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Client) .oclIsKindOf(Current)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Client)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Savings) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Savings)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Savings) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Savings)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Savings) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Savings)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Savings) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Savings)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Savings) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Savings)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Savings) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Savings)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Account) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Account)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Account) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Account)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Account) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Account)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Account) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Account)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Account) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Account)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Account) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Account)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>OclAny) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_OclAny)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>OclAny) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_OclAny)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>OclAny) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_OclAny)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>OclAny) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_OclAny)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>OclAny) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_OclAny)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Current) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Current)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Current) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Current)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Current) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Current)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Current) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Current)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Current) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Current)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Current) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Current)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Bank) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Bank)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Bank) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Bank)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Bank) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Bank)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Bank) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Bank)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Bank) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Bank)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Bank) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Bank)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Client) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Client)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Client) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Client)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Client) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Client)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Client) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Client)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Client) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Client)
lemma cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Client) .oclIsKindOf(Savings)))))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client, simp only: cp_OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Client)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Account) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Account)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Account, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Account)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Account) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Account)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Account, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Account)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Account) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Account)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Account, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Account)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Account) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Account)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Account, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Account)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Account) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Account)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Account, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Account)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Account) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Account)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Account, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Account)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>OclAny) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_OclAny, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_OclAny)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_OclAny, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>OclAny) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_OclAny, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_OclAny)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>OclAny) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_OclAny, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>OclAny) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_OclAny, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>OclAny) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_OclAny, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_OclAny)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Current) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Current)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Current, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Current)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Current) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Current)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Current, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Current)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Current) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Current)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Current, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Current)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Current) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Current)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Current, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Current)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Current) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Current)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Current, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Current)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Current) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Current)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Current, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Current)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Savings) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Savings)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Savings, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Savings)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Savings) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Savings)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Savings, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Savings) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Savings)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Savings, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Savings)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Savings) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Savings)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Savings, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Savings)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Savings) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Savings)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Savings, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Savings)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Savings) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Savings)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Savings, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Savings)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Bank) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Bank)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Bank, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Bank)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Bank) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Bank)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Bank, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Bank) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Bank)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Bank, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Bank)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Bank) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Bank)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Bank, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Bank)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Bank) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Bank)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Bank, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Bank)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Bank) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Bank)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Bank, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Bank)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Client) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Client)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_Client, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_Client)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Client) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Client)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_Client, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_Client)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Client) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Client)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_Client, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_Client)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Client) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Client)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_Client, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_Client)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Client) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Client)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_Client, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_Client)
lemma cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Client) .oclIsKindOf(Account)))))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Client)
by(simp only: cp_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_Client, simp only: cp_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_Client)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Bank) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Bank)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Bank) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Bank)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Bank) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Bank)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Bank) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Bank)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Bank) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Bank)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Bank) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Bank)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>OclAny) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_OclAny)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>OclAny) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_OclAny)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>OclAny) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_OclAny)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>OclAny) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_OclAny)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>OclAny) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_OclAny)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Client) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Client)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Client) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Client)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Client) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Client)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Client) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Client)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Client) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Client)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Client) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Client)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Savings) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Savings)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Savings) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Savings)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Savings) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Savings)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Savings) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Savings)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Savings) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Savings)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Savings) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Savings)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Account) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Account)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Account) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Account)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Account) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Account)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Account) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Account)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Account) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Account)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Account) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Account)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Current) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Current)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Current) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Current)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Current) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Current)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Current) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Current)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Current) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Current)
lemma cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Current) .oclIsKindOf(Bank)))))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current, simp only: cp_OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Current)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Client) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Client)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Client) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Client)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Client) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Client)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Client) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Client)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Client) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Client)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Client) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Client)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>OclAny) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_OclAny)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>OclAny) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>OclAny) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>OclAny) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_OclAny)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>OclAny) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_OclAny)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Bank) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Bank)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Bank) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Bank) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Bank)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Bank) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Bank)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Bank) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Bank)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Bank) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Bank)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Savings) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Savings)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Savings) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Savings) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Savings)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Savings) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Savings)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Savings) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Savings)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Savings) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Savings)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Account) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Account)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Account) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Account)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Account) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Account)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Account) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Account)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Account) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Account)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Account) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Account)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Current) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Current)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Current) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Current)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Current) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Current)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Current) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Current)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Current) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Current)
lemma cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Current) .oclIsKindOf(Client)))))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current, simp only: cp_OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Current)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_OclAny, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_OclAny, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_OclAny, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_OclAny, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_OclAny, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_OclAny, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_OclAny, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_OclAny, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_OclAny, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_OclAny, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>OclAny) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_OclAny)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_OclAny, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_OclAny, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Current) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Current)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Current, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Current, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Current)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Current) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Current)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Current, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Current, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Current)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Current) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Current)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Current, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Current, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Current)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Current) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Current)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Current, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Current, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Current)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Current) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Current)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Current, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Current, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Current)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Current : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Current) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Current)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Current, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Current, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Current)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Savings) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Savings)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Savings, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Savings, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Savings)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Savings) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Savings)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Savings, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Savings, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Savings)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Savings) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Savings)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Savings, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Savings, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Savings)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Savings) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Savings)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Savings, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Savings, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Savings)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Savings) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Savings)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Savings, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Savings, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Savings)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Savings : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Savings) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Savings)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Savings, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Savings, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Savings)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Account) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Account)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Account, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Account, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Account)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Account) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Account)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Account, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Account, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Account)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Account) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Account)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Account, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Account, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Account)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Account) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Account)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Account, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Account, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Account)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Account) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Account)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Account, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Account, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Account)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Account : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Account) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Account)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Account, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Account, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Account)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Bank) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Bank)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Bank, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Bank, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Bank)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Bank) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Bank)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Bank, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Bank, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Bank)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Bank) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Bank)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Bank, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Bank, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Bank)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Bank) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Bank)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Bank, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Bank, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Bank)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Bank) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Bank)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Bank, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Bank, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Bank)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Bank : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Bank) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Bank)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Bank, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Bank, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Bank)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>Client) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Client)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_Client, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_Client, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_Client)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Current)))::\<cdot>Client) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_Client)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_Client, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_Client, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_Client)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Savings)))::\<cdot>Client) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_Client)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_Client, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_Client, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_Client)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Account)))::\<cdot>Client) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_Client)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_Client, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_Client, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_Client)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Bank)))::\<cdot>Client) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_Client)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_Client, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_Client, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_Client)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Client : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>Client)))::\<cdot>Client) .oclIsKindOf(OclAny)))))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
  apply((rule cpI2[where f = "op or"], (rule allI)+, rule cp_OclOr)+)
  apply(simp only: cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_Client)
by(simp only: cp_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_Client, simp only: cp_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_Client, simp only: cp_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_Client)

(* 76 ************************************ 1180 + 1 *)
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

(* 77 ************************************ 1181 + 1 *)
subsection{* Execution with Invalid or Null as Argument *}

(* 78 ************************************ 1182 + 72 *)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_invalid : "((invalid::\<cdot>Current) .oclIsKindOf(Current)) = invalid"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_invalid)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_null : "((null::\<cdot>Current) .oclIsKindOf(Current)) = true"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_null)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_invalid : "((invalid::\<cdot>Account) .oclIsKindOf(Current)) = invalid"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_invalid)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_null : "((null::\<cdot>Account) .oclIsKindOf(Current)) = true"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_null)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclIsKindOf(Current)) = invalid"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_null : "((null::\<cdot>OclAny) .oclIsKindOf(Current)) = true"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_null)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_invalid : "((invalid::\<cdot>Savings) .oclIsKindOf(Current)) = invalid"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_invalid)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_null : "((null::\<cdot>Savings) .oclIsKindOf(Current)) = true"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_null)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_invalid : "((invalid::\<cdot>Bank) .oclIsKindOf(Current)) = invalid"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_invalid)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_null : "((null::\<cdot>Bank) .oclIsKindOf(Current)) = true"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_null)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_invalid : "((invalid::\<cdot>Client) .oclIsKindOf(Current)) = invalid"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_invalid)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_null : "((null::\<cdot>Client) .oclIsKindOf(Current)) = true"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_null)
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_invalid : "((invalid::\<cdot>Savings) .oclIsKindOf(Savings)) = invalid"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_invalid)
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_null : "((null::\<cdot>Savings) .oclIsKindOf(Savings)) = true"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_null)
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_invalid : "((invalid::\<cdot>Account) .oclIsKindOf(Savings)) = invalid"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_invalid)
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_null : "((null::\<cdot>Account) .oclIsKindOf(Savings)) = true"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_null)
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclIsKindOf(Savings)) = invalid"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_invalid)
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_null : "((null::\<cdot>OclAny) .oclIsKindOf(Savings)) = true"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_null)
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_invalid : "((invalid::\<cdot>Current) .oclIsKindOf(Savings)) = invalid"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_invalid)
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_null : "((null::\<cdot>Current) .oclIsKindOf(Savings)) = true"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_null)
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_invalid : "((invalid::\<cdot>Bank) .oclIsKindOf(Savings)) = invalid"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_invalid)
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_null : "((null::\<cdot>Bank) .oclIsKindOf(Savings)) = true"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_null)
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_invalid : "((invalid::\<cdot>Client) .oclIsKindOf(Savings)) = invalid"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_invalid)
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_null : "((null::\<cdot>Client) .oclIsKindOf(Savings)) = true"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_null)
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_invalid : "((invalid::\<cdot>Account) .oclIsKindOf(Account)) = invalid"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_invalid OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_invalid OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_invalid, simp)
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_null : "((null::\<cdot>Account) .oclIsKindOf(Account)) = true"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_null OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_null OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_null, simp)
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclIsKindOf(Account)) = invalid"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_invalid OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_invalid OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid, simp)
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_null : "((null::\<cdot>OclAny) .oclIsKindOf(Account)) = true"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_null OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_null OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_null, simp)
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_invalid : "((invalid::\<cdot>Current) .oclIsKindOf(Account)) = invalid"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_invalid OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_invalid OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_invalid, simp)
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_null : "((null::\<cdot>Current) .oclIsKindOf(Account)) = true"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_null OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_null OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_null, simp)
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_invalid : "((invalid::\<cdot>Savings) .oclIsKindOf(Account)) = invalid"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_invalid OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_invalid OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_invalid, simp)
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_null : "((null::\<cdot>Savings) .oclIsKindOf(Account)) = true"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_null OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_null OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_null, simp)
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_invalid : "((invalid::\<cdot>Bank) .oclIsKindOf(Account)) = invalid"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_invalid OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_invalid OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_invalid, simp)
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_null : "((null::\<cdot>Bank) .oclIsKindOf(Account)) = true"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_null OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_null OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_null, simp)
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_invalid : "((invalid::\<cdot>Client) .oclIsKindOf(Account)) = invalid"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_invalid OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_invalid OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_invalid, simp)
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_null : "((null::\<cdot>Client) .oclIsKindOf(Account)) = true"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_null OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_null OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_null, simp)
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_invalid : "((invalid::\<cdot>Bank) .oclIsKindOf(Bank)) = invalid"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_invalid)
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_null : "((null::\<cdot>Bank) .oclIsKindOf(Bank)) = true"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_null)
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclIsKindOf(Bank)) = invalid"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_invalid)
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_null : "((null::\<cdot>OclAny) .oclIsKindOf(Bank)) = true"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_null)
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_invalid : "((invalid::\<cdot>Client) .oclIsKindOf(Bank)) = invalid"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_invalid)
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_null : "((null::\<cdot>Client) .oclIsKindOf(Bank)) = true"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_null)
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_invalid : "((invalid::\<cdot>Savings) .oclIsKindOf(Bank)) = invalid"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_invalid)
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_null : "((null::\<cdot>Savings) .oclIsKindOf(Bank)) = true"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_null)
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_invalid : "((invalid::\<cdot>Account) .oclIsKindOf(Bank)) = invalid"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_invalid)
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_null : "((null::\<cdot>Account) .oclIsKindOf(Bank)) = true"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_null)
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_invalid : "((invalid::\<cdot>Current) .oclIsKindOf(Bank)) = invalid"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_invalid)
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_null : "((null::\<cdot>Current) .oclIsKindOf(Bank)) = true"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_null)
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_invalid : "((invalid::\<cdot>Client) .oclIsKindOf(Client)) = invalid"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_invalid)
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_null : "((null::\<cdot>Client) .oclIsKindOf(Client)) = true"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_null)
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclIsKindOf(Client)) = invalid"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid)
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_null : "((null::\<cdot>OclAny) .oclIsKindOf(Client)) = true"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_null)
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_invalid : "((invalid::\<cdot>Bank) .oclIsKindOf(Client)) = invalid"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_invalid)
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_null : "((null::\<cdot>Bank) .oclIsKindOf(Client)) = true"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_null)
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_invalid : "((invalid::\<cdot>Savings) .oclIsKindOf(Client)) = invalid"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_invalid)
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_null : "((null::\<cdot>Savings) .oclIsKindOf(Client)) = true"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_null)
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_invalid : "((invalid::\<cdot>Account) .oclIsKindOf(Client)) = invalid"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_invalid)
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_null : "((null::\<cdot>Account) .oclIsKindOf(Client)) = true"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_null)
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_invalid : "((invalid::\<cdot>Current) .oclIsKindOf(Client)) = invalid"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_invalid)
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_null : "((null::\<cdot>Current) .oclIsKindOf(Client)) = true"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_null)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_invalid OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_invalid OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null : "((null::\<cdot>OclAny) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_null OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_null OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_invalid : "((invalid::\<cdot>Current) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_invalid OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_invalid OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_invalid OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_null : "((null::\<cdot>Current) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_null OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_null OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_null OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_invalid : "((invalid::\<cdot>Savings) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_invalid OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_invalid OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_invalid OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_null : "((null::\<cdot>Savings) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_null OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_null OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_null OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_invalid : "((invalid::\<cdot>Account) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_invalid OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_invalid OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_invalid OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_null : "((null::\<cdot>Account) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_null OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_null OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_null OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_invalid : "((invalid::\<cdot>Bank) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_invalid OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_invalid OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_invalid OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_null : "((null::\<cdot>Bank) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_null OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_null OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_null OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_null, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_invalid : "((invalid::\<cdot>Client) .oclIsKindOf(OclAny)) = invalid"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_invalid OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_invalid OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_invalid OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_invalid, simp)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_null : "((null::\<cdot>Client) .oclIsKindOf(OclAny)) = true"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_null OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_null OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_null OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_null, simp)

(* 79 ************************************ 1254 + 1 *)
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

(* 80 ************************************ 1255 + 1 *)
subsection{* Validity and Definedness Properties *}

(* 81 ************************************ 1256 + 36 *)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclIsKindOf(Current)))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current, rule OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .oclIsKindOf(Current)))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account, rule OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsKindOf(Current)))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny, rule OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclIsKindOf(Current)))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings, rule OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .oclIsKindOf(Current)))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank, rule OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .oclIsKindOf(Current)))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client, rule OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclIsKindOf(Savings)))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings, rule OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .oclIsKindOf(Savings)))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account, rule OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsKindOf(Savings)))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny, rule OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclIsKindOf(Savings)))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current, rule OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .oclIsKindOf(Savings)))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank, rule OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .oclIsKindOf(Savings)))"
by(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client, rule OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .oclIsKindOf(Account)))"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account, rule defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_defined[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_defined[OF isdef]], OF OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsKindOf(Account)))"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny, rule defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_defined[OF isdef]], OF OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclIsKindOf(Account)))"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current, rule defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_defined[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_defined[OF isdef]], OF OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclIsKindOf(Account)))"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings, rule defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_defined[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_defined[OF isdef]], OF OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .oclIsKindOf(Account)))"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank, rule defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_defined[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_defined[OF isdef]], OF OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .oclIsKindOf(Account)))"
by(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client, rule defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_defined[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_defined[OF isdef]], OF OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .oclIsKindOf(Bank)))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank, rule OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsKindOf(Bank)))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny, rule OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .oclIsKindOf(Bank)))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client, rule OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclIsKindOf(Bank)))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings, rule OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .oclIsKindOf(Bank)))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account, rule OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclIsKindOf(Bank)))"
by(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current, rule OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .oclIsKindOf(Client)))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client, rule OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsKindOf(Client)))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny, rule OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .oclIsKindOf(Client)))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank, rule OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclIsKindOf(Client)))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings, rule OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .oclIsKindOf(Client)))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account, rule OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclIsKindOf(Client)))"
by(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current, rule OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_defined[OF isdef]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsKindOf(OclAny)))"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny, rule defined_or_I[OF defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined[OF isdef]], OF OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined[OF isdef]], OF OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclIsKindOf(OclAny)))"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current, rule defined_or_I[OF defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_defined[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_defined[OF isdef]], OF OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_defined[OF isdef]], OF OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclIsKindOf(OclAny)))"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings, rule defined_or_I[OF defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_defined[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_defined[OF isdef]], OF OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_defined[OF isdef]], OF OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .oclIsKindOf(OclAny)))"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account, rule defined_or_I[OF defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_defined[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_defined[OF isdef]], OF OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_defined[OF isdef]], OF OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .oclIsKindOf(OclAny)))"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank, rule defined_or_I[OF defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_defined[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_defined[OF isdef]], OF OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_defined[OF isdef]], OF OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_defined[OF isdef]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_defined : 
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .oclIsKindOf(OclAny)))"
by(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client, rule defined_or_I[OF defined_or_I[OF defined_or_I[OF OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_defined[OF isdef], OF OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_defined[OF isdef]], OF OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_defined[OF isdef]], OF OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_defined[OF isdef]]) 

(* 82 ************************************ 1292 + 36 *)
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclIsKindOf(Current)))"
by(rule OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .oclIsKindOf(Current)))"
by(rule OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsKindOf(Current)))"
by(rule OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclIsKindOf(Current)))"
by(rule OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Savings_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .oclIsKindOf(Current)))"
by(rule OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Bank_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .oclIsKindOf(Current)))"
by(rule OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Client_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclIsKindOf(Savings)))"
by(rule OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .oclIsKindOf(Savings)))"
by(rule OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsKindOf(Savings)))"
by(rule OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclIsKindOf(Savings)))"
by(rule OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Current_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .oclIsKindOf(Savings)))"
by(rule OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Bank_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .oclIsKindOf(Savings)))"
by(rule OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Client_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .oclIsKindOf(Account)))"
by(rule OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsKindOf(Account)))"
by(rule OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclIsKindOf(Account)))"
by(rule OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclIsKindOf(Account)))"
by(rule OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .oclIsKindOf(Account)))"
by(rule OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Bank_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .oclIsKindOf(Account)))"
by(rule OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Client_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .oclIsKindOf(Bank)))"
by(rule OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsKindOf(Bank)))"
by(rule OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .oclIsKindOf(Bank)))"
by(rule OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Client_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclIsKindOf(Bank)))"
by(rule OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Savings_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .oclIsKindOf(Bank)))"
by(rule OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Account_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclIsKindOf(Bank)))"
by(rule OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Current_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .oclIsKindOf(Client)))"
by(rule OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsKindOf(Client)))"
by(rule OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .oclIsKindOf(Client)))"
by(rule OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Bank_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclIsKindOf(Client)))"
by(rule OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Savings_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .oclIsKindOf(Client)))"
by(rule OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Account_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclIsKindOf(Client)))"
by(rule OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Current_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsKindOf(OclAny)))"
by(rule OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .oclIsKindOf(OclAny)))"
by(rule OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .oclIsKindOf(OclAny)))"
by(rule OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .oclIsKindOf(OclAny)))"
by(rule OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .oclIsKindOf(OclAny)))"
by(rule OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank_defined[OF isdef[THEN foundation20]]) 
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_defined' : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .oclIsKindOf(OclAny)))"
by(rule OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client_defined[OF isdef[THEN foundation20]]) 

(* 83 ************************************ 1328 + 1 *)
subsection{* Up Down Casting *}

(* 84 ************************************ 1329 + 6 *)
lemma actual_eq_static\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Current) .oclIsKindOf(Current))"
  apply(simp only: OclValid_def, insert isdef)
  apply(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Current)
  apply(auto simp: foundation16 bot_option_def split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split)
by((simp_all add: false_def true_def OclOr_def OclAnd_def OclNot_def)?) 
lemma actual_eq_static\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Savings) .oclIsKindOf(Savings))"
  apply(simp only: OclValid_def, insert isdef)
  apply(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Savings)
  apply(auto simp: foundation16 bot_option_def split: option.split ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split)
by((simp_all add: false_def true_def OclOr_def OclAnd_def OclNot_def)?) 
lemma actual_eq_static\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Account) .oclIsKindOf(Account))"
  apply(simp only: OclValid_def, insert isdef)
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account, subst (1) cp_OclOr, subst (2 1) cp_OclOr, simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account, simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
  apply(auto simp: cp_OclOr[symmetric ] foundation16 bot_option_def OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account split: option.split ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split)
by((simp_all add: false_def true_def OclOr_def OclAnd_def OclNot_def)?) 
lemma actual_eq_static\<^sub>B\<^sub>a\<^sub>n\<^sub>k : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Bank) .oclIsKindOf(Bank))"
  apply(simp only: OclValid_def, insert isdef)
  apply(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_Bank)
  apply(auto simp: foundation16 bot_option_def split: option.split ty\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split)
by((simp_all add: false_def true_def OclOr_def OclAnd_def OclNot_def)?) 
lemma actual_eq_static\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Client) .oclIsKindOf(Client))"
  apply(simp only: OclValid_def, insert isdef)
  apply(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_Client)
  apply(auto simp: foundation16 bot_option_def split: option.split ty\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split)
by((simp_all add: false_def true_def OclOr_def OclAnd_def OclNot_def)?) 
lemma actual_eq_static\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(OclAny))"
  apply(simp only: OclValid_def, insert isdef)
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny, subst (1) cp_OclOr, subst (2 1) cp_OclOr, subst (3 2 1) cp_OclOr, simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny, simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny, simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny, subst (4 3 2 1) cp_OclOr, subst (5 4 3 2 1) cp_OclOr, simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny, simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
  apply(auto simp: cp_OclOr[symmetric ] foundation16 bot_option_def OclIsTypeOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny OclIsTypeOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_OclAny OclIsTypeOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny OclIsTypeOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny split: option.split ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split ty\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t.split ty\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split ty\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s.split ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t.split ty\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split ty\<^sub>B\<^sub>a\<^sub>n\<^sub>k.split ty\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t.split)
by((simp_all add: false_def true_def OclOr_def OclAnd_def OclNot_def)?) 

(* 85 ************************************ 1335 + 7 *)
lemma actualKind\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_larger_staticKind\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Current) .oclIsKindOf(Account))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Current)
by(rule foundation25', rule actual_eq_static\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t[OF isdef]) 
lemma actualKind\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Current) .oclIsKindOf(OclAny))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Current)
by(rule foundation25', rule actualKind\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_larger_staticKind\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t[OF isdef]) 
lemma actualKind\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_larger_staticKind\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Savings) .oclIsKindOf(Account))"
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Savings)
by(rule foundation25, rule foundation25', rule actual_eq_static\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s[OF isdef]) 
lemma actualKind\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Savings) .oclIsKindOf(OclAny))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Savings)
by(rule foundation25', rule actualKind\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_larger_staticKind\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t[OF isdef]) 
lemma actualKind\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Account) .oclIsKindOf(OclAny))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Account)
by(rule foundation25', rule actual_eq_static\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t[OF isdef]) 
lemma actualKind\<^sub>B\<^sub>a\<^sub>n\<^sub>k_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Bank) .oclIsKindOf(OclAny))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Bank)
by(rule foundation25, rule foundation25', rule actual_eq_static\<^sub>B\<^sub>a\<^sub>n\<^sub>k[OF isdef]) 
lemma actualKind\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_larger_staticKind\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : 
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>Client) .oclIsKindOf(OclAny))"
  apply(simp only: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Client)
by(rule foundation25, rule foundation25, rule foundation25', rule actual_eq_static\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t[OF isdef]) 

(* 86 ************************************ 1342 + 7 *)
lemma not_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_then_Account_OclIsTypeOf_others_unfold : 
assumes isdef: "(\<tau> \<Turnstile> (\<delta> (X)))"
assumes iskin: "(\<tau> \<Turnstile> ((X::\<cdot>Account) .oclIsKindOf(Current)))"
shows "(\<tau> \<Turnstile> ((X::\<cdot>Account) .oclIsTypeOf(Current)))"
  using iskin
  apply(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account)
done 
lemma not_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others_unfold : 
assumes isdef: "(\<tau> \<Turnstile> (\<delta> (X)))"
assumes iskin: "(\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Current)))"
shows "(\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Current)))"
  using iskin
  apply(simp only: OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_OclAny)
done 
lemma not_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_then_Account_OclIsTypeOf_others_unfold : 
assumes isdef: "(\<tau> \<Turnstile> (\<delta> (X)))"
assumes iskin: "(\<tau> \<Turnstile> ((X::\<cdot>Account) .oclIsKindOf(Savings)))"
shows "(\<tau> \<Turnstile> ((X::\<cdot>Account) .oclIsTypeOf(Savings)))"
  using iskin
  apply(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account)
done 
lemma not_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_then_OclAny_OclIsTypeOf_others_unfold : 
assumes isdef: "(\<tau> \<Turnstile> (\<delta> (X)))"
assumes iskin: "(\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Savings)))"
shows "(\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Savings)))"
  using iskin
  apply(simp only: OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_OclAny)
done 
lemma not_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others_unfold : 
assumes isdef: "(\<tau> \<Turnstile> (\<delta> (X)))"
assumes iskin: "(\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Account)))"
shows "((\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Account))) \<or> ((\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Current))) \<or> (\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Savings)))))"
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
assumes iskin: "(\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Bank)))"
shows "(\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Bank)))"
  using iskin
  apply(simp only: OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_OclAny)
done 
lemma not_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others_unfold : 
assumes isdef: "(\<tau> \<Turnstile> (\<delta> (X)))"
assumes iskin: "(\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Client)))"
shows "(\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Client)))"
  using iskin
  apply(simp only: OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_OclAny)
done 

(* 87 ************************************ 1349 + 7 *)
lemma not_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_then_Account_OclIsTypeOf_others : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>Account) .oclIsKindOf(Current))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "(\<tau> \<Turnstile> ((X::\<cdot>Account) .oclIsTypeOf(Account)) \<or> \<tau> \<Turnstile> ((X::\<cdot>Account) .oclIsKindOf(Savings)))"
  using actual_eq_static\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account)
  apply(erule foundation26[OF defined_or_I[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_defined'[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_defined'[OF isdef]], OF OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_defined'[OF isdef]])
  apply(erule foundation26[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_defined'[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_defined'[OF isdef]])
  apply(simp)
  apply(simp)
  apply(simp add: iskin)
done 
lemma not_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Current))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "(\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(OclAny)) \<or> (\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Account)) \<or> (\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Bank)) \<or> (\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Client)) \<or> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Savings))))))"
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
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>Account) .oclIsKindOf(Savings))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "(\<tau> \<Turnstile> ((X::\<cdot>Account) .oclIsTypeOf(Account)) \<or> \<tau> \<Turnstile> ((X::\<cdot>Account) .oclIsKindOf(Current)))"
  using actual_eq_static\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t[OF isdef]
  apply(simp only: OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account)
  apply(erule foundation26[OF defined_or_I[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_defined'[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_defined'[OF isdef]], OF OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_Account_defined'[OF isdef]])
  apply(erule foundation26[OF OclIsTypeOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_Account_defined'[OF isdef], OF OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_Account_defined'[OF isdef]])
  apply(simp)
  apply(simp add: iskin)
  apply(simp)
done 
lemma not_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_then_OclAny_OclIsTypeOf_others : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Savings))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "(\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(OclAny)) \<or> (\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(Account)) \<or> (\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Bank)) \<or> (\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Client)) \<or> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Current))))))"
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
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Account))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "(\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(OclAny)) \<or> (\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Bank)) \<or> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Client))))"
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
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Bank))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "(\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(OclAny)) \<or> (\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Client)) \<or> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Account))))"
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
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Client))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "(\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsTypeOf(OclAny)) \<or> (\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Bank)) \<or> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Account))))"
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

(* 88 ************************************ 1356 + 9 *)
lemma down_cast_kind\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_from_Account_to_Current : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>Account) .oclIsKindOf(Current))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Current)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_then_Account_OclIsTypeOf_others[OF iskin, OF isdef], elim disjE)
  apply(rule down_cast_type\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_from_Account_to_Current, simp only: , simp only: isdef)
  apply(drule not_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_then_Account_OclIsTypeOf_others_unfold[OF isdef])
  apply(rule down_cast_type\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_from_Account_to_Current, simp only: , simp only: isdef)
done 
lemma down_cast_kind\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Current : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Current))"
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
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>Account) .oclIsKindOf(Savings))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Savings)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_then_Account_OclIsTypeOf_others[OF iskin, OF isdef], elim disjE)
  apply(rule down_cast_type\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_from_Account_to_Savings, simp only: , simp only: isdef)
  apply(drule not_OclIsKindOf\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_then_Account_OclIsTypeOf_others_unfold[OF isdef])
  apply(rule down_cast_type\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_from_Account_to_Savings, simp only: , simp only: isdef)
done 
lemma down_cast_kind\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_from_OclAny_to_Savings : 
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Savings))"
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
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Account))"
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
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Account))"
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
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Account))"
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
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Bank))"
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
assumes iskin: "\<not> \<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(Client))"
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (X .oclAsType(Client)) \<triangleq> invalid"
  apply(insert not_OclIsKindOf\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others[OF iskin, OF isdef], elim disjE)
  apply(rule down_cast_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_from_OclAny_to_Client, simp only: , simp only: isdef)
  apply(drule not_OclIsKindOf\<^sub>B\<^sub>a\<^sub>n\<^sub>k_then_OclAny_OclIsTypeOf_others_unfold[OF isdef])
  apply(rule down_cast_type\<^sub>B\<^sub>a\<^sub>n\<^sub>k_from_OclAny_to_Client, simp only: , simp only: isdef)
  apply(drule not_OclIsKindOf\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_then_OclAny_OclIsTypeOf_others_unfold[OF isdef])
  apply(auto simp: isdef down_cast_type\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_from_OclAny_to_Client down_cast_type\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_from_OclAny_to_Client down_cast_type\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_from_OclAny_to_Client)
done 

(* 89 ************************************ 1365 + 1 *)
section{* OclAllInstances *}

(* 90 ************************************ 1366 + 1 *)
text{* 
   To denote OCL-types occuring in OCL expressions syntactically---as, for example,  as
``argument'' of \inlineisar{oclAllInstances()}---we use the inverses of the injection
functions into the object universes; we show that this is sufficient ``characterization.''  *}

(* 91 ************************************ 1367 + 6 *)
definition "Current = OclAsType\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_\<AA>"
definition "Savings = OclAsType\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_\<AA>"
definition "Account = OclAsType\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<AA>"
definition "Bank = OclAsType\<^sub>B\<^sub>a\<^sub>n\<^sub>k_\<AA>"
definition "Client = OclAsType\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_\<AA>"
definition "OclAny = OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>"

(* 92 ************************************ 1373 + 1 *)
lemmas[simp,code_unfold] = Current_def
                            Savings_def
                            Account_def
                            Bank_def
                            Client_def
                            OclAny_def

(* 93 ************************************ 1374 + 1 *)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_some : "(OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> (x)) \<noteq> None"
by(simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def)

(* 94 ************************************ 1375 + 3 *)
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

(* 95 ************************************ 1378 + 1 *)
subsection{* OclIsTypeOf *}

(* 96 ************************************ 1379 + 2 *)
lemma ex_ssubst : "(\<forall>x \<in> B. (s (x)) = (t (x))) \<Longrightarrow> (\<exists>x \<in> B. (P ((s (x))))) = (\<exists>x \<in> B. (P ((t (x)))))"
by(simp)
lemma ex_def : "x \<in> \<lceil>\<lceil>\<lfloor>\<lfloor>Some ` (X - {None})\<rfloor>\<rfloor>\<rceil>\<rceil> \<Longrightarrow> (\<exists>y. x = \<lfloor>\<lfloor>y\<rfloor>\<rfloor>)"
by(auto)

(* 97 ************************************ 1381 + 24 *)
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

(* 98 ************************************ 1405 + 1 *)
subsection{* OclIsKindOf *}

(* 99 ************************************ 1406 + 18 *)
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

(* 100 ************************************ 1424 + 21 *)
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

(* 101 ************************************ 1445 + 1 *)
section{* The Accessors *}

(* 102 ************************************ 1446 + 1 *)
text{*  *}

(* 103 ************************************ 1447 + 1 *)
text{* 
  \label{sec:eam-accessors} *}

(* 104 ************************************ 1448 + 1 *)
subsection{* Definition *}

(* 105 ************************************ 1449 + 1 *)
text{* 
   We start with a oid for the association; this oid can be used
in presence of association classes to represent the association inside an object,
pretty much similar to the \inlineisar+Employee_DesignModel_UMLPart+, where we stored
an \verb+oid+ inside the class as ``pointer.''  *}

(* 106 ************************************ 1450 + 10 *)
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

(* 107 ************************************ 1460 + 10 *)
definition "oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k> = 2"
definition "oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r> = 0"
definition "oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k> = 2"
definition "oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r> = 0"
definition "oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k> = 2"
definition "oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r> = 0"
definition "oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s> = 2"
definition "oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s> = 1"
definition "oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s> = 0"
definition "oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<b>\<a>\<n>\<k>\<s> = 1"

(* 108 ************************************ 1470 + 1 *)
text{* 
   From there on, we can already define an empty state which must contain
for $\mathit{oid}_{Person}\mathcal{BOSS}$ the empty relation (encoded as association list, since there are
associations with a Sequence-like structure). *}

(* 109 ************************************ 1471 + 5 *)
definition "eval_extract x f = (\<lambda>\<tau>. (case x \<tau> of \<lfloor>\<lfloor>obj\<rfloor>\<rfloor> \<Rightarrow> (f ((oid_of (obj))) (\<tau>))
    | _ \<Rightarrow> invalid \<tau>))"
definition "in_pre_state = fst"
definition "in_post_state = snd"
definition "reconst_basetype = (\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)"
definition "reconst_basetype\<^sub>V\<^sub>o\<^sub>i\<^sub>d x = Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e o (reconst_basetype (x))"

(* 110 ************************************ 1476 + 1 *)
text{* 
   The @{text pre_post}-parameter is configured with @{text fst} or
@{text snd}, the @{text to_from}-parameter either with the identity @{term id} or
the following combinator @{text switch}:  *}

(* 111 ************************************ 1477 + 2 *)
ML{* val switch2_01 = (fn [x0 , x1] => (x0 , x1)) *}
ML{* val switch2_10 = (fn [x0 , x1] => (x1 , x0)) *}

(* 112 ************************************ 1479 + 3 *)
definition "switch\<^sub>2_01 = (\<lambda> [x0 , x1] \<Rightarrow> (x0 , x1))"
definition "switch\<^sub>2_10 = (\<lambda> [x0 , x1] \<Rightarrow> (x1 , x0))"
definition "deref_assocs pre_post to_from assoc_oid f oid = (\<lambda>\<tau>. (case (assocs ((pre_post (\<tau>))) (assoc_oid)) of \<lfloor>S\<rfloor> \<Rightarrow> (f ((deref_assocs_list (to_from) (oid) (S))) (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"

(* 113 ************************************ 1482 + 6 *)
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

(* 114 ************************************ 1488 + 10 *)
definition "deref_assocs\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k> fst_snd f = (deref_assocs (fst_snd) (switch\<^sub>2_01) (oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>) (f)) \<circ> oid_of"
definition "deref_assocs\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r> fst_snd f = (deref_assocs (fst_snd) (switch\<^sub>2_01) (oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>) (f)) \<circ> oid_of"
definition "deref_assocs\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k> fst_snd f = (deref_assocs (fst_snd) (switch\<^sub>2_01) (oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k>) (f)) \<circ> oid_of"
definition "deref_assocs\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r> fst_snd f = (deref_assocs (fst_snd) (switch\<^sub>2_01) (oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r>) (f)) \<circ> oid_of"
definition "deref_assocs\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k> fst_snd f = (deref_assocs (fst_snd) (switch\<^sub>2_01) (oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>) (f)) \<circ> oid_of"
definition "deref_assocs\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r> fst_snd f = (deref_assocs (fst_snd) (switch\<^sub>2_01) (oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>) (f)) \<circ> oid_of"
definition "deref_assocs\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s> fst_snd f = (deref_assocs (fst_snd) (switch\<^sub>2_10) (oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>) (f)) \<circ> oid_of"
definition "deref_assocs\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s> fst_snd f = (deref_assocs (fst_snd) (switch\<^sub>2_01) (oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s>) (f)) \<circ> oid_of"
definition "deref_assocs\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s> fst_snd f = (deref_assocs (fst_snd) (switch\<^sub>2_10) (oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>) (f)) \<circ> oid_of"
definition "deref_assocs\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<b>\<a>\<n>\<k>\<s> fst_snd f = (deref_assocs (fst_snd) (switch\<^sub>2_10) (oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<b>\<a>\<n>\<k>\<s>) (f)) \<circ> oid_of"

(* 115 ************************************ 1498 + 1 *)
text{* 
   pointer undefined in state or not referencing a type conform object representation  *}

(* 116 ************************************ 1499 + 12 *)
definition "select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t> f = (\<lambda> (mk\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (_) (\<bottom>)) \<Rightarrow> null
    | (mk\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (_) (\<lfloor>x_\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t>\<rfloor>)) \<Rightarrow> (f (x_\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t>)))"
definition "select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<m>\<a>\<x> f = (\<lambda> (mk\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (_) (\<bottom>)) \<Rightarrow> null
    | (mk\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (_) (\<lfloor>x_\<m>\<a>\<x>\<rfloor>)) \<Rightarrow> (f (x_\<m>\<a>\<x>)))"
definition "select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<i>\<d> f = (\<lambda> (mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (_) (\<bottom>) (_)) \<Rightarrow> null
    | (mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (_) (\<lfloor>x_\<i>\<d>\<rfloor>) (_)) \<Rightarrow> (f (x_\<i>\<d>)))"
definition "select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e> f = (\<lambda> (mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (_) (_) (\<bottom>)) \<Rightarrow> null
    | (mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (_) (_) (\<lfloor>x_\<b>\<a>\<l>\<a>\<n>\<c>\<e>\<rfloor>)) \<Rightarrow> (f (x_\<b>\<a>\<l>\<a>\<n>\<c>\<e>)))"
definition "select\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<n>\<a>\<m>\<e> f = (\<lambda> (mk\<^sub>B\<^sub>a\<^sub>n\<^sub>k (_) (\<bottom>)) \<Rightarrow> null
    | (mk\<^sub>B\<^sub>a\<^sub>n\<^sub>k (_) (\<lfloor>x_\<n>\<a>\<m>\<e>\<rfloor>)) \<Rightarrow> (f (x_\<n>\<a>\<m>\<e>)))"
definition "select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e> f = (\<lambda> (mk\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (_) (\<bottom>) (_) (_)) \<Rightarrow> null
    | (mk\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (_) (\<lfloor>x_\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e>\<rfloor>) (_) (_)) \<Rightarrow> (f (x_\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e>)))"
definition "select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<d>\<d>\<r>\<e>\<s>\<s> f = (\<lambda> (mk\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (_) (_) (\<bottom>) (_)) \<Rightarrow> null
    | (mk\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (_) (_) (\<lfloor>x_\<a>\<d>\<d>\<r>\<e>\<s>\<s>\<rfloor>) (_)) \<Rightarrow> (f (x_\<a>\<d>\<d>\<r>\<e>\<s>\<s>)))"
definition "select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<g>\<e> f = (\<lambda> (mk\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (_) (_) (_) (\<bottom>)) \<Rightarrow> null
    | (mk\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (_) (_) (_) (\<lfloor>x_\<a>\<g>\<e>\<rfloor>)) \<Rightarrow> (f (x_\<a>\<g>\<e>)))"
definition "select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<i>\<d> f = (\<lambda> (mk\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (_) (\<bottom>) (_))) (_)) \<Rightarrow> null
    | (mk\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (_) (\<lfloor>x_\<i>\<d>\<rfloor>) (_))) (_)) \<Rightarrow> (f (x_\<i>\<d>)))"
definition "select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e> f = (\<lambda> (mk\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (_) (_) (\<bottom>))) (_)) \<Rightarrow> null
    | (mk\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (_) (_) (\<lfloor>x_\<b>\<a>\<l>\<a>\<n>\<c>\<e>\<rfloor>))) (_)) \<Rightarrow> (f (x_\<b>\<a>\<l>\<a>\<n>\<c>\<e>)))"
definition "select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<i>\<d> f = (\<lambda> (mk\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s ((mk\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (_) (\<bottom>) (_))) (_)) \<Rightarrow> null
    | (mk\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s ((mk\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (_) (\<lfloor>x_\<i>\<d>\<rfloor>) (_))) (_)) \<Rightarrow> (f (x_\<i>\<d>)))"
definition "select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<l>\<a>\<n>\<c>\<e> f = (\<lambda> (mk\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s ((mk\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (_) (_) (\<bottom>))) (_)) \<Rightarrow> null
    | (mk\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s ((mk\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (_) (_) (\<lfloor>x_\<b>\<a>\<l>\<a>\<n>\<c>\<e>\<rfloor>))) (_)) \<Rightarrow> (f (x_\<b>\<a>\<l>\<a>\<n>\<c>\<e>)))"

(* 117 ************************************ 1511 + 10 *)
definition "select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<n>\<k> = select_object_any\<^sub>S\<^sub>e\<^sub>t"
definition "select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<w>\<n>\<e>\<r> = select_object_any\<^sub>S\<^sub>e\<^sub>t"
definition "select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<n>\<k> = select_object_any\<^sub>S\<^sub>e\<^sub>t"
definition "select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<o>\<w>\<n>\<e>\<r> = select_object_any\<^sub>S\<^sub>e\<^sub>t"
definition "select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<n>\<k> = select_object_any\<^sub>S\<^sub>e\<^sub>t"
definition "select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<o>\<w>\<n>\<e>\<r> = select_object_any\<^sub>S\<^sub>e\<^sub>t"
definition "select\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s> = select_object\<^sub>S\<^sub>e\<^sub>t"
definition "select\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<c>\<l>\<i>\<e>\<n>\<t>\<s> = select_object\<^sub>S\<^sub>e\<^sub>t"
definition "select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s> = select_object\<^sub>S\<^sub>e\<^sub>t"
definition "select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<n>\<k>\<s> = select_object\<^sub>S\<^sub>e\<^sub>t"

(* 118 ************************************ 1521 + 28 *)
consts dot\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t> :: "(\<AA>, '\<alpha>) val \<Rightarrow> Currency" ("(_) .overdraft")
consts dot\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> Currency" ("(_) .overdraft@pre")
consts dot\<m>\<a>\<x> :: "(\<AA>, '\<alpha>) val \<Rightarrow> Currency" ("(_) .max")
consts dot\<m>\<a>\<x>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> Currency" ("(_) .max@pre")
consts dot_0_\<b>\<a>\<n>\<k> :: "(\<AA>, '\<alpha>) val \<Rightarrow> \<cdot>Bank" ("(_) .bank")
consts dot_0_\<b>\<a>\<n>\<k>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> \<cdot>Bank" ("(_) .bank@pre")
consts dot_0_\<o>\<w>\<n>\<e>\<r> :: "(\<AA>, '\<alpha>) val \<Rightarrow> \<cdot>Client" ("(_) .owner")
consts dot_0_\<o>\<w>\<n>\<e>\<r>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> \<cdot>Client" ("(_) .owner@pre")
consts dot\<i>\<d> :: "(\<AA>, '\<alpha>) val \<Rightarrow> Integer" ("(_) .id")
consts dot\<i>\<d>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> Integer" ("(_) .id@pre")
consts dot\<b>\<a>\<l>\<a>\<n>\<c>\<e> :: "(\<AA>, '\<alpha>) val \<Rightarrow> Currency" ("(_) .balance")
consts dot\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> Currency" ("(_) .balance@pre")
consts dot_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s> :: "(\<AA>, '\<alpha>) val \<Rightarrow> Set_Account" ("(_) .b'_accounts")
consts dot_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> Set_Account" ("(_) .b'_accounts@pre")
consts dot_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s> :: "(\<AA>, '\<alpha>) val \<Rightarrow> Set_Client" ("(_) .clients")
consts dot_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> Set_Client" ("(_) .clients@pre")
consts dot\<n>\<a>\<m>\<e> :: "(\<AA>, '\<alpha>) val \<Rightarrow> String" ("(_) .name")
consts dot\<n>\<a>\<m>\<e>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> String" ("(_) .name@pre")
consts dot_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s> :: "(\<AA>, '\<alpha>) val \<Rightarrow> Set_Account" ("(_) .c'_accounts")
consts dot_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> Set_Account" ("(_) .c'_accounts@pre")
consts dot_1_\<b>\<a>\<n>\<k>\<s> :: "(\<AA>, '\<alpha>) val \<Rightarrow> Set_Bank" ("(_) .banks")
consts dot_1_\<b>\<a>\<n>\<k>\<s>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> Set_Bank" ("(_) .banks@pre")
consts dot\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e> :: "(\<AA>, '\<alpha>) val \<Rightarrow> String" ("(_) .clientname")
consts dot\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> String" ("(_) .clientname@pre")
consts dot\<a>\<d>\<d>\<r>\<e>\<s>\<s> :: "(\<AA>, '\<alpha>) val \<Rightarrow> String" ("(_) .address")
consts dot\<a>\<d>\<d>\<r>\<e>\<s>\<s>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> String" ("(_) .address@pre")
consts dot\<a>\<g>\<e> :: "(\<AA>, '\<alpha>) val \<Rightarrow> Integer" ("(_) .age")
consts dot\<a>\<g>\<e>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> Integer" ("(_) .age@pre")

(* 119 ************************************ 1549 + 44 *)
defs(overloaded) dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t> : "(x::\<cdot>Current) .overdraft \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (in_post_state) ((select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t>at_pre : "(x::\<cdot>Current) .overdraft@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (in_pre_state) ((select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<m>\<a>\<x> : "(x::\<cdot>Savings) .max \<equiv> (eval_extract (x) ((deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (in_post_state) ((select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<m>\<a>\<x> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<m>\<a>\<x>at_pre : "(x::\<cdot>Savings) .max@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (in_pre_state) ((select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<m>\<a>\<x> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k> : "(x::\<cdot>Account) .bank \<equiv> (eval_extract (x) ((deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (in_post_state) ((deref_assocs\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k> (in_post_state) ((select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<n>\<k> ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_post_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r> : "(x::\<cdot>Account) .owner \<equiv> (eval_extract (x) ((deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (in_post_state) ((deref_assocs\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r> (in_post_state) ((select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<o>\<w>\<n>\<e>\<r> ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_post_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<i>\<d> : "(x::\<cdot>Account) .id \<equiv> (eval_extract (x) ((deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (in_post_state) ((select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<i>\<d> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e> : "(x::\<cdot>Account) .balance \<equiv> (eval_extract (x) ((deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (in_post_state) ((select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre : "(x::\<cdot>Account) .bank@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (in_pre_state) ((deref_assocs\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k> (in_pre_state) ((select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<n>\<k> ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_pre_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre : "(x::\<cdot>Account) .owner@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (in_pre_state) ((deref_assocs\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r> (in_pre_state) ((select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<o>\<w>\<n>\<e>\<r> ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_pre_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<i>\<d>at_pre : "(x::\<cdot>Account) .id@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (in_pre_state) ((select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<i>\<d> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre : "(x::\<cdot>Account) .balance@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (in_pre_state) ((select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s> : "(x::\<cdot>Bank) .b_accounts \<equiv> (eval_extract (x) ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_post_state) ((deref_assocs\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s> (in_post_state) ((select\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s> ((deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (in_post_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s> : "(x::\<cdot>Bank) .clients \<equiv> (eval_extract (x) ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_post_state) ((deref_assocs\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s> (in_post_state) ((select\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<c>\<l>\<i>\<e>\<n>\<t>\<s> ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_post_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<n>\<a>\<m>\<e> : "(x::\<cdot>Bank) .name \<equiv> (eval_extract (x) ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_post_state) ((select\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<n>\<a>\<m>\<e> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>at_pre : "(x::\<cdot>Bank) .b_accounts@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_pre_state) ((deref_assocs\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s> (in_pre_state) ((select\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s> ((deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (in_pre_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s>at_pre : "(x::\<cdot>Bank) .clients@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_pre_state) ((deref_assocs\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s> (in_pre_state) ((select\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<c>\<l>\<i>\<e>\<n>\<t>\<s> ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_pre_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<n>\<a>\<m>\<e>at_pre : "(x::\<cdot>Bank) .name@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_pre_state) ((select\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<n>\<a>\<m>\<e> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s> : "(x::\<cdot>Client) .c_accounts \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_post_state) ((deref_assocs\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s> (in_post_state) ((select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s> ((deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (in_post_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<b>\<a>\<n>\<k>\<s> : "(x::\<cdot>Client) .banks \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_post_state) ((deref_assocs\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<b>\<a>\<n>\<k>\<s> (in_post_state) ((select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<n>\<k>\<s> ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_post_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e> : "(x::\<cdot>Client) .clientname \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_post_state) ((select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<d>\<d>\<r>\<e>\<s>\<s> : "(x::\<cdot>Client) .address \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_post_state) ((select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<d>\<d>\<r>\<e>\<s>\<s> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<g>\<e> : "(x::\<cdot>Client) .age \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_post_state) ((select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<g>\<e> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>at_pre : "(x::\<cdot>Client) .c_accounts@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_pre_state) ((deref_assocs\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s> (in_pre_state) ((select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s> ((deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (in_pre_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<b>\<a>\<n>\<k>\<s>at_pre : "(x::\<cdot>Client) .banks@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_pre_state) ((deref_assocs\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<b>\<a>\<n>\<k>\<s> (in_pre_state) ((select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<n>\<k>\<s> ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_pre_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e>at_pre : "(x::\<cdot>Client) .clientname@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_pre_state) ((select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<d>\<d>\<r>\<e>\<s>\<s>at_pre : "(x::\<cdot>Client) .address@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_pre_state) ((select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<d>\<d>\<r>\<e>\<s>\<s> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<g>\<e>at_pre : "(x::\<cdot>Client) .age@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_pre_state) ((select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<g>\<e> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k> : "(x::\<cdot>Current) .bank \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (in_post_state) ((deref_assocs\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k> (in_post_state) ((select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<n>\<k> ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_post_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r> : "(x::\<cdot>Current) .owner \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (in_post_state) ((deref_assocs\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r> (in_post_state) ((select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<w>\<n>\<e>\<r> ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_post_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<i>\<d> : "(x::\<cdot>Current) .id \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (in_post_state) ((select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<i>\<d> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e> : "(x::\<cdot>Current) .balance \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (in_post_state) ((select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre : "(x::\<cdot>Current) .bank@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (in_pre_state) ((deref_assocs\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k> (in_pre_state) ((select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<n>\<k> ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_pre_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre : "(x::\<cdot>Current) .owner@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (in_pre_state) ((deref_assocs\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r> (in_pre_state) ((select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<w>\<n>\<e>\<r> ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_pre_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<i>\<d>at_pre : "(x::\<cdot>Current) .id@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (in_pre_state) ((select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<i>\<d> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre : "(x::\<cdot>Current) .balance@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t (in_pre_state) ((select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k> : "(x::\<cdot>Savings) .bank \<equiv> (eval_extract (x) ((deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (in_post_state) ((deref_assocs\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k> (in_post_state) ((select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<n>\<k> ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_post_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r> : "(x::\<cdot>Savings) .owner \<equiv> (eval_extract (x) ((deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (in_post_state) ((deref_assocs\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r> (in_post_state) ((select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<o>\<w>\<n>\<e>\<r> ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_post_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<i>\<d> : "(x::\<cdot>Savings) .id \<equiv> (eval_extract (x) ((deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (in_post_state) ((select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<i>\<d> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<l>\<a>\<n>\<c>\<e> : "(x::\<cdot>Savings) .balance \<equiv> (eval_extract (x) ((deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (in_post_state) ((select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<l>\<a>\<n>\<c>\<e> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k>at_pre : "(x::\<cdot>Savings) .bank@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (in_pre_state) ((deref_assocs\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k> (in_pre_state) ((select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<n>\<k> ((deref_oid\<^sub>B\<^sub>a\<^sub>n\<^sub>k (in_pre_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r>at_pre : "(x::\<cdot>Savings) .owner@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (in_pre_state) ((deref_assocs\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r> (in_pre_state) ((select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<o>\<w>\<n>\<e>\<r> ((deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (in_pre_state) (reconst_basetype))))))))))"
defs(overloaded) dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<i>\<d>at_pre : "(x::\<cdot>Savings) .id@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (in_pre_state) ((select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<i>\<d> (reconst_basetype))))))"
defs(overloaded) dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre : "(x::\<cdot>Savings) .balance@pre \<equiv> (eval_extract (x) ((deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (in_pre_state) ((select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<l>\<a>\<n>\<c>\<e> (reconst_basetype))))))"

(* 120 ************************************ 1593 + 1 *)
lemmas dot_accessor = dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t>
                            dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t>at_pre
                            dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<m>\<a>\<x>
                            dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<m>\<a>\<x>at_pre
                            dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>
                            dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>
                            dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<i>\<d>
                            dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>
                            dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre
                            dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre
                            dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<i>\<d>at_pre
                            dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre
                            dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>
                            dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s>
                            dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<n>\<a>\<m>\<e>
                            dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>at_pre
                            dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s>at_pre
                            dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<n>\<a>\<m>\<e>at_pre
                            dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>
                            dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<b>\<a>\<n>\<k>\<s>
                            dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e>
                            dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<d>\<d>\<r>\<e>\<s>\<s>
                            dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<g>\<e>
                            dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>at_pre
                            dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<b>\<a>\<n>\<k>\<s>at_pre
                            dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e>at_pre
                            dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<d>\<d>\<r>\<e>\<s>\<s>at_pre
                            dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<g>\<e>at_pre
                            dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>
                            dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>
                            dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<i>\<d>
                            dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>
                            dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre
                            dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre
                            dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<i>\<d>at_pre
                            dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre
                            dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k>
                            dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r>
                            dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<i>\<d>
                            dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<l>\<a>\<n>\<c>\<e>
                            dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k>at_pre
                            dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r>at_pre
                            dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<i>\<d>at_pre
                            dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre

(* 121 ************************************ 1594 + 1 *)
subsection{* Context Passing *}

(* 122 ************************************ 1595 + 1 *)
lemmas[simp,code_unfold] = eval_extract_def

(* 123 ************************************ 1596 + 44 *)
lemma cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t> : "(cp ((\<lambda>X. (X::\<cdot>Current) .overdraft)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t>at_pre : "(cp ((\<lambda>X. (X::\<cdot>Current) .overdraft@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<m>\<a>\<x> : "(cp ((\<lambda>X. (X::\<cdot>Savings) .max)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<m>\<a>\<x>at_pre : "(cp ((\<lambda>X. (X::\<cdot>Savings) .max@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k> : "(cp ((\<lambda>X. (X::\<cdot>Account) .bank)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r> : "(cp ((\<lambda>X. (X::\<cdot>Account) .owner)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<i>\<d> : "(cp ((\<lambda>X. (X::\<cdot>Account) .id)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e> : "(cp ((\<lambda>X. (X::\<cdot>Account) .balance)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre : "(cp ((\<lambda>X. (X::\<cdot>Account) .bank@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre : "(cp ((\<lambda>X. (X::\<cdot>Account) .owner@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<i>\<d>at_pre : "(cp ((\<lambda>X. (X::\<cdot>Account) .id@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre : "(cp ((\<lambda>X. (X::\<cdot>Account) .balance@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s> : "(cp ((\<lambda>X. (X::\<cdot>Bank) .b_accounts)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s> : "(cp ((\<lambda>X. (X::\<cdot>Bank) .clients)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<n>\<a>\<m>\<e> : "(cp ((\<lambda>X. (X::\<cdot>Bank) .name)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>at_pre : "(cp ((\<lambda>X. (X::\<cdot>Bank) .b_accounts@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s>at_pre : "(cp ((\<lambda>X. (X::\<cdot>Bank) .clients@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<n>\<a>\<m>\<e>at_pre : "(cp ((\<lambda>X. (X::\<cdot>Bank) .name@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s> : "(cp ((\<lambda>X. (X::\<cdot>Client) .c_accounts)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<b>\<a>\<n>\<k>\<s> : "(cp ((\<lambda>X. (X::\<cdot>Client) .banks)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e> : "(cp ((\<lambda>X. (X::\<cdot>Client) .clientname)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<d>\<d>\<r>\<e>\<s>\<s> : "(cp ((\<lambda>X. (X::\<cdot>Client) .address)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<g>\<e> : "(cp ((\<lambda>X. (X::\<cdot>Client) .age)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>at_pre : "(cp ((\<lambda>X. (X::\<cdot>Client) .c_accounts@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<b>\<a>\<n>\<k>\<s>at_pre : "(cp ((\<lambda>X. (X::\<cdot>Client) .banks@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e>at_pre : "(cp ((\<lambda>X. (X::\<cdot>Client) .clientname@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<d>\<d>\<r>\<e>\<s>\<s>at_pre : "(cp ((\<lambda>X. (X::\<cdot>Client) .address@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<g>\<e>at_pre : "(cp ((\<lambda>X. (X::\<cdot>Client) .age@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k> : "(cp ((\<lambda>X. (X::\<cdot>Current) .bank)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r> : "(cp ((\<lambda>X. (X::\<cdot>Current) .owner)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<i>\<d> : "(cp ((\<lambda>X. (X::\<cdot>Current) .id)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e> : "(cp ((\<lambda>X. (X::\<cdot>Current) .balance)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre : "(cp ((\<lambda>X. (X::\<cdot>Current) .bank@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre : "(cp ((\<lambda>X. (X::\<cdot>Current) .owner@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<i>\<d>at_pre : "(cp ((\<lambda>X. (X::\<cdot>Current) .id@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre : "(cp ((\<lambda>X. (X::\<cdot>Current) .balance@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k> : "(cp ((\<lambda>X. (X::\<cdot>Savings) .bank)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r> : "(cp ((\<lambda>X. (X::\<cdot>Savings) .owner)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<i>\<d> : "(cp ((\<lambda>X. (X::\<cdot>Savings) .id)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<l>\<a>\<n>\<c>\<e> : "(cp ((\<lambda>X. (X::\<cdot>Savings) .balance)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k>at_pre : "(cp ((\<lambda>X. (X::\<cdot>Savings) .bank@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r>at_pre : "(cp ((\<lambda>X. (X::\<cdot>Savings) .owner@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<i>\<d>at_pre : "(cp ((\<lambda>X. (X::\<cdot>Savings) .id@pre)))"
by(auto simp: dot_accessor cp_def)
lemma cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre : "(cp ((\<lambda>X. (X::\<cdot>Savings) .balance@pre)))"
by(auto simp: dot_accessor cp_def)

(* 124 ************************************ 1640 + 1 *)
lemmas[simp,code_unfold] = cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t>
                            cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t>at_pre
                            cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<m>\<a>\<x>
                            cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<m>\<a>\<x>at_pre
                            cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>
                            cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>
                            cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<i>\<d>
                            cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>
                            cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre
                            cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre
                            cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<i>\<d>at_pre
                            cp_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre
                            cp_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>
                            cp_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s>
                            cp_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<n>\<a>\<m>\<e>
                            cp_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>at_pre
                            cp_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s>at_pre
                            cp_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<n>\<a>\<m>\<e>at_pre
                            cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>
                            cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<b>\<a>\<n>\<k>\<s>
                            cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e>
                            cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<d>\<d>\<r>\<e>\<s>\<s>
                            cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<g>\<e>
                            cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>at_pre
                            cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<b>\<a>\<n>\<k>\<s>at_pre
                            cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e>at_pre
                            cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<d>\<d>\<r>\<e>\<s>\<s>at_pre
                            cp_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<g>\<e>at_pre
                            cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>
                            cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>
                            cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<i>\<d>
                            cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>
                            cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre
                            cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre
                            cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<i>\<d>at_pre
                            cp_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre
                            cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k>
                            cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r>
                            cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<i>\<d>
                            cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<l>\<a>\<n>\<c>\<e>
                            cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k>at_pre
                            cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r>at_pre
                            cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<i>\<d>at_pre
                            cp_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre

(* 125 ************************************ 1641 + 1 *)
subsection{* Execution with Invalid or Null as Argument *}

(* 126 ************************************ 1642 + 88 *)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t>_invalid : "(invalid::\<cdot>Current) .overdraft = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t>_null : "(null::\<cdot>Current) .overdraft = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t>at_pre_invalid : "(invalid::\<cdot>Current) .overdraft@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t>at_pre_null : "(null::\<cdot>Current) .overdraft@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<m>\<a>\<x>_invalid : "(invalid::\<cdot>Savings) .max = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<m>\<a>\<x>_null : "(null::\<cdot>Savings) .max = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<m>\<a>\<x>at_pre_invalid : "(invalid::\<cdot>Savings) .max@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<m>\<a>\<x>at_pre_null : "(null::\<cdot>Savings) .max@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>_invalid : "(invalid::\<cdot>Account) .bank = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>_null : "(null::\<cdot>Account) .bank = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>_invalid : "(invalid::\<cdot>Account) .owner = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>_null : "(null::\<cdot>Account) .owner = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<i>\<d>_invalid : "(invalid::\<cdot>Account) .id = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<i>\<d>_null : "(null::\<cdot>Account) .id = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>_invalid : "(invalid::\<cdot>Account) .balance = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>_null : "(null::\<cdot>Account) .balance = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre_invalid : "(invalid::\<cdot>Account) .bank@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre_null : "(null::\<cdot>Account) .bank@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre_invalid : "(invalid::\<cdot>Account) .owner@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre_null : "(null::\<cdot>Account) .owner@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<i>\<d>at_pre_invalid : "(invalid::\<cdot>Account) .id@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<i>\<d>at_pre_null : "(null::\<cdot>Account) .id@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre_invalid : "(invalid::\<cdot>Account) .balance@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre_null : "(null::\<cdot>Account) .balance@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>_invalid : "(invalid::\<cdot>Bank) .b_accounts = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>_null : "(null::\<cdot>Bank) .b_accounts = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s>_invalid : "(invalid::\<cdot>Bank) .clients = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s>_null : "(null::\<cdot>Bank) .clients = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<n>\<a>\<m>\<e>_invalid : "(invalid::\<cdot>Bank) .name = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<n>\<a>\<m>\<e>_null : "(null::\<cdot>Bank) .name = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>at_pre_invalid : "(invalid::\<cdot>Bank) .b_accounts@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>at_pre_null : "(null::\<cdot>Bank) .b_accounts@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s>at_pre_invalid : "(invalid::\<cdot>Bank) .clients@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s>at_pre_null : "(null::\<cdot>Bank) .clients@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<n>\<a>\<m>\<e>at_pre_invalid : "(invalid::\<cdot>Bank) .name@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<n>\<a>\<m>\<e>at_pre_null : "(null::\<cdot>Bank) .name@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>_invalid : "(invalid::\<cdot>Client) .c_accounts = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>_null : "(null::\<cdot>Client) .c_accounts = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<b>\<a>\<n>\<k>\<s>_invalid : "(invalid::\<cdot>Client) .banks = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<b>\<a>\<n>\<k>\<s>_null : "(null::\<cdot>Client) .banks = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e>_invalid : "(invalid::\<cdot>Client) .clientname = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e>_null : "(null::\<cdot>Client) .clientname = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<d>\<d>\<r>\<e>\<s>\<s>_invalid : "(invalid::\<cdot>Client) .address = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<d>\<d>\<r>\<e>\<s>\<s>_null : "(null::\<cdot>Client) .address = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<g>\<e>_invalid : "(invalid::\<cdot>Client) .age = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<g>\<e>_null : "(null::\<cdot>Client) .age = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>at_pre_invalid : "(invalid::\<cdot>Client) .c_accounts@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>at_pre_null : "(null::\<cdot>Client) .c_accounts@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<b>\<a>\<n>\<k>\<s>at_pre_invalid : "(invalid::\<cdot>Client) .banks@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<b>\<a>\<n>\<k>\<s>at_pre_null : "(null::\<cdot>Client) .banks@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e>at_pre_invalid : "(invalid::\<cdot>Client) .clientname@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e>at_pre_null : "(null::\<cdot>Client) .clientname@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<d>\<d>\<r>\<e>\<s>\<s>at_pre_invalid : "(invalid::\<cdot>Client) .address@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<d>\<d>\<r>\<e>\<s>\<s>at_pre_null : "(null::\<cdot>Client) .address@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<g>\<e>at_pre_invalid : "(invalid::\<cdot>Client) .age@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<g>\<e>at_pre_null : "(null::\<cdot>Client) .age@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>_invalid : "(invalid::\<cdot>Current) .bank = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>_null : "(null::\<cdot>Current) .bank = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>_invalid : "(invalid::\<cdot>Current) .owner = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>_null : "(null::\<cdot>Current) .owner = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<i>\<d>_invalid : "(invalid::\<cdot>Current) .id = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<i>\<d>_null : "(null::\<cdot>Current) .id = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>_invalid : "(invalid::\<cdot>Current) .balance = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>_null : "(null::\<cdot>Current) .balance = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre_invalid : "(invalid::\<cdot>Current) .bank@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre_null : "(null::\<cdot>Current) .bank@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre_invalid : "(invalid::\<cdot>Current) .owner@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre_null : "(null::\<cdot>Current) .owner@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<i>\<d>at_pre_invalid : "(invalid::\<cdot>Current) .id@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<i>\<d>at_pre_null : "(null::\<cdot>Current) .id@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre_invalid : "(invalid::\<cdot>Current) .balance@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre_null : "(null::\<cdot>Current) .balance@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k>_invalid : "(invalid::\<cdot>Savings) .bank = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k>_null : "(null::\<cdot>Savings) .bank = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r>_invalid : "(invalid::\<cdot>Savings) .owner = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r>_null : "(null::\<cdot>Savings) .owner = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<i>\<d>_invalid : "(invalid::\<cdot>Savings) .id = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<i>\<d>_null : "(null::\<cdot>Savings) .id = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<l>\<a>\<n>\<c>\<e>_invalid : "(invalid::\<cdot>Savings) .balance = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<l>\<a>\<n>\<c>\<e>_null : "(null::\<cdot>Savings) .balance = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k>at_pre_invalid : "(invalid::\<cdot>Savings) .bank@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k>at_pre_null : "(null::\<cdot>Savings) .bank@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r>at_pre_invalid : "(invalid::\<cdot>Savings) .owner@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r>at_pre_null : "(null::\<cdot>Savings) .owner@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<i>\<d>at_pre_invalid : "(invalid::\<cdot>Savings) .id@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<i>\<d>at_pre_null : "(null::\<cdot>Savings) .id@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre_invalid : "(invalid::\<cdot>Savings) .balance@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def invalid_def)
lemma dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre_null : "(null::\<cdot>Savings) .balance@pre = invalid"
by(rule ext, simp add: dot_accessor bot_option_def null_fun_def null_option_def)

(* 127 ************************************ 1730 + 1 *)
subsection{* Representation in States *}

(* 128 ************************************ 1731 + 44 *)
lemma defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t> : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .overdraft)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .overdraft)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .overdraft)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .overdraft@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .overdraft@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .overdraft@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<m>\<a>\<x> : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .max)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .max)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<m>\<a>\<x>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .max)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<m>\<a>\<x>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<m>\<a>\<x>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .max@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .max@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<m>\<a>\<x>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .max@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<m>\<a>\<x>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k> : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .bank)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .bank)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .bank)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r> : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .owner)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .owner)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .owner)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<i>\<d> : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .id)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .id)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<i>\<d>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .id)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<i>\<d>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e> : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .balance)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .balance)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .balance)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .bank@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .bank@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .bank@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .owner@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .owner@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .owner@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<i>\<d>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .id@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .id@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<i>\<d>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .id@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<i>\<d>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .balance@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .balance@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .balance@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s> : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .b_accounts)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .b_accounts)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .b_accounts)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s> : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .clients)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .clients)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .clients)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<n>\<a>\<m>\<e> : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .name)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .name)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<n>\<a>\<m>\<e>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .name)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<n>\<a>\<m>\<e>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .b_accounts@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .b_accounts@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .b_accounts@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .clients@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .clients@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .clients@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<n>\<a>\<m>\<e>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Bank) .name@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .name@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<n>\<a>\<m>\<e>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .name@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<n>\<a>\<m>\<e>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s> : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .c_accounts)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .c_accounts)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .c_accounts)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<b>\<a>\<n>\<k>\<s> : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .banks)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .banks)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<b>\<a>\<n>\<k>\<s>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .banks)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<b>\<a>\<n>\<k>\<s>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e> : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .clientname)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .clientname)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .clientname)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<d>\<d>\<r>\<e>\<s>\<s> : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .address)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .address)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<d>\<d>\<r>\<e>\<s>\<s>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .address)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<d>\<d>\<r>\<e>\<s>\<s>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<g>\<e> : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .age)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .age)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<g>\<e>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .age)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<g>\<e>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .c_accounts@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .c_accounts@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .c_accounts@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<b>\<a>\<n>\<k>\<s>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .banks@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .banks@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<b>\<a>\<n>\<k>\<s>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .banks@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_1_\<b>\<a>\<n>\<k>\<s>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .clientname@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .clientname@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .clientname@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<d>\<d>\<r>\<e>\<s>\<s>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .address@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .address@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<d>\<d>\<r>\<e>\<s>\<s>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .address@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<d>\<d>\<r>\<e>\<s>\<s>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<g>\<e>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Client) .age@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .age@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<g>\<e>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .age@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<a>\<g>\<e>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k> : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .bank)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .bank)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .bank)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r> : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .owner)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .owner)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .owner)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<i>\<d> : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .id)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .id)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<i>\<d>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .id)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<i>\<d>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e> : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .balance)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .balance)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .balance)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .bank@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .bank@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .bank@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .owner@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .owner@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .owner@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<i>\<d>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .id@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .id@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<i>\<d>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .id@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<i>\<d>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .balance@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .balance@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .balance@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k> : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .bank)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .bank)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .bank)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r> : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .owner)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .owner)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .owner)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<i>\<d> : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .id)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .id)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<i>\<d>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .id)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<i>\<d>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<l>\<a>\<n>\<c>\<e> : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .balance)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .balance)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<l>\<a>\<n>\<c>\<e>_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .balance)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<l>\<a>\<n>\<c>\<e>_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .bank@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .bank@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .bank@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .owner@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .owner@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .owner@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<i>\<d>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .id@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .id@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<i>\<d>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .id@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<i>\<d>at_pre_null)
by(simp add: defined_split)
lemma defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre : "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .balance@pre)) \<Longrightarrow> \<tau> \<Turnstile> (\<delta> (X))"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .balance@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre_invalid)
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .balance@pre)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16' dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre_null)
by(simp add: defined_split)

(* 129 ************************************ 1775 + 12 *)
lemma is_repr_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k> : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .bank))"
shows "(is_represented_in_state (in_post_state) (X .bank) (Bank) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_post_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k> is_represented_in_state_def select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<n>\<k>_def deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_def in_post_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_post_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k> is_represented_in_state_def deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  apply(simp add: deref_assocs\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>_def deref_assocs_def)
  apply(case_tac "(assocs ((in_post_state (\<tau>))) (oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>))", simp add: invalid_def bot_option_def, simp add: select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<n>\<k>_def)
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
lemma is_repr_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r> : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .owner))"
shows "(is_represented_in_state (in_post_state) (X .owner) (Client) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_post_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r> is_represented_in_state_def select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<o>\<w>\<n>\<e>\<r>_def deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_def in_post_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_post_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r> is_represented_in_state_def deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  apply(simp add: deref_assocs\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>_def deref_assocs_def)
  apply(case_tac "(assocs ((in_post_state (\<tau>))) (oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>))", simp add: invalid_def bot_option_def, simp add: select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<o>\<w>\<n>\<e>\<r>_def)
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
lemma is_repr_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .bank@pre))"
shows "(is_represented_in_state (in_pre_state) (X .bank@pre) (Bank) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_pre_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre is_represented_in_state_def select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<n>\<k>_def deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_def in_pre_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_pre_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre is_represented_in_state_def deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  apply(simp add: deref_assocs\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>_def deref_assocs_def)
  apply(case_tac "(assocs ((in_pre_state (\<tau>))) (oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>))", simp add: invalid_def bot_option_def, simp add: select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<b>\<a>\<n>\<k>_def)
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
lemma is_repr_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Account) .owner@pre))"
shows "(is_represented_in_state (in_pre_state) (X .owner@pre) (Client) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_pre_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre is_represented_in_state_def select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<o>\<w>\<n>\<e>\<r>_def deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_def in_pre_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_pre_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre is_represented_in_state_def deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  apply(simp add: deref_assocs\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>_def deref_assocs_def)
  apply(case_tac "(assocs ((in_pre_state (\<tau>))) (oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>))", simp add: invalid_def bot_option_def, simp add: select\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<o>\<w>\<n>\<e>\<r>_def)
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
lemma is_repr_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k> : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .bank))"
shows "(is_represented_in_state (in_post_state) (X .bank) (Bank) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_post_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k> is_represented_in_state_def select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<n>\<k>_def deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_def in_post_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_post_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k> is_represented_in_state_def deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  apply(simp add: deref_assocs\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>_def deref_assocs_def)
  apply(case_tac "(assocs ((in_post_state (\<tau>))) (oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>))", simp add: invalid_def bot_option_def, simp add: select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<n>\<k>_def)
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
lemma is_repr_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r> : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .owner))"
shows "(is_represented_in_state (in_post_state) (X .owner) (Client) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_post_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r> is_represented_in_state_def select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<w>\<n>\<e>\<r>_def deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_def in_post_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_post_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r> is_represented_in_state_def deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  apply(simp add: deref_assocs\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>_def deref_assocs_def)
  apply(case_tac "(assocs ((in_post_state (\<tau>))) (oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>))", simp add: invalid_def bot_option_def, simp add: select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<w>\<n>\<e>\<r>_def)
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
lemma is_repr_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .bank@pre))"
shows "(is_represented_in_state (in_pre_state) (X .bank@pre) (Bank) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_pre_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre is_represented_in_state_def select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<n>\<k>_def deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_def in_pre_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_pre_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>at_pre is_represented_in_state_def deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  apply(simp add: deref_assocs\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>_def deref_assocs_def)
  apply(case_tac "(assocs ((in_pre_state (\<tau>))) (oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<b>\<a>\<n>\<k>))", simp add: invalid_def bot_option_def, simp add: select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<b>\<a>\<n>\<k>_def)
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
lemma is_repr_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Current) .owner@pre))"
shows "(is_represented_in_state (in_pre_state) (X .owner@pre) (Client) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_pre_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre is_represented_in_state_def select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<w>\<n>\<e>\<r>_def deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_def in_pre_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_pre_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>at_pre is_represented_in_state_def deref_oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  apply(simp add: deref_assocs\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>_def deref_assocs_def)
  apply(case_tac "(assocs ((in_pre_state (\<tau>))) (oid\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t_0_\<o>\<w>\<n>\<e>\<r>))", simp add: invalid_def bot_option_def, simp add: select\<^sub>C\<^sub>u\<^sub>r\<^sub>r\<^sub>e\<^sub>n\<^sub>t\<o>\<w>\<n>\<e>\<r>_def)
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
lemma is_repr_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k> : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .bank))"
shows "(is_represented_in_state (in_post_state) (X .bank) (Bank) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k>[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_post_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k> is_represented_in_state_def select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<n>\<k>_def deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_def in_post_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_post_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k> is_represented_in_state_def deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  apply(simp add: deref_assocs\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k>_def deref_assocs_def)
  apply(case_tac "(assocs ((in_post_state (\<tau>))) (oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k>))", simp add: invalid_def bot_option_def, simp add: select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<n>\<k>_def)
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
lemma is_repr_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r> : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .owner))"
shows "(is_represented_in_state (in_post_state) (X .owner) (Client) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r>[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_post_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r> is_represented_in_state_def select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<o>\<w>\<n>\<e>\<r>_def deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_def in_post_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_post_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r> is_represented_in_state_def deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  apply(simp add: deref_assocs\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r>_def deref_assocs_def)
  apply(case_tac "(assocs ((in_post_state (\<tau>))) (oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r>))", simp add: invalid_def bot_option_def, simp add: select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<o>\<w>\<n>\<e>\<r>_def)
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
lemma is_repr_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k>at_pre : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .bank@pre))"
shows "(is_represented_in_state (in_pre_state) (X .bank@pre) (Bank) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k>at_pre[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_pre_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k>at_pre is_represented_in_state_def select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<n>\<k>_def deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_def in_pre_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_pre_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k>at_pre is_represented_in_state_def deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  apply(simp add: deref_assocs\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k>_def deref_assocs_def)
  apply(case_tac "(assocs ((in_pre_state (\<tau>))) (oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<b>\<a>\<n>\<k>))", simp add: invalid_def bot_option_def, simp add: select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<b>\<a>\<n>\<k>_def)
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
lemma is_repr_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r>at_pre : 
assumes def_dot: "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>Savings) .owner@pre))"
shows "(is_represented_in_state (in_pre_state) (X .owner@pre) (Client) (\<tau>))"
  apply(insert defined_mono_dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r>at_pre[OF def_dot, simplified foundation16])
  apply(case_tac "(X (\<tau>))", simp add: bot_option_def)
  proof - fix a0 show "(X (\<tau>)) \<noteq> null \<Longrightarrow> (X (\<tau>)) = (Some (a0)) \<Longrightarrow> ?thesis"
  apply(case_tac "a0", simp add: null_option_def bot_option_def, clarify)
  proof - fix a show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> ?thesis"
  apply(case_tac "(heap ((in_pre_state (\<tau>))) ((oid_of (a))))", simp add: invalid_def bot_option_def)
  apply(insert def_dot, simp add: dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r>at_pre is_represented_in_state_def select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<o>\<w>\<n>\<e>\<r>_def deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_def in_pre_state_def defined_def OclValid_def false_def true_def invalid_def bot_fun_def split: split_if_asm)
  proof - fix b show "(X (\<tau>)) = (Some ((Some (a)))) \<Longrightarrow> (heap ((in_pre_state (\<tau>))) ((oid_of (a)))) = (Some (b)) \<Longrightarrow> ?thesis"
  apply(insert def_dot[simplified foundation16], auto simp: dot\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r>at_pre is_represented_in_state_def deref_oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_def bot_option_def null_option_def)
  apply(case_tac "b", simp_all add: invalid_def bot_option_def)
  apply(simp add: deref_assocs\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r>_def deref_assocs_def)
  apply(case_tac "(assocs ((in_pre_state (\<tau>))) (oid\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s_0_\<o>\<w>\<n>\<e>\<r>))", simp add: invalid_def bot_option_def, simp add: select\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s\<o>\<w>\<n>\<e>\<r>_def)
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

(* 130 ************************************ 1787 + 1 *)
section{* A Little Infra-structure on Example States *}

(* 131 ************************************ 1788 + 1 *)
text{*  *}

(* 132 ************************************ 1789 + 1 *)
text{* 

The example we are defining in this section comes from the figure~\ref{fig:eam1_system-states}.
\begin{figure}
\includegraphics[width=\textwidth]{figures/pre-post.pdf}
\caption{(a) pre-state $\sigma_1$ and
  (b) post-state $\sigma_1'$.}
\label{fig:eam1_system-states}
\end{figure}
 *}

(* 133 ************************************ 1790 + 1 *)
lemmas [simp,code_unfold] = state.defs
                            const_ss

(* 134 ************************************ 1791 + 1 *)
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

(* 135 ************************************ 1792 + 4 *)
definition "oid3 = 3"
definition "oid4 = 4"
definition "oid5 = 5"
definition "oid6 = 6"

(* 136 ************************************ 1796 + 8 *)
definition "Saving1\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t = (mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t_\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s ((mk\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s ((mk\<E>\<X>\<T>\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>s (oid3) (None) (None))) (\<lfloor>2000\<rfloor>))))) (None) (None))"
definition "(Saving1::\<cdot>Account) = (\<lambda>_. \<lfloor>\<lfloor>Saving1\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<rfloor>\<rfloor>)"
definition "Client1\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t = (mk\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (oid4))) (None) (None) (None))"
definition "(Client1::\<cdot>Client) = (\<lambda>_. \<lfloor>\<lfloor>Client1\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<rfloor>\<rfloor>)"
definition "Account1\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t = (mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t ((mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (oid5))) (\<lfloor>250\<rfloor>) (None))"
definition "(Account1::\<cdot>Account) = (\<lambda>_. \<lfloor>\<lfloor>Account1\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<rfloor>\<rfloor>)"
definition "Bank1\<^sub>B\<^sub>a\<^sub>n\<^sub>k = (mk\<^sub>B\<^sub>a\<^sub>n\<^sub>k ((mk\<E>\<X>\<T>\<^sub>B\<^sub>a\<^sub>n\<^sub>k (oid6))) (\<lfloor>(let c = char_of_nat in c 092 # c 060 # CHR ''i'' # CHR ''n'' # CHR ''f'' # CHR ''i'' # CHR ''n'' # CHR ''i'' # CHR ''t'' # CHR ''y'' # c 062 # c 092 # c 060 # CHR ''h'' # CHR ''e'' # CHR ''a'' # CHR ''r'' # CHR ''t'' # CHR ''s'' # CHR ''u'' # CHR ''i'' # CHR ''t'' # c 062 # c 032 # c 092 # c 060 # CHR ''L'' # CHR ''o'' # CHR ''n'' # CHR ''g'' # CHR ''l'' # CHR ''e'' # CHR ''f'' # CHR ''t'' # CHR ''r'' # CHR ''i'' # CHR ''g'' # CHR ''h'' # CHR ''t'' # CHR ''a'' # CHR ''r'' # CHR ''r'' # CHR ''o'' # CHR ''w'' # c 062 # c 032 # c 092 # c 060 # CHR ''i'' # CHR ''n'' # CHR ''f'' # CHR ''i'' # CHR ''n'' # CHR ''i'' # CHR ''t'' # CHR ''y'' # c 062 # c 092 # c 060 # CHR ''e'' # CHR ''p'' # CHR ''s'' # CHR ''i'' # CHR ''l'' # CHR ''o'' # CHR ''n'' # c 062 # [])\<rfloor>))"
definition "(Bank1::\<cdot>Bank) = (\<lambda>_. \<lfloor>\<lfloor>Bank1\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<rfloor>\<rfloor>)"

(* 137 ************************************ 1804 + 1 *)
definition "instance\<^sub>B\<^sub>a\<^sub>n\<^sub>k\<^sub>1095\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<^sub>1095\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t\<^sub>1095\<^sub>S\<^sub>a\<^sub>v\<^sub>i\<^sub>n\<^sub>g\<^sub>1 = (\<lambda>Bank1 Account1 Client1 Saving1. (Account1 , Saving1 , Client1 , Bank1 , Saving1))"

(* 138 ************************************ 1805 + 1 *)
ML{* (Ty'.check ([(OCL.Writeln , "Saving1 .owner = Set{ Client1 }") , (OCL.Writeln , "Saving1 .bank = Set{ Bank1 }") , (OCL.Writeln , "Client1 .banks = Set{ Bank1 }") , (OCL.Writeln , "Client1 .c_accounts = Set{ Saving1 , Account1 }") , (OCL.Writeln , "Account1 .owner = Set{ Client1 }") , (OCL.Writeln , "Account1 .bank = Set{ Bank1 }") , (OCL.Writeln , "Bank1 .clients = Set{ Client1 }") , (OCL.Writeln , "Bank1 .b_accounts = Set{ Saving1 , Account1 }")]) (" error(s)")) *}

(* 139 ************************************ 1806 + 3 *)
generation_syntax [ shallow ]
setup{* (Generation_mode.update_compiler_config ((K (let open OCL in Ocl_compiler_config_ext (true, NONE, Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 3), (Code_Numeral.Nat 7)), I ((Code_Numeral.Nat 0), (Code_Numeral.Nat 0)), Gen_default, SOME (OclClass ((OCL.SS_base (OCL.ST "OclAny")), nil, uncurry cons (OclClass ((OCL.SS_base (OCL.ST "Client")), uncurry cons (I ((OCL.SS_base (OCL.ST "c_accounts")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((OCL.SS_base (OCL.ST "oid")), (Code_Numeral.Nat 1), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), NONE), nil), SOME ((OCL.SS_base (OCL.ST "owner"))), nil, ()), (OCL.SS_base (OCL.ST "Client")), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "c_accounts"))), nil, ()), (OCL.SS_base (OCL.ST "Account")), ()), ())), nil))), uncurry cons (I ((OCL.SS_base (OCL.ST "banks")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((OCL.SS_base (OCL.ST "oid")), (Code_Numeral.Nat 0), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "clients"))), nil, ()), (OCL.SS_base (OCL.ST "Client")), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "banks"))), nil, ()), (OCL.SS_base (OCL.ST "Bank")), ()), ())), nil))), uncurry cons (I ((OCL.SS_base (OCL.ST "clientname")), OclTy_base_string), uncurry cons (I ((OCL.SS_base (OCL.ST "address")), OclTy_base_string), uncurry cons (I ((OCL.SS_base (OCL.ST "age")), OclTy_base_integer), nil))))), nil), uncurry cons (OclClass ((OCL.SS_base (OCL.ST "Bank")), uncurry cons (I ((OCL.SS_base (OCL.ST "b_accounts")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((OCL.SS_base (OCL.ST "oid")), (Code_Numeral.Nat 2), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), NONE), nil), SOME ((OCL.SS_base (OCL.ST "bank"))), nil, ()), (OCL.SS_base (OCL.ST "Bank")), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "b_accounts"))), nil, ()), (OCL.SS_base (OCL.ST "Account")), ()), ())), nil))), uncurry cons (I ((OCL.SS_base (OCL.ST "clients")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((OCL.SS_base (OCL.ST "oid")), (Code_Numeral.Nat 0), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "banks"))), nil, ()), (OCL.SS_base (OCL.ST "Bank")), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "clients"))), nil, ()), (OCL.SS_base (OCL.ST "Client")), ()), ())), nil))), uncurry cons (I ((OCL.SS_base (OCL.ST "name")), OclTy_base_string), nil))), nil), uncurry cons (OclClass ((OCL.SS_base (OCL.ST "Account")), uncurry cons (I ((OCL.SS_base (OCL.ST "bank")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((OCL.SS_base (OCL.ST "oid")), (Code_Numeral.Nat 2), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "b_accounts"))), nil, ()), (OCL.SS_base (OCL.ST "Account")), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), NONE), nil), SOME ((OCL.SS_base (OCL.ST "bank"))), nil, ()), (OCL.SS_base (OCL.ST "Bank")), ()), ())), nil))), uncurry cons (I ((OCL.SS_base (OCL.ST "owner")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((OCL.SS_base (OCL.ST "oid")), (Code_Numeral.Nat 1), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "c_accounts"))), nil, ()), (OCL.SS_base (OCL.ST "Account")), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), NONE), nil), SOME ((OCL.SS_base (OCL.ST "owner"))), nil, ()), (OCL.SS_base (OCL.ST "Client")), ()), ())), nil))), uncurry cons (I ((OCL.SS_base (OCL.ST "id")), OclTy_base_integer), uncurry cons (I ((OCL.SS_base (OCL.ST "balance")), OclTy_class_syn ((OCL.SS_base (OCL.ST "Currency")))), nil)))), uncurry cons (OclClass ((OCL.SS_base (OCL.ST "Savings")), uncurry cons (I ((OCL.SS_base (OCL.ST "max")), OclTy_class_syn ((OCL.SS_base (OCL.ST "Currency")))), nil), nil), uncurry cons (OclClass ((OCL.SS_base (OCL.ST "Current")), uncurry cons (I ((OCL.SS_base (OCL.ST "overdraft")), OclTy_class_syn ((OCL.SS_base (OCL.ST "Currency")))), nil), nil), nil))), nil))))), uncurry cons (OclAstInstance (OclInstance (uncurry cons (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Saving1"))), (OCL.SS_base (OCL.ST "Account")), OclAttrCast ((OCL.SS_base (OCL.ST "Savings")), OclAttrNoCast (uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "max")), ShallB_term (OclDefInteger ((OCL.SS_base (OCL.ST "2000")))))), nil)), nil), ()), uncurry cons (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Client1"))), (OCL.SS_base (OCL.ST "Client")), OclAttrNoCast (uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "c_accounts")), ShallB_str ((OCL.SS_base (OCL.ST "Saving1"))))), uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "banks")), ShallB_str ((OCL.SS_base (OCL.ST "Bank1"))))), nil))), ()), uncurry cons (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Account1"))), (OCL.SS_base (OCL.ST "Account")), OclAttrNoCast (uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "id")), ShallB_term (OclDefInteger ((OCL.SS_base (OCL.ST "250")))))), uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "owner")), ShallB_str ((OCL.SS_base (OCL.ST "Client1"))))), nil))), ()), uncurry cons (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Bank1"))), (OCL.SS_base (OCL.ST "Bank")), OclAttrNoCast (uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "b_accounts")), ShallB_list (uncurry cons (ShallB_str ((OCL.SS_base (OCL.ST "Saving1"))), uncurry cons (ShallB_str ((OCL.SS_base (OCL.ST "Account1"))), nil))))), uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "name")), ShallB_term (OclDefString ((OCL.SS_base (OCL.ST "\<infinity>\<heartsuit> \<Longleftrightarrow> \<infinity>\<epsilon>")))))), nil))), ()), nil)))))), uncurry cons (OclAstClassSynonym (OclClassSynonym ((OCL.SS_base (OCL.ST "Currency")), OclTy_base_real)), uncurry cons (OclAstClassRaw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Current"))), uncurry cons (uncurry cons (OclTyCore_pre ((OCL.SS_base (OCL.ST "Account"))), nil), nil)), uncurry cons (I ((OCL.SS_base (OCL.ST "overdraft")), OclTy_object (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Currency"))), nil))), nil), nil, false, ())), uncurry cons (OclAstClassRaw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Savings"))), uncurry cons (uncurry cons (OclTyCore_pre ((OCL.SS_base (OCL.ST "Account"))), nil), nil)), uncurry cons (I ((OCL.SS_base (OCL.ST "max")), OclTy_object (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Currency"))), nil))), nil), nil, false, ())), uncurry cons (OclAstAssociation (Ocl_association_ext (OclAssTy_association, OclAssRel (uncurry cons (I (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Account"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "b_accounts"))), nil, ())), uncurry cons (I (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Bank"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), NONE), nil), SOME ((OCL.SS_base (OCL.ST "bank"))), nil, ())), nil))), ())), uncurry cons (OclAstAssociation (Ocl_association_ext (OclAssTy_association, OclAssRel (uncurry cons (I (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Account"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "c_accounts"))), nil, ())), uncurry cons (I (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Client"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), NONE), nil), SOME ((OCL.SS_base (OCL.ST "owner"))), nil, ())), nil))), ())), uncurry cons (OclAstAssociation (Ocl_association_ext (OclAssTy_association, OclAssRel (uncurry cons (I (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Bank"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "banks"))), nil, ())), uncurry cons (I (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Client"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "clients"))), nil, ())), nil))), ())), uncurry cons (OclAstClassRaw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Account"))), nil), uncurry cons (I ((OCL.SS_base (OCL.ST "id")), OclTy_base_integer), uncurry cons (I ((OCL.SS_base (OCL.ST "balance")), OclTy_object (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Currency"))), nil))), nil)), nil, false, ())), uncurry cons (OclAstClassRaw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Client"))), nil), uncurry cons (I ((OCL.SS_base (OCL.ST "clientname")), OclTy_base_string), uncurry cons (I ((OCL.SS_base (OCL.ST "address")), OclTy_base_string), uncurry cons (I ((OCL.SS_base (OCL.ST "age")), OclTy_base_integer), nil))), nil, false, ())), uncurry cons (OclAstClassRaw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Bank"))), nil), uncurry cons (I ((OCL.SS_base (OCL.ST "name")), OclTy_base_string), nil), nil, false, ())), nil)))))))))), uncurry cons (I ((OCL.ST "Bank1"), I (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Bank1"))), (OCL.SS_base (OCL.ST "Bank")), OclAttrNoCast (uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "b_accounts")), ShallB_list (uncurry cons (ShallB_str ((OCL.SS_base (OCL.ST "Saving1"))), uncurry cons (ShallB_str ((OCL.SS_base (OCL.ST "Account1"))), nil))))), uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "name")), ShallB_term (OclDefString ((OCL.SS_base (OCL.ST "\<infinity>\<heartsuit> \<Longleftrightarrow> \<infinity>\<epsilon>")))))), nil))), ()), Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 3), (Code_Numeral.Nat 6)))), uncurry cons (I ((OCL.ST "Account1"), I (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Account1"))), (OCL.SS_base (OCL.ST "Account")), OclAttrNoCast (uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "id")), ShallB_term (OclDefInteger ((OCL.SS_base (OCL.ST "250")))))), uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "owner")), ShallB_str ((OCL.SS_base (OCL.ST "Client1"))))), nil))), ()), Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 3), (Code_Numeral.Nat 5)))), uncurry cons (I ((OCL.ST "Client1"), I (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Client1"))), (OCL.SS_base (OCL.ST "Client")), OclAttrNoCast (uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "c_accounts")), ShallB_str ((OCL.SS_base (OCL.ST "Saving1"))))), uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "banks")), ShallB_str ((OCL.SS_base (OCL.ST "Bank1"))))), nil))), ()), Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 3), (Code_Numeral.Nat 4)))), uncurry cons (I ((OCL.ST "Saving1"), I (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Saving1"))), (OCL.SS_base (OCL.ST "Account")), OclAttrCast ((OCL.SS_base (OCL.ST "Savings")), OclAttrNoCast (uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "max")), ShallB_term (OclDefInteger ((OCL.SS_base (OCL.ST "2000")))))), nil)), nil), ()), Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 3), (Code_Numeral.Nat 3)))), nil)))), nil, true, false, I (uncurry cons ((OCL.ST "dot\<a>\<g>\<e>at_pre"), uncurry cons ((OCL.ST "dot\<a>\<d>\<d>\<r>\<e>\<s>\<s>at_pre"), uncurry cons ((OCL.ST "dot\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e>at_pre"), uncurry cons ((OCL.ST "dot_1_\<b>\<a>\<n>\<k>\<s>at_pre"), uncurry cons ((OCL.ST "dot_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>at_pre"), uncurry cons ((OCL.ST "dot\<n>\<a>\<m>\<e>at_pre"), uncurry cons ((OCL.ST "dot_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s>at_pre"), uncurry cons ((OCL.ST "dot_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>at_pre"), uncurry cons ((OCL.ST "dot\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre"), uncurry cons ((OCL.ST "dot\<i>\<d>at_pre"), uncurry cons ((OCL.ST "dot_0_\<o>\<w>\<n>\<e>\<r>at_pre"), uncurry cons ((OCL.ST "dot_0_\<b>\<a>\<n>\<k>at_pre"), uncurry cons ((OCL.ST "dot\<m>\<a>\<x>at_pre"), uncurry cons ((OCL.ST "dot\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t>at_pre"), nil)))))))))))))), uncurry cons ((OCL.ST "dot\<a>\<g>\<e>"), uncurry cons ((OCL.ST "dot\<a>\<d>\<d>\<r>\<e>\<s>\<s>"), uncurry cons ((OCL.ST "dot\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e>"), uncurry cons ((OCL.ST "dot_1_\<b>\<a>\<n>\<k>\<s>"), uncurry cons ((OCL.ST "dot_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>"), uncurry cons ((OCL.ST "dot\<n>\<a>\<m>\<e>"), uncurry cons ((OCL.ST "dot_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s>"), uncurry cons ((OCL.ST "dot_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>"), uncurry cons ((OCL.ST "dot\<b>\<a>\<l>\<a>\<n>\<c>\<e>"), uncurry cons ((OCL.ST "dot\<i>\<d>"), uncurry cons ((OCL.ST "dot_0_\<o>\<w>\<n>\<e>\<r>"), uncurry cons ((OCL.ST "dot_0_\<b>\<a>\<n>\<k>"), uncurry cons ((OCL.ST "dot\<m>\<a>\<x>"), uncurry cons ((OCL.ST "dot\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t>"), nil))))))))))))))), uncurry cons ((OCL.ST "Sequence_Client"), uncurry cons ((OCL.ST "Set_Client"), uncurry cons ((OCL.ST "Sequence_Bank"), uncurry cons ((OCL.ST "Set_Bank"), uncurry cons ((OCL.ST "Sequence_Account"), uncurry cons ((OCL.ST "Set_Account"), nil)))))), I (NONE, false), ()) end)))) *}
State[shallow] \<sigma>\<^sub>1' = [ Account1, Client1, Bank1, Saving1 ]

(* 140 ************************************ 1809 + 1 *)
State[shallow] ss = [  ]

(* 141 ************************************ 1810 + 1 *)
PrePost[shallow] ss \<sigma>\<^sub>1'

(* 142 ************************************ 1811 + 2 *)
definition OclInt25 ("\<two>\<five>")
  where "OclInt25 = (\<lambda>_. \<lfloor>\<lfloor>25\<rfloor>\<rfloor>)"
definition OclReal250_0 ("\<two>\<five>\<zero>.\<zero>")
  where "OclReal250_0 = (\<lambda>_. \<lfloor>\<lfloor>250\<rfloor>\<rfloor>)"

(* 143 ************************************ 1813 + 2 *)
setup{* (Generation_mode.update_compiler_config ((K (let open OCL in Ocl_compiler_config_ext (true, NONE, Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 3), (Code_Numeral.Nat 7)), I ((Code_Numeral.Nat 0), (Code_Numeral.Nat 0)), Gen_default, SOME (OclClass ((OCL.SS_base (OCL.ST "OclAny")), nil, uncurry cons (OclClass ((OCL.SS_base (OCL.ST "Client")), uncurry cons (I ((OCL.SS_base (OCL.ST "c_accounts")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((OCL.SS_base (OCL.ST "oid")), (Code_Numeral.Nat 1), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), NONE), nil), SOME ((OCL.SS_base (OCL.ST "owner"))), nil, ()), (OCL.SS_base (OCL.ST "Client")), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "c_accounts"))), nil, ()), (OCL.SS_base (OCL.ST "Account")), ()), ())), nil))), uncurry cons (I ((OCL.SS_base (OCL.ST "banks")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((OCL.SS_base (OCL.ST "oid")), (Code_Numeral.Nat 0), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "clients"))), nil, ()), (OCL.SS_base (OCL.ST "Client")), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "banks"))), nil, ()), (OCL.SS_base (OCL.ST "Bank")), ()), ())), nil))), uncurry cons (I ((OCL.SS_base (OCL.ST "clientname")), OclTy_base_string), uncurry cons (I ((OCL.SS_base (OCL.ST "address")), OclTy_base_string), uncurry cons (I ((OCL.SS_base (OCL.ST "age")), OclTy_base_integer), nil))))), nil), uncurry cons (OclClass ((OCL.SS_base (OCL.ST "Bank")), uncurry cons (I ((OCL.SS_base (OCL.ST "b_accounts")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((OCL.SS_base (OCL.ST "oid")), (Code_Numeral.Nat 2), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), NONE), nil), SOME ((OCL.SS_base (OCL.ST "bank"))), nil, ()), (OCL.SS_base (OCL.ST "Bank")), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "b_accounts"))), nil, ()), (OCL.SS_base (OCL.ST "Account")), ()), ())), nil))), uncurry cons (I ((OCL.SS_base (OCL.ST "clients")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((OCL.SS_base (OCL.ST "oid")), (Code_Numeral.Nat 0), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "banks"))), nil, ()), (OCL.SS_base (OCL.ST "Bank")), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "clients"))), nil, ()), (OCL.SS_base (OCL.ST "Client")), ()), ())), nil))), uncurry cons (I ((OCL.SS_base (OCL.ST "name")), OclTy_base_string), nil))), nil), uncurry cons (OclClass ((OCL.SS_base (OCL.ST "Account")), uncurry cons (I ((OCL.SS_base (OCL.ST "bank")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((OCL.SS_base (OCL.ST "oid")), (Code_Numeral.Nat 2), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "b_accounts"))), nil, ()), (OCL.SS_base (OCL.ST "Account")), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), NONE), nil), SOME ((OCL.SS_base (OCL.ST "bank"))), nil, ()), (OCL.SS_base (OCL.ST "Bank")), ()), ())), nil))), uncurry cons (I ((OCL.SS_base (OCL.ST "owner")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((OCL.SS_base (OCL.ST "oid")), (Code_Numeral.Nat 1), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "c_accounts"))), nil, ()), (OCL.SS_base (OCL.ST "Account")), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), NONE), nil), SOME ((OCL.SS_base (OCL.ST "owner"))), nil, ()), (OCL.SS_base (OCL.ST "Client")), ()), ())), nil))), uncurry cons (I ((OCL.SS_base (OCL.ST "id")), OclTy_base_integer), uncurry cons (I ((OCL.SS_base (OCL.ST "balance")), OclTy_class_syn ((OCL.SS_base (OCL.ST "Currency")))), nil)))), uncurry cons (OclClass ((OCL.SS_base (OCL.ST "Savings")), uncurry cons (I ((OCL.SS_base (OCL.ST "max")), OclTy_class_syn ((OCL.SS_base (OCL.ST "Currency")))), nil), nil), uncurry cons (OclClass ((OCL.SS_base (OCL.ST "Current")), uncurry cons (I ((OCL.SS_base (OCL.ST "overdraft")), OclTy_class_syn ((OCL.SS_base (OCL.ST "Currency")))), nil), nil), nil))), nil))))), uncurry cons (OclAstDefBaseL (OclDefBase (uncurry cons (OclDefInteger ((OCL.SS_base (OCL.ST "25"))), uncurry cons (OclDefReal (I ((OCL.SS_base (OCL.ST "250")), (OCL.SS_base (OCL.ST "0")))), nil)))), uncurry cons (OclAstDefPrePost (Floor1, OclDefPP (NONE, OclDefPPCoreBinding ((OCL.SS_base (OCL.ST "ss"))), SOME (OclDefPPCoreBinding ((OCL.SS_base (OCL.ST "\<sigma>\<^sub>1'")))))), uncurry cons (OclAstDefState (Floor1, OclDefSt ((OCL.SS_base (OCL.ST "ss")), nil)), uncurry cons (OclAstDefState (Floor1, OclDefSt ((OCL.SS_base (OCL.ST "\<sigma>\<^sub>1'")), uncurry cons (OclDefCoreBinding ((OCL.SS_base (OCL.ST "Account1"))), uncurry cons (OclDefCoreBinding ((OCL.SS_base (OCL.ST "Client1"))), uncurry cons (OclDefCoreBinding ((OCL.SS_base (OCL.ST "Bank1"))), uncurry cons (OclDefCoreBinding ((OCL.SS_base (OCL.ST "Saving1"))), nil)))))), uncurry cons (OclAstInstance (OclInstance (uncurry cons (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Saving1"))), (OCL.SS_base (OCL.ST "Account")), OclAttrCast ((OCL.SS_base (OCL.ST "Savings")), OclAttrNoCast (uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "max")), ShallB_term (OclDefInteger ((OCL.SS_base (OCL.ST "2000")))))), nil)), nil), ()), uncurry cons (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Client1"))), (OCL.SS_base (OCL.ST "Client")), OclAttrNoCast (uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "c_accounts")), ShallB_str ((OCL.SS_base (OCL.ST "Saving1"))))), uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "banks")), ShallB_str ((OCL.SS_base (OCL.ST "Bank1"))))), nil))), ()), uncurry cons (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Account1"))), (OCL.SS_base (OCL.ST "Account")), OclAttrNoCast (uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "id")), ShallB_term (OclDefInteger ((OCL.SS_base (OCL.ST "250")))))), uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "owner")), ShallB_str ((OCL.SS_base (OCL.ST "Client1"))))), nil))), ()), uncurry cons (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Bank1"))), (OCL.SS_base (OCL.ST "Bank")), OclAttrNoCast (uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "b_accounts")), ShallB_list (uncurry cons (ShallB_str ((OCL.SS_base (OCL.ST "Saving1"))), uncurry cons (ShallB_str ((OCL.SS_base (OCL.ST "Account1"))), nil))))), uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "name")), ShallB_term (OclDefString ((OCL.SS_base (OCL.ST "\<infinity>\<heartsuit> \<Longleftrightarrow> \<infinity>\<epsilon>")))))), nil))), ()), nil)))))), uncurry cons (OclAstClassSynonym (OclClassSynonym ((OCL.SS_base (OCL.ST "Currency")), OclTy_base_real)), uncurry cons (OclAstClassRaw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Current"))), uncurry cons (uncurry cons (OclTyCore_pre ((OCL.SS_base (OCL.ST "Account"))), nil), nil)), uncurry cons (I ((OCL.SS_base (OCL.ST "overdraft")), OclTy_object (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Currency"))), nil))), nil), nil, false, ())), uncurry cons (OclAstClassRaw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Savings"))), uncurry cons (uncurry cons (OclTyCore_pre ((OCL.SS_base (OCL.ST "Account"))), nil), nil)), uncurry cons (I ((OCL.SS_base (OCL.ST "max")), OclTy_object (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Currency"))), nil))), nil), nil, false, ())), uncurry cons (OclAstAssociation (Ocl_association_ext (OclAssTy_association, OclAssRel (uncurry cons (I (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Account"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "b_accounts"))), nil, ())), uncurry cons (I (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Bank"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), NONE), nil), SOME ((OCL.SS_base (OCL.ST "bank"))), nil, ())), nil))), ())), uncurry cons (OclAstAssociation (Ocl_association_ext (OclAssTy_association, OclAssRel (uncurry cons (I (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Account"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "c_accounts"))), nil, ())), uncurry cons (I (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Client"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), NONE), nil), SOME ((OCL.SS_base (OCL.ST "owner"))), nil, ())), nil))), ())), uncurry cons (OclAstAssociation (Ocl_association_ext (OclAssTy_association, OclAssRel (uncurry cons (I (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Bank"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "banks"))), nil, ())), uncurry cons (I (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Client"))), nil), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 1)), SOME (Mult_star)), nil), SOME ((OCL.SS_base (OCL.ST "clients"))), nil, ())), nil))), ())), uncurry cons (OclAstClassRaw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Account"))), nil), uncurry cons (I ((OCL.SS_base (OCL.ST "id")), OclTy_base_integer), uncurry cons (I ((OCL.SS_base (OCL.ST "balance")), OclTy_object (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Currency"))), nil))), nil)), nil, false, ())), uncurry cons (OclAstClassRaw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Client"))), nil), uncurry cons (I ((OCL.SS_base (OCL.ST "clientname")), OclTy_base_string), uncurry cons (I ((OCL.SS_base (OCL.ST "address")), OclTy_base_string), uncurry cons (I ((OCL.SS_base (OCL.ST "age")), OclTy_base_integer), nil))), nil, false, ())), uncurry cons (OclAstClassRaw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((OCL.SS_base (OCL.ST "Bank"))), nil), uncurry cons (I ((OCL.SS_base (OCL.ST "name")), OclTy_base_string), nil), nil, false, ())), nil)))))))))))))), uncurry cons (I ((OCL.ST "Bank1"), I (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Bank1"))), (OCL.SS_base (OCL.ST "Bank")), OclAttrNoCast (uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "b_accounts")), ShallB_list (uncurry cons (ShallB_str ((OCL.SS_base (OCL.ST "Saving1"))), uncurry cons (ShallB_str ((OCL.SS_base (OCL.ST "Account1"))), nil))))), uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "name")), ShallB_term (OclDefString ((OCL.SS_base (OCL.ST "\<infinity>\<heartsuit> \<Longleftrightarrow> \<infinity>\<epsilon>")))))), nil))), ()), Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 3), (Code_Numeral.Nat 6)))), uncurry cons (I ((OCL.ST "Account1"), I (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Account1"))), (OCL.SS_base (OCL.ST "Account")), OclAttrNoCast (uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "id")), ShallB_term (OclDefInteger ((OCL.SS_base (OCL.ST "250")))))), uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "owner")), ShallB_str ((OCL.SS_base (OCL.ST "Client1"))))), nil))), ()), Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 3), (Code_Numeral.Nat 5)))), uncurry cons (I ((OCL.ST "Client1"), I (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Client1"))), (OCL.SS_base (OCL.ST "Client")), OclAttrNoCast (uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "c_accounts")), ShallB_str ((OCL.SS_base (OCL.ST "Saving1"))))), uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "banks")), ShallB_str ((OCL.SS_base (OCL.ST "Bank1"))))), nil))), ()), Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 3), (Code_Numeral.Nat 4)))), uncurry cons (I ((OCL.ST "Saving1"), I (Ocl_instance_single_ext (SOME ((OCL.SS_base (OCL.ST "Saving1"))), (OCL.SS_base (OCL.ST "Account")), OclAttrCast ((OCL.SS_base (OCL.ST "Savings")), OclAttrNoCast (uncurry cons (I (NONE, I ((OCL.SS_base (OCL.ST "max")), ShallB_term (OclDefInteger ((OCL.SS_base (OCL.ST "2000")))))), nil)), nil), ()), Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 3), (Code_Numeral.Nat 3)))), nil)))), nil, true, true, I (uncurry cons ((OCL.ST "dot\<a>\<g>\<e>at_pre"), uncurry cons ((OCL.ST "dot\<a>\<d>\<d>\<r>\<e>\<s>\<s>at_pre"), uncurry cons ((OCL.ST "dot\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e>at_pre"), uncurry cons ((OCL.ST "dot_1_\<b>\<a>\<n>\<k>\<s>at_pre"), uncurry cons ((OCL.ST "dot_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>at_pre"), uncurry cons ((OCL.ST "dot\<n>\<a>\<m>\<e>at_pre"), uncurry cons ((OCL.ST "dot_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s>at_pre"), uncurry cons ((OCL.ST "dot_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>at_pre"), uncurry cons ((OCL.ST "dot\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre"), uncurry cons ((OCL.ST "dot\<i>\<d>at_pre"), uncurry cons ((OCL.ST "dot_0_\<o>\<w>\<n>\<e>\<r>at_pre"), uncurry cons ((OCL.ST "dot_0_\<b>\<a>\<n>\<k>at_pre"), uncurry cons ((OCL.ST "dot\<m>\<a>\<x>at_pre"), uncurry cons ((OCL.ST "dot\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t>at_pre"), nil)))))))))))))), uncurry cons ((OCL.ST "dot\<a>\<g>\<e>"), uncurry cons ((OCL.ST "dot\<a>\<d>\<d>\<r>\<e>\<s>\<s>"), uncurry cons ((OCL.ST "dot\<c>\<l>\<i>\<e>\<n>\<t>\<n>\<a>\<m>\<e>"), uncurry cons ((OCL.ST "dot_1_\<b>\<a>\<n>\<k>\<s>"), uncurry cons ((OCL.ST "dot_1_\<c>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>"), uncurry cons ((OCL.ST "dot\<n>\<a>\<m>\<e>"), uncurry cons ((OCL.ST "dot_0_\<c>\<l>\<i>\<e>\<n>\<t>\<s>"), uncurry cons ((OCL.ST "dot_1_\<b>095\<a>\<c>\<c>\<o>\<u>\<n>\<t>\<s>"), uncurry cons ((OCL.ST "dot\<b>\<a>\<l>\<a>\<n>\<c>\<e>"), uncurry cons ((OCL.ST "dot\<i>\<d>"), uncurry cons ((OCL.ST "dot_0_\<o>\<w>\<n>\<e>\<r>"), uncurry cons ((OCL.ST "dot_0_\<b>\<a>\<n>\<k>"), uncurry cons ((OCL.ST "dot\<m>\<a>\<x>"), uncurry cons ((OCL.ST "dot\<o>\<v>\<e>\<r>\<d>\<r>\<a>\<f>\<t>"), nil))))))))))))))), uncurry cons ((OCL.ST "Sequence_Client"), uncurry cons ((OCL.ST "Set_Client"), uncurry cons ((OCL.ST "Sequence_Bank"), uncurry cons ((OCL.ST "Set_Bank"), uncurry cons ((OCL.ST "Sequence_Account"), uncurry cons ((OCL.ST "Set_Account"), nil)))))), I (NONE, false), ()) end)))) *}
Context[shallow] c : Savings   Inv  : "(\<lambda> self c. (\<zero>.\<zero> <\<^sub>r\<^sub>e\<^sub>a\<^sub>l (c .max)))"
  Inv  : "(\<lambda> self c. (c .balance \<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l (c .max) and \<zero>.\<zero> \<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l (c .balance)))"

(* 144 ************************************ 1815 + 1 *)
Context[shallow] c : Current   Inv  : "(\<lambda> self c. (\<two>\<five> \<le>\<^sub>i\<^sub>n\<^sub>t (c .owner .age) implies (c .overdraft \<doteq> \<two>\<five>\<zero>.\<zero>)))"
  Inv  : "(\<lambda> self c. (c .owner .age <\<^sub>i\<^sub>n\<^sub>t \<two>\<five>   implies (c .overdraft \<doteq> \<zero>.\<zero>)))"

(* 145 ************************************ 1816 + 1 *)
Context[shallow] c : Client   Inv  : "(\<lambda> self c. (c .banks ->forAll\<^sub>S\<^sub>e\<^sub>t(b | b .b_accounts ->select\<^sub>S\<^sub>e\<^sub>t(a | (a .owner \<doteq> c) and
                                                                  (a .oclIsTypeOf(Current)))
                                             ->size\<^sub>S\<^sub>e\<^sub>t() \<le>\<^sub>i\<^sub>n\<^sub>t \<one>)))"

(* 146 ************************************ 1817 + 3 *)
consts dot\<c>\<r>\<e>\<a>\<t>\<e>095\<c>\<l>\<i>\<e>\<n>\<t> :: "(\<AA>, '\<alpha>) val \<Rightarrow> (String) \<Rightarrow> (Integer) \<Rightarrow> (\<cdot>Bank) \<Rightarrow> (Integer)" ("(_) .create'_client'((_),(_),(_)')")
consts dot\<c>\<r>\<e>\<a>\<t>\<e>095\<c>\<l>\<i>\<e>\<n>\<t>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> (String) \<Rightarrow> (Integer) \<Rightarrow> (\<cdot>Bank) \<Rightarrow> (Integer)" ("(_) .create'_client@pre'((_),(_),(_)')")
Context[shallow] Bank :: create_client (clientname : String, age : Integer, bank : Bank) : Integer
  Pre : "(\<lambda> bank age clientname self. (bank .clients ->forAll\<^sub>S\<^sub>e\<^sub>t(c | c .clientname <> clientname or (c .age <> age))))"
  Post : "(\<lambda> bank age clientname self result. (bank .clients ->exists\<^sub>S\<^sub>e\<^sub>t(c | c .clientname \<doteq> clientname and (c .age \<doteq> age))))"

(* 147 ************************************ 1820 + 3 *)
consts dot\<g>\<e>\<t>095\<b>\<a>\<l>\<a>\<n>\<c>\<e> :: "(\<AA>, '\<alpha>) val \<Rightarrow> (String) \<Rightarrow> (Integer) \<Rightarrow> (Real)" ("(_) .get'_balance'((_),(_)')")
consts dot\<g>\<e>\<t>095\<b>\<a>\<l>\<a>\<n>\<c>\<e>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> (String) \<Rightarrow> (Integer) \<Rightarrow> (Real)" ("(_) .get'_balance@pre'((_),(_)')")
Context[shallow] Account :: get_balance (c : String, no : Integer) : Real
  Pre : "(\<lambda> no c self. (self .id \<doteq> no and ((self .owner .clientname) \<doteq> c)))"
  Post : "(\<lambda> no c self result. (result \<doteq> (self .balance)))"

(* 148 ************************************ 1823 + 3 *)
consts dot\<d>\<e>\<p>\<o>\<s>\<i>\<t> :: "(\<AA>, '\<alpha>) val \<Rightarrow> (String) \<Rightarrow> (Integer) \<Rightarrow> (Real) \<Rightarrow> (Real)" ("(_) .deposit'((_),(_),(_)')")
consts dot\<d>\<e>\<p>\<o>\<s>\<i>\<t>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> (String) \<Rightarrow> (Integer) \<Rightarrow> (Real) \<Rightarrow> (Real)" ("(_) .deposit@pre'((_),(_),(_)')")
Context[shallow] Account :: deposit (c : String, no : Integer, amount : Real) : Real
  Pre : "(\<lambda> amount no c self. (self .id \<doteq> no and ((self .owner .clientname) \<doteq> c) and (\<zero>.\<zero>  \<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l amount)))"
  Post : "(\<lambda> amount no c self result. (self .balance \<doteq> (self .balance@pre +\<^sub>r\<^sub>e\<^sub>a\<^sub>l amount)))"

(* 149 ************************************ 1826 + 3 *)
consts dot\<w>\<i>\<t>\<h>\<d>\<r>\<a>\<w> :: "(\<AA>, '\<alpha>) val \<Rightarrow> (String) \<Rightarrow> (Integer) \<Rightarrow> (Real) \<Rightarrow> (Real)" ("(_) .withdraw'((_),(_),(_)')")
consts dot\<w>\<i>\<t>\<h>\<d>\<r>\<a>\<w>at_pre :: "(\<AA>, '\<alpha>) val \<Rightarrow> (String) \<Rightarrow> (Integer) \<Rightarrow> (Real) \<Rightarrow> (Real)" ("(_) .withdraw@pre'((_),(_),(_)')")
Context[shallow] Account :: withdraw (c : String, no : Integer, amount : Real) : Real
  Pre : "(\<lambda> amount no c self. (self .id \<doteq> no and ((self .owner .clientname) \<doteq> c) and (\<zero>.\<zero>  \<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l amount)))"
  Post : "(\<lambda> amount no c self result. (self .balance \<doteq> (self .balance@pre -\<^sub>r\<^sub>e\<^sub>a\<^sub>l amount)))"

end
