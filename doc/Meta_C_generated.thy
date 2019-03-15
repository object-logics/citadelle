theory Meta_C_generated imports "../src/UML_Main"   "../src/compiler/Static"   "../examples/C_Model_init" begin

(* 1 ************************************ 0 + 0 *)  (* term Floor1_infra.print_infra_enum_synonym *)

(* 2 ************************************ 0 + 1 *)
text \<open>\<close>

(* 3 ************************************ 1 + 1 *)
text \<open>
   \label{ex:Meta-C-generatedemployee-analysis:uml} \<close>

(* 4 ************************************ 2 + 1 *)
section \<open>Class Model: Introduction\<close>

(* 5 ************************************ 3 + 1 *)
text \<open>

  For certain concepts like classes and class-types, only a generic
  definition for its resulting semantics can be given. Generic means,
  there is a function outside \HOL that ``compiles'' a concrete,
  closed-world class diagram into a ``theory'' of this data model,
  consisting of a bunch of definitions for classes, accessors, method,
  casts, and tests for actual types, as well as proofs for the
  fundamental properties of these operations in this concrete data
  model. \<close>

(* 6 ************************************ 4 + 1 *)
text \<open>
   Such generic function or ``compiler'' can be implemented in
  Isabelle on the \ML level.  This has been done, for a semantics
  following the open-world assumption, for \UML 2.0
  in~\cite{brucker.ea:extensible:2008-b, brucker:interactive:2007}. In
  this paper, we follow another approach for \UML 2.4: we define the
  concepts of the compilation informally, and present a concrete
  example which is verified in Isabelle/\HOL. \<close>

(* 7 ************************************ 5 + 1 *)
subsection \<open>Outlining the Example\<close>

(* 8 ************************************ 6 + 1 *)
text \<open>\<close>

(* 9 ************************************ 7 + 1 *)
text \<open>
   We are presenting here an ``analysis-model'' of the (slightly
modified) example Figure 7.3, page 20 of
the \OCL standard~\cite{omg:ocl:2012}.
Here, analysis model means that associations
were really represented as relation on objects on the state---as is
intended by the standard---rather by pointers between objects as is
done in our ``design model''.
To be precise, this theory contains the formalization of the data-part
covered by the \UML class model (see \autoref{fig:Meta-C-generatedperson-ana}):\<close>

(* 10 ************************************ 8 + 1 *)
text_raw \<open>\<close>

(* 11 ************************************ 9 + 1 *)
text_raw \<open>

\begin{figure}
  \centering\scalebox{.3}{\includegraphics{figures/person.png}}%
  \caption{A simple \UML class model drawn from Figure 7.3,
  page 20 of~\cite{omg:ocl:2012}. \label{fig:Meta-C-generatedperson-ana}}
\end{figure}
\<close>

(* 12 ************************************ 10 + 1 *)
text \<open>
   This means that the association (attached to the association class
\inlineocl{EmployeeRanking}) with the association ends \inlineocl+boss+ and \inlineocl+employees+ is implemented
by the attribute  \inlineocl+boss+ and the operation \inlineocl+employees+ (to be discussed in the \OCL part
captured by the subsequent theory).
\<close>

(* 13 ************************************ 11 + 1 *)
section \<open>Class Model: The Construction of the Object Universe\<close>

(* 14 ************************************ 12 + 1 *)
text \<open>
   Our data universe  consists in the concrete class diagram just of node's,
and implicitly of the class object. Each class implies the existence of a class
type defined for the corresponding object representations as follows: \<close>

(* 15 ************************************ 13 + 2 *)  (* term Floor1_infra.print_infra_datatype_class_1 *)
datatype ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y "oid"
datatype ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y "ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y"

(* 16 ************************************ 15 + 2 *)  (* term Floor1_infra.print_infra_datatype_class_2 *)
datatype ty2\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = mk2\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y 
datatype ty2oid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = mk2oid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y "oid" "ty2\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y"

(* 17 ************************************ 17 + 2 *)  (* term Floor1_infra.print_infra_datatype_equiv_2of1 *)
definition "class_ty_ext_equiv_2of1_aux\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = (\<lambda>oid. (\<lambda> (mk2\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ) \<Rightarrow> (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (oid))))))"
definition "class_ty_ext_equiv_2of1\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = (\<lambda> (mk2oid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (oid) (t)) \<Rightarrow> (class_ty_ext_equiv_2of1_aux\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (oid) (t)))"

(* 18 ************************************ 19 + 3 *)  (* term Floor1_infra.print_infra_datatype_equiv_1of2 *)
definition "class_ty_ext_equiv_1of2_get_oid_inh\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = (\<lambda> (mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (oid)) \<Rightarrow> (oid))"
definition "class_ty_ext_equiv_1of2_aux\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = (\<lambda> (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (t)) \<Rightarrow> (mk2\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ))"
definition "class_ty_ext_equiv_1of2\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = (\<lambda> (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (t)) \<Rightarrow> (case (class_ty_ext_equiv_1of2_get_oid_inh\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (t)) of (oid) \<Rightarrow> (mk2oid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (oid) ((class_ty_ext_equiv_1of2_aux\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (t))))))))"

(* 19 ************************************ 22 + 1 *)
text \<open>
   Now, we construct a concrete ``universe of OclAny types'' by injection into a
sum type containing the class types. This type of OclAny will be used as instance
for all respective type-variables. \<close>

(* 20 ************************************ 23 + 1 *)  (* term Floor1_infra.print_infra_datatype_universe *)
datatype \<AA> = in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y "ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y"

(* 21 ************************************ 24 + 1 *)
text \<open>
   Having fixed the object universe, we can introduce type synonyms that exactly correspond
to \OCL types. Again, we exploit that our representation of \OCL is a ``shallow embedding'' with a
one-to-one correspondance of \OCL-types to types of the meta-language \HOL. \<close>

(* 22 ************************************ 25 + 7 *)  (* term Floor1_infra.print_infra_type_synonym_class *)
type_synonym Void = "\<AA> Void"
type_synonym Boolean = "\<AA> Boolean"
type_synonym Integer = "\<AA> Integer"
type_synonym Real = "\<AA> Real"
type_synonym String = "\<AA> String"
type_synonym '\<alpha> val' = "(\<AA>, '\<alpha>) val"
type_notation val' ("\<cdot>(_)")

(* 23 ************************************ 32 + 1 *)  (* term Floor1_infra.print_infra_type_synonym_class_higher *)
type_synonym OclAny = "\<langle>\<langle>ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>"

(* 24 ************************************ 33 + 0 *)  (* term Floor1_infra.print_infra_type_synonym_class_rec *)

(* 25 ************************************ 33 + 0 *)  (* term Floor1_infra.print_infra_enum_syn *)

(* 26 ************************************ 33 + 1 *)
text \<open>
   To reuse key-elements of the library like referential equality, we have
to show that the object universe belongs to the type class ``oclany,'' \ie,
 each class type has to provide a function @{term oid_of} yielding the Object ID (oid) of the object. \<close>

(* 27 ************************************ 34 + 1 *)  (* term Floor1_infra.print_infra_instantiation_class *)
instantiation ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: object
begin
  definition oid_of_ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def : "oid_of = (\<lambda> mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y t \<Rightarrow> (case t of (mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (t)) \<Rightarrow> t))"
  instance ..
end

(* 28 ************************************ 35 + 1 *)  (* term Floor1_infra.print_infra_instantiation_universe *)
instantiation \<AA> :: object
begin
  definition oid_of_\<AA>_def : "oid_of = (\<lambda> in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y OclAny \<Rightarrow> oid_of OclAny)"
  instance ..
end

(* 29 ************************************ 36 + 1 *)
section \<open>Class Model: Instantiation of the Generic Strict Equality\<close>

(* 30 ************************************ 37 + 1 *)
text \<open>
   We instantiate the referential equality
on @{text "Person"} and @{text "OclAny"} \<close>

(* 31 ************************************ 38 + 1 *)  (* term Floor1_infra.print_instantia_def_strictrefeq *)
overloading StrictRefEq \<equiv> "(StrictRefEq::(\<cdot>OclAny) \<Rightarrow> _ \<Rightarrow> _)"
begin
  definition StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : "(x::\<cdot>OclAny) \<doteq> y \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
end

(* 32 ************************************ 39 + 1 *)  (* term Floor1_infra.print_instantia_lemmas_strictrefeq *)
lemmas[simp,code_unfold] = StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y

(* 33 ************************************ 40 + 1 *)
text \<open>
   For each Class \emph{C}, we will have a casting operation \inlineocl{.oclAsType($C$)},
   a test on the actual type \inlineocl{.oclIsTypeOf($C$)} as well as its relaxed form
   \inlineocl{.oclIsKindOf($C$)} (corresponding exactly to Java's \verb+instanceof+-operator.
\<close>

(* 34 ************************************ 41 + 1 *)
text \<open>
   Thus, since we have two class-types in our concrete class hierarchy, we have
two operations to declare and to provide two overloading definitions for the two static types.
\<close>

(* 35 ************************************ 42 + 1 *)
section \<open>Class Model: OclAsType\<close>

(* 36 ************************************ 43 + 1 *)
subsection \<open>Definition\<close>

(* 37 ************************************ 44 + 1 *)  (* term Floor1_astype.print_astype_consts *)
consts OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: "'\<alpha> \<Rightarrow> \<cdot>OclAny" ("(_) .oclAsType'(OclAny')")

(* 38 ************************************ 45 + 1 *)  (* term Floor1_astype.print_astype_class *)
overloading OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y \<equiv> "(OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y::(\<cdot>OclAny) \<Rightarrow> _)"
begin
  definition OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny : "(x::\<cdot>OclAny) .oclAsType(OclAny) \<equiv> x"
end

(* 39 ************************************ 46 + 1 *)  (* term Floor1_astype.print_astype_from_universe *)
definition "OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> = Some o (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> OclAny)"

(* 40 ************************************ 47 + 1 *)  (* term Floor1_astype.print_astype_lemmas_id *)
lemmas[simp,code_unfold] = OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny

(* 41 ************************************ 48 + 1 *)
subsection \<open>Context Passing\<close>

(* 42 ************************************ 49 + 1 *)  (* term Floor1_astype.print_astype_lemma_cp *)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclAsType(OclAny)))))"
sorry

(* 43 ************************************ 50 + 1 *)  (* term Floor1_astype.print_astype_lemmas_cp *)
lemmas[simp,code_unfold] = cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny

(* 44 ************************************ 51 + 1 *)
subsection \<open>Execution with Invalid or Null as Argument\<close>

(* 45 ************************************ 52 + 2 *)  (* term Floor1_astype.print_astype_lemma_strict *)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclAsType(OclAny)) = invalid"
sorry
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null : "((null::\<cdot>OclAny) .oclAsType(OclAny)) = null"
sorry

(* 46 ************************************ 54 + 1 *)  (* term Floor1_astype.print_astype_lemmas_strict *)
lemmas[simp,code_unfold] = OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid
                            OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null

(* 47 ************************************ 55 + 1 *)
subsection \<open>Validity and Definedness Properties\<close>

(* 48 ************************************ 56 + 0 *)  (* term Floor1_astype.print_astype_defined *)

(* 49 ************************************ 56 + 1 *)
subsection \<open>Up Down Casting\<close>

(* 50 ************************************ 57 + 0 *)  (* term Floor1_astype.print_astype_up_d_cast0 *)

(* 51 ************************************ 57 + 0 *)  (* term Floor1_astype.print_astype_up_d_cast *)

(* 52 ************************************ 57 + 0 *)  (* term Floor1_astype.print_astype_d_up_cast *)

(* 53 ************************************ 57 + 1 *)
subsection \<open>Const\<close>

(* 54 ************************************ 58 + 1 *)  (* term Floor1_astype.print_astype_lemma_const *)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_const : "(const ((X::\<cdot>OclAny))) \<Longrightarrow> (const (X .oclAsType(OclAny)))"
sorry

(* 55 ************************************ 59 + 1 *)  (* term Floor1_astype.print_astype_lemmas_const *)
lemmas[simp,code_unfold] = OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_const

(* 56 ************************************ 60 + 1 *)
section \<open>Class Model: OclIsTypeOf\<close>

(* 57 ************************************ 61 + 1 *)
subsection \<open>Definition\<close>

(* 58 ************************************ 62 + 1 *)  (* term Floor1_istypeof.print_istypeof_consts *)
consts OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsTypeOf'(OclAny')")

(* 59 ************************************ 63 + 1 *)  (* term Floor1_istypeof.print_istypeof_class *)
overloading OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y \<equiv> "(OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y::(\<cdot>OclAny) \<Rightarrow> _)"
begin
  definition OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny : "(x::\<cdot>OclAny) .oclIsTypeOf(OclAny) \<equiv> (\<lambda>\<tau>. (case (x (\<tau>)) of \<bottom> \<Rightarrow> (invalid (\<tau>))
    | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> (true (\<tau>))
    | \<lfloor>\<lfloor>(mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y ((mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (_))))\<rfloor>\<rfloor> \<Rightarrow> (true (\<tau>))))"
end

(* 60 ************************************ 64 + 1 *)  (* term Floor1_istypeof.print_istypeof_from_universe *)
definition "OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::\<cdot>OclAny) .oclIsTypeOf(OclAny)))"

(* 61 ************************************ 65 + 1 *)  (* term Floor1_istypeof.print_istypeof_lemmas_id *)
lemmas[simp,code_unfold] = OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny

(* 62 ************************************ 66 + 1 *)
subsection \<open>Context Passing\<close>

(* 63 ************************************ 67 + 1 *)  (* term Floor1_istypeof.print_istypeof_lemma_cp *)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclIsTypeOf(OclAny)))))"
sorry

(* 64 ************************************ 68 + 1 *)  (* term Floor1_istypeof.print_istypeof_lemmas_cp *)
lemmas[simp,code_unfold] = cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny

(* 65 ************************************ 69 + 1 *)
subsection \<open>Execution with Invalid or Null as Argument\<close>

(* 66 ************************************ 70 + 2 *)  (* term Floor1_istypeof.print_istypeof_lemma_strict *)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclIsTypeOf(OclAny)) = invalid"
sorry
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null : "((null::\<cdot>OclAny) .oclIsTypeOf(OclAny)) = true"
sorry

(* 67 ************************************ 72 + 1 *)  (* term Floor1_istypeof.print_istypeof_lemmas_strict *)
lemmas[simp,code_unfold] = OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid
                            OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null

(* 68 ************************************ 73 + 1 *)
subsection \<open>Validity and Definedness Properties\<close>

(* 69 ************************************ 74 + 1 *)  (* term Floor1_istypeof.print_istypeof_defined *)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsTypeOf(OclAny)))"
sorry

(* 70 ************************************ 75 + 1 *)  (* term Floor1_istypeof.print_istypeof_defined' *)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsTypeOf(OclAny)))"
sorry

(* 71 ************************************ 76 + 1 *)
subsection \<open>Up Down Casting\<close>

(* 72 ************************************ 77 + 0 *)  (* term Floor1_istypeof.print_istypeof_up_larger *)

(* 73 ************************************ 77 + 0 *)  (* term Floor1_istypeof.print_istypeof_up_d_cast *)

(* 74 ************************************ 77 + 1 *)
subsection \<open>Const\<close>

(* 75 ************************************ 78 + 1 *)
section \<open>Class Model: OclIsKindOf\<close>

(* 76 ************************************ 79 + 1 *)
subsection \<open>Definition\<close>

(* 77 ************************************ 80 + 1 *)  (* term Floor1_iskindof.print_iskindof_consts *)
consts OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_) .oclIsKindOf'(OclAny')")

(* 78 ************************************ 81 + 1 *)  (* term Floor1_iskindof.print_iskindof_class *)
overloading OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y \<equiv> "(OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y::(\<cdot>OclAny) \<Rightarrow> _)"
begin
  definition OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny : "(x::\<cdot>OclAny) .oclIsKindOf(OclAny) \<equiv> (x .oclIsTypeOf(OclAny))"
end

(* 79 ************************************ 82 + 1 *)  (* term Floor1_iskindof.print_iskindof_from_universe *)
definition "OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> = (\<lambda> (in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (OclAny)) \<Rightarrow> (((((\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)) (OclAny))::\<cdot>OclAny) .oclIsKindOf(OclAny)))"

(* 80 ************************************ 83 + 1 *)  (* term Floor1_iskindof.print_iskindof_lemmas_id *)
lemmas[simp,code_unfold] = OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny

(* 81 ************************************ 84 + 1 *)
subsection \<open>Context Passing\<close>

(* 82 ************************************ 85 + 1 *)  (* term Floor1_iskindof.print_iskindof_lemma_cp *)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny : "(cp (p)) \<Longrightarrow> (cp ((\<lambda>x. (((p ((x::\<cdot>OclAny)))::\<cdot>OclAny) .oclIsKindOf(OclAny)))))"
sorry

(* 83 ************************************ 86 + 1 *)  (* term Floor1_iskindof.print_iskindof_lemmas_cp *)
lemmas[simp,code_unfold] = cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny

(* 84 ************************************ 87 + 1 *)
subsection \<open>Execution with Invalid or Null as Argument\<close>

(* 85 ************************************ 88 + 2 *)  (* term Floor1_iskindof.print_iskindof_lemma_strict *)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid : "((invalid::\<cdot>OclAny) .oclIsKindOf(OclAny)) = invalid"
sorry
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null : "((null::\<cdot>OclAny) .oclIsKindOf(OclAny)) = true"
sorry

(* 86 ************************************ 90 + 1 *)  (* term Floor1_iskindof.print_iskindof_lemmas_strict *)
lemmas[simp,code_unfold] = OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_invalid
                            OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_null

(* 87 ************************************ 91 + 1 *)
subsection \<open>Validity and Definedness Properties\<close>

(* 88 ************************************ 92 + 1 *)  (* term Floor1_iskindof.print_iskindof_defined *)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined :
assumes isdef: "\<tau> \<Turnstile> (\<upsilon> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsKindOf(OclAny)))"
sorry

(* 89 ************************************ 93 + 1 *)  (* term Floor1_iskindof.print_iskindof_defined' *)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_defined' :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> (\<delta> ((X::\<cdot>OclAny) .oclIsKindOf(OclAny)))"
sorry

(* 90 ************************************ 94 + 1 *)
subsection \<open>Up Down Casting\<close>

(* 91 ************************************ 95 + 1 *)  (* term Floor1_iskindof.print_iskindof_up_eq_asty *)
lemma actual_eq_static\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :
assumes isdef: "\<tau> \<Turnstile> (\<delta> (X))"
shows "\<tau> \<Turnstile> ((X::\<cdot>OclAny) .oclIsKindOf(OclAny))"
sorry

(* 92 ************************************ 96 + 0 *)  (* term Floor1_iskindof.print_iskindof_up_larger *)

(* 93 ************************************ 96 + 0 *)  (* term Floor1_iskindof.print_iskindof_up_istypeof_unfold *)

(* 94 ************************************ 96 + 0 *)  (* term Floor1_iskindof.print_iskindof_up_istypeof *)

(* 95 ************************************ 96 + 0 *)  (* term Floor1_iskindof.print_iskindof_up_d_cast *)

(* 96 ************************************ 96 + 1 *)
subsection \<open>Const\<close>

(* 97 ************************************ 97 + 1 *)
section \<open>Class Model: OclAllInstances\<close>

(* 98 ************************************ 98 + 1 *)
text \<open>
   To denote \OCL-types occurring in \OCL expressions syntactically---as, for example,  as
``argument'' of \inlineisar{oclAllInstances()}---we use the inverses of the injection
functions into the object universes; we show that this is sufficient ``characterization.'' \<close>

(* 99 ************************************ 99 + 1 *)  (* term Floor1_allinst.print_allinst_def_id *)
definition "OclAny = OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>"

(* 100 ************************************ 100 + 1 *)  (* term Floor1_allinst.print_allinst_lemmas_id *)
lemmas[simp,code_unfold] = OclAny_def

(* 101 ************************************ 101 + 1 *)  (* term Floor1_allinst.print_allinst_astype *)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_some : "(OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> (x)) \<noteq> None"
sorry

(* 102 ************************************ 102 + 3 *)  (* term Floor1_allinst.print_allinst_exec *)
lemma OclAllInstances_generic\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_exec :
shows "(OclAllInstances_generic (pre_post) (OclAny)) = (\<lambda>\<tau>. (Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (\<lfloor>\<lfloor>Some ` OclAny ` (ran ((heap ((pre_post (\<tau>))))))\<rfloor>\<rfloor>)))"
sorry
lemma OclAllInstances_at_post\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_exec :
shows "(OclAllInstances_at_post (OclAny)) = (\<lambda>\<tau>. (Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (\<lfloor>\<lfloor>Some ` OclAny ` (ran ((heap ((snd (\<tau>))))))\<rfloor>\<rfloor>)))"
sorry
lemma OclAllInstances_at_pre\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_exec :
shows "(OclAllInstances_at_pre (OclAny)) = (\<lambda>\<tau>. (Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (\<lfloor>\<lfloor>Some ` OclAny ` (ran ((heap ((fst (\<tau>))))))\<rfloor>\<rfloor>)))"
sorry

(* 103 ************************************ 105 + 1 *)
subsection \<open>OclIsTypeOf\<close>

(* 104 ************************************ 106 + 2 *)  (* term Floor1_allinst.print_allinst_istypeof_pre *)
lemma ex_ssubst : "(\<forall>x \<in> B. (s (x)) = (t (x))) \<Longrightarrow> (\<exists>x \<in> B. (P ((s (x))))) = (\<exists>x \<in> B. (P ((t (x)))))"
sorry
lemma ex_def : "x \<in> \<lceil>\<lceil>\<lfloor>\<lfloor>Some ` (X - {None})\<rfloor>\<rfloor>\<rceil>\<rceil> \<Longrightarrow> (\<exists>y. x = \<lfloor>\<lfloor>y\<rfloor>\<rfloor>)"
sorry

(* 105 ************************************ 108 + 3 *)  (* term Floor1_allinst.print_allinst_istypeof *)
lemma OclAny_OclAllInstances_generic_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (OclAny))) (OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
sorry
lemma OclAny_OclAllInstances_at_post_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (OclAny))) (OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
sorry
lemma OclAny_OclAllInstances_at_pre_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (OclAny))) (OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
sorry

(* 106 ************************************ 111 + 1 *)
subsection \<open>OclIsKindOf\<close>

(* 107 ************************************ 112 + 3 *)  (* term Floor1_allinst.print_allinst_iskindof_eq *)
lemma OclAny_OclAllInstances_generic_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y : "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_generic (pre_post) (OclAny))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
sorry
lemma OclAny_OclAllInstances_at_post_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_post (OclAny))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
sorry
lemma OclAny_OclAllInstances_at_pre_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :
shows "\<tau> \<Turnstile> (UML_Set.OclForall ((OclAllInstances_at_pre (OclAny))) (OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y))"
sorry

(* 108 ************************************ 115 + 0 *)  (* term Floor1_allinst.print_allinst_iskindof_larger *)

(* 109 ************************************ 115 + 1 *)
section \<open>Class Model: The Accessors\<close>

(* 110 ************************************ 116 + 1 *)
text \<open>\<close>

(* 111 ************************************ 117 + 1 *)
text \<open>
  \label{sec:Meta-C-generatedeam-accessors}\<close>

(* 112 ************************************ 118 + 1 *)
subsection \<open>Definition\<close>

(* 113 ************************************ 119 + 1 *)
text \<open>
   We start with a oid for the association; this oid can be used
in presence of association classes to represent the association inside an object,
pretty much similar to the \inlineisar+Employee_DesignModel_UMLPart+, where we stored
an \verb+oid+ inside the class as ``pointer.'' \<close>

(* 114 ************************************ 120 + 0 *)  (* term Floor1_access.print_access_oid_uniq_ml *)

(* 115 ************************************ 120 + 0 *)  (* term Floor1_access.print_access_oid_uniq *)

(* 116 ************************************ 120 + 1 *)
text \<open>
   From there on, we can already define an empty state which must contain
for $\mathit{oid}_{Person}\mathcal{BOSS}$ the empty relation (encoded as association list, since there are
associations with a Sequence-like structure).\<close>

(* 117 ************************************ 121 + 5 *)  (* term Floor1_access.print_access_eval_extract *)
definition "eval_extract x f = (\<lambda>\<tau>. (case x \<tau> of \<lfloor>\<lfloor>obj\<rfloor>\<rfloor> \<Rightarrow> (f ((oid_of (obj))) (\<tau>))
    | _ \<Rightarrow> invalid \<tau>))"
definition "in_pre_state = fst"
definition "in_post_state = snd"
definition "reconst_basetype = (\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)"
definition "reconst_basetype\<^sub>V\<^sub>o\<^sub>i\<^sub>d x = Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e o (reconst_basetype (x))"

(* 118 ************************************ 126 + 1 *)
text \<open>
   The @{text pre_post}-parameter is configured with @{text fst} or
@{text snd}, the @{text to_from}-parameter either with the identity @{term id} or
the following combinator @{text switch}: \<close>

(* 119 ************************************ 127 + 0 *)  (* term Floor1_access.print_access_choose_ml *)

(* 120 ************************************ 127 + 1 *)  (* term Floor1_access.print_access_choose *)
definition "deref_assocs pre_post to_from assoc_oid f oid = (\<lambda>\<tau>. (case (assocs ((pre_post (\<tau>))) (assoc_oid)) of \<lfloor>S\<rfloor> \<Rightarrow> (f ((deref_assocs_list (to_from) (oid) (S))) (\<tau>))
    | _ \<Rightarrow> (invalid (\<tau>))))"

(* 121 ************************************ 128 + 1 *)  (* term Floor1_access.print_access_deref_oid *)
definition "deref_oid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y fst_snd f oid = (\<lambda>\<tau>. (case (heap (fst_snd \<tau>) (oid)) of \<lfloor>in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y obj\<rfloor> \<Rightarrow> f obj \<tau>
    | _ \<Rightarrow> invalid \<tau>))"

(* 122 ************************************ 129 + 0 *)  (* term Floor1_access.print_access_deref_assocs *)

(* 123 ************************************ 129 + 1 *)
text \<open>
   pointer undefined in state or not referencing a type conform object representation \<close>

(* 124 ************************************ 130 + 0 *)  (* term Floor1_access.print_access_select *)

(* 125 ************************************ 130 + 0 *)  (* term Floor1_access.print_access_select_obj *)

(* 126 ************************************ 130 + 0 *)  (* term Floor1_access.print_access_dot_consts *)

(* 127 ************************************ 130 + 0 *)  (* term Floor1_access.print_access_dot *)

(* 128 ************************************ 130 + 0 *)  (* term Floor1_access.print_access_dot_lemmas_id *)

(* 129 ************************************ 130 + 1 *)
subsection \<open>Context Passing\<close>

(* 130 ************************************ 131 + 1 *)  (* term Floor1_access.print_access_dot_cp_lemmas *)
lemmas[simp,code_unfold] = eval_extract_def

(* 131 ************************************ 132 + 0 *)  (* term Floor1_access.print_access_dot_lemma_cp *)

(* 132 ************************************ 132 + 0 *)  (* term Floor1_access.print_access_dot_lemmas_cp *)

(* 133 ************************************ 132 + 1 *)
subsection \<open>Execution with Invalid or Null as Argument\<close>

(* 134 ************************************ 133 + 0 *)  (* term Floor1_access.print_access_lemma_strict *)

(* 135 ************************************ 133 + 1 *)
subsection \<open>Representation in States\<close>

(* 136 ************************************ 134 + 0 *)  (* term Floor1_access.print_access_def_mono *)

(* 137 ************************************ 134 + 0 *)  (* term Floor1_access.print_access_is_repr *)

(* 138 ************************************ 134 + 0 *)  (* term Floor1_access.print_access_repr_allinst *)

(* 139 ************************************ 134 + 1 *)
section \<open>Class Model: Towards the Object Instances\<close>

(* 140 ************************************ 135 + 1 *)
text \<open>\<close>

(* 141 ************************************ 136 + 1 *)
text_raw \<open>\<close>

(* 142 ************************************ 137 + 1 *)
text \<open>

The example we are defining in this section comes from the \autoref{fig:Meta-C-generatedeam1_system-states}.
\<close>

(* 143 ************************************ 138 + 1 *)
text_raw \<open>
\begin{figure}
\includegraphics[width=\textwidth]{figures/pre-post.pdf}
\caption{(a) pre-state $\sigma_1$ and
  (b) post-state $\sigma_1'$.}
\label{fig:Meta-C-generatedeam1_system-states}
\end{figure}
\<close>

(* 144 ************************************ 139 + 1 *)  (* term Floor1_examp.print_examp_def_st_defs *)
lemmas [simp,code_unfold] = state.defs
                            const_ss

(* 145 ************************************ 140 + 0 *)  (* term Floor1_astype.print_astype_lemmas_id2 *)

(* 146 ************************************ 140 + 1 *)
section \<open>Haskell\<close>

(* 147 ************************************ 141 + 230 *)  (* term Floor1_haskabelle.print_haskell *)
old_datatype Position = Position0 "int" "string" "int" "int"
                        | NoPosition0 
                        | BuiltinPosition0 
                        | InternalPosition0 
definition "Position = Position0"
definition "NoPosition = NoPosition0"
definition "BuiltinPosition = BuiltinPosition0"
definition "InternalPosition = InternalPosition0"
type_synonym PosLength = "(Position, int) Product_Type.prod"
old_datatype Name = Name0 "int"
definition "Name = Name0"
old_datatype NodeInfo = OnlyPos0 "Position" "PosLength"
                        | NodeInfo0 "Position" "PosLength" "Name"
definition "OnlyPos = OnlyPos0"
definition "NodeInfo = NodeInfo0"
old_datatype Ident = Ident0 "string" "int" "NodeInfo"
definition "Ident = Ident0"
old_datatype SUERef = AnonymousRef0 "Name"
                        | NamedRef0 "Ident"
definition "AnonymousRef = AnonymousRef0"
definition "NamedRef = NamedRef0"
old_datatype CChar = CChar0 "char" "HOL.bool"
                        | CChars0 "char List.list" "HOL.bool"
definition "CChar = CChar0"
definition "CChars = CChars0"
old_datatype CIntRepr = DecRepr0 
                        | HexRepr0 
                        | OctalRepr0 
definition "DecRepr = DecRepr0"
definition "HexRepr = HexRepr0"
definition "OctalRepr = OctalRepr0"
old_datatype CIntFlag = FlagUnsigned0 
                        | FlagLong0 
                        | FlagLongLong0 
                        | FlagImag0 
definition "FlagUnsigned = FlagUnsigned0"
definition "FlagLong = FlagLong0"
definition "FlagLongLong = FlagLongLong0"
definition "FlagImag = FlagImag0"
old_datatype CFloat = CFloat0 "string"
definition "CFloat = CFloat0"
old_datatype ClangCVersion = ClangCVersion0 "string"
definition "ClangCVersion = ClangCVersion0"
old_datatype CString = CString0 "string" "HOL.bool"
definition "CString = CString0"
old_datatype 'f Flags = Flags0 "int"
definition "Flags = Flags0"
old_datatype CInteger = CInteger0 "int" "CIntRepr" "CIntFlag Flags"
definition "CInteger = CInteger0"
old_datatype CAssignOp = CAssignOp0 
                        | CMulAssOp0 
                        | CDivAssOp0 
                        | CRmdAssOp0 
                        | CAddAssOp0 
                        | CSubAssOp0 
                        | CShlAssOp0 
                        | CShrAssOp0 
                        | CAndAssOp0 
                        | CXorAssOp0 
                        | COrAssOp0 
definition "CAssignOp = CAssignOp0"
definition "CMulAssOp = CMulAssOp0"
definition "CDivAssOp = CDivAssOp0"
definition "CRmdAssOp = CRmdAssOp0"
definition "CAddAssOp = CAddAssOp0"
definition "CSubAssOp = CSubAssOp0"
definition "CShlAssOp = CShlAssOp0"
definition "CShrAssOp = CShrAssOp0"
definition "CAndAssOp = CAndAssOp0"
definition "CXorAssOp = CXorAssOp0"
definition "COrAssOp = COrAssOp0"
old_datatype CBinaryOp = CMulOp0 
                        | CDivOp0 
                        | CRmdOp0 
                        | CAddOp0 
                        | CSubOp0 
                        | CShlOp0 
                        | CShrOp0 
                        | CLeOp0 
                        | CGrOp0 
                        | CLeqOp0 
                        | CGeqOp0 
                        | CEqOp0 
                        | CNeqOp0 
                        | CAndOp0 
                        | CXorOp0 
                        | COrOp0 
                        | CLndOp0 
                        | CLorOp0 
definition "CMulOp = CMulOp0"
definition "CDivOp = CDivOp0"
definition "CRmdOp = CRmdOp0"
definition "CAddOp = CAddOp0"
definition "CSubOp = CSubOp0"
definition "CShlOp = CShlOp0"
definition "CShrOp = CShrOp0"
definition "CLeOp = CLeOp0"
definition "CGrOp = CGrOp0"
definition "CLeqOp = CLeqOp0"
definition "CGeqOp = CGeqOp0"
definition "CEqOp = CEqOp0"
definition "CNeqOp = CNeqOp0"
definition "CAndOp = CAndOp0"
definition "CXorOp = CXorOp0"
definition "COrOp = COrOp0"
definition "CLndOp = CLndOp0"
definition "CLorOp = CLorOp0"
old_datatype CUnaryOp = CPreIncOp0 
                        | CPreDecOp0 
                        | CPostIncOp0 
                        | CPostDecOp0 
                        | CAdrOp0 
                        | CIndOp0 
                        | CPlusOp0 
                        | CMinOp0 
                        | CCompOp0 
                        | CNegOp0 
definition "CPreIncOp = CPreIncOp0"
definition "CPreDecOp = CPreDecOp0"
definition "CPostIncOp = CPostIncOp0"
definition "CPostDecOp = CPostDecOp0"
definition "CAdrOp = CAdrOp0"
definition "CIndOp = CIndOp0"
definition "CPlusOp = CPlusOp0"
definition "CMinOp = CMinOp0"
definition "CCompOp = CCompOp0"
definition "CNegOp = CNegOp0"
old_datatype 'a CStorageSpecifier = CAuto0 "'a"
                        | CRegister0 "'a"
                        | CStatic0 "'a"
                        | CExtern0 "'a"
                        | CTypedef0 "'a"
                        | CThread0 "'a"
definition "CAuto = CAuto0"
definition "CRegister = CRegister0"
definition "CStatic = CStatic0"
definition "CExtern = CExtern0"
definition "CTypedef = CTypedef0"
definition "CThread = CThread0"
type_synonym CStorageSpec = "NodeInfo CStorageSpecifier"
old_datatype 'a CFunctionSpecifier = CInlineQual0 "'a"
                        | CNoreturnQual0 "'a"
definition "CInlineQual = CInlineQual0"
definition "CNoreturnQual = CNoreturnQual0"
type_synonym CFunSpec = "NodeInfo CFunctionSpecifier"
old_datatype CStructTag = CStructTag0 
                        | CUnionTag0 
definition "CStructTag = CStructTag0"
definition "CUnionTag = CUnionTag0"
old_datatype 'a CConstant = CIntConst0 "CInteger" "'a"
                        | CCharConst0 "CChar" "'a"
                        | CFloatConst0 "CFloat" "'a"
                        | CStrConst0 "CString" "'a"
definition "CIntConst = CIntConst0"
definition "CCharConst = CCharConst0"
definition "CFloatConst = CFloatConst0"
definition "CStrConst = CStrConst0"
type_synonym CConst = "NodeInfo CConstant"
old_datatype 'a CStringLiteral = CStrLit0 "CString" "'a"
definition "CStrLit = CStrLit0"
old_datatype 'a CFunctionDef = CFunDef0 "'a CDeclarationSpecifier List.list" "'a CDeclarator" "'a CDeclaration List.list" "'a CStatement" "'a"
and 'a CDeclaration = CDecl0 "'a CDeclarationSpecifier List.list" "(('a CDeclarator C_Model_init.option, 'a CInitializer C_Model_init.option) Product_Type.prod, 'a CExpression C_Model_init.option) Product_Type.prod List.list" "'a"
                        | CStaticAssert0 "'a CExpression" "'a CStringLiteral" "'a"
and 'a CDeclarator = CDeclr0 "Ident C_Model_init.option" "'a CDerivedDeclarator List.list" "'a CStringLiteral C_Model_init.option" "'a CAttribute List.list" "'a"
and 'a CDerivedDeclarator = CPtrDeclr0 "'a CTypeQualifier List.list" "'a"
                        | CArrDeclr0 "'a CTypeQualifier List.list" "'a CArraySize" "'a"
                        | CFunDeclr0 "(Ident List.list, ('a CDeclaration List.list, HOL.bool) Product_Type.prod) C_Model_init.Either" "'a CAttribute List.list" "'a"
and 'a CArraySize = CNoArrSize0 "HOL.bool"
                        | CArrSize0 "HOL.bool" "'a CExpression"
and 'a CStatement = CLabel0 "Ident" "'a CStatement" "'a CAttribute List.list" "'a"
                        | CCase0 "'a CExpression" "'a CStatement" "'a"
                        | CCases0 "'a CExpression" "'a CExpression" "'a CStatement" "'a"
                        | CDefault0 "'a CStatement" "'a"
                        | CExpr0 "'a CExpression C_Model_init.option" "'a"
                        | CCompound0 "Ident List.list" "'a CCompoundBlockItem List.list" "'a"
                        | CIf0 "'a CExpression" "'a CStatement" "'a CStatement C_Model_init.option" "'a"
                        | CSwitch0 "'a CExpression" "'a CStatement" "'a"
                        | CWhile0 "'a CExpression" "'a CStatement" "HOL.bool" "'a"
                        | CFor0 "('a CExpression C_Model_init.option, 'a CDeclaration) C_Model_init.Either" "'a CExpression C_Model_init.option" "'a CExpression C_Model_init.option" "'a CStatement" "'a"
                        | CGoto0 "Ident" "'a"
                        | CGotoPtr0 "'a CExpression" "'a"
                        | CCont0 "'a"
                        | CBreak0 "'a"
                        | CReturn0 "'a CExpression C_Model_init.option" "'a"
                        | CAsm0 "'a CAssemblyStatement" "'a"
and 'a CAssemblyStatement = CAsmStmt0 "'a CTypeQualifier C_Model_init.option" "'a CStringLiteral" "'a CAssemblyOperand List.list" "'a CAssemblyOperand List.list" "'a CStringLiteral List.list" "'a"
and 'a CAssemblyOperand = CAsmOperand0 "Ident C_Model_init.option" "'a CStringLiteral" "'a CExpression" "'a"
and 'a CCompoundBlockItem = CBlockStmt0 "'a CStatement"
                        | CBlockDecl0 "'a CDeclaration"
                        | CNestedFunDef0 "'a CFunctionDef"
and 'a CDeclarationSpecifier = CStorageSpec0 "'a CStorageSpecifier"
                        | CTypeSpec0 "'a CTypeSpecifier"
                        | CTypeQual0 "'a CTypeQualifier"
                        | CFunSpec0 "'a CFunctionSpecifier"
                        | CAlignSpec0 "'a CAlignmentSpecifier"
and 'a CTypeSpecifier = CVoidType0 "'a"
                        | CCharType0 "'a"
                        | CShortType0 "'a"
                        | CIntType0 "'a"
                        | CLongType0 "'a"
                        | CFloatType0 "'a"
                        | CDoubleType0 "'a"
                        | CSignedType0 "'a"
                        | CUnsigType0 "'a"
                        | CBoolType0 "'a"
                        | CComplexType0 "'a"
                        | CInt128Type0 "'a"
                        | CSUType0 "'a CStructureUnion" "'a"
                        | CEnumType0 "'a CEnumeration" "'a"
                        | CTypeDef0 "Ident" "'a"
                        | CTypeOfExpr0 "'a CExpression" "'a"
                        | CTypeOfType0 "'a CDeclaration" "'a"
                        | CAtomicType0 "'a CDeclaration" "'a"
and 'a CTypeQualifier = CConstQual0 "'a"
                        | CVolatQual0 "'a"
                        | CRestrQual0 "'a"
                        | CAtomicQual0 "'a"
                        | CAttrQual0 "'a CAttribute"
                        | CNullableQual0 "'a"
                        | CNonnullQual0 "'a"
and 'a CAlignmentSpecifier = CAlignAsType0 "'a CDeclaration" "'a"
                        | CAlignAsExpr0 "'a CExpression" "'a"
and 'a CStructureUnion = CStruct0 "CStructTag" "Ident C_Model_init.option" "'a CDeclaration List.list C_Model_init.option" "'a CAttribute List.list" "'a"
and 'a CEnumeration = CEnum0 "Ident C_Model_init.option" "(Ident, 'a CExpression C_Model_init.option) Product_Type.prod List.list C_Model_init.option" "'a CAttribute List.list" "'a"
and 'a CInitializer = CInitExpr0 "'a CExpression" "'a"
                        | CInitList0 "('a CPartDesignator List.list, 'a CInitializer) Product_Type.prod List.list" "'a"
and 'a CPartDesignator = CArrDesig0 "'a CExpression" "'a"
                        | CMemberDesig0 "Ident" "'a"
                        | CRangeDesig0 "'a CExpression" "'a CExpression" "'a"
and 'a CAttribute = CAttr0 "Ident" "'a CExpression List.list" "'a"
and 'a CExpression = CComma0 "'a CExpression List.list" "'a"
                        | CAssign0 "CAssignOp" "'a CExpression" "'a CExpression" "'a"
                        | CCond0 "'a CExpression" "'a CExpression C_Model_init.option" "'a CExpression" "'a"
                        | CBinary0 "CBinaryOp" "'a CExpression" "'a CExpression" "'a"
                        | CCast0 "'a CDeclaration" "'a CExpression" "'a"
                        | CUnary0 "CUnaryOp" "'a CExpression" "'a"
                        | CSizeofExpr0 "'a CExpression" "'a"
                        | CSizeofType0 "'a CDeclaration" "'a"
                        | CAlignofExpr0 "'a CExpression" "'a"
                        | CAlignofType0 "'a CDeclaration" "'a"
                        | CComplexReal0 "'a CExpression" "'a"
                        | CComplexImag0 "'a CExpression" "'a"
                        | CIndex0 "'a CExpression" "'a CExpression" "'a"
                        | CCall0 "'a CExpression" "'a CExpression List.list" "'a"
                        | CMember0 "'a CExpression" "Ident" "HOL.bool" "'a"
                        | CVar0 "Ident" "'a"
                        | CConst0 "'a CConstant"
                        | CCompoundLit0 "'a CDeclaration" "('a CPartDesignator List.list, 'a CInitializer) Product_Type.prod List.list" "'a"
                        | CGenericSelection0 "'a CExpression" "('a CDeclaration C_Model_init.option, 'a CExpression) Product_Type.prod List.list" "'a"
                        | CStatExpr0 "'a CStatement" "'a"
                        | CLabAddrExpr0 "Ident" "'a"
                        | CBuiltinExpr0 "'a CBuiltinThing"
and 'a CBuiltinThing = CBuiltinVaArg0 "'a CExpression" "'a CDeclaration" "'a"
                        | CBuiltinOffsetOf0 "'a CDeclaration" "'a CPartDesignator List.list" "'a"
                        | CBuiltinTypesCompatible0 "'a CDeclaration" "'a CDeclaration" "'a"
definition "CFunDef = CFunDef0"
definition "CDecl = CDecl0"
definition "CStaticAssert = CStaticAssert0"
definition "CDeclr = CDeclr0"
definition "CPtrDeclr = CPtrDeclr0"
definition "CArrDeclr = CArrDeclr0"
definition "CFunDeclr = CFunDeclr0"
definition "CNoArrSize = CNoArrSize0"
definition "CArrSize = CArrSize0"
definition "CLabel = CLabel0"
definition "CCase = CCase0"
definition "CCases = CCases0"
definition "CDefault = CDefault0"
definition "CExpr = CExpr0"
definition "CCompound = CCompound0"
definition "CIf = CIf0"
definition "CSwitch = CSwitch0"
definition "CWhile = CWhile0"
definition "CFor = CFor0"
definition "CGoto = CGoto0"
definition "CGotoPtr = CGotoPtr0"
definition "CCont = CCont0"
definition "CBreak = CBreak0"
definition "CReturn = CReturn0"
definition "CAsm = CAsm0"
definition "CAsmStmt = CAsmStmt0"
definition "CAsmOperand = CAsmOperand0"
definition "CBlockStmt = CBlockStmt0"
definition "CBlockDecl = CBlockDecl0"
definition "CNestedFunDef = CNestedFunDef0"
definition "CStorageSpec = CStorageSpec0"
definition "CTypeSpec = CTypeSpec0"
definition "CTypeQual = CTypeQual0"
definition "CFunSpec = CFunSpec0"
definition "CAlignSpec = CAlignSpec0"
definition "CVoidType = CVoidType0"
definition "CCharType = CCharType0"
definition "CShortType = CShortType0"
definition "CIntType = CIntType0"
definition "CLongType = CLongType0"
definition "CFloatType = CFloatType0"
definition "CDoubleType = CDoubleType0"
definition "CSignedType = CSignedType0"
definition "CUnsigType = CUnsigType0"
definition "CBoolType = CBoolType0"
definition "CComplexType = CComplexType0"
definition "CInt128Type = CInt128Type0"
definition "CSUType = CSUType0"
definition "CEnumType = CEnumType0"
definition "CTypeDef = CTypeDef0"
definition "CTypeOfExpr = CTypeOfExpr0"
definition "CTypeOfType = CTypeOfType0"
definition "CAtomicType = CAtomicType0"
definition "CConstQual = CConstQual0"
definition "CVolatQual = CVolatQual0"
definition "CRestrQual = CRestrQual0"
definition "CAtomicQual = CAtomicQual0"
definition "CAttrQual = CAttrQual0"
definition "CNullableQual = CNullableQual0"
definition "CNonnullQual = CNonnullQual0"
definition "CAlignAsType = CAlignAsType0"
definition "CAlignAsExpr = CAlignAsExpr0"
definition "CStruct = CStruct0"
definition "CEnum = CEnum0"
definition "CInitExpr = CInitExpr0"
definition "CInitList = CInitList0"
definition "CArrDesig = CArrDesig0"
definition "CMemberDesig = CMemberDesig0"
definition "CRangeDesig = CRangeDesig0"
definition "CAttr = CAttr0"
definition "CComma = CComma0"
definition "CAssign = CAssign0"
definition "CCond = CCond0"
definition "CBinary = CBinary0"
definition "CCast = CCast0"
definition "CUnary = CUnary0"
definition "CSizeofExpr = CSizeofExpr0"
definition "CSizeofType = CSizeofType0"
definition "CAlignofExpr = CAlignofExpr0"
definition "CAlignofType = CAlignofType0"
definition "CComplexReal = CComplexReal0"
definition "CComplexImag = CComplexImag0"
definition "CIndex = CIndex0"
definition "CCall = CCall0"
definition "CMember = CMember0"
definition "CVar = CVar0"
definition "CConst = CConst0"
definition "CCompoundLit = CCompoundLit0"
definition "CGenericSelection = CGenericSelection0"
definition "CStatExpr = CStatExpr0"
definition "CLabAddrExpr = CLabAddrExpr0"
definition "CBuiltinExpr = CBuiltinExpr0"
definition "CBuiltinVaArg = CBuiltinVaArg0"
definition "CBuiltinOffsetOf = CBuiltinOffsetOf0"
definition "CBuiltinTypesCompatible = CBuiltinTypesCompatible0"
type_synonym 'a CInitializerList = "('a CPartDesignator List.list, 'a CInitializer) Product_Type.prod List.list"
old_datatype 'a CExternalDeclaration = CDeclExt0 "'a CDeclaration"
                        | CFDefExt0 "'a CFunctionDef"
                        | CAsmExt0 "'a CStringLiteral" "'a"
definition "CDeclExt = CDeclExt0"
definition "CFDefExt = CFDefExt0"
definition "CAsmExt = CAsmExt0"
old_datatype 'a CTranslationUnit = CTranslUnit0 "'a CExternalDeclaration List.list" "'a"
definition "CTranslUnit = CTranslUnit0"
type_synonym CTranslUnit = "NodeInfo CTranslationUnit"
type_synonym CExtDecl = "NodeInfo CExternalDeclaration"
type_synonym CFunDef = "NodeInfo CFunctionDef"
type_synonym CDecl = "NodeInfo CDeclaration"
type_synonym CDeclr = "NodeInfo CDeclarator"
type_synonym CDerivedDeclr = "NodeInfo CDerivedDeclarator"
type_synonym CArrSize = "NodeInfo CArraySize"
type_synonym CStat = "NodeInfo CStatement"
type_synonym CAsmStmt = "NodeInfo CAssemblyStatement"
type_synonym CAsmOperand = "NodeInfo CAssemblyOperand"
type_synonym CBlockItem = "NodeInfo CCompoundBlockItem"
type_synonym CDeclSpec = "NodeInfo CDeclarationSpecifier"
type_synonym CTypeSpec = "NodeInfo CTypeSpecifier"
type_synonym CTypeQual = "NodeInfo CTypeQualifier"
type_synonym CAlignSpec = "NodeInfo CAlignmentSpecifier"
type_synonym CStructUnion = "NodeInfo CStructureUnion"
type_synonym CEnum = "NodeInfo CEnumeration"
type_synonym CInit = "NodeInfo CInitializer"
type_synonym CInitList = "NodeInfo CInitializerList"
type_synonym CDesignator = "NodeInfo CPartDesignator"
type_synonym CAttr = "NodeInfo CAttribute"
type_synonym CExpr = "NodeInfo CExpression"
type_synonym CBuiltin = "NodeInfo CBuiltinThing"
type_synonym CStrLit = "NodeInfo CStringLiteral"

end
