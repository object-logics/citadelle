theory OCL_compiler_aux
imports "~~/src/HOL/Library/RBT"
        "~~/src/HOL/Library/Char_ord"
        "~~/src/HOL/Library/List_lexord"
        "~~/src/HOL/Library/Code_Char"
begin

type_synonym nat = natural

section{* Preliminaries Compiler *}

subsection{* Oid-Management *}

definition "Succ x = x + 1"

datatype internal_oid = Oid nat
datatype internal_oids = Oids nat (* start *)
                              nat (* oid for assoc (incremented from start) *)
                              nat (* oid for inh (incremented from start) *)

definition "oidInit = (\<lambda> Oid n \<Rightarrow> Oids n n n)"

definition "oidSucAssoc = (\<lambda> Oids n1 n2 n3 \<Rightarrow> Oids n1 (Succ n2) (Succ n3))"
definition "oidSucInh = (\<lambda> Oids n1 n2 n3 \<Rightarrow> Oids n1 n2 (Succ n3))"
definition "oidGetAssoc = (\<lambda> Oids _ n _ \<Rightarrow> Oid n)"
definition "oidGetInh = (\<lambda> Oids _ _ n \<Rightarrow> Oid n)"

definition "oidReinitAll = (\<lambda>Oids n1 _ _ \<Rightarrow> Oids n1 n1 n1)"
definition "oidReinitInh = (\<lambda>Oids n1 n2 _ \<Rightarrow> Oids n1 n2 n2)"


subsection{* RBT Miscellaneous *}

subsection{* ... *} (* optimized data-structure version *)

datatype opt_attr_type = OptInh | OptOwn
datatype opt_ident = OptIdent nat

instantiation internal_oid :: linorder
begin
 definition "n_of_internal_oid = (\<lambda> Oid n \<Rightarrow> n)"
 definition "n \<le> m \<longleftrightarrow> n_of_internal_oid n \<le> n_of_internal_oid m"
 definition "n < m \<longleftrightarrow> n_of_internal_oid n < n_of_internal_oid m"
 instance
   apply(default)
   apply (metis less_eq_internal_oid_def less_imp_le less_internal_oid_def not_less)
   apply (metis less_eq_internal_oid_def order_refl)
   apply (metis less_eq_internal_oid_def order.trans)
   apply(simp add: less_eq_internal_oid_def n_of_internal_oid_def, case_tac x, case_tac y, simp)
 by (metis le_cases less_eq_internal_oid_def)
end

instantiation opt_ident :: linorder
begin
 definition "n_of_opt_ident = (\<lambda> OptIdent n \<Rightarrow> n)"
 definition "n \<le> m \<longleftrightarrow> n_of_opt_ident n \<le> n_of_opt_ident m"
 definition "n < m \<longleftrightarrow> n_of_opt_ident n < n_of_opt_ident m"
 instance
 apply(default)
 apply (metis less_eq_opt_ident_def less_imp_le less_opt_ident_def not_less)
 apply (metis less_eq_opt_ident_def order_refl)
   apply (metis less_eq_opt_ident_def order.trans)
   apply(simp add: less_eq_opt_ident_def n_of_opt_ident_def, case_tac x, case_tac y, simp)
 by (metis le_cases less_eq_opt_ident_def)
end

subsection{* ... *}

definition "List_map f l = rev (foldl (\<lambda>l x. f x # l) [] l)"
definition "List_mapi f l = rev (fst (foldl (\<lambda>(l,cpt) x. (f cpt x # l, Succ cpt)) ([], 0::nat) l))"
definition "List_iter f = foldl (\<lambda>_. f) ()"
definition "flatten l = foldl (\<lambda>acc l. foldl (\<lambda>acc x. x # acc) acc (rev l)) [] (rev l)"
definition List_append (infixr "@@" 65) where "List_append a b = flatten [a, b]"
definition "List_filter f l = rev (foldl (\<lambda>l x. if f x then x # l else l) [] l)"
definition "rev_map f = foldl (\<lambda>l x. f x # l) []"
definition "fold_list f l accu =
  (let (l, accu) = List.fold (\<lambda>x (l, accu). let (x, accu) = f x accu in (x # l, accu)) l ([], accu) in
   (rev l, accu))"
definition "char_escape = Char Nibble0 Nibble9"
definition "modify_def v k f rbt =
  (case lookup rbt k of None \<Rightarrow> insert k (f v) rbt
                      | Some _ \<Rightarrow> map_entry k f rbt)"
definition "Option_bind f = (\<lambda> None \<Rightarrow> None | Some x \<Rightarrow> f x)"
definition "List_assoc x1 l = List.fold (\<lambda>(x2, v). \<lambda>None \<Rightarrow> if x1 = x2 then Some v else None | x \<Rightarrow> x) l None"
definition "List_split l = (List_map fst l, List_map snd l)"
definition "List_upto i j = 
 (let to_i = \<lambda>n. int_of_integer (integer_of_natural n) in
  List_map (natural_of_integer o integer_of_int) (upto (to_i i) (to_i j)))"
definition "lookup2 rbt = (\<lambda>(x1, x2). Option_bind (\<lambda>rbt. lookup rbt x2) (lookup rbt x1))"
definition "insert2 = (\<lambda>(x1, x2) v. modify_def empty x1 (insert x2 v))"

end
