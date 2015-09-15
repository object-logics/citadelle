theory Design_generated imports "../Toy_Library"   "../Toy_Library_Static"   "../embedding/Generator_dynamic" begin

(* 1 ************************************ 0 + 10 *)
datatype ty\<E>\<X>\<T>\<^sub>A\<^sub>t\<^sub>o\<^sub>m = mk\<E>\<X>\<T>\<^sub>A\<^sub>t\<^sub>o\<^sub>m "oid" "oid list option" "int option" "bool option" "nat option" "unit option"
datatype ty\<^sub>A\<^sub>t\<^sub>o\<^sub>m = mk\<^sub>A\<^sub>t\<^sub>o\<^sub>m "ty\<E>\<X>\<T>\<^sub>A\<^sub>t\<^sub>o\<^sub>m" "int option"
datatype ty\<E>\<X>\<T>\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e = mk\<E>\<X>\<T>\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e_\<^sub>A\<^sub>t\<^sub>o\<^sub>m "ty\<^sub>A\<^sub>t\<^sub>o\<^sub>m"
                        | mk\<E>\<X>\<T>\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e "oid" "oid list option" "int option" "bool option" "nat option" "unit option"
datatype ty\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e = mk\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e "ty\<E>\<X>\<T>\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e"
datatype ty\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n = mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e "ty\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e"
                        | mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<^sub>A\<^sub>t\<^sub>o\<^sub>m "ty\<^sub>A\<^sub>t\<^sub>o\<^sub>m"
                        | mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n "oid" "nat option" "unit option"
datatype ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n = mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n "ty\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" "oid list option" "int option" "bool option"
datatype ty\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y = mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
                        | mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e "ty\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e"
                        | mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>A\<^sub>t\<^sub>o\<^sub>m "ty\<^sub>A\<^sub>t\<^sub>o\<^sub>m"
                        | mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y "oid"
datatype ty\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y = mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y "ty\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y" "nat option" "unit option"
datatype ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y "ty\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y"
                        | mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
                        | mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e "ty\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e"
                        | mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<^sub>A\<^sub>t\<^sub>o\<^sub>m "ty\<^sub>A\<^sub>t\<^sub>o\<^sub>m"
                        | mk\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y "oid"
datatype ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y "ty\<E>\<X>\<T>\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y"

(* 2 ************************************ 10 + 1 *)
datatype \<AA> = in\<^sub>A\<^sub>t\<^sub>o\<^sub>m "ty\<^sub>A\<^sub>t\<^sub>o\<^sub>m"
                        | in\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e "ty\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e"
                        | in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
                        | in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y "ty\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y"
                        | in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y "ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y"

(* 3 ************************************ 11 + 5 *)
type_synonym Atom = "\<langle>\<langle>ty\<^sub>A\<^sub>t\<^sub>o\<^sub>m\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>"
type_synonym Molecule = "\<langle>\<langle>ty\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>"
type_synonym Person = "\<langle>\<langle>ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>"
type_synonym Galaxy = "\<langle>\<langle>ty\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>"
type_synonym OclAny = "\<langle>\<langle>ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>"

(* 4 ************************************ 16 + 3 *)
definition "oid\<^sub>A\<^sub>t\<^sub>o\<^sub>m_0___boss = 0"
definition "oid\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e_0___boss = 0"
definition "oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss = 0"

(* 5 ************************************ 19 + 2 *)
definition "switch\<^sub>2_01 = (\<lambda> [x0 , x1] \<Rightarrow> (x0 , x1))"
definition "switch\<^sub>2_10 = (\<lambda> [x0 , x1] \<Rightarrow> (x1 , x0))"

(* 6 ************************************ 21 + 3 *)
definition "oid1 = 1"
definition "oid2 = 2"
definition "inst_assoc1 = (\<lambda>oid_class to_from oid. ((case (deref_assocs_list ((to_from::oid list list \<Rightarrow> oid list \<times> oid list)) ((oid::oid)) ((drop ((((map_of_list ([(oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss , (List.map ((\<lambda>(x , y). [x , y]) o switch\<^sub>2_01) ([[[oid1] , [oid2]]])))]))) ((oid_class::oid))))))) of Nil \<Rightarrow> None
    | l \<Rightarrow> (Some (l)))::oid list option))"

(* 7 ************************************ 24 + 0 *)

(* 8 ************************************ 24 + 2 *)
definition "oid3 = 3"
definition "inst_assoc3 = (\<lambda>oid_class to_from oid. ((case (deref_assocs_list ((to_from::oid list list \<Rightarrow> oid list \<times> oid list)) ((oid::oid)) ((drop ((((map_of_list ([]))) ((oid_class::oid))))))) of Nil \<Rightarrow> None
    | l \<Rightarrow> (Some (l)))::oid list option))"

(* 9 ************************************ 26 + 0 *)

(* 10 ************************************ 26 + 4 *)
generation_syntax [ shallow (generation_semantics [ design ]) ]
setup{* (Generation_mode.update_compiler_config ((K (let open META in Compiler_env_config_ext (true, NONE, Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 1), (Code_Numeral.Nat 4)), I ((Code_Numeral.Nat 0), (Code_Numeral.Nat 0)), Gen_only_design, SOME (OclClass ((META.SS_base (META.ST "OclAny")), nil, uncurry cons (OclClass ((META.SS_base (META.ST "Galaxy")), uncurry cons (I ((META.SS_base (META.ST "wormhole")), OclTy_base_unlimitednatural), uncurry cons (I ((META.SS_base (META.ST "is_sound")), OclTy_base_void), nil)), uncurry cons (OclClass ((META.SS_base (META.ST "Person")), uncurry cons (I ((META.SS_base (META.ST "boss")), OclTy_object (OclTyObj (OclTyCore (Ocl_ty_class_ext ((META.SS_base (META.ST "oid")), (Code_Numeral.Nat 0), (Code_Numeral.Nat 2), Ocl_ty_class_node_ext ((Code_Numeral.Nat 0), Ocl_multiplicity_ext (uncurry cons (I (Mult_star, NONE), nil), NONE, uncurry cons (Set, nil), ()), (META.SS_base (META.ST "Person")), ()), Ocl_ty_class_node_ext ((Code_Numeral.Nat 1), Ocl_multiplicity_ext (uncurry cons (I (Mult_nat ((Code_Numeral.Nat 0)), SOME (Mult_nat ((Code_Numeral.Nat 1)))), nil), SOME ((META.SS_base (META.ST "boss"))), uncurry cons (Set, nil), ()), (META.SS_base (META.ST "Person")), ()), ())), nil))), uncurry cons (I ((META.SS_base (META.ST "salary")), OclTy_base_integer), uncurry cons (I ((META.SS_base (META.ST "is_meta_thinking")), OclTy_base_boolean), nil))), uncurry cons (OclClass ((META.SS_base (META.ST "Molecule")), nil, uncurry cons (OclClass ((META.SS_base (META.ST "Atom")), uncurry cons (I ((META.SS_base (META.ST "size")), OclTy_base_integer), nil), nil), nil)), nil)), nil)), nil))), uncurry cons (META_instance (OclInstance (uncurry cons (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3"))), SOME ((META.SS_base (META.ST "Person"))), OclAttrNoCast (uncurry cons (I (NONE, I ((META.SS_base (META.ST "salary")), ShallB_term (OclDefInteger ((META.SS_base (META.ST "1")))))), nil)), ()), nil))), uncurry cons (META_instance (OclInstance (uncurry cons (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1"))), SOME ((META.SS_base (META.ST "Person"))), OclAttrNoCast (uncurry cons (I (NONE, I ((META.SS_base (META.ST "salary")), ShallB_term (OclDefInteger ((META.SS_base (META.ST "1300")))))), uncurry cons (I (NONE, I ((META.SS_base (META.ST "boss")), ShallB_str ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2"))))), nil))), ()), uncurry cons (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2"))), SOME ((META.SS_base (META.ST "Person"))), OclAttrNoCast (uncurry cons (I (NONE, I ((META.SS_base (META.ST "salary")), ShallB_term (OclDefInteger ((META.SS_base (META.ST "1800")))))), nil)), ()), nil)))), uncurry cons (META_class_raw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((META.SS_base (META.ST "Person"))), uncurry cons (uncurry cons (OclTyCore_pre ((META.SS_base (META.ST "Galaxy"))), nil), nil)), uncurry cons (I ((META.SS_base (META.ST "salary")), OclTy_base_integer), uncurry cons (I ((META.SS_base (META.ST "boss")), OclTy_object (OclTyObj (OclTyCore_pre ((META.SS_base (META.ST "Person"))), nil))), uncurry cons (I ((META.SS_base (META.ST "is_meta_thinking")), OclTy_base_boolean), nil))), nil, false, ())), uncurry cons (META_class_raw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((META.SS_base (META.ST "Galaxy"))), nil), uncurry cons (I ((META.SS_base (META.ST "wormhole")), OclTy_base_unlimitednatural), uncurry cons (I ((META.SS_base (META.ST "is_sound")), OclTy_base_void), nil)), nil, false, ())), uncurry cons (META_class_raw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((META.SS_base (META.ST "Molecule"))), uncurry cons (uncurry cons (OclTyCore_pre ((META.SS_base (META.ST "Person"))), nil), nil)), nil, nil, false, ())), uncurry cons (META_class_raw (Floor1, Ocl_class_raw_ext (OclTyObj (OclTyCore_pre ((META.SS_base (META.ST "Atom"))), uncurry cons (uncurry cons (OclTyCore_pre ((META.SS_base (META.ST "Molecule"))), nil), nil)), uncurry cons (I ((META.SS_base (META.ST "size")), OclTy_base_integer), nil), nil, false, ())), nil)))))), uncurry cons (I ((META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3"), I (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3"))), SOME ((META.SS_base (META.ST "Person"))), OclAttrNoCast (uncurry cons (I (NONE, I ((META.SS_base (META.ST "salary")), ShallB_term (OclDefInteger ((META.SS_base (META.ST "1")))))), nil)), ()), Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 1), (Code_Numeral.Nat 3)))), uncurry cons (I ((META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2"), I (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2"))), SOME ((META.SS_base (META.ST "Person"))), OclAttrNoCast (uncurry cons (I (NONE, I ((META.SS_base (META.ST "salary")), ShallB_term (OclDefInteger ((META.SS_base (META.ST "1800")))))), nil)), ()), Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 1), (Code_Numeral.Nat 2)))), uncurry cons (I ((META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1"), I (Ocl_instance_single_ext (SOME ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1"))), SOME ((META.SS_base (META.ST "Person"))), OclAttrNoCast (uncurry cons (I (NONE, I ((META.SS_base (META.ST "salary")), ShallB_term (OclDefInteger ((META.SS_base (META.ST "1300")))))), uncurry cons (I (NONE, I ((META.SS_base (META.ST "boss")), ShallB_str ((META.SS_base (META.ST "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2"))))), nil))), ()), Oids ((Code_Numeral.Nat 0), (Code_Numeral.Nat 1), (Code_Numeral.Nat 1)))), nil))), nil, false, false, I (nil, nil), nil, I (NONE, false), ()) end)))) *}
Instance \<sigma>\<^sub>1_object0 :: Person = [ "salary" = 1000, "boss" = self 1 ]
     and \<sigma>\<^sub>1_object1 :: Person = [ "salary" = 1200 ]
     and \<sigma>\<^sub>1_object2 :: Person = [ "salary" = 2600, "boss" = X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 ]
     and \<sigma>\<^sub>1_object4 :: Person = [ "salary" = 2300, "boss" = self 2 ]
State[shallow] \<sigma>\<^sub>1 = [ \<sigma>\<^sub>1_object0, \<sigma>\<^sub>1_object1, \<sigma>\<^sub>1_object2, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1, \<sigma>\<^sub>1_object4, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 ]

(* 11 ************************************ 30 + 1 *)
State[shallow] \<sigma>\<^sub>1' = [ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 ]

(* 12 ************************************ 31 + 1 *)
PrePost[shallow] \<sigma>\<^sub>1 \<sigma>\<^sub>1'

end
