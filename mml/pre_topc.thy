theory pre_topc
imports struct_0
begin

abbreviation "TopStruct_fields \<equiv> (#carrier \<rightarrow> set';topology \<rightarrow> Subset-Family-of' the' carrier #)"




mdefinition "struct TopStruct TopStruct_fields"
:well_defined_property[of _ _ "{carrier}\<union>{topology}"]
  by (auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

(*  :struct_well_defined
proof(rule Fields_add_argM1[OF one_sorted(5)])
    fix X1 assume "X1 be one_sorted_fields\<bar>Struct"
    hence "the carrier of X1 be set" using field by auto
    thus "inhabited( Subset-Family-of-struct X1)" by auto
qed(simp_all add:string)
*)

lemmas TopStructA = TopStruct(1)
lemmas [ex] = TopStruct(2,3)
lemmas TopStructD = TopStruct(4)
lemmas TopStructR = TopStruct(5)


theorem TopStruct_inheritance[ty_parent]:
  "X be TopStruct \<Longrightarrow> X be 1-sorted" using TopStruct(1) one_sorted(1) by simp

theorem TopStruct_inheritance1:
  "X be TopStruct \<Longrightarrow> (the topology of X) be Subset-Family-of (the carrier of X)" using field TopStruct(1) by auto

end
