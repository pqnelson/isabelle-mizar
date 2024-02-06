theory group_1a
imports algstr_0 pre_topc
begin


abbreviation "TopaddGrStr_fields\<equiv>(#carrier \<rightarrow> set'; addF\<rightarrow> BinOp-of' the' carrier;topology \<rightarrow> Subset-Family-of' the' carrier #)"


mdefinition
  "struct TopaddGrStr TopaddGrStr_fields"
:well_defined_property[of _ _ "{carrier}\<union>{addF}\<union>{topology}"]
  by (auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)
(*:struct_well_defined
proof(rule Fields_add_argM1[OF addMagma_d(5)],simp add:string,simp add:string)
   fix X1 assume "X1 be addMagma_fields\<bar>Struct"
    hence "the carrier of X1 be set" using field by auto
    thus "inhabited( Subset-Family-of the carrier of X1)" by auto
  qed *)

theorem TopaddGrStr_inheritance[ty_parent]:
  "X be TopaddGrStr \<Longrightarrow> X be addMagma \<and> X be TopStruct" using TopaddGrStr(1) addMagma(1) TopStruct(1) by simp

end
