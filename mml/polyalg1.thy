\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory polyalg1
  imports vectsp_2
begin

abbreviation AlgebraStr_fields_prefix ("AlgebraStr'_fields _" [110] 110) where "AlgebraStr_fields F \<equiv> (#
   carrier \<rightarrow> (\<lambda>S. set);
   addF \<rightarrow> (\<lambda>S. BinOp-of the carrier of S);
   ZeroF \<rightarrow> (\<lambda>S. Element-of the carrier of S);
   multF \<rightarrow> (\<lambda>S. BinOp-of the carrier of S);
   OneF \<rightarrow> (\<lambda>S. Element-of the carrier of S);
   lmult \<rightarrow>  Function-of' [: the carrier of F,the' carrier ':], the' carrier#)"

mdefinition AlgebraStr_over ("AlgebraStr-over _") where
  mlet "F be 1-sorted"
  "struct AlgebraStr-over F AlgebraStr_fields F"
:well_defined_property[of _ _ "{carrier}\<union>{addF}\<union>{ZeroF}\<union>{multF}\<union>{OneF}\<union>{lmult}"]
  by (auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

theorem AlgebraStr_over_inheritance[ty_parent]:
  assumes[ty]: "F be 1-sorted" "X be AlgebraStr-over F"
        shows "X be doubleLoopStr" "X be ModuleStr-over F" using AlgebraStr_over(1)[of F X] ModuleStr_over(1)[of F X] doubleLoopStrA[of X]
  by auto

end