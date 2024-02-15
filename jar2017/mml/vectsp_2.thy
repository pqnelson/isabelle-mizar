\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory vectsp_2
  imports vectsp_1
begin

abbreviation RightModStr_fields_prefix ("RightModStr'_fields _" [110] 110) where
 "RightModStr_fields F \<equiv> (#carrier \<rightarrow> set'; addF\<rightarrow> BinOp-of' the' carrier;ZeroF \<rightarrow> Element-of' the' carrier;
               rmult \<rightarrow>  Function-of' [:' the' carrier,the carrier of F:], the' carrier #)"

mdefinition RightModStr_over ("RightModStr-over _") where
  mlet "F be 1-sorted"
  "struct RightModStr-over F RightModStr_fields F"
:well_defined_property[of _ _ "{carrier}\<union>{addF}\<union>{ZeroF}\<union>{rmult}"]
  by (auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)
(*  :struct_well_defined
proof(rule Fields_add_argM1[OF addLoopStr_d(5)])
    fix X1 assume "X1 be addLoopStr_fields\<bar>Struct"
    hence A1: "the carrier of X1 be set" "the carrier of F be set" using field[of X1] by mauto
    thus "inhabited(Function-of [: the carrier of X1, the carrier of F:], the carrier of X1)" by auto
  qed (simp_all add:string)
*)

theorem RightModStr_inheritance[ty_parent]:
  "F be 1-sorted \<Longrightarrow> X be RightModStr-over F \<Longrightarrow> X be addLoopStr" using RightModStr_over(1) addLoopStrA by simp

abbreviation BiModStr_fields_prefix ("BiModStr'_fields _" [110] 110) where
 "BiModStr_fields F \<equiv>(#carrier \<rightarrow> set'; addF\<rightarrow> BinOp-of' the' carrier; ZeroF \<rightarrow> Element-of' the' carrier;
               lmult \<rightarrow>  Function-of' [: the carrier of F,the' carrier ':], the' carrier;
               rmult \<rightarrow>  Function-of' [:' the' carrier,the carrier of F:], the' carrier #)"

mdefinition BiModStr_over ("BiModStr-over _") where
  mlet "F be 1-sorted"
  "struct BiModStr-over F BiModStr_fields F"
:well_defined_property[of _ _ "{carrier}\<union>{addF}\<union>{ZeroF}\<union>{lmult}\<union>{rmult}"]
  by (auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)
(*  :struct_well_defined
proof(rule Fields_add_argM1[OF ModuleStr_over(5)])
    fix X1 assume [ty]: "X1 be ModuleStr_fields F\<bar>Struct"
    have A1: "the carrier of X1 be set" "the carrier of F be set" by (intro field[THEN iffD1,THEN conjunct1]) mauto
    hence " [: the carrier of X1, the carrier of F:] be set" using zfmisc_1_def_2_ty by simp
    thus "inhabited(Function-of [: the carrier of X1, the carrier of F:], the carrier of X1)" using funct_2_cl_ex A1 by auto
qed (simp_all add:string)
 *)

theorem BiModStr_inheritance[ty_parent]:
  assumes [ty]:"F be 1-sorted" "X be BiModStr-over F"
  shows "X be ModuleStr-over F" "X be RightModStr-over F"
using BiModStr_over(1)[of F X] ModuleStr_over(1)[of F X] RightModStr_over(1)[of F X] by auto

end