\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Group_1a
  imports Algstr_0 Pre_topc
begin

abbreviation "TopaddGrStr_fields\<equiv>(#carrier \<rightarrow> set'; addF\<rightarrow> BinOp-of' the' carrier;topology \<rightarrow> Subset-Family-of' the' carrier #)"       

definition "struct TopaddGrStr TopaddGrStr_fields"   

lemma TopaddGrStr_well:" TopaddGrStr_fields well defined on {carrier} \<union>{addF}\<union>{topology}" 
proof(rule  Fields_add_argM1[OF addMagma_well],simp add:string,simp add:string)  
  show "for X1 be addMagma_fields\<parallel>Function holds ex it be  Subset-Family-of the carrier of X1 st True" 
  proof(rule ballI)
    fix X1 assume "X1 be addMagma_fields\<parallel>Function"
    hence "the carrier of X1 be set" using field by auto 
    thus "ex it be Subset-Family-of the carrier of X1 st True"  using Subset_Family_of_ex by auto
  qed    
qed    


schematic_goal TopaddGrStr:
   shows ?X by (rule struct_well_defined[OF TopaddGrStr_def TopaddGrStr_well])
    
theorem TopaddGrStr_inheritance:
  "X be TopaddGrStr \<Longrightarrow> X be addMagma & X be TopStruct" using TopaddGrStr addMagma TopStruct by simp

end  