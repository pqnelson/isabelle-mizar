\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Pre_topc
  imports Struct_0
begin

abbreviation "TopStruct_fields \<equiv> (#carrier \<rightarrow> set';topology \<rightarrow> Subset-Family-of' the' carrier #)"
    
definition "struct TopStruct TopStruct_fields" 

lemma TopStruct_well:"TopStruct_fields well defined on {carrier} \<union>{topology}" 
proof(rule  Fields_add_argM1[OF one_sorted_well],simp add:string,simp add:string)  
  show "for X1 be one_sorted_fields\<parallel>Function holds ex it be Subset-Family-of (the carrier of X1) st True" 
  proof(rule ballI)
    fix X1 assume "X1 be one_sorted_fields\<parallel>Function"
    hence "the carrier of X1 be set" using field by auto 
    thus "ex it be Subset-Family-of the carrier of X1 st True"  using Subset_Family_of_ex by auto
  qed    
qed    

schematic_goal TopStruct:
   shows ?X by (rule struct_well_defined[OF TopStruct_def TopStruct_well])
   
theorem addMagma_inheritance:
  "X be TopStruct \<Longrightarrow> X be one-sorted" using TopStruct one_sorted by simp

end