\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Polyalg1
  imports Vectsp_2
begin
  
abbreviation AlgebraStr_fields_prefix ("AlgebraStr'_fields _") where "AlgebraStr_fields F \<equiv> (#
   carrier \<rightarrow> \<lambda>S. set;
   addF \<rightarrow> \<lambda>S. BinOp-of the carrier of S;
   ZeroF \<rightarrow> \<lambda>S. Element-of the carrier of S;
   multF \<rightarrow> \<lambda>S. BinOp-of the carrier of S;
   OneF \<rightarrow> \<lambda>S. Element-of the carrier of S;
   lmult \<rightarrow>  Function-of' [: the carrier of F,the' carrier ':], the' carrier#)"
    
   
definition AlgebraStr_over ("AlgebraStr-over _") where 
  "struct AlgebraStr-over F AlgebraStr_fields F" 
      

lemma AlgebraStr_over_well:
  assumes "F be one-sorted"
  shows "AlgebraStr_fields F well defined on {carrier} \<union>{addF}\<union>{ZeroF}\<union>{multF}\<union>{OneF} \<union>{lmult}" 
proof(rule Fields_add_argM1[OF doubleLoopStr_well],simp add:string,simp add:string)  
  show "for X1 be  doubleLoopStr_fields\<parallel>Function holds ex it be Function-of [: the carrier of F, the carrier of X1:], the carrier of X1 st True" 
  proof(rule ballI)
    fix X1 assume "X1 be doubleLoopStr_fields\<parallel>Function"
    hence A1: "the carrier of X1 be set" "the carrier of F be set" using field assms one_sorted by auto 
    hence " [: the carrier of F, the carrier of X1:] be set" using zfmisc_1_def_2a by simp       
    thus "ex it be Function-of [: the carrier of F, the carrier of X1:], the carrier of X1 st True" using funct_2_cl_ex A1 by auto        
  qed    
qed    

schematic_goal AlgebraStr_over:
   assumes "F be one_sorted"
   shows ?X by (rule struct_well_defined[OF AlgebraStr_over_def AlgebraStr_over_well[OF assms]])
    
theorem AlgebraStr_over_inheritance:
  assumes "F be one_sorted" 
          "X be AlgebraStr-over F"
  shows "X be doubleLoopStr" "X be ModuleStr-over F" using  AlgebraStr_over ModuleStr_over doubleLoopStr assms by auto
  
end