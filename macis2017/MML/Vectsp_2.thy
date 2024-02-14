\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Vectsp_2
  imports Vectsp_1
begin

abbreviation RightModStr_fields_prefix ("RightModStr'_fields _") where
 "RightModStr_fields F \<equiv>(#carrier \<rightarrow> set'; addF\<rightarrow> BinOp-of' the' carrier;ZeroF \<rightarrow> Element-of' the' carrier;
               rmult \<rightarrow>  Function-of' [:' the' carrier,the carrier of F:], the' carrier #)"       
    
definition  RightModStr_over ("RightModStr-over _") where 
  "struct RightModStr-over F RightModStr_fields F"   
  
lemma RightModStr_over_well:
  assumes "F be one-sorted"
  shows "RightModStr_fields F well defined on {carrier}\<union>{addF}\<union>{ZeroF}\<union>{rmult}" 
proof(rule  Fields_add_argM1[OF addLoopStr_well],simp add:string,simp add:string)  
  show "for X1 be  addLoopStr_fields\<parallel>Function holds ex it be Function-of [: the carrier of X1, the carrier of F:], the carrier of X1 st True" 
  proof(rule ballI)
    fix X1 assume "X1 be addLoopStr_fields\<parallel>Function"
    hence A1: "the carrier of X1 be set" "the carrier of F be set" using field assms one_sorted by auto+ 
    hence " [: the carrier of X1, the carrier of F:] be set" using zfmisc_1_def_2a by simp       
    thus "ex it be Function-of [: the carrier of X1, the carrier of F:], the carrier of X1 st True" using funct_2_cl_ex A1 by auto        
  qed    
qed    

schematic_goal RightModStr_over:
   assumes "F be one_sorted"
   shows ?X by (rule struct_well_defined[OF RightModStr_over_def RightModStr_over_well[OF assms]])
    
theorem  RightModStr_inheritance:
  "F be one_sorted \<Longrightarrow> X be  RightModStr-over F \<Longrightarrow> X be addLoopStr" using  RightModStr_over addLoopStr by simp

abbreviation BiModStr_fields_prefix ("BiModStr'_fields _") where
 "BiModStr_fields F \<equiv>(#carrier \<rightarrow> set'; addF\<rightarrow> BinOp-of' the' carrier; ZeroF \<rightarrow> Element-of' the' carrier;
               lmult \<rightarrow>  Function-of' [: the carrier of F,the' carrier ':], the' carrier;
               rmult \<rightarrow>  Function-of' [:' the' carrier,the carrier of F:], the' carrier #)"   
    
definition  BiModStr_over ("BiModStr-over _") where 
  "struct BiModStr-over F BiModStr_fields F"   
  
lemma BiModStr_over_well:
  assumes "F be one-sorted"
  shows "BiModStr_fields F well defined on {carrier}\<union>{addF}\<union>{ZeroF}\<union>{lmult}\<union>{rmult}" 
proof(rule  Fields_add_argM1[OF ModuleStr_over_well[OF assms]],simp add:string,simp add:string)
  show "for X1 be ModuleStr_fields F\<parallel>Function holds ex it be Function-of [: the carrier of X1, the carrier of F:], the carrier of X1 st True" 
  proof(rule ballI)
    fix X1 assume "X1 be  ModuleStr_fields F\<parallel>Function"
    hence A1: "the carrier of X1 be set" "the carrier of F be set" using field assms one_sorted by auto+ 
    hence " [: the carrier of X1, the carrier of F:] be set" using zfmisc_1_def_2a by simp       
    thus "ex it be Function-of [: the carrier of X1, the carrier of F:], the carrier of X1 st True" using funct_2_cl_ex A1 by auto        
  qed
qed

schematic_goal BiModStr_over:
   assumes "F be one_sorted"
   shows ?X by (rule struct_well_defined[OF BiModStr_over_def BiModStr_over_well[OF assms]])

theorem  BiModStr_inheritance:
  assumes "F be one_sorted" "X be  BiModStr-over F"
  shows "X be ModuleStr-over F" "X be RightModStr-over F" 
using BiModStr_over ModuleStr_over RightModStr_over assms by auto

end