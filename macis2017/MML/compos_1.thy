\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory compos_1
  imports compos_0 "../Mizar/Mizar_struct" Funct_2
begin

text_raw \<open>\DefineSnippet{COM_Struct}{\<close>
definition COM_Struct :: "Mode"  ("COM-Struct") where
  "struct COM-Struct (# InstructionsF \<rightarrow> \<lambda>_. Instructions #)"
text_raw \<open>}%EndSnippet\<close>

lemma COM_Struct_well:"(# InstructionsF \<rightarrow> \<lambda>_. Instructions #) well defined on {InstructionsF}"
proof(rule First_0_arg_Mode)
  show "ex x being Instructions st True" proof (rule bexI[of _ "{[0,{},{}]}"])
    show "{[0,{},{}]} be Instructions" using Instructions_ex by simp
    show "True" by simp                        
  qed
qed
  
schematic_goal COM_Struct:
  shows ?X by (rule struct_well_defined[OF COM_Struct_def COM_Struct_well])

abbreviation compos_1_mode_1 ("Instruction-of _") where
  "Instruction-of S \<equiv> Element-of the InstructionsF of S"
    
definition compos_1_def_10 ("halt \<^sub>_") where
  "func halt \<^sub>S \<rightarrow> Instruction-of S equals
     halt the InstructionsF of S"
    
schematic_goal compos_1_def_10:
  assumes "S be COM-Struct" shows "?X" 
proof (rule equals_property[OF compos_1_def_10_def, of S]) 
  have "the InstructionsF of S be Instructions" using field assms COM_Struct by auto
  thus "halt the InstructionsF of S be Instruction-of S" using compos_0_def_11[of "the InstructionsF of S"]  by auto   
qed  

abbreviation Instruction_Sequence ("Instruction-Sequence-of _") where
  "Instruction-Sequence-of S \<equiv> (the InstructionsF of S)-valued \<parallel> ManySortedSet-of NAT"
  
definition compos_1_def_12 ("_ _:halts'_at _") where
  "let S be COM-Struct &
       p be NAT-defined \<bar>(the InstructionsF of S)-valued \<parallel>Function & 
       l be set
   pred p S:halts_at l means
     l in dom p & p. l = halt \<^sub>S"

theorem compos_1_def_13:
  "let S be COM-Struct &
       s be Instruction-Sequence-of S & 
       l be Nat
  redefine pred s S:halts_at l means
    s. l = halt \<^sub>S"
proof(rule redefine_pred_means_property, simp)
  assume A1: "S be COM-Struct & s be the' InstructionsF(S) -valued  \<parallel>  ManySortedSet-of NAT & l be Nat"
  hence "dom s=NAT" "l in NAT" using partfun_1_def_2a nat_2 by auto 
  thus "s S:halts_at l iff s . l = halt \<^sub>S" using A1 compos_1_def_12_def[of S s l] all_set by auto      
qed

end