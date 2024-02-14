\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Memstr_0
  imports Struct_0
begin
  
abbreviation MemStruct_fields_prefix ("Mem-Struct'_fields _") 
  where "Mem-Struct_fields N \<equiv> (#
   carrier \<rightarrow> \<lambda>S. set;
   ZeroF \<rightarrow> \<lambda>S. Element-of the carrier of S;
   Object-Kind \<rightarrow> \<lambda>S. Function-of the carrier of S, N;
   ValuesF \<rightarrow>  \<lambda>S. ManySortedSet-of N#)"

    
text_raw \<open>\DefineSnippet{MemStructEx1}{\<close>
term "{[carrier,the set]}\<union>
      {[ZeroF,the Element-of the set]}\<union>
      {[Object-Kind,the Function-of the carrier of (the set), N]}\<union>
      {[ValuesF,the ManySortedSet-of N]}"  
text_raw \<open>}%EndSnippet\<close>
  
text_raw \<open>\DefineSnippet{MemStruct}{\<close>
definition MemStruct_over ("Mem-Struct-over _") where 
"struct Mem-Struct-over N (# 
   carrier \<rightarrow> \<lambda>S. set;
   ZeroF \<rightarrow> \<lambda>S. Element-of the carrier of S;
   Object-Kind \<rightarrow> \<lambda>S. Function-of the carrier of S, N;
   ValuesF \<rightarrow>  \<lambda>S. ManySortedSet-of N
#)"
text_raw \<open>}%EndSnippet\<close>

lemma MemStruct_over_well_1:
  assumes "N be set" 
  shows "(#carrier \<rightarrow> \<lambda>S. set;
           ZeroF \<rightarrow> \<lambda>S. Element-of the carrier of S;
           Object-Kind \<rightarrow> \<lambda>S. Function-of the carrier of S, N#) well defined on {carrier} \<union>{ZeroF}\<union>{Object-Kind}"
proof(rule Fields_add_argM1[OF ZeroStr_well],simp add:string,simp add:string)
  show "for X1 be  ZeroStr_fields\<parallel>Function holds ex it be Function-of the carrier of X1, N st True" 
  proof(rule ballI)
    fix X1 assume "X1 be ZeroStr_fields\<parallel>Function"
    hence A1: "the carrier of X1 be set" "N be set" using field assms one_sorted by auto+ 
    thus "ex it be Function-of the carrier of X1, N st True" using funct_2_cl_ex A1 by auto        
  qed  
qed
 
lemma MemStruct_over_well:
  assumes "N be set" 
  shows "Mem-Struct_fields N well defined on {carrier} \<union>{ZeroF}\<union>{Object-Kind}\<union>{ValuesF}"
proof(rule Fields_add_0_arg_Mode[OF MemStruct_over_well_1[OF assms]],simp add:string)
  show "ex it be ManySortedSet-of N st True" using pboole_cl_ex assms by auto 
qed
  
schematic_goal MemStruct_over:
  assumes "N be set"
  shows ?X by (rule struct_well_defined[OF MemStruct_over_def MemStruct_over_well[OF assms]])

theorem MemStruct_over_inheritance:
  assumes "N be set" 
          "X be Mem-Struct-over N"
  shows "X be ZeroStr" using  MemStruct_over ZeroStr assms by auto
    
definition Instruction_Counter_prefix  ("IC \<^sub>_")
where memstr_0_synonym_1: "let N be set & S be Mem-Struct-over N synonym IC \<^sub>S for 0\<^sub>S"

definition Data_Locations_prefix  ("Data-Locations \<^sub>_")
where memstr_0_synonym_2: "let N be set & S be Mem-Struct-over N synonym Data-Locations \<^sub>S for NonZero \<^sub>S"   

text_raw \<open>\DefineSnippet{memstr_0_def_2}{\<close>  
definition memstr_0_def_2 ( "the'_Values'_of _ " 190) where
  "func the_Values_of M \<rightarrow> ManySortedSet-of the carrier of M equals
     the ValuesF of M \<circ> the Object-Kind of M"
text_raw \<open>}%EndSnippet\<close>  

schematic_goal memstr_0_def_2:
  assumes "N be with_zero\<parallel>set & S be Mem-Struct-over N" shows "?X"    
proof (rule equals_property[OF memstr_0_def_2_def,of S])
  have N: "N <> {}" using assms with_zero by auto
  let ?V = "the ValuesF of S"
  let ?O = "the Object-Kind of S" 
  have V: "?V be  ManySortedSet-of N" using assms MemStruct_over field by auto
  have O: "?O be Function-of the carrier of S, N" using assms MemStruct_over field by auto
  
  hence O1: "?O be Function" using all_set relset_1_cl_1 relset_1_def_1  by auto  
  hence A0: "?V*`?O be Function" using assms  funct_1_cl_F[of ?O ?V] V by auto
  have A2: "dom  ?O = the carrier of S" using O funct_2_def_1a[of ?O] N by auto 
  have "?O is N-valued" using relset_1_cl_2 all_set O by auto     
  hence A1: "rng ?O c= N" using relat_1_def_19a[of ?O N] by auto
  have "dom ?V=N"  using partfun_1_def_2a V by simp
  hence "dom (?V*`?O) = the carrier of S" using A2 V O1 funct_2_lm_1[of ?O ?V] A1 by auto
  thus "?V*`?O be ManySortedSet-of the carrier of S" using 
     A0 pboole_def_1_th_1 by auto
qed
     
text_raw \<open>\DefineSnippet{memstr_0_mode_1}{\<close>
abbreviation memstr_0_mode_1 ("PartState-of _" 190) where 
  "PartState-of M \<equiv> the carrier of M-defined \<bar> the_Values_of M-compatible \<parallel> Function"  
text_raw \<open>}%EndSnippet\<close>

definition memstr_0_def_3 ("_ :with'_non-empty'_values") where memstr_0_def_3[THEN defattr_property]:
  "attr N :with_non-empty_values means (\<lambda>S. (S be Mem-Struct-over N) & (the_Values_of S) is non-empty)"
  
theorem memstr_0_cl_1:
  "let N be with_zero\<parallel>set & S be N:with_non-empty_values \<parallel> Mem-Struct-over N
   cluster (the carrier of S):total for PartState-of S"  
proof-
  assume A1: "N be with_zero\<parallel>set & S be N:with_non-empty_values \<parallel> Mem-Struct-over N"
  hence A2: "the_Values_of S be non-empty\<parallel> Function " using memstr_0_def_3 memstr_0_def_2 by auto
  have "the_Values_of S is (the carrier of S):total" using A1 memstr_0_def_2[of N S] by auto 
  thus ?thesis using funct_2_cl_comp[of "the carrier of S" "the_Values_of S"]  A1 A2 all_set by auto
qed
  
text_raw \<open>\DefineSnippet{memstr_0_mode_2}{\<close>
abbreviation memstr_0_mode_2 ("State-of _" 190)
  where "State-of M \<equiv>
         (the carrier of M):total \<bar> the_Values_of M-compatible \<parallel> Function"  
text_raw \<open>}%EndSnippet\<close>

abbreviation memstr_0_mode_3 ("Object-of _" 190)
where "Object-of S \<equiv> Element-of-struct S"

definition memstr_0_def_4_prefix ( "ObjectKind'( _ , _ ') _ " 190) where
  "func ObjectKind(N,S) o \<rightarrow> Element-of N equals
    (the Object-Kind of S).o "

schematic_goal memstr_0_def_4:
  assumes "N be with_zero\<parallel>set & S be non empty-struct \<parallel> Mem-Struct-over N & o be Object-of S" shows "?X"    
proof (rule equals_property[OF memstr_0_def_4_prefix_def,of S o N])
  have N: "N <> {}" using assms with_zero by auto
  let ?O = "the Object-Kind of S" 
  have O: "?O be Function-of the carrier of S, N" using assms MemStruct_over field by auto
  hence O1: "?O be Function" using all_set relset_1_cl_1 relset_1_def_1  by auto  
  have A2: "dom  ?O = the carrier of S" using O funct_2_def_1a[of ?O] N by auto 
  have "?O is N-valued" using relset_1_cl_2 all_set O by auto     
  hence A1: "rng ?O c= N" using relat_1_def_19a[of ?O N] by auto
  have "the carrier of S <>{}" using struct_0_def_1_b assms by auto
  hence "o in dom ?O" using A2 assms Element_of_rule1[of _ o] by auto
 thus  "(?O .o) be Element-of N"  using  A1 funct_1_def_3[of ?O] O1 Element_of_rule by auto   
qed
  
definition memstr_0_def_5_prefix ( "Values'( _ , _ ') _ " 190) where
  "func Values(N,S) o \<rightarrow> set equals
    (the_Values_of S).o"

schematic_goal memstr_0_def_5:
  assumes "N be with_zero\<parallel>set & S be non empty-struct \<parallel> Mem-Struct-over N & o be Object-of S" shows "?X"    
proof (rule equals_property[OF memstr_0_def_5_prefix_def,of S o N])
  show "((the_Values_of S).o) be set" using all_set by auto
qed

 theorem memstr_0_cl_2:
  "let N be with_zero\<parallel>set & 
       S be non empty-struct \<bar> N:with_non-empty_values \<parallel> Mem-Struct-over N &
       o be Object-of S
   cluster Values(N,S) o \<rightarrow> non empty"
 proof-
   let ?VS = "the_Values_of S"
   assume A0: "N be with_zero\<parallel>set & 
       S be non empty-struct \<bar> N:with_non-empty_values \<parallel> Mem-Struct-over N &
       o be Object-of S"
   hence Vo: "Values(N,S) o =  ?VS .o" using A0 memstr_0_def_5 by simp          
   have VS: "?VS be ManySortedSet-of the carrier of S" using A0 memstr_0_def_2[of N S] by auto   
   hence A2: "dom ?VS = the carrier of S" using partfun_1_def_2a by auto  
   have VS1:"?VS be Function" using VS by auto
   have "the carrier of S <>{}" using VS struct_0_def_1_b A0 by auto
   hence "o in dom ?VS" using A2 A0 Element_of_rule1[of _ o] by auto
   hence H: "?VS. o in rng ?VS" using funct_1_def_3[OF VS1] by auto     
   have "?VS is non-empty" using memstr_0_def_3 A0 by auto    
   hence "?VS. o <> {}" using H funct_1_def_9 by auto
   thus "Values(N,S) o is non empty" using Vo xboole_0_lm_1 all_set by auto
 qed
   
   
definition memstr_0_def_8_prefix ( "DataPart \<^sub>_ _ " 190) where
  "func DataPart \<^sub>S p \<rightarrow> PartState-of S equals
    p | Data-Locations \<^sub>S"
  
schematic_goal memstr_0_def_8:
  assumes "N be with_zero\<parallel>set & S be Mem-Struct-over N & p be PartState-of S" shows "?X"    
proof (rule equals_property[OF memstr_0_def_8_prefix_def,of p S])
  let ?D="Data-Locations \<^sub>S"
  let ?pD ="p | ?D" 
  let ?V = "the_Values_of S"
  have W1: "?pD be Function" using assms funct_1_cl all_set relat_1_def_11 by auto
  have "dom p c= the carrier of S" using assms relat_1_def_18a by simp
  hence "dom ?pD c= the carrier of S" using assms relat_1_th_55[of ?D p] all_set by auto
  hence W2: "?pD is the carrier of S -defined" using W1 relat_1_def_18a all_set by auto  
  have W3: "?pD is ?V  -compatible"
  proof(unfold funct_1_def_14,intro conjI ballI impI)
    show "?pD be Function" using W1 by simp
    show "?V be Function" using assms memstr_0_def_2 by auto 
    fix x assume A1: "x be object" "x in dom ?pD"
    hence A2: "?pD. x = p .x" using funct_1_th_47 assms all_set by auto
    have "x in dom p" using  A1 relat_1_th_51 assms all_set by auto
    hence "p. x in ?V.x" using funct_1_def_14 assms by auto          
    thus "?pD. x in ?V. x" using A2 by auto   
  qed    
  show "?pD be PartState-of S" using W1 W2 W3 by simp
qed

definition memstr_0_def_9 ("_ :data-only") where memstr_0_def_9[THEN defattr_property]:
  "attr S :data-only means (\<lambda>p. (p be PartState-of  S) & dom p misses {IC \<^sub>S})"

theorem memstr_0_th_3[rule_format]:
  "for N be with_zero\<parallel>set holds
      for S be Mem-Struct-over N holds
         for p be PartState-of S holds 
           not IC \<^sub>S in dom DataPart \<^sub>S p"
proof(intro ballI)
  fix N S p
  assume T0: "N be with_zero\<parallel>set" 
         "S be Mem-Struct-over N"
         "p be PartState-of S"
  show "not IC \<^sub>S in dom DataPart \<^sub>S p"
  proof
    have "S be ZeroStr" using T0 MemStruct_over_inheritance by auto  
    hence A1: "NonZero \<^sub>S = ([#]S) \\ {0\<^sub>S}" using struct_0_def_17 by simp    
    assume "IC \<^sub>S in dom DataPart \<^sub>S p"
    hence "IC \<^sub>S in dom (p | Data-Locations \<^sub>S)" using T0 memstr_0_def_8[of N S p] by auto 
    hence "0\<^sub>S in NonZero \<^sub>S" using relat_1_th_51 T0 all_set memstr_0_synonym_2[of N S] memstr_0_synonym_1[of N S] T0 by auto 
    thus "False" using tarski_def_1b A1 by auto    
  qed  
qed
  
theorem memstr_0_th_4[rule_format]:
  "for N be with_zero\<parallel>set holds
      for S be Mem-Struct-over N holds
         for p be PartState-of S holds 
            {IC \<^sub>S}  misses dom DataPart \<^sub>S p"
proof(intro ballI)
  fix N S p
  assume T0: "N be with_zero\<parallel>set" 
         "S be Mem-Struct-over N"
         "p be PartState-of S"
  have "{IC \<^sub>S}  meets dom DataPart \<^sub>S p implies False"
  proof
    assume "{IC \<^sub>S}  meets dom DataPart \<^sub>S p"
    then obtain x where
      A1: "x be object" "x in {IC \<^sub>S}  & x in dom DataPart \<^sub>S p" using xboole_0_th_3 all_set by auto 
    hence "x = IC \<^sub>S" using tarski_def_1b by auto
    thus "False" using A1 memstr_0_th_3 T0 by auto    
  qed
  thus "{IC \<^sub>S}  misses dom DataPart \<^sub>S p" using xboole_0_antonym_meets all_set by auto         
qed  
text_raw \<open>\DefineSnippet{memstr_0_th_6}{\<close>  
theorem memstr_0_th_6:
  "for N be with_zero\<parallel>set holds
      for S be Mem-Struct-over N holds
         for p be PartState-of S holds
    p is S:data-only iff dom p c= Data-Locations \<^sub>S"
text_raw \<open>}%EndSnippet\<close>  
proof(intro ballI,rule iffI3)
  fix N S p  
  assume T0: "N be with_zero\<parallel>set" 
         "S be Mem-Struct-over N"
         "p be PartState-of S"
   have T1: "S be ZeroStr" using T0 MemStruct_over_inheritance by auto  
  hence A2: "Data-Locations \<^sub>S = ([#]S) \\ {IC \<^sub>S}" using struct_0_def_17 memstr_0_synonym_2[of N S] memstr_0_synonym_1[of N S] T0 by simp  
  show "p is S:data-only implies dom p c= Data-Locations \<^sub>S"
  proof(rule impI,unfold tarski_def_3, intro ballI impI)
    fix x
    assume A1: "p is S:data-only" "x be object" "x in dom p"
    hence "dom p misses {IC \<^sub>S}" using memstr_0_def_9 by auto
    hence "(dom p \<inter> {IC \<^sub>S}) is empty " using xboole_0_def_7 all_set xboole_0_def_2c by auto 
    hence A3: "not x in {IC \<^sub>S}" using A1(3) xboole_0_def_1a all_set by auto               
    have "x in [#]S" using T0 A1(3) struct_0_def_3 T1 ZeroStr_inheritance by auto     
    thus "x in Data-Locations \<^sub>S" using A2 A3 xboole_0_def_5 by auto      
  qed
  assume A3: "dom p c= Data-Locations \<^sub>S"
   have "dom p meets {IC \<^sub>S}  implies False"
  proof
    assume "dom p meets {IC \<^sub>S}"
    then obtain x where
      A1: "x be object" "x in dom p  & x in {IC \<^sub>S}" using xboole_0_th_3 all_set by auto 
    thus "False" using A3 A2 tarski_def_1b by auto    
  qed    
  hence "dom p misses {IC \<^sub>S}" using xboole_0_antonym_meets all_set by auto
  thus "p is S:data-only" using memstr_0_def_9 T0 by simp   
qed  

end