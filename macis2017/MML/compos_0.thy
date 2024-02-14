\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory compos_0
  imports finseq_1
begin

definition compos_0_def_1 ("standard-ins") where compos_0_def_1[THEN defattr_property]: 
  "attr standard-ins means (\<lambda>S. S be set & (ex X be non empty \<parallel>set st S c= [:NAT, NAT*,X*:]))"   

definition InsCode  ("InsCode _")
where compos_0_synonym_1: "let x be object synonym InsCode x for x`1`1"

definition JumpPart  ("JumpPart _")
where compos_0_synonym_2: "let x be object synonym JumpPart x for x`1`2"

definition AddressPart  ("AddressPart _")
where compos_0_synonym_3: "let x be object synonym AddressPart x for x`2"

text_raw \<open>\DefineSnippet{instruction}{\<close>
term "[InsCode i, JumpPart i, AddressPart i]"  
text_raw \<open>}%EndSnippet\<close>
  
theorem compos_0_cl_1:
  "let S be non empty \<bar>standard-ins \<parallel>set & 
       I be Element-of S
   cluster AddressPart I \<rightarrow> FinSequence-like \<bar> Function_like \<bar> Relation_like"
proof-
  assume A1: "S be non empty \<bar>standard-ins \<parallel>set & 
       I be Element-of S"
  then obtain X where
    A2: "X be non empty \<parallel>set"  "S c= [:NAT, NAT*,X*:]" using compos_0_def_1 by auto 
  have "I in S" using A1 Element_of[of S I] by auto
  hence "I in [:[:NAT, NAT*:],X*:]" using A2(2) zfmisc_1_def_3 all_set by auto 
  then obtain i1 i2 i3 where
     "i1 be object" "i2 be object"  "i3 be object" and
    A3: "I = [[i1,i2],i3] & i1 in NAT & i2 in NAT* & i3 in X*" using zfmisc_3 by auto
  have "AddressPart I = i3" using compos_0_synonym_3 A3 xtuple_0_reduce by auto
  hence "AddressPart I be FinSequence-of X" using A3 finseq_1_def_11 A2 by auto 
  thus "AddressPart I is FinSequence-like \<bar> Function_like \<bar> Relation_like" using finseq_1_def_4 A2 by auto    
qed  
  
theorem compos_0_cl_2:
  "let S be non empty \<bar>standard-ins \<parallel>set & 
       I be Element-of S
   cluster JumpPart I \<rightarrow> FinSequence-like \<bar> Function_like \<bar> Relation_like"
proof-
  assume A1: "S be non empty \<bar>standard-ins \<parallel>set & 
       I be Element-of S"
  then obtain X where
    A2: "X be non empty \<parallel>set"  "S c= [:NAT, NAT*,X*:]" using compos_0_def_1 by auto 
  have "I in S" using A1 Element_of[of S I] by auto
  hence "I in [:[:NAT, NAT*:],X*:]" using A2(2) zfmisc_1_def_3 all_set by auto 
  then obtain i1 i2 i3 where
     "i1 be object" "i2 be object"  "i3 be object" and
    A3: "I = [[i1,i2],i3] & i1 in NAT & i2 in NAT* & i3 in X*" using zfmisc_3 by auto
  have "JumpPart I = i2" using compos_0_synonym_2 A3 xtuple_0_reduce by auto
  hence "JumpPart I be FinSequence-of NAT" using A3 finseq_1_def_11 all_set by auto 
  thus "JumpPart I is FinSequence-like \<bar> Function_like \<bar> Relation_like" using finseq_1_def_4 all_set by auto       
qed  
    
definition compos_0_def_2 ("InsCodes _") where
  "func InsCodes S \<rightarrow> set equals
     proj1 (proj1 S)"

schematic_goal compos_0_def_2:
  assumes "S be set" shows "?X" by (rule equals_property[OF compos_0_def_2_def, of S, OF all_set]) 

abbreviation compos_0_mode_1 ("InsType-of _") where
  "InsType-of S \<equiv> Element-of InsCodes S"
    
theorem compos_0_redef_1:
  "let S be non empty \<bar>standard-ins \<parallel>set &
       I be Element-of S
  redefine func InsCode I \<rightarrow> InsType-of S"
proof-
  assume A1: "S be non empty \<bar>standard-ins \<parallel>set &
       I be Element-of S"
   then obtain X where
    A2: "X be non empty \<parallel>set"  "S c= [:NAT, NAT*,X*:]" using compos_0_def_1 by auto 
  have B1: "I in S" using A1 Element_of[of S I] by auto
  hence "I in [:[:NAT, NAT*:],X*:]" using A2(2) zfmisc_1_def_3 all_set by auto 
  then obtain i1 i2 i3 where
     "i1 be object" "i2 be object"  "i3 be object" and
    A3: "I = [[i1,i2],i3] & i1 in NAT & i2 in NAT* & i3 in X*" using zfmisc_3 by auto
  have A4: "InsCode I = i1" using compos_0_synonym_1 A3 xtuple_0_reduce by auto       
  have "[i1,i2] in proj1 S" using xtuple_0_def_12 all_set B1 A3 by auto
  hence "i1 in InsCodes S" using xtuple_0_def_12 all_set B1 A3 A1  compos_0_def_2 by auto    
  hence "i1 be Element-of InsCodes S" using Element_of_rule by auto
  thus "InsCode I be InsType-of S" using A4 by auto    
qed  

text_raw \<open>\DefineSnippet{compos_0_def_3}{\<close>  
definition compos_0_def_3 ("JumpParts _ , _") where
  "func JumpParts I , T \<rightarrow> set equals
     {JumpPart i where i be Element-of I: InsCode i = T }"
text_raw \<open>}%EndSnippet\<close>
  
schematic_goal compos_0_def_3:
  assumes "S be non empty \<bar>standard-ins \<parallel>set &
           T be InsType-of S" 
  shows "?X" by (rule equals_property[OF compos_0_def_3_def, of S T, OF all_set]) 
  
definition compos_0_def_4 ("AddressParts _ , _") where
  "func AddressParts S , T \<rightarrow> set equals
     { AddressPart I where I be Element-of S: InsCode I = T }"
    
schematic_goal compos_0_def_4:
  assumes "S be non empty\<bar>standard-ins\<parallel>set &
           T be InsType-of S" 
  shows "?X" by (rule equals_property[OF compos_0_def_4_def, of S T, OF all_set])   

text_raw \<open>\DefineSnippet{compos_0_def_5}{\<close> 
definition compos_0_def_5 ("homogeneous") where  
  "attr homogeneous means (\<lambda>I. 
     I be non empty\<bar>standard-ins\<parallel>set & 
      (for i,j be Element-of I st InsCode i = InsCode j holds
         dom JumpPart i = dom JumpPart j))"   
text_raw \<open>}%EndSnippet\<close>

lemmas  compos_0_def_5 = compos_0_def_5_def[THEN defattr_property]
  
  text_raw \<open>\DefineSnippet{compos_0_def_7}{\<close> 
definition compos_0_def_7 ("J|A-independent") where 
  "attr J|A-independent means (\<lambda>I. 
     I be non empty\<bar>standard-ins\<parallel>set & 
     (for n be Nat, f1,f2 be NAT-valued \<parallel>Function, p be object
        st dom f1 = dom f2 & [n,f1,p] in I holds [n,f2,p] in I))"   
  text_raw \<open>}%EndSnippet\<close>
 
lemmas  compos_0_def_7 = compos_0_def_7_def[THEN defattr_property]

    
text_raw \<open>\DefineSnippet{compos_0_def_10}{\<close>  
definition compos_0_def_10 ("with'_halt") where compos_0_def_10[THEN defattr_property]: 
  "attr with_halt means (\<lambda>S. S be set & [0,{},{}] in S)"  
text_raw \<open>}%EndSnippet\<close>

definition compos_0_def_11 ("halt _") where
  "func halt S \<rightarrow> Element-of S equals
     [0,{},{}]"
      
schematic_goal compos_0_def_11:
  assumes "S be with_halt \<parallel>set" shows "?X"
proof (rule equals_property[OF compos_0_def_11_def, of S]) 
  have "[0,{},{}] in S" using assms compos_0_def_10 by auto
  thus "[0,{},{}] be Element-of S" using Element_of_rule by auto     
qed
  
theorem compos_0_cl_10[rule_format]:
  "cluster with_halt \<rightarrow> non empty for set" 
proof(intro ballI impI)
  fix X assume A1: "X be set" "X is with_halt"
  hence "[0,{},{}] in X" using compos_0_def_10 by auto  
  thus "X is non empty" using  xboole_0_cl_3 A1 by auto  
qed

text_raw \<open>\DefineSnippet{Instructions}{\<close>
abbreviation
  "Instructions \<equiv> J|A-independent\<bar>homogeneous\<bar>with_halt\<bar>standard-ins\<parallel>set"
text_raw \<open>}%EndSnippet\<close>
theorem Instructions_non_empty:
  "X be Instructions \<Longrightarrow> X is non empty"
proof-
  assume "X be Instructions"
  hence "[0,{},{}] in X" using compos_0_def_10 by auto
  thus "X is non empty" using xboole_0_def_1b all_set by auto    
qed    

theorem Instructions_ex:
  "{[0,{},{}]} be Instructions"
proof-
  let ?x = "[0,{},{}]"
  let ?I = "{?x}" 
  have W1: "?I is standard-ins" unfolding compos_0_def_1
  proof(rule conjI)
    show "?I be set" by auto
    show "ex X be non empty  \<parallel>  set st  ?I \<subseteq> [: NAT , NAT* , X* :]"   
    proof(rule bexI[of _ NAT],unfold tarski_def_3,intro ballI impI)
      show "NAT be non empty\<parallel>set" using NAT_non_empty by auto
      fix x assume "x in {?x}"
      hence A1:"x=?x" using tarski_def_1b by auto
      have A2: "{} in NAT" "{} in NAT*" using  zero_nat finseq_1_th by simp+
      hence "[{},{}] in [:NAT,NAT*:]" by auto
      hence "x in [: [:NAT , NAT*:] , NAT* :]"  using A1 A2 by auto
      thus "x in [: NAT , NAT* , NAT* :]" using zfmisc_1_def_3 all_set by auto          
    qed
  qed 
  have W2:"?I is with_halt" using tarski_def_1b compos_0_def_10 by auto
  have W3:"?I is non empty" using xboole_0_cl_3 by auto    
  have W4: "?I is homogeneous" unfolding compos_0_def_5
  proof(intro conjI ballI impI)
    show "?I be non empty  \<bar>  standard-ins  \<parallel>  set" using W1 W3 by auto
    fix I J 
    assume "I be Element-of ?I" "J be Element-of ?I" 
    hence "I in ?I" "J in ?I" using W3 by auto
    hence "I=?x" "J=?x" using tarski_def_1b by auto
    thus "dom JumpPart I = dom JumpPart J" by simp    
  qed  
  have "?I is J|A-independent" unfolding compos_0_def_7
  proof(intro conjI ballI impI)
    show "?I be non empty  \<bar>  standard-ins  \<parallel>  set" using W1 W3 by auto
    fix T f1 f2 p
    assume A1:  "T be Nat" "f1 be NAT -valued  \<parallel>  Function"
       "f2 be NAT -valued  \<parallel>  Function" "dom f1 = dom f2 & [T , f1 , p] in ?I"
    have "[T , f1 , p] in ?I" using A1 by auto
    hence L: "[T , f1 , p] = ?x" using tarski_def_1b by auto
    have L1:"[T,f1] = [0,{}]" using xtuple_0_th_1[rule_format, OF L] by auto 
    have "f1 = {}" using  xtuple_0_th_1[rule_format, OF L1] by auto
    hence "dom f1 = {}" using relat_1_def_1a by auto
    hence "f1=f2" using relat_1_th_41 A1 by auto
    thus "[T , f2 , p] in ?I" using A1 by auto
  qed 
  thus ?thesis using W1 W2 W4 by auto
qed  
  
end