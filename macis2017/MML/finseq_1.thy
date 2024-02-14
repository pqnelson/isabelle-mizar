\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory finseq_1
  imports "../Mizar/Mizar_Nat" "Funct_1"
begin

definition finseq_1_def_1 ("Seg _") where
  "func Seg n \<rightarrow> set equals
     { i where i be Element-of NAT: i <> {} & i c= n }"
    
schematic_goal finseq_1_def_1:
  assumes "n be Element-of NAT" shows "?X" by (rule equals_property[OF finseq_1_def_1_def, of n, OF all_set]) 
  
theorem finseq_1_cl_1:
  "Seg {} = {}"
proof
  show "Seg {} be set" "{} be set" using all_set by auto
  fix x
  show "x in Seg {} iff x in {}"
  proof(rule iffI3)
    show "x in Seg {} implies x in {}"
    proof
      assume "x in Seg {}"
      hence B1: "x in { i where i be Element-of NAT: i <> {} & i c= {} }" using finseq_1_def_1 nat_0 by auto 
     obtain v where 
    T2:"v be  Element-of NAT" and
    A2: "v = x" and
    A3: "x <>{} & x c= {}" using Fraenkel_A1_ex[OF _ B1] by auto 
      have "{} c= x" using xboole_0_def_2 xboole_0_def_1a by auto
      thus "x in {}" using A3 xboole_0_def_10 all_set by auto     
    qed
    assume "x in {}"       
    thus "x in Seg {}" using xboole_0_def_1a xboole_0_def_1b all_set by auto  
  qed
qed
 
theorem finseq_1_cl:
  "n be Element-of NAT implies Seg n c=  NAT"
proof(rule impI,unfold tarski_def_3,intro ballI impI)
  assume A1: "n be Element-of NAT"
  fix x 
  assume "x be object" "x in Seg n"
  hence B1: "x in { i where i be Element-of NAT: i <> {} & i c= n }" using finseq_1_def_1 A1 by auto
   obtain i where 
    T2:"i be Element-of NAT" and
    A2: "i = x" and
    A3: "i <>{} & i c= n" using Fraenkel_A1_ex[OF _ B1] by auto           
  show "x in NAT" using T2 A2 nat_1[of i] by simp
qed  
  
  
definition finseq_1_def_2::Attr ("FinSequence-like")
  where finseq_1_def_2[THEN defattr_property]: 
     "attr FinSequence-like means (\<lambda>F. F be Relation & (ex n be Element-of NAT st dom F = Seg n))"
   
abbreviation 
  "FinSequence \<equiv> FinSequence-like \<parallel> Function"

theorem finseq_1_cl_2:
  "cluster empty \<rightarrow> FinSequence-like for set"
proof(intro ballI impI,unfold finseq_1_def_2,rule conjI)
  fix X assume A1: "X be set" "X is empty"
  thus "X be Relation" using relat_1_cl_1 by simp   
  have "dom X = Seg {}" using finseq_1_cl_1 relat_1_cl_20 A1 by auto
  thus "ex n be Element-of NAT st dom X=Seg n" using nat_0 by auto    
qed  
  
definition finseq_1_def_4 ("FinSequence-of _")
  where "mode FinSequence-of D \<rightarrow> FinSequence means
     (\<lambda>it. rng it c= D)"  

schematic_goal finseq_1_def_4: 
  assumes "D be set" shows "?X"
proof (rule mode_property[OF  finseq_1_def_4_def, of D])    
  have "{} is empty" by auto
  hence A1: "{} be FinSequence"  using finseq_1_cl_2 funct_1_cl_1 relat_1_def_1a by auto    
  have "rng {} ={}" using relat_1_def_1a by auto 
  then show "ex x be FinSequence st  rng x \<subseteq> D" using A1 by auto      
qed
  
definition finseq_1_def_11 ("_*") where
  "func D* \<rightarrow> set means
     \<lambda>it. for x be object holds
         x in it iff x be FinSequence-of D"

schematic_goal finseq_1_def_11:
  assumes "D be set" shows "?X"
proof (induct rule: means_property[OF finseq_1_def_11_def, of D,case_names existence uniqueness])
  case existence
    let ?P = "\<lambda>p . p be FinSequence-of D"
    have A0: "bool [:NAT,D:] be set" using all_set by auto
     obtain IT where
   A1:"IT be set"  "for x being object holds x in IT iff x in bool [:NAT,D:] & ?P(x)" using xboole_0_sch_1[OF A0, of ?P] by blast
     show "ex IT be set st for x be object holds x in IT iff x be FinSequence-of D"
     proof(rule bexI[of _ IT],rule ballI, rule iffI3)
       show "IT be set" using A1(1) by simp 
       fix x assume "x be object"
       show "x in IT implies x be FinSequence-of D" using A1 by auto
       assume A2: "x be FinSequence-of D" 
       then obtain n where 
         A3:"n be Element-of NAT" "dom x = Seg n" using finseq_1_def_2 finseq_1_def_4 all_set by auto    
       have A4: "rng x c= D" using A2 finseq_1_def_4 all_set by auto 
       have "dom x c= NAT" using A3 finseq_1_cl[of n] A3 by auto
       hence A5: "[:dom x,rng x:] c= [:NAT,D:]" using A4 A3(1) zfmisc_1_th_96[of D "rng x" NAT "dom x"] all_set by auto    
       have "x c= [:dom x,rng x:]" using relat_1_th_7[of x] A2 finseq_1_def_4 all_set by auto    
       hence "x c= [:NAT,D:]" using A5 by auto
       hence "x in bool [:NAT,D:]" using all_set zfmisc_1_def_1 by auto    
       thus "x in IT" using A1(2) A2 by auto 
     qed
   case uniqueness     
  fix A1 A2
  assume A1:"A1 be set" "(for x be object holds
         x in A1 iff x be FinSequence-of D)" and
        A2: "A2 be set" "for x be object holds
         x in A2 iff x be FinSequence-of D"
    {
      fix x
      assume Z1: "x be object"
      have "x in A1 iff (x be FinSequence-of D)" using Z1 A1 by auto
      then have "x in A1 \<longleftrightarrow> x in A2" using Z1 A2 by auto
    }
  thus "A1 = A2" using tarski_th_2[OF A1(1) A2(1)] by auto
qed  

theorem finseq_1_th:
  "{} in D*"
proof-
  have "{} is empty" by auto
  hence A1: "{} be FinSequence"  using finseq_1_cl_2 funct_1_cl_1 relat_1_def_1a by auto    
  have "rng {} ={}" using relat_1_def_1a by auto 
  hence "{} be FinSequence-of D" using A1 finseq_1_def_4 all_set by auto
  thus "{} in D*" using finseq_1_def_11 all_set by auto    
qed  
  
end