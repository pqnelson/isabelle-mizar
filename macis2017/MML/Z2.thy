\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Z2
  imports Algstr_0
begin

definition A: "Zero \<equiv> {}" 
definition B: "One \<equiv> {Zero}"

lemma [simp]: "Zero<>One" using tarski_def_1b[of One Zero] prefix_in_irreflexive all_set B A by auto  
lemma [simp]: "[Zero,Zero]<>[Zero,One]" "[Zero,Zero]<>[One,Zero]" "[Zero,Zero]<>[One,One]"
      "[Zero,One]<>[One,Zero]" "[Zero,One]<>[One,One]" "[One,Zero]<>[One,One]"
  using xtuple_0_th_1[of Zero Zero Zero One] xtuple_0_th_1[of Zero Zero One Zero] xtuple_0_th_1[of Zero Zero One One]
        xtuple_0_th_1[of Zero One One Zero] xtuple_0_th_1[of Zero One One One] xtuple_0_th_1[of One Zero One One]by simp+ 
    
theorem DomZ2: "{[Zero,Zero]}\<union>{[Zero,One]}\<union>{[One,Zero]}\<union>{[One,One]} = [:{Zero,One},{Zero,One}:]" 
  proof(unfold xboole_0_def_10[OF all_set all_set],rule conjI) 
    show "{[Zero,Zero]}\<union>{[Zero,One]}\<union>{[One,Zero]}\<union>{[One,One]} \<subseteq> [:{Zero,One},{Zero,One}:]"
      using tarski_def_1b by auto 
    show "[:{Zero,One},{Zero,One}:] \<subseteq> {[Zero,Zero]}\<union>{[Zero,One]}\<union>{[One,Zero]}\<union>{[One,One]} "
    proof (unfold tarski_def_3,intro ballI impI)
      fix xy assume "xy in [:{Zero,One},{Zero,One}:]"
      then obtain x y where
        A1: "xy=[x,y]" "x in {Zero,One} & y in {Zero,One}" using zfmisc_1_def_1 by auto
      thus "xy in {[Zero,Zero]}\<union>{[Zero,One]}\<union>{[One,Zero]}\<union>{[One,One]}" using tarski_def_1b by auto
    qed
  qed

theorem Rng_1:
  "rng {[s,D]}={D}"
proof-
  have "{[s,D]} be Relation" using relat_1_cl_7 by simp
  thus ?thesis using relat_1_th_3[of D s "{[s,D]}"] by auto
qed

theorem Rng_2:
  "rng ({[s1,D1]} \<union> {[s2,D2]}) = {D1}\<union>{D2}"
proof-
  have A1:"{[s1,D1]} be Relation & {[s2,D2]} be Relation" using relat_1_cl_7 by simp
  have "({[s1,D1]} \<union> {[s2,D2]}) be Relation" using relat_1_cl_5[OF A1] by auto
  hence "rng ({[s1,D1]} \<union> {[s2,D2]}) = (rng {[s1,D1]}) \<union> (rng {[s2,D2]})" using xtuple_th_24 relat_1_def_1a by simp
  thus ?thesis using Rng_1 by auto
qed
  
theorem Rng_3:
  "rng ({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) = {D1}\<union>{D2}\<union>{D3}"
proof-
  have A2:"{[s1,D1]} be Relation & {[s2,D2]} be Relation" using relat_1_cl_7 by simp
    have A3: "({[s1,D1]} \<union> {[s2,D2]}) be Relation &  {[s3,D3]} be Relation" using relat_1_cl_7 relat_1_cl_5[OF A2] by simp
  have A4: "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) be Relation" using  relat_1_cl_7 relat_1_cl_5[OF A3] by simp
  hence "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) be Relation" using relat_1_cl_5[of "{[s1,D1]} \<union> {[s2,D2]}" "{[s3,D3]}"] by simp
  hence "rng ({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) = (rng ({[s1,D1]}\<union>{[s2,D2]})) \<union> (rng {[s3,D3]})" using xtuple_th_24 relat_1_def_1a by simp
  thus ?thesis using Rng_1 Rng_2 by auto
qed 
  
theorem Rng_4:
  "rng ({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}) = {D1}\<union>{D2}\<union>{D3}\<union>{D4}"
proof-
  have A2:"{[s1,D1]} be Relation & {[s2,D2]} be Relation" using relat_1_cl_7 by simp
  have A3: "({[s1,D1]} \<union> {[s2,D2]}) be Relation &  {[s3,D3]} be Relation" using relat_1_cl_7 relat_1_cl_5[OF A2] by simp
   have A4: "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) be Relation &  {[s4,D4]} be Relation " using  relat_1_cl_7 relat_1_cl_5[OF A3] by simp
  have A5: "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}) be Relation " using  relat_1_cl_7 relat_1_cl_5[OF A4] by simp     
  hence "rng ({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}) = (rng ({[s1,D1]}\<union>{[s2,D2]}\<union>{[s3,D3]})) \<union> (rng {[s4,D4]})" using xtuple_th_24 relat_1_def_1a by simp
  thus ?thesis using Rng_1 Rng_3 by auto
qed

definition addZ2 ("addZ2") where
  "func addZ2 \<rightarrow> BinOp-of {Zero,One} equals
     {[[Zero,Zero],Zero]}\<union>{[[Zero,One],One]}\<union>{[[One,Zero],One]}\<union>{[[One,One],Zero]}"
  
schematic_goal addZ2:
  shows "?X"
proof (rule equals_property [OF addZ2_def])
  let ?A ="{[[Zero,Zero],Zero]}\<union>{[[Zero,One],One]}\<union>{[[One,Zero],One]}\<union>{[[One,One],Zero]}"
  have T1:"?A be Function" using Function_4[of "[Zero,Zero]" ] by auto 
  have T2:"dom ?A = [:{Zero,One},{Zero,One}:]" using DomZ2 Dom_4 by auto
  have "rng ?A = {Zero,One}" using Rng_4 tarski_def_1b by auto   
  thus "?A be BinOp-of {Zero,One}" using binop_1_mode_2_def funct_2_th_2[OF T1] T2 by simp 
qed
  
definition multZ2 ("multZ2") where
  "func multZ2 \<rightarrow> BinOp-of {Zero,One} equals
     {[[Zero,Zero],Zero]}\<union>{[[Zero,One],Zero]}\<union>{[[One,Zero],Zero]}\<union>{[[One,One],One]}"
  
schematic_goal multZ2:
  shows "?X"
proof (rule equals_property [OF multZ2_def])
  let ?A ="{[[Zero,Zero],Zero]}\<union>{[[Zero,One],Zero]}\<union>{[[One,Zero],Zero]}\<union>{[[One,One],One]}"
  have T1:"?A be Function" using Function_4[of "[Zero,Zero]" ] by auto 
  have T2:"dom ?A = [:{Zero,One},{Zero,One}:]" using DomZ2 Dom_4 by auto
  have "rng ?A = {Zero,One}" using Rng_4 tarski_def_1b by auto   
  thus "?A be BinOp-of {Zero,One}" using binop_1_mode_2_def funct_2_th_2[OF T1] T2 by simp 
qed

definition Z ("Z") where
  "func Z \<rightarrow> doubleLoopStr equals
     {[carrier,{Zero,One}]}\<union>{[addF,addZ2]}\<union>{[multF,multZ2]}\<union>{[OneF,One]}\<union>{[ZeroF,Zero]}"
  
schematic_goal Z:
  shows "?X"
proof (rule equals_property [OF Z_def])
  let ?A = "{[carrier,{Zero,One}]}\<union>{[addF,addZ2]}\<union>{[multF,multZ2]}\<union>{[OneF,One]}\<union>{[ZeroF,Zero]}"
  have "Zero be Element-of {Zero,One}" "One be Element-of {Zero,One}" using Element_of_rule by auto+  
  thus T1: "?A be doubleLoopStr" using doubleLoopStr_ag[of "{Zero,One}" addZ2 multZ2 One Zero] all_set multZ2 addZ2 by auto
qed  
  
theorem Z2d:
  shows "Zero be Element-of-struct Z"
        "One be Element-of-struct Z"
        "x be Element-of-struct Z \<Longrightarrow> x = One or x = Zero"
        "0\<^sub>Z = Zero" "1\<^sub>Z = One"
        "Zero\<oplus>\<^sub>Z Zero = Zero" "Zero\<oplus>\<^sub>Z One = One" "One\<oplus>\<^sub>Z Zero = One" "One\<oplus>\<^sub>Z One = Zero"
        "Zero\<otimes>\<^sub>Z Zero = Zero" "Zero\<otimes>\<^sub>Z One = Zero" "One\<otimes>\<^sub>Z Zero = Zero" "One\<otimes>\<^sub>Z One = One"
        "the carrier of Z={Zero,One}"
proof-
  have T0: "Z be doubleLoopStr" "Z be Function" "Z be one-sorted" "Z be ZeroStr" "Z be OneStr" "Z be addMagma" "Z be multMagma"
       using Z doubleLoopStr one_sorted OneStr ZeroStr addMagma multMagma by auto
  have T1: "the carrier of Z={Zero,One}" "the ZeroF of Z=Zero" "the OneF of Z=One" "the multF of Z=multZ2" "the addF of Z=addZ2" using 
     the_selector_of_1[OF T0(2),of carrier "{Zero,One}"] the_selector_of_1[OF T0(2),of ZeroF Zero] 
     the_selector_of_1[OF T0(2),of OneF One] the_selector_of_1[OF T0(2),of multF multZ2]
     the_selector_of_1[OF T0(2),of addF addZ2] string by (simp add:Z[THEN conjunct2])+
  thus T2: "Zero be Element-of-struct Z"
        "One be Element-of-struct Z" using Element_of_rule by auto  
  show "x be Element-of-struct Z \<Longrightarrow> x = One or x = Zero"
  proof-
    assume A1: "x be Element-of-struct Z"
    have "Zero in the carrier of Z" using T1(1) by auto
    hence "x in the carrier of Z" using A1  Element_of_rule1[of _ x] by auto
    thus ?thesis using T1(1) by auto    
  qed  
  show "0\<^sub>Z = Zero" "1\<^sub>Z = One" using struct_0_def_6[OF T0(4)] T1  struct_0_def_7[OF T0(5)] T1 by auto
  have A0:"addZ2 be Function" using addZ2 binop_1_mode_2_def relset_1_def_1 relset_1_cl_1 all_set by auto   
  let ?A =" {[[Zero , Zero] , Zero]} \<union> {[[Zero , One] , One]} \<union> {[[One , Zero] , One]} \<union> {[[One , One] , Zero]}"   
  have  A1: "addZ2 = ?A" using addZ2 by simp
  have "[[Zero , Zero] , Zero] in ?A" using tarski_def_1b by auto
  hence "[[Zero , Zero] , Zero] in addZ2" using A1  by auto+
  hence "addZ2. [Zero , Zero] = Zero" using funct_1_th_1[OF A0] by auto
  thus "Zero\<oplus>\<^sub>Z Zero = Zero" using T0(6) T1(5) algstr_0_def_1 T2 binop_0_def_1 A0 funct_1_th_1[OF A0] by auto 
  have "[[Zero , One] , One] in ?A" using tarski_def_1b by auto
  hence "[[Zero , One] , One] in addZ2" using A1  by auto+
  hence "addZ2. [Zero , One] = One" using funct_1_th_1[OF A0] by auto
  thus "Zero\<oplus>\<^sub>Z One = One" using T0(6) T1(5) algstr_0_def_1 T2 binop_0_def_1 A0 funct_1_th_1[OF A0] by auto  
  have "[[One , Zero] , One] in ?A" using tarski_def_1b by auto
  hence "[[One , Zero] , One] in addZ2" using A1  by auto+
  hence "addZ2. [One , Zero] = One" using funct_1_th_1[OF A0] by auto
  thus "One \<oplus>\<^sub>Z Zero = One" using T0(6) T1(5) algstr_0_def_1 T2 binop_0_def_1 A0 funct_1_th_1[OF A0] by auto 
  have "[[One , One] , Zero] in ?A" using tarski_def_1b by auto
  hence "[[One , One] , Zero] in addZ2" using A1  by auto+
  hence "addZ2. [One , One] = Zero" using funct_1_th_1[OF A0] by auto
  thus "One \<oplus>\<^sub>Z One = Zero" using T0(6) T1(5) algstr_0_def_1 T2 binop_0_def_1 A0 funct_1_th_1[OF A0] by auto
  have A0:"multZ2 be Function" using multZ2 binop_1_mode_2_def relset_1_def_1 relset_1_cl_1 all_set by auto  
  let ?M =" {[[Zero , Zero] , Zero]} \<union> {[[Zero , One] , Zero]} \<union> {[[One , Zero] , Zero]} \<union> {[[One , One] , One]}"   
  have  A1: "multZ2 = ?M" using multZ2 by simp
  have "[[Zero , Zero] , Zero] in ?M" using tarski_def_1b by auto
  hence "[[Zero , Zero] , Zero] in multZ2" using A1  by auto+
  hence "multZ2. [Zero , Zero] = Zero" using funct_1_th_1[OF A0] by auto
  thus "Zero\<otimes>\<^sub>Z Zero = Zero" using T0(7) T1(4) algstr_0_def_18 T2 binop_0_def_1 A0 funct_1_th_1[OF A0] by auto 
  have "[[Zero , One] , Zero] in ?M" using tarski_def_1b by auto
  hence "[[Zero , One] , Zero] in multZ2" using A1  by auto+
  hence "multZ2. [Zero , One] = Zero" using funct_1_th_1[OF A0] by auto
  thus "Zero\<otimes>\<^sub>Z One = Zero" using T0(7) T1(4) algstr_0_def_18 T2 binop_0_def_1 A0 funct_1_th_1[OF A0] by auto  
  have "[[One , Zero] , Zero] in ?M" using tarski_def_1b by auto
  hence "[[One , Zero] , Zero] in multZ2" using A1  by auto+
  hence "multZ2. [One , Zero] = Zero" using funct_1_th_1[OF A0] by auto
  thus "One \<otimes>\<^sub>Z Zero = Zero" using T0(7) T1(4) algstr_0_def_18 T2 binop_0_def_1 A0 funct_1_th_1[OF A0] by auto 
  have "[[One , One] , One] in ?M" using tarski_def_1b by auto
  hence "[[One , One] , One] in multZ2" using A1  by auto+
  hence "multZ2. [One , One] = One" using funct_1_th_1[OF A0] by auto
  thus "One \<otimes>\<^sub>Z One = One" "the carrier of Z={Zero,One}" using T0(7) T1(1,4) algstr_0_def_18 T2 binop_0_def_1 A0 funct_1_th_1[OF A0] by auto 
qed

end