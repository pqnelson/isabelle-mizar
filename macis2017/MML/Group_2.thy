\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Group_2
  imports Group_1
begin

text_raw \<open>\DefineSnippet{group2def1}{\<close>
definition group_2_def_1 (infix "\<hungarumlaut>\<^sup>-\<^sup>1 \<^sub>" 150) where
  "func A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G \<rightarrow> Subset-of-struct G equals
     {g\<^sup>-\<^sup>1\<^sub>G where g be Element-of-struct G : g in A}"
text_raw \<open>}%EndSnippet\<close>

schematic_goal group_2_def_1:
  assumes "G be Group" "A be Subset-of-struct G"
  shows ?X
proof (induct rule: equals_property[OF group_2_def_1_def, case_names coherence])
  case coherence
  let ?F = "{g\<^sup>-\<^sup>1\<^sub>G where g be Element-of-struct G:g in A}"
  have "?F \<subseteq> the carrier of G" 
  proof(unfold tarski_def_3,rule ballI,rule impI)
    fix x assume T0:"x be object" and A1:"x in ?F"
    then obtain g where 
      T1: "g be (Element-of-struct G)" and 
      A1: "x= g\<^sup>-\<^sup>1\<^sub>G" "g in A" using subset_1_def_2 Fraenkel_A1_ex[OF _ A1] by auto
    have C1: "the carrier of G is non empty" using  assms(2) Subset_in_rule A1(2) xboole_0_def_1b all_set by auto
    thus "x in_struct G" using group_1_def_5[OF assms(1) T1] group_1_def_5[OF assms(1) T1]Element_of(1)[OF C1] A1 by auto
  qed
  thus "?F be (Subset-of-struct G)" using Subset_of_rule by simp    
qed

theorem group_2_def_1_involutiveness:
  "G be Group \<Longrightarrow>  A be Subset-of-struct G \<Longrightarrow> 
  for B be Subset-of-struct G st B = A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G holds A = B\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"
proof(rule ballI,rule impI)
  fix B assume T0:"G be Group" "A be (Subset-of-struct G)" "B be (Subset-of-struct G)" "B = A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G" 
  hence  T1:"A \<subseteq> the carrier of G" using Subset_in_rule group_2_def_1[of G B] by auto 
  have S: "sethood-of (Element-of-struct G)" using subset_1_def_2 by simp
  show "A = B \<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"
  proof (unfold xboole_0_def_10[OF all_set all_set],rule conjI)
    show "A \<subseteq> B \<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"
    proof(unfold tarski_def_3,rule ballI,rule impI)
      fix a assume "a be object" and A1: "a in A"
      have C1: "the carrier of G is non empty" using  T0 Subset_in_rule A1 xboole_0_def_1b all_set by auto
      hence T2: "a be (Element-of-struct G)" using A1 T1 by auto
      hence T3: "a \<^sup>-\<^sup>1\<^sub>G be (Element-of-struct G)" using group_1_def_5 T0(1) by auto
      have A2: "(a \<^sup>-\<^sup>1\<^sub>G) \<^sup>-\<^sup>1\<^sub>G = a" using  group_1_def_5_involutiveness T0 T2 by auto 
      have "a \<^sup>-\<^sup>1\<^sub>G in B" using Fraenkel_A1_in[OF S T2, of "\<lambda>g. g in A" " \<lambda>g. g\<^sup>-\<^sup>1\<^sub>G",OF A1] group_2_def_1 T0(1,2,4) by auto
      thus  "a in B\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G" using A2 Fraenkel_A1_in[OF S T3, of "\<lambda>g. g in B" " \<lambda>g.  g\<^sup>-\<^sup>1\<^sub>G"] group_2_def_1 T0(1,3)  by auto
    qed  
    show "B\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G \<subseteq> A "
    proof(unfold tarski_def_3,rule ballI,rule impI)
      fix a assume "a be object" and A1: "a in B\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"
      hence A3: "a in {g\<^sup>-\<^sup>1\<^sub>G where g be Element-of-struct G:g in B}" using T0 group_2_def_1[of G B] by auto
      obtain b where
         A4: "b be (Element-of-struct G)" "a = b\<^sup>-\<^sup>1\<^sub>G" " b in B" using group_2_def_1 Fraenkel_A1_ex[OF _ A3] by auto 
      hence A5: "b in {g\<^sup>-\<^sup>1\<^sub>G where g be Element-of-struct G:g in A}" using T0 group_2_def_1[of G A] by auto
      obtain c where
         A6: "c be (Element-of-struct G)" "b = c\<^sup>-\<^sup>1\<^sub>G" " c in A" using group_2_def_1 Fraenkel_A1_ex[OF _ A5] by auto 
      thus "a in A" using  group_1_def_5_involutiveness T0 A4 by auto 
    qed
  qed 
qed

theorem group_2_th_2[rule_format]:
  "for G be Group, A be Subset-of-struct G holds
      x in A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G iff (ex g be Element-of-struct G st x = g\<^sup>-\<^sup>1\<^sub>G & g in A)"
proof(intro ballI,rule iffI3)
  fix G A
  assume T0: "G be Group" "A be Subset-of-struct G"
  show " x in A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G implies (ex g be Element-of-struct G st x = g\<^sup>-\<^sup>1\<^sub>G & g in A)"
    using Fraenkel_A1_ex group_2_def_1[OF T0(1,2) ] by auto
  assume "ex g be Element-of-struct G st x = g\<^sup>-\<^sup>1\<^sub>G & g in A" 
  then obtain g where
    T1: "g be Element-of-struct G" and A1:"x = g\<^sup>-\<^sup>1\<^sub>G & g in A" by auto      
  show "x in A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"  using group_2_def_1[OF T0(1,2) ]  Fraenkel_A1_in[OF _ T1]
     using A1 by auto
qed 


text_raw \<open>\DefineSnippet{group_2_th_3}{\<close>
theorem group_2_th_3:
  assumes "G be Group"
          "g be Element-of-struct G"
   shows "{g}\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G = {g\<^sup>-\<^sup>1\<^sub>G}"
text_raw \<open>}%EndSnippet\<close>
proof(unfold xboole_0_def_10[OF all_set all_set],rule conjI)
  have T1: "{g} be Subset-of-struct G" using struct_0_redef_1 assms multMagma_inheritance by auto
  show "{g}\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G \<subseteq> { g\<^sup>-\<^sup>1\<^sub>G}"
  proof(unfold tarski_def_3,rule ballI,rule impI)
    fix x assume "x be object" "x in {g}\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"
    then obtain a where T2:"a be Element-of-struct G" and 
      A1:"x = a\<^sup>-\<^sup>1\<^sub>G" and  
      A2:"a in {g}" using group_2_th_2 assms T1 by auto
    have "a=g" using A2 tarski_def_1b by simp
    thus "x in { g\<^sup>-\<^sup>1\<^sub>G}" using tarski_def_1b A1 by auto
  qed
  show "{g\<^sup>-\<^sup>1\<^sub>G} \<subseteq> {g}\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"
  proof(unfold tarski_def_3,rule ballI,rule impI)
    fix x assume "x be object" "x in {g\<^sup>-\<^sup>1\<^sub>G}"
    hence A3: "x = g\<^sup>-\<^sup>1\<^sub>G" using tarski_def_1b by auto
    have "g in {g} & h in {h,g}" using tarski_def_1 by auto
    thus "x in {g}\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G" using A3 group_2_th_2 assms T1 by auto
  qed  
qed    

text_raw \<open>\DefineSnippet{group_2_th_4}{\<close>  
theorem group_2_th_4:
  assumes "G be Group"
     "h be Element-of-struct G" "g be Element-of-struct G"
  shows "{h, g}\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G = {h\<^sup>-\<^sup>1\<^sub>G, g\<^sup>-\<^sup>1\<^sub>G}"
text_raw \<open>}%EndSnippet\<close>
proof(unfold xboole_0_def_10[OF all_set all_set],rule conjI)
  have T1: "{h, g} be (Subset-of-struct G)" using struct_0_redef_2 assms multMagma_inheritance by auto
  show "{h, g}\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G \<subseteq> {h\<^sup>-\<^sup>1\<^sub>G, g\<^sup>-\<^sup>1\<^sub>G}"
  proof(unfold tarski_def_3,rule ballI,rule impI)
    fix x assume "x be object" "x in {h, g}\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"
    then obtain a where T2:"a be Element-of-struct G" and 
      A1:"x = a\<^sup>-\<^sup>1\<^sub>G" and  
      A2:"a in {h, g}" using group_2_th_2 assms T1 by auto
    have "a=h or a=g" using A2 by simp
    thus "x in {h\<^sup>-\<^sup>1\<^sub>G, g\<^sup>-\<^sup>1\<^sub>G}" using A1 by auto
  qed
  show "{h\<^sup>-\<^sup>1\<^sub>G, g\<^sup>-\<^sup>1\<^sub>G} \<subseteq> {h, g}\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"
  proof(unfold tarski_def_3,rule ballI,rule impI)
    fix x assume "x be object" "x in {h\<^sup>-\<^sup>1\<^sub>G, g\<^sup>-\<^sup>1\<^sub>G}"
    hence A3: "x = g\<^sup>-\<^sup>1\<^sub>G or x = h\<^sup>-\<^sup>1\<^sub>G" using tarski_def_2b by auto
    have "g in {h,g} & h in {h,g}" by auto
    thus "x in {h, g}\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G" using A3 group_2_th_2 assms T1 by auto
  qed  
qed    

text_raw \<open>\DefineSnippet{group2def2}{\<close>
definition group_2_def_2(" _  \<Otimes>\<^sub>_ _" [66, 1000, 67] 66) where
  "func A  \<Otimes>\<^sub>G B \<rightarrow> Subset-of-struct G equals
     {a \<otimes>\<^sub>G b where a be Element-of-struct G,
                     b be Element-of-struct G : a in A & b in B}"
text_raw \<open>}%EndSnippet\<close>
  
schematic_goal group_2_def_2:
  assumes "G be Group" "A be Subset-of-struct G" "B be Subset-of-struct G"
  shows ?X
proof (induct rule: equals_property[OF group_2_def_2_def, case_names coherence])
  case coherence
  let ?F = " {a \<otimes>\<^sub>G b where a be Element-of-struct G, b be Element-of-struct G :a in A & b in B}"
  have "?F \<subseteq> the carrier of G" 
  proof(unfold tarski_def_3,rule ballI,rule impI)
    fix x assume T0:"x be object" and A1:"x in ?F"
    then obtain a b where 
      T1: "a be Element-of-struct G" "b be Element-of-struct G" and 
      A1: "x=  a  \<otimes>\<^sub>G b" "a in A & b in B" using subset_1_def_2 Fraenkel_A2_ex[OF _ A1] by auto
    have C1: "the carrier of G is non empty" using  assms(2) Subset_in_rule A1(2) xboole_0_def_1b all_set by auto
    thus "x in_struct G" using algstr_0_def_18[of G a b] assms T1 Element_of(1)[OF C1] A1 by auto
  qed
  thus "?F be Subset-of-struct G" using Subset_of_rule by simp    
qed  
  
theorem group_2_th_8[rule_format]:
  "for G be Group, A, B be Subset-of-struct G holds
      x in A  \<Otimes>\<^sub>G B iff (ex a,b be Element-of-struct G st x = a \<otimes>\<^sub>G b & a in A & b in B)"
proof(intro ballI,rule iffI3)
  fix G A B
  assume T0: "G be Group" "A be (Subset-of-struct G)" "B be (Subset-of-struct G)"
  show "x in A  \<Otimes>\<^sub>G B implies (ex a,b be Element-of-struct G st x = a \<otimes>\<^sub>G b & a in A & b in B)"
    using Fraenkel_A2_ex group_2_def_2[OF T0 ] by auto
  assume "ex a,b be Element-of-struct G st x = a \<otimes>\<^sub>G b & a in A & b in B" 
  then obtain a b where
    T1: "a be Element-of-struct G" "b be Element-of-struct G" and A1:"x = a \<otimes>\<^sub>G b" and A2:"a in A & b in B" by auto      
  show "x in A  \<Otimes>\<^sub>G B"  using group_2_def_2[OF T0]  Fraenkel_A2_in[OF _ _ T1(1) T1(2),simplified,of "\<lambda>a b. a in A & b in B"]
     using A1 A2 by auto
qed 
  
text_raw \<open>\DefineSnippet{group_2_th_11}{\<close>  
theorem group_2_th_11:
  assumes "G be Group"
          "A be Subset-of-struct G" "B be Subset-of-struct G"
  shows "(A  \<Otimes>\<^sub>G B) \<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G = B\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G  \<Otimes>\<^sub>G A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"  
text_raw \<open>}%EndSnippet\<close>
proof(unfold xboole_0_def_10[OF all_set all_set],rule conjI)
  have T1: "(A  \<Otimes>\<^sub>G B) be Subset-of-struct G" "(A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G) be Subset-of-struct G" "(B\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G) be Subset-of-struct G" 
     using group_2_def_2 group_2_def_1 assms by auto+
  show "(A  \<Otimes>\<^sub>G B) \<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G \<subseteq> B\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G  \<Otimes>\<^sub>G A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"
    proof(unfold tarski_def_3,rule ballI,rule impI)
      fix x assume "x be object"
      assume "x in (A  \<Otimes>\<^sub>G B) \<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G" 
      then obtain g where
        T2: "g be Element-of-struct G" and A1:"x = g\<^sup>-\<^sup>1\<^sub>G" "g in A  \<Otimes>\<^sub>G B" using group_2_th_2 assms T1 by auto
      obtain g1 g2 where
        T3:"g1 be Element-of-struct G" "g2 be Element-of-struct G" and A2: "g = g1 \<otimes>\<^sub>G g2" "g1 in A & g2 in B" using A1 group_2_th_8[OF assms] by auto
      have T4:"g1\<^sup>-\<^sup>1\<^sub>G be Element-of-struct G" "g2\<^sup>-\<^sup>1\<^sub>G be Element-of-struct G" using T3 assms group_1_def_5 by auto
      have A5: "g1\<^sup>-\<^sup>1\<^sub>G in A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G & g2\<^sup>-\<^sup>1\<^sub>G in B\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"  using group_2_th_2 T3 assms A2(2) by auto
      have "x = g2\<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G g1\<^sup>-\<^sup>1\<^sub>G" using group_1_th_16 assms A1 A2 T3 by auto 
      thus "x in B\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G  \<Otimes>\<^sub>G A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G" using  A5 group_2_th_8 T4 assms T1 by auto
    qed
  show "B\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G  \<Otimes>\<^sub>G A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G \<subseteq> (A  \<Otimes>\<^sub>G B) \<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G"
    proof(unfold tarski_def_3,rule ballI,rule impI)
      fix x assume "x be object"
      assume "x in B\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G  \<Otimes>\<^sub>G A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G" 
      then obtain h2 h1 where
        T2:"h2 be Element-of-struct G" "h1 be Element-of-struct G" 
         and A1: "x = h2 \<otimes>\<^sub>G h1" "h2 in B\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G & h1 in A\<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G" using group_2_th_8 assms T1 by auto
      obtain g1 where
        T3: "g1 be Element-of-struct G" and A2:"h1 = g1\<^sup>-\<^sup>1\<^sub>G" "g1 in A" using group_2_th_2 assms T1 A1 by auto
      obtain g2 where
        T4: "g2 be Element-of-struct G" and A3:"h2 = g2\<^sup>-\<^sup>1\<^sub>G" "g2 in B" using group_2_th_2 assms T1 A1 by auto
      have T5: "(g1 \<otimes>\<^sub>G g2) be  Element-of-struct G" using algstr_0_def_18[of G g1 g2]  assms T3 T4  by auto
      have A4: "g1 \<otimes>\<^sub>G g2 in A  \<Otimes>\<^sub>G B" using  assms T3 T4 group_2_th_8 A2 A3 by auto 
      have "x = (g1 \<otimes>\<^sub>G g2)\<^sup>-\<^sup>1\<^sub>G" using group_1_th_16 assms T3 T4 A1 A2 A3 by auto
      thus "x in (A  \<Otimes>\<^sub>G B) \<hungarumlaut>\<^sup>-\<^sup>1\<^sub>G" using group_2_th_2 assms(1) T1(1) A2 A3 T5 A4 by auto
    qed 
  qed  

text_raw \<open>\DefineSnippet{group_2_th_19}{\<close>    
theorem group_2_th_19:
  assumes "G be Group" 
     "g1 be Element-of-struct G" "g2 be Element-of-struct G"
     "h1 be Element-of-struct G" "h2 be Element-of-struct G"
  shows "{g1,g2}  \<Otimes>\<^sub>G {h1,h2} =
     {g1 \<otimes>\<^sub>G h1,g1 \<otimes>\<^sub>G h2 ,g2 \<otimes>\<^sub>G h1 ,g2 \<otimes>\<^sub>G h2 }"
text_raw \<open>}%EndSnippet\<close>
proof(unfold xboole_0_def_10[OF all_set all_set],rule conjI)
  have T1: "{g1, g2} be Subset-of-struct G" "{h1, h2} be Subset-of-struct G" 
    using struct_0_redef_2 assms multMagma_inheritance by auto
  show "{g1,g2}  \<Otimes>\<^sub>G {h1,h2} \<subseteq> {g1 \<otimes>\<^sub>G h1,g1 \<otimes>\<^sub>G h2 ,g2 \<otimes>\<^sub>G h1 ,g2 \<otimes>\<^sub>G h2 }"
  proof(unfold tarski_def_3,rule ballI,rule impI)
    fix x assume "x be object" "x in {g1,g2}  \<Otimes>\<^sub>G {h1,h2}"
    then obtain a b where T2:"a be Element-of-struct G" "b be Element-of-struct G" and 
      A1:"x = a \<otimes>\<^sub>G b" and  
      A2:"a in {g1, g2} & b in {h1,h2}" using group_2_th_8[OF assms(1) T1] by auto
    have "a=g1 or a=g2" "b=h1 or b=h2" using A2 by auto
    thus "x in {g1 \<otimes>\<^sub>G h1,g1 \<otimes>\<^sub>G h2 ,g2 \<otimes>\<^sub>G h1 ,g2 \<otimes>\<^sub>G h2 }" using A1 by auto
  qed
  show "{g1 \<otimes>\<^sub>G h1,g1 \<otimes>\<^sub>G h2 ,g2 \<otimes>\<^sub>G h1 ,g2 \<otimes>\<^sub>G h2 } \<subseteq> {g1,g2}  \<Otimes>\<^sub>G {h1,h2}"
  proof(unfold tarski_def_3,rule ballI,rule impI)
    fix x assume "x be object" "x in {g1 \<otimes>\<^sub>G h1,g1 \<otimes>\<^sub>G h2 ,g2 \<otimes>\<^sub>G h1 ,g2 \<otimes>\<^sub>G h2 }"
    hence A3: "x = g1 \<otimes>\<^sub>G h1 or x = g1 \<otimes>\<^sub>G h2 or x = g2 \<otimes>\<^sub>G h1 or x = g2 \<otimes>\<^sub>G h2" by auto
    have "g1 in {g1,g2} & g2 in {g1,g2}" "h1 in {h1,h2} & h2 in {h1,h2}" by auto
    thus "x in {g1,g2}  \<Otimes>\<^sub>G {h1,h2}" using A3 group_2_th_8[OF assms(1) T1] assms by auto
  qed
qed

end