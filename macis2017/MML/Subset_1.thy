\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Subset_1
  imports Zfmisc_1
begin

theorem subset_1_cl_1:
  assumes "X be set"
  shows "cluster bool X \<rightarrow> non empty"
using assms zfmisc_1_def_1 by (auto intro!: exI[of _ "X"])
lemmas [simp,type_infer] = subset_1_cl_1[OF all_set]

definition subset_1_def_1_prefix :: "Set \<Rightarrow> Mode" ("( Element-of _ )" 105) where
  "mode Element-of X \<rightarrow> set means (\<lambda>it. ((it in X) if (X is non empty) otherwise (it is empty)))"
schematic_goal subset_1_def_1: 
  assumes "X be set" shows "?X"
apply (rule mode_property[OF  subset_1_def_1_prefix_def, of X])
using assms xboole_0_cl_2 by (auto simp: all_set) (* originally uses TARSKI:1 *)

text_raw \<open>\DefineSnippet{ElementofP}{\<close>
abbreviation (input) ElementofS :: "(Set \<Rightarrow> Set) \<Rightarrow> (Set \<Rightarrow> Mode)" ("Element-of'' _") where
  "Element-of' F \<equiv> \<lambda>it. Element-of F(it)"  
text_raw \<open>}%EndSnippet\<close>
  
lemma Element_of[simp]:
  "X is non empty \<Longrightarrow> (x be Element-of X) iff x in X"
  "X is empty \<Longrightarrow> (x be Element-of X) iff x is empty"
  using subset_1_def_1 all_set by auto

lemma Element_of_rule1:
  "X<>{} \<Longrightarrow> x be Element-of X \<Longrightarrow> x in X"
proof-
  assume A1: "X <>{}" "x be Element-of X"
  hence "X is non empty" using xboole_0_def_1b all_set by auto
  thus "x in X" using A1 by auto    
qed
  
    
lemma Element_of_rule:
  "x in X \<Longrightarrow> x be Element-of X" using all_set subset_1_def_1 by auto

theorem sethood_of_Element_of[simp]:
  "sethood-of Element-of X"  
proof(unfold sethood_def, cases "X={}")
   assume A1: "X={}"
   show "ex SH being set st (for x being object holds (x be (Element-of X) iff x in SH))"
     proof(intro bexI[of _ "{{}}"] ballI impI)
        show "{{}} be set" by simp  
        fix x
        assume "x be object"
        show "x be (Element-of X) iff x in {{}}" 
          proof(intro iffI2)
            show "x be (Element-of X) implies x in {{}}"
              proof
                assume "x be Element-of X" 
                hence "x={}" using A1 subset_1_def_1 by auto
                thus "x in {{}}" using tarski_def_1 by simp
              qed
            show "x in {{}} implies x be (Element-of X)"
                 proof
                    assume "x in {{}}"
                    hence "x={}" using tarski_def_1 by simp
                    thus "x be Element-of X" using A1 subset_1_def_1 by auto
                 qed
          qed
     qed 
next
assume A1: "X<>{}"
   show "ex SH being set st (for x being object holds (x be (Element-of X) iff x in SH))"
     proof(intro bexI[of _ "X"] ballI impI)
        show "X be set" using all_set by simp  
        fix x
        assume "x be object"
        show "x be (Element-of X) iff x in X" using A1 subset_1_def_1 all_set by auto
     qed  
qed
      
    
definition Subset_prefix ("( Subset-of _ )" 105)
where subset_1_def_2 : "Subset-of X \<equiv> Element-of (bool X)"

lemma subset_1_cl_3:
  "let Y be non empty \<parallel> set 
   cluster non empty for Subset-of Y"
proof-
  assume A: "Y be non empty \<parallel> set"
  hence B: "(bool Y) is non empty" using A subset_1_cl_1 by simp
  hence "Y be Element-of (bool Y)" using A subset_1_def_1 zfmisc_1_def_1 by auto
  thus ?thesis  using subset_1_def_2 A by auto
qed

text_raw \<open>\DefineSnippet{subset_0_def_4}{\<close>
definition subset_0_def_4("'(_,_')`")
where
  "func (E,A)` \<rightarrow> Subset-of E equals
     E \\ A"
text_raw \<open>}%EndSnippet\<close>    
schematic_goal  subset_0_def_4:
   assumes "E be set & A be Subset-of E"
   shows "?X"
 proof (induct rule: equals_property[OF subset_0_def_4_def,of E A,case_names coherence])
  case coherence
  have  "E\\A in bool E" using zfmisc_1_def_1 assms by auto
  thus "(E\\A) be Subset-of E" using Element_of_rule subset_1_def_2 by auto
qed
 
lemma Subset_of_rule:
  "X \<subseteq> A \<Longrightarrow> X be Subset-of A" using zfmisc_1_def_1[of A,THEN conjunct1] 
        Element_of_rule[of X "bool A"] subset_1_def_2 all_set by auto

lemma Subset_in_rule:
  "X be Subset-of A \<Longrightarrow> X \<subseteq> A"
  using Element_of(1)[of "bool A" X,OF subset_1_cl_1[of A,OF all_set],THEN iffD1] 
        zfmisc_1_def_1[THEN conjunct1,THEN conjunct2,OF all_set,rule_format, of X A,OF all_set,THEN iffD1] subset_1_def_2 by auto

lemma Subset_trans:
  "A be Subset-of B \<Longrightarrow> B be Subset-of C \<Longrightarrow> A be Subset-of C"
proof-
  assume "A be Subset-of B" "B be Subset-of C"
  hence "A \<subseteq> B" " B\<subseteq> C" using Subset_in_rule by auto
  hence "A \<subseteq> C" by auto
  thus "A be Subset-of C" using Subset_of_rule by auto
qed
    
definition Subset_Family_prefix ("( Subset-Family-of _ )" 105)
where Setfam_1_def_1 : "Subset-Family-of X \<equiv> Subset-of (bool X)"

lemma Subset_Family_of_ex:
  "ex X be Subset-Family-of Y st True" unfolding  Setfam_1_def_1 subset_1_def_2 using subset_1_def_1[THEN conjunct2] all_set by auto 

definition with_zero_prefix::Attr ("with'_zero")
  where with_zero[THEN defattr_property]: "attr with_zero means (\<lambda>IT. IT be set & {} in IT)"

theorem with_zero_cl:
  "cluster with_zero \<rightarrow> non empty for set"
proof(rule ballI,rule impI)
  fix X assume A1: "X be set" "X is with_zero"
  hence "{} in X" using with_zero by simp
  thus "X is non empty" using xboole_0_def_1b A1 by auto    
qed

end