\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Subset_1
  imports Zfmisc_1
begin

theorem subset_1_cl_1:
  assumes "X be set"
  shows "cluster bool X \<rightarrow> non empty"
using assms zfmisc_1_def_1 by (auto intro!: exI[of _ "X"])
lemmas [simp] = subset_1_cl_1[OF all_set]

definition subset_1_def_1_prefix :: "Set \<Rightarrow> Mode" ("( Element-of _ )" 105) where
  "mode Element-of X \<rightarrow> set means (\<lambda>it. ((it in X) if (X is non empty) otherwise (it is empty)))"
schematic_goal subset_1_def_1: 
  assumes "X be set" shows "?X"
apply (rule mode_property[OF  subset_1_def_1_prefix_def, of X])
using assms xboole_0_cl_2 by (auto simp: all_set) (* originally uses TARSKI:1 *)

lemma [simp]:
  "X is non empty \<Longrightarrow> (x be Element-of X) iff x in X"
  "X is empty \<Longrightarrow> (x be Element-of X) iff x is empty"
  using subset_1_def_1 all_set by auto

lemma Element_of_rule:
  "x in X \<Longrightarrow> x be Element-of X" using all_set subset_1_def_1 by auto

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

end