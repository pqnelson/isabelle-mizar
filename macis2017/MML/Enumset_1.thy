\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Enumset_1
  imports Xboole_0
begin

definition enumset1_def_1("{ _ , _ , _ }") where
" func {x1, x2, x3} \<rightarrow> set means \<lambda>it. (for x being object holds x in it iff (x = x1 or x = x2 or x = x3))"

schematic_goal enumset1_def_1:
  assumes "x1 be object & x2 be object & x3 be object" shows "?X"
proof (induct rule: means_property[OF enumset1_def_1_def,of x1 x2 x3, case_names existence uniqueness])
  case existence  
    have "for x being object holds x in {x1,x2}\<union>{x3} iff (x = x1 or x = x2 or x = x3)" using tarski_def_1b by auto
    thus "ex X be set st for x being object holds x in X iff (x = x1 or x = x2 or x = x3)" using all_set[of "{x1,x2}\<union>{x3}"] by blast
next
  case uniqueness
  fix IT1 IT2
  assume A: "IT1 be set" "for x being object holds (x in IT1 iff (x = x1 or x = x2 or x = x3))"
          "IT2 be set" "for x being object holds (x in IT2 iff (x = x1 or x = x2 or x = x3))"
  {
    fix x
    assume Z1: "x be object"
    have "x in IT1 iff (x = x1 or x = x2 or x = x3)" using Z1 A(2) by auto
    hence "x in IT1 iff x in IT2" using Z1 A(4) by auto
  }
  thus "IT1 = IT2" using tarski_th_2 A by auto
qed
 
lemmas enumset1_def_1b[simp] = enumset1_def_1[THEN conjunct1,THEN conjunct2,simplified,rule_format]
lemmas enumset1_def_1a = enumset1_def_1[THEN conjunct1,THEN conjunct1,simplified,rule_format]

definition enumset1_def_2("{ _ , _ , _ , _ }") where
" func {x1, x2, x3, x4} \<rightarrow> set means \<lambda>it. (for x being object holds x in it iff (x = x1 or x = x2 or x = x3 or x = x4))"

schematic_goal enumset1_def_2:
  assumes "x1 be object & x2 be object & x3 be object & x4 be object" shows "?X"
proof (induct rule: means_property[OF enumset1_def_2_def,of x1 x2 x3 x4, case_names existence uniqueness])
  case existence  
    have "for x being object holds x in {x1,x2}\<union>{x3,x4} iff (x = x1 or x = x2 or x = x3 or x=x4)" by auto
    thus "ex X be set st for x being object holds x in X iff (x = x1 or x = x2 or x = x3 or x=x4)" using all_set[of "{x1,x2}\<union>{x3,x4}"] by blast
next
  case uniqueness
  fix IT1 IT2
  assume A: "IT1 be set" "for x being object holds (x in IT1 iff (x = x1 or x = x2 or x = x3 or x=x4))"
          "IT2 be set" "for x being object holds (x in IT2 iff (x = x1 or x = x2 or x = x3 or x=x4))"
  {
    fix x
    assume Z1: "x be object"
    have "x in IT1 iff (x = x1 or x = x2 or x = x3 or x=x4)" using Z1 A(2) by auto
    hence "x in IT1 iff x in IT2" using Z1 A(4) by auto
  }
  thus "IT1 = IT2" using tarski_th_2 A by auto
qed

lemmas enumset1_def_2b[simp] = enumset1_def_2[THEN conjunct1,THEN conjunct2,simplified,rule_format]
lemmas enumset1_def_2a = enumset1_def_2[THEN conjunct1,THEN conjunct1,simplified,rule_format]

reserve x1 for object

mtheorem enumset1_th_29:
  "{ x1,x1 } = { x1 }"
proof-
  have A1: "x1 be set" using tarski_0_1 by simp 
  {
    fix x
    have "x in { x1,x1 } iff x = x1" using tarski_def_2 by auto
    hence "x in { x1,x1 } iff x in { x1 }" using tarski_def_1 by auto
  }
  thus "{ x1,x1 } = { x1 }" using tarski_th_2[OF A1] by auto
qed

end