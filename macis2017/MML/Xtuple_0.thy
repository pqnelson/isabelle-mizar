\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Xtuple_0
  imports Xboole_0 Enumset_1
begin

reserve x,y,z,y1,y2 for object
reserve X,Y for set

definition pair_like :: Attr ("pair")
   where xtuple_0_def_1a[THEN defattr_property,simp]:
  "attr pair means (\<lambda>X. X be object & (ex x1,x2 be object st X=[x1,x2]))"

theorem xtuple_0_lm_1:
   "{x} = {y1,y2} implies x = y1"
proof
  assume "{ x } = { y1,y2 }"
  hence "y1 in { x }" using tarski_def_2b by simp
  thus "x = y1" using tarski_def_1b by simp
qed

theorem xtuple_0_lm_2:  
   "{x} = {y1,y2} implies y1 = y2"
proof
  assume A1: "{ x } = { y1,y2 }"
  hence A2: "x = y1" using A1 xtuple_0_lm_1[of "x"] by simp 
  have "{y1,y2} = {y2,y1}"  by auto
  hence "x= y2" using A1 xtuple_0_lm_1[of "x"] A1 by simp
  thus "y1 = y2" using A2 by simp
qed

theorem xtuple_0_lm_3: 
   "{ x1,x2 } = { y1,y2 } implies x1 = y1 or x1 = y2"
proof
   assume A1: "{ x1,x2 } = { y1,y2 }"
   have "x1 in {x1,x2}" using tarski_def_2 by auto
   hence "x1 in {y1,y2}" using A1 by simp
   thus "x1 = y1 or x1 = y2" using tarski_def_2 by simp
qed

theorem xtuple_0_th_1:
  "[x1,x2] = [y1,y2] implies x1 = y1 & x2 = y2"
proof
  have A0:" {{x1,x2},{x1}} =[x1,x2]" "{{y1,y2},{y1}}=[y1,y2]" using tarski_def_5 by auto
  assume A1: "[x1,x2] = [y1,y2]"
  hence A1' :" {{x1},{x1,x2}} = {{y1,y2},{y1}}" using tarski_def_2_commutativity[rule_format, of "{x1}" "{x1,x2}"] A0 by simp
  show "x1=y1 & x2=y2"
proof (cases "y1=y2")
  assume A5: "y1=y2"
  hence "{{x1,x2},{x1}} = {{y1},{y1}}" using A1 enumset1_th_29 A0 by auto
  also have "\<dots> = {{y1}}" using enumset1_th_29 by auto
  finally have "{{x1,x2},{x1}} = {{y1}}" by simp
  hence B: "{ y1 } = { x1,x2 }" using xtuple_0_lm_1[of "{y1}" "{x1,x2}" "{x1}"]  by auto
  hence "{y1}= {x2,x1}" by auto
  hence "y1 = x1 & y1 = x2"  using B xtuple_0_lm_1[of "y1" "x1" "x2"] xtuple_0_lm_1[of "y1" "x2" "x1"] by simp
  thus ?thesis using A5 by auto
next  
   assume A2: "y1<>y2"
   hence A3: "{x1} <> {y1,y2}" using xtuple_0_lm_2[of "x1" "y1" "y2"] by auto
   hence B1: "{x1} = {y1}" using A1 A1' xtuple_0_lm_3[of "{x1}" "{x1,x2}" "{y1,y2}"]  by auto
   have "x1 in {x1}" using tarski_def_1 by simp
   hence A4:"x1=y1" using B1 tarski_def_1 by simp
   have B2: "{y1,y2} = {x1,x2}" using A1 A1' A3 xtuple_0_lm_3[of "{y1,y2}" "{y1}" "{x1}" "{x1,x2}"] by auto
   have "y2 in {y1,y2}" using tarski_def_2 by simp
   hence "y2 in {x1,x2}" using B2 by simp
   hence "y2 = x1 or y2 = x2" using tarski_def_2 by auto 
   hence "x2 = y2" using  A2 A4 by auto
   with A4 show ?thesis by simp
  qed
qed 

text_raw \<open>\DefineSnippet{permissive_def}{\<close>
definition xtuple_0_def_2_prefix (" _ `1" [90] 95) where
  "assume x is pair
   func x `1 \<rightarrow> object means
     (\<lambda>it. for y1,y2 be object st x=[y1,y2] holds it = y1)"
text_raw \<open>}%EndSnippet\<close>

schematic_goal xtuple_0_def_2:
assumes "x be object" shows "?X"
proof (induct rule: assume_means_property[OF xtuple_0_def_2_prefix_def assms, of x,  
    case_names existence uniqueness coherence])
  case existence
    assume "x is pair"
    then obtain x1 x2 where
       "x1 be object" "x2 be object" and A1: "x = [x1,x2]" using  xtuple_0_def_1a by auto
    show "ex it being object st for y1,y2 be object st x=[y1,y2] holds it = y1"
      proof(rule bexI[of _ x1],intro ballI impI)
        show "x1 be object" by simp
        fix y1 y2
        assume "y1 be object" "y2 be object" "x=[y1,y2]"
        thus "x1 = y1" using xtuple_0_th_1[of x1 x2 y1 y2] A1 by simp
      qed
  next
   case uniqueness
     assume "x is pair"
     then obtain x1 x2 where
       T0: "x1 be object" "x2 be object" and A1: "x = [x1,x2]" using  xtuple_0_def_1a by auto
     fix e1 e2 
     assume T0: "e1 be object"
                "e2 be object" and
    A2: "for y1,y2 be object st x=[y1,y2] holds e1 = y1" and 
    A3: "for y1,y2 be object st x=[y1,y2] holds e2 = y1"
    have "e1 = x1" "e2=x1" using A1 A2[rule_format] A3[rule_format]  by simp+
    thus "e1=e2" by simp
  next
   case coherence
     show "ex x being object st True" by auto
qed

definition xtuple_0_def_3_prefix (" _ `2" [90] 95) where
  "assume x is pair
   func x `2 \<rightarrow> object means (\<lambda>it. for y1,y2 be object st x=[y1,y2] holds it = y2)"

schematic_goal xtuple_0_def_3:
assumes "x be object" shows "?X"
proof (induct rule: assume_means_property[OF xtuple_0_def_3_prefix_def assms, of x,  case_names existence uniqueness coherence])
  case existence
    assume "x is pair"
    then obtain x1 x2 where
       "x1 be object" "x2 be object" and A1: "x = [x1,x2]" using  xtuple_0_def_1a by auto
    show "ex it being object st for y1,y2 be object st x=[y1,y2] holds it = y2"
      proof(rule bexI[of _ x2],intro ballI impI)
        show "x2 be object" by simp
        fix y1 y2
        assume "y1 be object" "y2 be object" "x=[y1,y2]"
        thus "x2 = y2" using xtuple_0_th_1[of x1 x2 y1 y2] A1 by simp
      qed
  next
   case uniqueness
     assume "x is pair"
     then obtain x1 x2 where
       T0: "x1 be object" "x2 be object" and A1: "x = [x1,x2]" using  xtuple_0_def_1a by auto
     fix e1 e2 
     assume T0: "e1 be object"
                "e2 be object" and
    A2: "for y1,y2 be object st x=[y1,y2] holds e1 = y2" and 
    A3: "for y1,y2 be object st x=[y1,y2] holds e2 = y2"
    have "e1 = x2" "e2=x2" using A1 A2[rule_format] A3[rule_format]  by simp+
    thus "e1=e2" by simp
  next
   case coherence
     show "ex x being object st True" by auto
qed

theorem xtuple_0_reduce:
  "[x,y]`1 =x" "[x,y]`2=y"
proof-
  have "[x,y] is pair" using xtuple_0_def_1a by auto 
  thus "[x,y]`1 =x" "[x,y]`2=y" using xtuple_0_def_3[of "[x,y]"]  xtuple_0_def_2[of "[x,y]"] by auto    
qed  

theorem xtuple_0_th_6:
 "[x,y] in X implies x in union union X"
proof 
  have B:"{x} be set &  [x,y] be set " using all_set by simp
  assume A1: "[x,y] in X"
  have A0:" {{x,y},{x}} =[x,y]" using tarski_def_5 by auto
  hence "{x} in [x,y]" using tarski_def_2b[of "{x}" "{x,y}" "{x}"] by simp
  hence "ex Y being set st ({x} in Y & Y in X)" using A1 B by blast
  hence A2: "{x} in union X" using tarski_def_4 by auto
  have "x in {x}" using tarski_def_2 tarski_def_1b by simp
  hence "ex Y being set st x in Y & Y in (union X)" using A2 B by blast 
  thus  "x in union union X" using tarski_def_4 by auto 
qed

theorem xtuple_0_th_7:
 "[x,y] in X implies y in union union X"
proof 
  have B:"{x,y} be set &  [x,y] be set " using all_set by simp
  assume A1: "[x,y] in X"
 have A0:" {{x,y},{x}} =[x,y]" using tarski_def_5 by auto
  hence "{x,y} in [x,y]" using tarski_def_2b[of "{x,y}" "{x,y}" "{x}"] by simp
 hence "ex Y being set st ({x,y} in Y & Y in X)" using A1 B by blast
  hence A2: "{x,y} in union X" using tarski_def_4 by auto
  have "y in {x,y}" using tarski_def_2 by simp
  hence "ex Y being set st y in Y & Y in (union X)" using A2 B by blast 
  thus  "y in union union X" using tarski_def_4 by auto 
qed

definition xtuple_0_def_12 ("proj1 _") where (*let X be set*)
  "func proj1 X \<rightarrow> set means \<lambda>it. (for x holds x in it iff (ex y st [x,y] in X))"
schematic_goal xtuple_0_def_12:
  assumes "X be set" shows "?X"
proof (induct rule: means_property[OF xtuple_0_def_12_def, of X,case_names existence uniqueness])
  case existence
     let ?Q = "\<lambda>d1. ex y st [d1,y] in X"
    obtain Y where 
    A1: "Y be set & (for x being object holds x in Y iff x in union union X & ?Q(x))"
      using xboole_0_sch_1[of "union union X" "?Q"] by auto 
    show "ex Y being set st for x holds x in Y iff (ex y st [x,y] in X)"
      proof (intro bexI[of _ Y])
        show "Y be set" using A1 by simp
        show "for x holds x in Y iff (ex y st [x,y] in X)"
           proof (intro ballI,rule iffI2)
              fix x assume "x be object"            
              show "x in Y implies (ex y st [x,y] in X)" using A1 by auto
              show "(ex y st [x,y] in X) implies x in Y"
                proof
                   assume "ex y st [x,y] in X"
                   then obtain y where
                     A2: "y be object" "[x,y] in X" by auto
                   hence "x in union union X" using xtuple_0_th_6 by auto
                   thus "x in Y" using A1 A2 by auto
                qed
           qed 
      qed   
  case uniqueness 
    fix X1 X2
    assume T0:"X1 be set" and T1:"X2 be set" and
       A3: "for x holds x in X1 iff (ex y st [x,y] in X)" and
      A4: "for x holds x in X2 iff (ex y st [x,y] in X)"
       {
      fix x
       assume "x be object"
        have "x in X1 iff (ex y st [x,y] in X)" using  A3 by simp
        hence "x in X1 iff x in X2" using A4 by simp
       }
    thus "X1 = X2" using tarski_th_2 T0 T1 by auto
qed

lemmas [simp] = xtuple_0_def_12[THEN conjunct1,THEN conjunct2,simplified,rule_format,OF all_set]
lemmas [simp,type_infer] = xtuple_0_def_12[THEN conjunct1,THEN conjunct1,simplified,rule_format,OF all_set]

definition  xtuple_0_def_13 ("proj2 _") where
   "func proj2 X \<rightarrow> set means \<lambda>it. (for x holds x in it iff (ex y st [y,x] in X))"
schematic_goal xtuple_0_def_13:
  assumes "X be set" shows "?X"
proof (induct rule: means_property[OF xtuple_0_def_13_def, of X,case_names existence uniqueness])
  case existence
     let ?Q = "\<lambda>d1. ex y st [y,d1] in X"
    obtain Y where 
    A1: "Y be set & (for x being object holds x in Y iff x in union union X & ?Q(x))"
      using xboole_0_sch_1[of "union union X" "?Q"] by auto 
    show "ex Y being set st for x holds x in Y iff (ex y st [y,x] in X)"
      proof (intro bexI[of _ Y])
        show "Y be set" using A1 by simp
        show "for x holds x in Y iff (ex y st [y,x] in X)"
           proof (intro ballI,rule iffI2)
              fix x assume "x be object"            
              show "x in Y implies (ex y st [y,x] in X)" using A1 by auto
              show "(ex y st [y,x] in X) implies x in Y"
                proof
                   assume "ex y st [y,x] in X"
                   then obtain y where
                     A2: "y be object" "[y,x] in X" by auto
                   hence "x in union union X" using xtuple_0_th_7 by auto
                   thus "x in Y" using A1 A2 by auto
                qed
           qed 
      qed   
  case uniqueness 
    fix X1 X2
    assume T0:"X1 be set" and T1:"X2 be set" and
       A3: "for x holds x in X1 iff (ex y st [y,x] in X)" and
      A4: "for x holds x in X2 iff (ex y st [y,x] in X)"
       {
      fix x
       assume "x be object"
        have "x in X1 iff (ex y st [y,x] in X)" using  A3 by simp
        hence "x in X1 iff x in X2" using A4 by simp
       }
    thus "X1 = X2" using tarski_th_2 T0 T1 by auto
qed

lemmas [simp] = xtuple_0_def_13[THEN conjunct1,THEN conjunct2,simplified,rule_format,OF all_set]
lemmas [simp,type_infer] = xtuple_0_def_13[THEN conjunct1,THEN conjunct1,simplified,rule_format,OF all_set]

mtheorem xtuple_0_th_8:
 "X \<subseteq> Y implies proj1 X \<subseteq> proj1 Y" by auto

mtheorem xtuple_th_23:
 "proj1 (X \<union> Y) = (proj1 X) \<union> (proj1 Y)" by auto

mtheorem xtuple_th_24:
 "proj2 (X \<union> Y) = (proj2 X) \<union> (proj2 Y)" by auto

end