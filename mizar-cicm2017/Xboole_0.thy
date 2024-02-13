\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Xboole_0
imports Tarski
begin

(*XBOOLE_0*) 

theorem xboole_0_sch_1:
  "A be set \<Longrightarrow>
    ex X being set st for x being object holds
      x in X iff x in A & P(x)"
proof-
  assume A0:"A be set"
  let ?Q = "\<lambda>x. \<lambda>y. (x=y & P(x))"
  have A1: "for x,y,z being object holds
    ?Q (x,y) & ?Q (x,  z) implies y = z" by simp
  obtain X where
  A2:"X be set & (for x being object holds x in X iff
    (ex y being object st y in A & ?Q (y,x)))"
       using tarski_sch_1[OF A0 A1] by blast
  thus "ex X being set st
    (for x being object holds x in X iff x in A & P(x))"
      by auto
qed

definition empty::Attr ("empty")
  where xboole_0_def_1a[THEN defattr_property,simp]: "attr empty means (\<lambda>X. X be set & not (ex x st x in X))"

definition nonempty :: Attr ("non empty")
where xboole_0_def_1b[THEN defattr_property,simp]: "attr nonempty means (\<lambda>X. X be set & (ex x st x in X))"

theorem xboole_0_cl_1[simp]:
   "cluster empty for set"
proof -
   let ?P = "\<lambda>x. False"
   have A0:"(the set) be set" using the_property set_exists by auto
  obtain X where
   A1:"X be set & (for x being object holds x in X iff x in (the set) & ?P(x))" using xboole_0_sch_1[OF A0, of ?P] by blast
   have "not(ex x being object st (x in X))" using A1 by auto
   thus ?thesis using A1 by auto
qed

definition xboole_0_def_2_prefix ("{}") where
  "func {} \<rightarrow> set equals the empty\<parallel>set"

schematic_goal xboole_0_def_2:
  shows "?X"
proof (rule equals_property[OF xboole_0_def_2_prefix_def])
  show "(the empty \<parallel>set) be set" using the_property[of "empty\<parallel>set"] xboole_0_cl_1 by auto
qed



lemmas xboole_0_def_2a[simp] = xboole_0_def_2[THEN conjunct1]
lemmas xboole_0_def_2b = xboole_0_def_2[THEN conjunct2]
lemma xboole_0_def_2c : "{} is empty" using the_property[of "empty\<parallel>set"] xboole_0_cl_1  xboole_0_def_2b by auto
definition xboole_0_def_3(infixl "\<union>" 65) where
"func X \<union> Y \<rightarrow> set means \<lambda>it. for x holds x in it iff x in X or x in Y"

schematic_goal xboole_0_def_3:
  assumes "X be set & Y be set" shows "?X"
proof (induct rule: means_property[OF xboole_0_def_3_def,of X Y, case_names existence uniqueness])
  case existence
      have "(union {X,Y}) be set & (for x being object holds (x in union {X,Y} iff x in X or x in Y))"
        proof (intro conjI)
          show "(union {X,Y}) be set" using assms tarski_def_2 tarski_def_4 by auto
          show "for x being object holds (x in union {X,Y} iff x in X or x in Y)"
            proof (intro ballI,rule iffI2)
              fix x
              assume Z1: "x be object"
              show "x in union {X,Y} implies x in X or x in Y"
                proof
                  assume "x in union { X , Y }"
                  then have "ex Z being set st x in Z & Z in {X,Y}" using  assms tarski_def_2 tarski_def_4 using Z1 tarski_def_4 by auto
                  thus "x in X or x in Y" using  assms tarski_def_2 by auto
                qed
              have "X in {X,Y} or Y in {X,Y}" using assms tarski_def_2 by auto
              then   show "(x in X or x in Y) implies x in union {X,Y}" using assms Z1 tarski_def_2 tarski_def_4 by auto
            qed
        qed
        thus "ex it be set st (for x holds x in it iff x in X or x in Y)"  by blast
  case uniqueness     
  fix A1 A2
  assume A1:"A1 be set" "(for x being object holds (x in A1 iff x in X or x in Y))" and
        A2: "A2 be set" "(for x being object holds (x in A2 iff x in X or x in Y))"
    {
      fix x
      assume Z1: "x be object"
      have "x in A1 iff (x in X or x in Y)" using Z1 A1 by auto
      then have "x in A1 \<longleftrightarrow> x in A2" using Z1 A2 by auto
    }
  thus "A1 = A2" using tarski_th_2[OF A1(1) A2(1)] by auto
qed

(* Again if a user writes "X \<union> Y" we think he wants it to be a set *)
lemmas xboole_0_def_3a[simp] = xboole_0_def_3[unfolded atomize_conjL[symmetric],THEN conjunct1,THEN conjunct1,OF all_set,OF all_set]
lemmas xboole_0_def_3b[simp] = xboole_0_def_3[THEN conjunct1,THEN conjunct2,simplified all_set,simplified,rule_format]

text_raw \<open>\DefineSnippet{xboole_0_def_3_commutativity}{\<close>
theorem xboole_0_def_3_commutativity: 
  "commutativity set xboole_0_def_3" by auto
text_raw \<open>}%EndSnippet\<close>
lemmas [simp] = xboole_0_def_3_commutativity[rule_format,OF all_set,OF all_set]

text_raw \<open>\DefineSnippet{xboole_0_def_3_idempotence}{\<close>
theorem xboole_0_def_3_idempotence: 
  "idempotence set xboole_0_def_3" by auto
text_raw \<open>}%EndSnippet\<close>

lemmas [simp] = xboole_0_def_3_idempotence[rule_format, OF all_set]

definition xboole_0_def_4(infixl "\<inter>" 70) where
"func X \<inter> Y \<rightarrow> set means \<lambda>it. (for x holds (x in it iff (x in X & x in Y)))"

schematic_goal xboole_0_def_4:
  assumes "X be set & Y be set" shows "?X"
proof (rule means_property[OF xboole_0_def_4_def,of X Y])
  show  "ex Z being set st for x being object holds (x in Z iff (x in X & x in Y))"
    using xboole_0_sch_1 assms by simp
  fix A1 A2
  assume T0:"A1 be set" "A2 be set"
  assume A1: "for x being object holds (x in A1 iff (x in X & x in Y))"
     and A2: "for x being object holds (x in A2 iff (x in X & x in Y))"
  {
      fix x
      assume T1:"x be object"
      have "x in A1 iff (x in X & x in Y)" using A1 T0 T1 by auto
      then have "x in A1 iff x in A2" using A2 T0 T1 by auto
  }
  thus "A1 = A2" using tarski_th_2 T0 by auto
qed

lemmas xboole_0_def_4a[simp] = xboole_0_def_4[unfolded atomize_conjL[symmetric],THEN conjunct1,THEN conjunct1,OF all_set,OF all_set]
lemmas xboole_0_def_4b[simp] = xboole_0_def_4[unfolded atomize_conjL[symmetric],THEN conjunct1,THEN conjunct2,simplified all_set,simplified,rule_format]

theorem xboole_0_def_4_commutativity:
  "commutativity set xboole_0_def_4" 
proof(intro ballI)
  fix X Y
  assume A1: "X be set" "Y be set"  
   have T1:"(X \<inter> Y) be set &  (Y \<inter> X) be set" using A1 xboole_0_def_4 by auto
   {fix x
    assume T1:"x be object"
    have "x in X\<inter>Y iff x in X & x in Y" using xboole_0_def_4 A1 T1 by  auto
    hence "x in X\<inter>Y iff x in Y\<inter>X" using xboole_0_def_4 A1 T1 by auto
  }
  thus "X \<inter> Y = Y \<inter> X" using tarski_th_2 T1 by auto
qed
lemmas [simp] = xboole_0_def_4_commutativity[rule_format,OF all_set,OF all_set]

theorem xboole_0_def_4_idempotence: "idempotence set xboole_0_def_4" 
proof(intro ballI)
   fix X
   assume A1: "X be set"
   have T1: "(X \<inter> X) be set" using xboole_0_def_4 A1 by auto
   {
     fix x
     assume T1:"x be object"
     have "x in X \<inter> X iff x in X " using xboole_0_def_4 A1 T1 by auto   
   }
   thus "X \<inter> X = X" using tarski_th_2[of "X \<inter> X" "X"] all_set by auto
qed
lemmas [simp] = xboole_0_def_4_idempotence[rule_format,OF all_set]

definition prefix_min (infixl "\\" 70) where
"(*let X be set & Y be set*)
    func X \\ Y \<rightarrow> set means \<lambda>it.
    for x being object holds (x in it iff (x in X & not x in Y))"

schematic_goal xboole_0_def_5:
  assumes "X be set & Y be set" shows "?X"
proof (rule means_property[OF prefix_min_def])
  show  "ex Z being set st for x being object holds (x in Z iff (x in X & not x in Y))"
    using xboole_0_sch_1 assms by auto
  fix A1 A2
  assume T0:"A1 be set" "A2 be set"
  assume A1: "for x being object holds (x in A1 iff (x in X & not x in Y))"
     and A2: "for x being object holds (x in A2 iff (x in X & not x in Y))"
  {
      fix x
      assume T1:"x be object"
      have "x in A1 iff (x in X & not x in Y)" using A1 T0 T1 by auto
      then have "x in A1 iff x in A2" using A2 T0 T1 by auto
  }
  thus "A1 = A2" using tarski_th_2 T0 by auto
qed

lemmas xboole_0_def_5a[simp] = xboole_0_def_5[unfolded atomize_conjL[symmetric],THEN conjunct1,THEN conjunct1,OF all_set]


lemmas xboole_0_def_5aa[simp] = xboole_0_def_5[unfolded atomize_conjL[symmetric],THEN conjunct1,THEN conjunct1,OF all_set,OF all_set]

lemmas xboole_0_def_5b[simp] = xboole_0_def_5[unfolded atomize_conjL[symmetric],THEN conjunct1,THEN conjunct2,simplified all_set,simplified,rule_format]

definition xboole_0_def_6 (infixl "\\+\\" 65)
where
" func X \\+\\ Y \<rightarrow> set equals (X \\ Y) \<union> (Y \\ X)"

schematic_goal xboole_0_def_6:
   assumes "X be set & Y be set"
   shows "?X"
proof (rule equals_property[OF xboole_0_def_6_def])
  show "((X \\ Y) \<union> (Y \\ X)) be set" using assms xboole_0_def_5 by auto
qed

lemmas xboole_0_def_6b[simp] = xboole_0_def_6[simplified all_set, simplified]

theorem xboole_0_def_6_commutativity: 
"commutativity set xboole_0_def_6" by auto
lemmas [simp] = xboole_0_def_6_commutativity[rule_format,OF all_set,OF all_set]

definition xboole_0_def_7 (infixl "misses" 60) where
  xboole_0_def_7: "X be set & Y be set \<Longrightarrow> (X misses Y) iff X \<inter> Y = {}"
lemmas [simp] = xboole_0_def_7[simplified all_set, simplified]
  
  
text_raw \<open>\DefineSnippet{xboole_0_def_6_symmetry}{\<close>
theorem xboole_0_def_6_symmetry: 
  "symmetry set xboole_0_def_7" by auto
text_raw \<open>}%EndSnippet\<close>
definition xboole_0_def_8 (infixl "c<" 40)
where xboole_0_def_8: "X be set \<Longrightarrow> Y be set \<Longrightarrow> (X c< Y) iff X c= Y & X<>Y"

syntax "Xboole_0.xboole_0_def_8" :: "Set \<Rightarrow> Set \<Rightarrow> o" (infixl "\<subset>" 40)

lemmas [simp] = xboole_0_def_8[simplified all_set,simplified]

text_raw \<open>\DefineSnippet{xboole_0_def_8_irreflexivity}{\<close>
mtheorem xboole_0_def_8_irreflexivity:
  "irreflexive set xboole_0_def_8" using assms by auto
text_raw \<open>}%EndSnippet\<close>
  
text_raw \<open>\DefineSnippet{xboole_0_def_8_asymmetry}{\<close>
theorem xboole_0_def_8_asymmetry:
  "asymmetry set xboole_0_def_8"
text_raw \<open>}%EndSnippet\<close>
proof(intro ballI)
  fix X Y
  assume A0: "X be set" "Y be set"
  have "X c< Y \<Longrightarrow> not Y c< X"
    proof-
  assume A1:"X c<Y"
  show "not (Y c<X)"
   proof
    assume A2: "Y c< X"
     {
        fix x
        assume T1:"x be object"
        have A3:"x in X implies x in Y" using tarski_def_3 A0 T1 A1 by auto
        have   "x in Y implies x in X" using tarski_def_3 A0 T1 A2 by auto
        hence "x in X iff x in Y" using A3 by auto
     }
    hence "X = Y" using tarski_th_2 A0 by auto
    thus "False" using A1 A0 by auto
  qed  
qed
  thus "not (X c< Y & Y c< X)" by iprover
qed  

definition
  xboole_0_def_9 ("_ , _ are c= comparable"[50,50] 40)
where
  xboole_0_def_9: "X be set & Y be set \<Longrightarrow> 
       X,Y are c= comparable iff (X c= Y or Y c= X)"
lemmas [simp] = xboole_0_def_9[simplified all_set,simplified]

theorem xboole_0_def_9_symmetry[simp]:
  "symmetry set xboole_0_def_9" by auto

theorem xboole_0_def_10[unfolded atomize_conjL[symmetric]]:
   "let X be set & Y be set 
   redefine pred X = Y means X c= Y & Y c= X"
proof-
  assume T0: "X be set & Y be set"
  show "X = Y iff (X c= Y & Y c= X)"
     proof(rule iffI2)
        show "X = Y implies (X c= Y & Y c= X)" using T0 by auto
        show "(X c= Y & Y c= X) implies X=Y"
          proof
            assume A1:"X c= Y & Y c= X"
              {
                 fix x
                 assume T1:"x be object"
                 have A2:"x in X implies x in Y" using tarski_def_3 T0 T1 A1 by blast
                 have   "x in Y implies x in X" using tarski_def_3 T0 T1 A1 by blast
                 hence "x in X iff x in Y" using A2 by auto
              }
            thus "X=Y" using T0 tarski_th_2 by auto
          qed
     qed
qed



definition meets_prefix ("_ meets _" 60)
where xboole_0_antonym_meets: "let X be set & Y be set antonym X meets Y for X misses Y"

mtheorem xboole_0_th_1: "x in X \\+\\ Y iff not (x in X iff x in Y)" 
proof -
  have "x in X \\+\\ Y iff x in X \\ Y or x in Y \\ X" using assms by auto
  thus "x in X \\+\\ Y iff not (x in X iff x in Y)" using xboole_0_def_5 assms by auto
qed

mtheorem xboole_th2:  "(for x holds (not x in X) iff (x in Y iff x in Z)) implies X = Y \\+\\ Z"
by (intro impI tarski_0_2[rule_format]) (auto simp: assms)

theorem xboole_0_cl_2[simp]:
  "cluster {} \<rightarrow> empty"
proof -
  have "\<exists>x. x be empty \<parallel> set" using xboole_0_cl_1 by auto
  hence "(the empty \<parallel> set) be empty \<parallel> set" using xboole_0_def_2 the_property by blast 
  thus "{} is empty" using xboole_0_def_2 by auto
qed

lemma [simp]: "\<not>x in {}" using xboole_0_cl_2 by simp

theorem xboole_0_cl_3[rule_format]: 
   "let x be object 
    cluster {x} \<rightarrow> non empty"
proof-
  assume T0:"x be object"
  have "x in {x}" using tarski_def_1 T0 by auto
  hence "ex z being object st z in {x}" using T0 by auto
  thus "{x} is non empty" using tarski_def_1 T0 by auto
qed

theorem xboole_0_cl_4[rule_format]: 
  "let x be object & y be object 
   cluster {x,y} \<rightarrow> non empty"
proof - 
  assume T0:"x be object & y be object"
  have "x in {x,y}" using tarski_def_2 T0 by auto
  hence "ex z being object st z in {x,y}" using T0 by auto
  thus "{x,y} is non empty" using tarski_def_2 T0 by auto
qed

theorem xboole_0_cl_5:
  "cluster non empty for set"
proof
  have "(the object) be object" using object_exists the_property by auto
  thus "{the object} is non empty" using xboole_0_cl_3 by auto
  show "{the object} be set" using tarski_0_1 by auto
qed

theorem xboole_0_cl_6:
  "let D be non empty \<parallel> set & X be set
   cluster D \<union> X \<rightarrow> non empty"
proof-
  assume A0: "D be non empty \<parallel>set & X be set"
  obtain x where
    A1: "x be object & x in D" using A0 by auto
  hence "x in D \<union> X" using xboole_0_def_3 A0 by auto
  thus "(D \<union> X) is non empty" using A0 xboole_0_def_3 A1 by auto
qed

mtheorem xboole_0_lm_1:
   "X is empty implies X={}"
proof
  assume A1: "X is empty"
  hence "not (ex x st x in X)" using assms xboole_0_def_2 by auto
  hence "for x holds x in {} iff x in X" using xboole_0_cl_2 by auto
  thus "X = {}" using assms by auto
qed

lemma [simp]: "x in X implies X <> {}"
using xboole_0_cl_2 by auto

mtheorem xboole_0_th_3: "(X meets Y) iff (ex x being object st x in X & x in Y)"
proof
  assume "X meets Y"
  hence "X \<inter> Y <> {}" using xboole_0_antonym_meets[of X Y] assms by auto
  hence "(X \<inter> Y) is non empty" using xboole_0_lm_1[of "X \<inter> Y"] by auto
  then obtain x where
    A1:"x be object & x in X \<inter> Y" by auto
  have "x be object & x in X & x in Y" using A1 xboole_0_def_4 by auto        
  thus "ex x being object st x in X & x in Y" by auto
next
  assume "ex x being object st x in X & x in Y"
  then obtain x where
  A2:"x be object & x in X & x in Y" by auto
  have "x in X \<inter> Y" using A2 xboole_0_def_4 by auto
  hence "X \<inter> Y <> {}" using assms A2 by auto
  thus "X meets Y" using xboole_0_antonym_meets[of X Y] assms by simp
qed

mtheorem xboole_0_th_4:
  "(X meets Y) iff (ex x st x in X\<inter> Y)"
proof 
  assume "X meets Y"
  hence "X \<inter> Y <>{} " using xboole_0_antonym_meets[of X Y] assms by auto
  hence "(X \<inter> Y) is non empty" using xboole_0_lm_1[of "X \<inter> Y"] by auto
  then obtain x where
    A1:"x be object & x in X\<inter>Y" by auto
  have "x be object & x in X \<inter> Y" using A1 by auto        
  thus "ex x being object st x in X \<inter> Y" by auto
next
  assume "ex x being object st x in X\<inter> Y"
  then obtain x where
  A2:"x be object & x in X \<inter> Y" by auto
  have "X \<inter> Y <> {}" using A2 by auto
  thus "X meets Y" using xboole_0_antonym_meets[of X Y] assms by auto
qed

theorem xboole_0_th_5:
  "for X,Y being set, x being object st
    X misses Y & x in X \<union> Y holds ((x in X & not x in Y) or (x in Y & not x in X))"
proof (intro ballI, intro impI)
  fix X Y x
  assume T0:"X be set" "Y be set" "x be object"
  assume A1:"X misses Y & x in X \<union> Y"
  hence "x in X or x in Y" using xboole_0_def_3 T0 by auto
  thus "(x in X & not x in Y) or (x in Y & not x in X)" using A1 T0 xboole_0_th_3 xboole_0_antonym_meets[of X Y] by auto
qed

theorem xboole_0_sch_2:
  assumes "X1 be set" "X2 be set"
    "for x being object holds x in X1 iff P(x)"
    "for x being object holds x in X2 iff P(x)"
  shows "X1 = X2"
  using tarski_th_2 assms by auto

lemmas xboole_0_sch_3 = xboole_0_sch_2

theorem xboole_0_th_6:
  "for X,Y being set st X c< Y holds
     ex x being object st x in Y & not x in X"
  using xboole_0_def_8 xboole_0_def_10 tarski_def_3 by auto

theorem xboole_0_th_7:
  "for X being set st X <> {} holds ex x being object st x in X"
    using xboole_0_lm_1 by auto

theorem xboole_0_th_8:
  "for X,Y being set st X c< Y holds
     ex x being object st x in Y & X c= Y\\{x}"
proof (intro ballI, intro impI)
  fix X Y
  assume T0:"X be set" "Y be set"
  assume A1:"X c< Y"
  then obtain x where
    T1:"x be object" and A2: "x in Y" and
    A3:" not x in X" using xboole_0_th_6 T0 by blast 
  have T1_1:"{x} be set" using T1 tarski_def_1 by auto
  have "x be object & x in Y & X c= Y\\{x}"
    proof (intro conjI)
       show "x be object" using T1 by simp
       show "x in Y" using A2 by simp
       show "X c= Y\\{x}" 
         unfolding tarski_def_3
         proof (intro ballI,intro impI)         
            fix y
            assume T2:"y be object"
            assume A4:"y in X"
            hence "y <> x" using A3 T0 T1_1 by auto
            hence A5: "not y in {x}" using tarski_def_1 T1 T2 by auto
            have "X c= Y" using A1 T0 by simp
            hence A6: "y in Y" using A4 T1 T2 tarski_def_3 T0 by auto
            show "y in Y\\{x}" using A5 A6 xboole_0_def_5b by auto
         qed
    qed
  thus "ex x being object st x in Y & X c= Y\\{x}" by auto
qed

definition include_antyonym_prefix  ("_ c\\= _" 40)
where xboole_0_antonym_2: "let X be set & Y be set antonym X c\\= Y for X c= Y"


definition in_antyonym_prefix  ("_ nin _" 40)
where xboole_0_antonym_3: "let x be object & X be set antonym x nin X for x in X"

end
