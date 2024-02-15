\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Relat_1
  imports Zfmisc_1 Subset_1
begin

reserve x for object

definition Relation_like :: Attr where relat_1_def_1a[THEN defattr_property,simp]:
  "Relation_like \<equiv> define_attr (\<lambda>IT. IT be set & (for x holds x in IT implies (ex y, z st x = [y, z])))"

definition nonRelation_like :: Attr where relat_1_def_1b[THEN defattr_property,simp]:
  "nonRelation_like \<equiv> define_attr (\<lambda>IT. IT be set & not (for x holds x in IT implies (ex y, z st x = [y, z])))"

theorem relat_1_cl_1: 
  "cluster empty \<rightarrow> Relation_like for set" by auto

theorem relat_1_cl_0:
"cluster Relation_like for set"
proof
  show "{} is Relation_like" using relat_1_cl_1 by auto
  show "{} be set" by simp
qed    
    
abbreviation "Relation \<equiv> Relation_like \<parallel> set"

reserve R,P for Relation

theorem relat_1_cl_5:
  "let P be Relation & R be Relation
   cluster P \<union> R \<rightarrow> Relation_like"
proof-
  assume T0:"P be Relation & R be Relation"  
  have A0: "for x holds x in P implies (ex y, z st x = [y, z])" using T0 relat_1_def_1a by simp
  have "for x holds x in R implies (ex y, z st x = [y, z])" using T0 relat_1_def_1a by simp
  hence "for x holds x in P\<union>R implies (ex y, z st x = [y, z])" using A0 xboole_0_def_3 by simp auto
  thus "(P \<union> R) is Relation_like" using T0 relat_1_def_1a by simp
qed 

theorem relat_1_cl_7:
   "let a be object & b be object
    cluster {[a,b]} \<rightarrow> Relation_like"
proof-
   assume T0:"a be object & b be object"
   show "{[a,b]} is Relation_like" unfolding relat_1_def_1a using tarski_def_1 by auto
qed 

text_raw \<open>\DefineSnippet{notation_dom}{\<close>
definition relat_1_notation_1_prefix ("dom _" [90] 90) where
  [simp]: "let R be Relation synonym dom R for proj1(R)"
text_raw \<open>}%EndSnippet\<close>

definition relat_1_notation_2_prefix ("rng _" [90] 90) where
  [simp]: "let R be Relation 
           synonym rng R for proj2(R)"

mtheorem relat_1_th_3:
  "R = {[x,y]} implies dom R = {x} & rng R = {y}"
proof(intro impI, rule conjI)
  assume A1: "R = {[x,y]}"
  have T0: "(dom R) be set" "(rng R) be set" using assms by auto
  have "for z being object holds z in dom R iff z in {x}"
  proof (rule ballI,rule iffI3)
     fix z
     assume "z be object"
     show "z in dom R implies z in {x}"
       proof
         assume "z in dom R"
         then obtain b where
            T1: "b be object" and A2: "[z,b] in R" using xtuple_0_def_12 assms by auto
          have "[z,b] = [x,y]" using A1 A2 tarski_def_1 by simp
          hence "z=x" using xtuple_0_th_1[of z b] by simp
          thus "z in {x}" using tarski_def_1 by simp
       qed 
     assume "z in {x}"
     hence "z=x" using tarski_def_1 by simp
     hence "[z,y] in R" using A1 tarski_def_1 by simp
     thus "z in dom R" using xtuple_0_def_12 assms by auto
  qed
  thus "dom R = {x}" using tarski_th_2 T0 by auto
  have "for z being object holds z in rng R iff z in {y}"
  proof (rule ballI,rule iffI3)
     fix z
     assume "z be object"
     show "z in rng R implies z in {y}"
       proof
         assume "z in rng R"
         then obtain b where
            T1: "b be object" and A2: "[b,z] in R" using xtuple_0_def_13 assms by auto
          have "[b,z] = [x,y]" using A1 A2 tarski_def_1 by simp
          hence "z=y" using xtuple_0_th_1[of b z] by simp
          thus "z in {y}" using tarski_def_1 by simp
       qed 
     assume "z in {y}"
     hence "z=y" using tarski_def_1 by simp
     hence "[x,z] in R" using A1 tarski_def_1 by simp
     thus "z in rng R" using xtuple_0_def_12 assms by auto
  qed
  thus "rng R = {y}" using tarski_th_2 T0 by auto
 qed

mtheorem relat_1_th_7:
  "R \<subseteq> [:dom R, rng R:]"
proof(unfold tarski_def_3, rule ballI, rule impI)
  fix r
  assume "r be object" and A1: "r in R"  
  then obtain x1 x2 where 
     T0: "x1 be object" "x2 be object" and A2: "r = [x1,x2]" 
         using A1 relat_1_def_1a assms by auto
  have "x1 in dom R" "x2 in rng R" using A1 A2 assms by auto
  thus "r in  [:dom R, rng R:]" using A2 zfmisc_1_th_87 by simp
qed 

definition relat_1_def_18_prefix_a :: "Set \<Rightarrow> Attr" ("_ -defined" [90] 190) where
 relat_1_def_18a[THEN defattr_property,simp]:
     "X-defined \<equiv> define_attr(\<lambda>R. R be Relation & X be set & dom R c= X)"

definition relat_1_def_18_prefix_b :: "Set \<Rightarrow> Attr" ("non _  -defined" [90] 90) where
 relat_1_def_18b[THEN defattr_property,simp]:
     "non X-defined \<equiv> define_attr(\<lambda>R. R be Relation & X be set & not dom R c= X)"

definition relat_1_def_19_prefix_a :: "Set \<Rightarrow> Attr" ("_ -valued" [90] 190) where
 relat_1_def_19a[THEN defattr_property,simp]:
     "Y-valued \<equiv> define_attr(\<lambda>R. R be Relation & Y be set & rng R c= Y)"

definition relat_1_def_19_prefix_b :: "Set \<Rightarrow> Attr" ("non _ -valued" [90] 190) where
 relat_1_def_19b[THEN defattr_property,simp]:
     "non Y-valued \<equiv> define_attr(\<lambda>R. R be Relation & Y be set & not rng R c= Y)"

theorem relat_1_sch_1:
   "A be set \<Longrightarrow> B be set 
       \<Longrightarrow> ex R being Relation st (for x,y holds
  [x,y] in R iff (x in A & y in B & P (x,y) ))"
proof-
   assume T0:"A be set" "B be set"
   let ?Q = "\<lambda> it.  ex x,y st it=[x,y] & P (x,y)"
   have T2: "[:A,B:] be set" by simp
   obtain X where
     T1:"X be set" and
A1: "for p being object holds p in X iff p in [:A , B:] & ?Q(p)"
   using xboole_0_sch_1[OF T2, of ?Q] by blast  
   show "ex R being Relation st (for x,y holds
           [x,y] in R iff (x in A & y in B & P (x,y) ))"
   proof (intro bexI[of  _ X] ballI)
       have "for p being object st p in X ex x,y st p=[x,y]"
      proof(intro ballI impI)
         fix p assume "p be object"
         assume "p in X"
        hence "ex x,y st p=[x,y] & P (x,y)" using A1 by simp
        thus  "ex x,y st p=[x,y]" by auto
      qed
      thus A2: "X be Relation" using T1 relat_1_def_1a by auto
      fix x y
      assume "x be object" "y be object"
      show "[x,y] in X iff (x in A & y in B & P (x,y))"
          proof (intro iffI2)
             show "[x,y] in X implies x in A & y in B & P (x, y)"
                proof
                   assume A3: "[x,y] in X"
                    then obtain xx yy where
                     "xx be object" "yy be object"
                   and A4: "[x,y]=[xx,yy]" and
                       A5: "P (xx,yy)"  using A1 by auto
                   have A6: "[x,y] in [:A,B:]" using A1 A3 by auto
                   have "x=xx & y=yy" using A4 xtuple_0_th_1[of "x" "y"] by auto
                   thus "x in A & y in B & P (x,y)" 
                      using A5 A6 zfmisc_1_th_87 by auto
                qed
             show "x in A & y in B & P (x,y)  implies [x,y] in X"
               proof (intro impI, elim conjE)
                 assume
                   A7: "x in A" "y in B" and A8: "P(x,y)"
                 have "[x,y] in [:A,B:]" using A7 zfmisc_1_th_87 by auto
                 thus "[x,y] in X" using A1 A8 by auto
               qed
   qed
   qed
qed

theorem relat_1_def_2[unfolded atomize_conjL[symmetric]]:
  "let P be Relation & R be Relation 
   redefine pred P = R means for a,b being object holds [a,b] in P iff [a,b] in R"
proof(rule redefine_pred_means_property[of "P be Relation & R be Relation"])
  assume A0: "P be Relation & R be Relation"
  show "P = R iff (for a,b being object holds ([a,b] in P iff [a,b] in R))"
     proof (intro iffI2)
        show "P = R implies (for a,b being object holds ([a,b] in P iff [a,b] in R))" by auto
        show "(for a,b being object holds ([a,b] in P iff [a,b] in R)) implies P=R"
             proof
                assume A1: "for a,b being object holds ([a,b] in P iff [a,b] in R)"
                have T2: "P be set" "R be set" using A0 by simp_all
                show "P = R"
                  proof (unfold xboole_0_def_10[OF T2], intro conjI)
                      show "P c= R"
                        proof (unfold tarski_def_3, intro ballI impI)
                            fix x 
                            assume "x be object"
                            assume A2: "x in P"
                            hence "ex y,z being object st x = [y,z]" using relat_1_def_1a A0 by simp
                            thus "x in R" using A1 A2 by auto
                        qed
                       show "R c= P"
                        proof (unfold tarski_def_3, intro ballI impI)
                            fix x 
                            assume "x be object"
                            assume A2: "x in R"
                            hence "ex y,z being object st x = [y,z]" using relat_1_def_1a A0 by simp
                            thus "x in P" using A1 A2 by auto
                        qed
                qed
            qed
     qed
qed




definition relat_1_def_7:: "Set \<Rightarrow> Set" (" _ ~" 190)
where "func R ~ \<rightarrow> Relation means \<lambda>it.(for x being object,y being object holds ([x,y] in it iff ([y,x] in R)))"

schematic_goal relat_1_def_7:
  assumes "R be Relation" shows "?X"
proof (induct rule: means_property[OF relat_1_def_7_def, of R,case_names existence uniqueness])
  case existence
      let ?Z = "\<lambda> x y.([y,x] in R)"
      have T1:"R be set" using assms by auto
      obtain P where
        T2: "P be Relation" and
        A2: "for x,y holds [x,y] in P iff x in rng R & y in dom R & ?Z (x,y)" 
         using assms relat_1_sch_1[of "rng R" "dom R" "?Z"] by auto
      show "ex P being Relation st 
            for x,y holds ([x,y] in P iff ([y,x] in R))"
       proof (intro bexI[of _ "P"])
         show "P be Relation" using T2 by simp
         show "for x,y holds ([x,y] in P iff ([y,x] in R))"
             proof (rule ballI,rule ballI,rule iffI3)
                fix x y
                assume "x be object" "y be object"
                show "[x , y] in P implies [y , x] in R" using A2 by auto
                assume A3: "[x , y] in R"
                hence "x in dom R" " y in rng R" using xtuple_0_def_12 xtuple_0_def_13 assms by auto
                thus " [y , x] in P" using A3 A2 by simp
             qed
       qed
   case uniqueness
      fix P1 P2 
      assume T3:"P1 be Relation " " P2 be Relation" and
             A2: "for x,y holds [x,y] in P1 iff [y,x] in R" and
             A3: "for x,y holds [x,y] in P2 iff [y,x] in R"
      show "P1=P2"
          proof (unfold relat_1_def_2[OF T3],intro ballI )    
            fix x y
            assume "x be object" "y be object"
            have "[x,y] in P1 iff [y,x]  in R" using A2 by auto
            thus "[x,y] in P1 iff [x,y] in P2" using A3 by auto
          qed
qed


lemmas [simp] = relat_1_def_7[THEN conjunct1,THEN conjunct2,simplified,rule_format,OF all_set]
lemmas [simp] = relat_1_def_7 [THEN conjunct1,THEN conjunct1,simplified]

text_raw \<open>*\DefineSnippet{relat_1_def_7_involutiveness}{\<close>
theorem relat_1_def_7_involutiveness:
    "involutiveness Relation relat_1_def_7"
text_raw \<open>}%EndSnippet\<close>
proof
  fix R
  assume T0: "R be Relation" 
  hence T1: "(R~)~ be Relation" using relat_1_def_7[of "R~",THEN conjunct1] by simp
  show "(R~)~ = R"
          proof (unfold relat_1_def_2[rule_format, OF T1 T0],intro ballI)    
            fix x y
            assume "x be object" "y be object"
            have "[x,y] in R~~ iff [y,x]  in R~" using T0 by auto
            thus "[x,y] in R~~ iff [x,y] in R" using T0 by auto
          qed
qed

  
definition relat_1_def_9_prefix:: "Set \<Rightarrow> Set \<Rightarrow> Set" (" _ * _" 190)
  where "func P * R  \<rightarrow> Relation means \<lambda>it.(for x being object,y being object holds ([x,y] in it iff ( 
ex z st [x,z] in P & [z,y] in R)))"

schematic_goal relat_1_def_9:
  assumes "P be Relation & R be Relation" shows "?X"
proof (induct rule: means_property[OF relat_1_def_9_prefix_def, of P R,case_names existence uniqueness])
  case existence
      let ?Z = "\<lambda> x y.(ex z st [x,z] in P & [z,y] in R)"
      have T1:"R be set" using assms by auto
      obtain PR where
        T2: "PR be Relation" and
        A2: "for x,y holds [x,y] in PR iff x in dom P & y in rng R & ?Z (x,y)" 
         using assms relat_1_sch_1[of "dom P" "rng R" "?Z"] by auto
      show "ex PR being Relation st 
            for x,y holds ([x,y] in PR iff (ex z st [x,z] in P & [z,y] in R))"
       proof (intro bexI[of _ "PR"])
         show "PR be Relation" using T2 by simp
         show "for x,y holds ([x,y] in PR iff (ex z st [x,z] in P & [z,y] in R))"
             proof (rule ballI,rule ballI,rule iffI3)
                fix x y
                assume "x be object" "y be object"
                show "[x , y] in PR implies (ex z st [x,z] in P & [z,y] in R)" using A2 by auto
                assume A3: "ex z st [x,z] in P & [z,y] in R"
                then obtain z where
                   "z be object" "[x,z] in P" "[z,y] in R" by auto 
                hence "x in dom P" " y in rng R" using xtuple_0_def_12 xtuple_0_def_13 assms by auto
                thus " [x , y] in PR" using A3 A2 by simp
             qed
       qed
   case uniqueness
      fix P1 P2 
      assume T3:"P1 be Relation " " P2 be Relation" and
             A2: "for x,y holds [x,y] in P1 iff (ex z st [x,z] in P & [z,y] in R)" and
             A3: "for x,y holds [x,y] in P2 iff (ex z st [x,z] in P & [z,y] in R)"
      show "P1=P2"
          proof (unfold relat_1_def_2[OF T3],intro ballI )    
            fix x y
            assume "x be object" "y be object"
            have "[x,y] in P1 iff (ex z st [x,z] in P & [z,y] in R)" using A2 by auto
            thus "[x,y] in P1 iff [x,y] in P2" using A3 by auto
          qed
qed
  
definition relat_1_def_8_prefix:: "Set \<Rightarrow> Set" ("id _" 190)
where "func id X \<rightarrow> Relation means \<lambda>it.(for x being object,y being object holds ([x,y] in it iff (x in X & x=y)))"

schematic_goal relat_1_def_8:
  assumes "X be set" shows "?X"
proof (induct rule: means_property[OF relat_1_def_8_prefix_def, of X,case_names existence uniqueness])
  case existence
      let ?Z = "\<lambda> x y.(x = y)"
      have T1:"X be set" using assms by auto
      obtain R where
        T2: "R be Relation" and
        A2: "for x,y holds [x,y] in R iff x in X & y in X & ?Z (x,y)" 
         using assms relat_1_sch_1[of "X" "X" "?Z"] by blast
      show "ex R being Relation st 
            for x,y holds ([x,y] in R iff (x in X & x=y))"
       proof (intro bexI[of _ "R"])
         show "R be Relation" using T2 by simp
         show "for x,y holds ([x,y] in R iff (x in X & x=y))" using A2 by auto 
       qed
   case uniqueness
      fix P1 P2 
      assume T3:"P1 be Relation " " P2 be Relation" and
             A2: "for x,y holds [x,y] in P1 iff x in X & x=y" and
             A3: "for x,y holds [x,y] in P2 iff x in X & x=y"
      show "P1=P2"
          proof (unfold relat_1_def_2[OF T3], intro ballI)    
            fix x y
            assume "x be object" "y be object"
            have "[x,y] in P1 iff x in X & x=y" using A2 by auto
            thus "[x,y] in P1 iff [x,y] in P2" using A3 by auto
          qed
qed


lemmas [simp] = relat_1_def_8[THEN conjunct1,THEN conjunct2,simplified,rule_format,OF all_set]
lemmas [simp] = relat_1_def_8 [THEN conjunct1,THEN conjunct1,simplified,rule_format,OF all_set]


text_raw \<open>*\DefineSnippet{reduce_id_dom}{\<close>
theorem relat_1_id_dom:
    "let X be set reduce dom (id X) to X"
text_raw \<open>}%EndSnippet\<close>
proof (intro impI)
  assume T0: "X be set"
  show "dom (id X) = X" 
    proof (unfold xboole_0_def_10[OF all_set all_set],intro conjI) 
       show "dom (id X) \<subseteq> X"
          proof (unfold tarski_def_3,intro ballI impI)      
            fix x 
            assume "x be object"
            assume "x in dom (id X)"
            then obtain  y where 
              "y be object" " [x,y] in (id X)" by auto
            thus "x in X"  by auto
          qed
       show "X \<subseteq> dom (id X)"
           proof (unfold tarski_def_3,intro ballI impI)      
            fix x 
            assume "x be object"
            assume "x in X"
            hence "[x,x] in id X" by auto
            thus "x in dom(id X)" by auto
          qed
     qed
qed

text_raw \<open>*\DefineSnippet{reduce_id_rng}{\<close>

theorem relat_1_id_rng:
  "let X be set reduce rng (id X) to X"
text_raw \<open>}%EndSnippet\<close>
proof (intro impI)
  assume T0: "X be set"
 show "rng (id X) = X"
      proof (unfold xboole_0_def_10[OF all_set all_set],intro conjI) 
       show "rng (id X) \<subseteq> X"
          proof (unfold tarski_def_3,intro ballI impI)      
            fix x 
            assume "x be object"
            assume "x in rng (id X)"
            then obtain  y where 
              "y be object" " [y,x] in (id X)" by auto
            thus "x in X"  by auto
          qed
       show "X \<subseteq> rng (id X)"
           proof (unfold tarski_def_3,intro ballI impI)      
            fix x 
            assume "x be object"
            assume "x in X"
            hence "[x,x] in id X" by auto
            thus "x in rng(id X)" by auto
          qed
     qed

   
qed



definition relat_1_def_11_prefix:: "Set \<Rightarrow> Set \<Rightarrow> Set" ("_ | _" 190)
  where "func (R | X) \<rightarrow> Relation means \<lambda>it.(for x being object,y being object holds ([x,y] in it iff (x in X & [x,y] in R)))"

schematic_goal relat_1_def_11:
  assumes "R be Relation" "X be set" shows "?X"
proof (induct rule: means_property[OF relat_1_def_11_prefix_def, of X R,case_names existence uniqueness])
  case existence
      let ?Z = "\<lambda> x y.(x in X & [x,y] in R)"
      have T1:"X be set" using assms by auto
      obtain S where
        T2: "S be Relation" and
        A2: "for x,y holds [x,y] in S iff x in dom R & y in rng R & ?Z (x,y)" 
         using assms relat_1_sch_1[of "dom R" "rng R" "?Z"] by auto
       show "ex S being Relation st 
            for x,y holds ([x,y] in S iff (x in X & [x,y] in R))"
       proof (intro bexI[of _ "S"])
         show "S be Relation" using T2 by simp
         show "for x,y holds ([x,y] in S iff (x in X & [x,y] in R))"
           proof(intro ballI)
              fix x y
              have "[x , y] in R \<Longrightarrow> x in dom R" "[x,y] in R \<Longrightarrow> y in rng R" using assms(1) xtuple_0_def_12[of R] xtuple_0_def_13[of R] by auto
              hence "[x,y] in R & x in X \<Longrightarrow> [x,y] in S" using A2 by auto
              thus "[x , y] in S iff x in X & [x , y] in R" using A2 by auto
           qed
       qed
   case uniqueness
      fix P1 P2 
      assume T3:"P1 be Relation " " P2 be Relation" and
             A2: "for x,y holds [x,y] in P1 iff x in X & [x,y] in R" and
             A3: "for x,y holds [x,y] in P2 iff x in X & [x,y] in R"
      show "P1=P2"
          proof (unfold relat_1_def_2[OF T3], intro ballI)    
            fix x y
            assume "x be object" "y be object"
            have "[x,y] in P1 iff x in X & [x,y] in R" using A2 by auto
            thus "[x,y] in P1 iff [x,y] in P2" using A3 by auto
          qed
qed

mtheorem relat_1_th_51:
  "x in dom(R|X) iff x in X & x in dom R"
proof(rule iffI3)
  have A1: "(R|X) be Relation" using relat_1_def_11[of R X,THEN conjunct1,OF assms(2,3)] by simp
  show "x in dom(R|X) implies x in X & x in dom R"
  proof
    assume "x in dom(R|X)"
    then obtain y where "y be object" and
    A1: "[x,y] in R|X" using xtuple_0_def_12[of "(R|X)"] A1 by auto
    have "x in X" "[x,y] in R" using A1 relat_1_def_11[of R X,OF assms(2,3),THEN conjunct1] by auto
    thus "x in X & x in dom R" using xtuple_0_def_12 assms by auto
  qed
  assume
A2: "x in X & x in dom R"
  then obtain y where "y be object" and
A3: "[x,y] in R" using xtuple_0_def_12 assms by auto
  hence "[x,y] in R|X" using  A2[THEN conjunct1] relat_1_def_11[of R X,OF assms(2,3),THEN conjunct1] assms by auto
  thus "x in dom (R|X)" using xtuple_0_def_12 A1 by auto
qed

mtheorem relat_1_th_55:
  "dom(R|X) = dom R \<inter> X"
proof-
  have "for x being object holds x in dom(R|X) iff x in dom R \<inter> X"
  proof(rule ballI)
    fix x
    have "x in dom(R|X) iff x in dom R & x in X" using relat_1_th_51 assms by auto
    thus "x in dom(R|X) iff x in dom R \<inter> X" using xboole_0_def_4 assms all_set by auto
  qed
  thus ?thesis using tarski_th_2 all_set by auto
qed

mtheorem relat_1_th_56:
  "X \<subseteq> dom R implies dom (R|X) = X"
proof
   assume A1: "X \<subseteq> dom R"
   hence "dom R \<inter> X \<subseteq> X" "X \<subseteq> dom R\<inter> X" by simp+
   hence "dom R \<inter> X = X" using all_set xboole_0_def_10 by simp
   thus "dom (R|X) = X" using relat_1_th_55 assms by simp 
qed

theorem relat_1_cl_10:
  "let R be non empty\<parallel>Relation
  cluster dom R \<rightarrow> non empty"
proof-
  let ?E="the (Element-of R)"
  assume A1: "R be non empty\<parallel>Relation"
  hence A2: "?E in R" using A1 subset_1_def_1[of R]  the_property[of "Element-of R"] by simp
  then obtain x1 x2 where 
     "x1 be object" "x2 be object" and A3: "?E = [x1,x2]" 
         using A1 relat_1_def_1a by auto
  thus "(dom R) is non empty" using A1 A2 xboole_0_def_1b xtuple_0_def_12 by auto
qed

theorem relat_1_cl_11:
  "let R be non empty\<parallel>Relation
  cluster rng R \<rightarrow> non empty"
proof-
  let ?E="the (Element-of R)"
  assume A1: "R be non empty\<parallel>Relation"
  hence A2: "?E in R" using A1 subset_1_def_1[of R]  the_property[of "Element-of R"] by simp
  then obtain x1 x2 where 
     "x1 be object" "x2 be object" and A3: "?E = [x1,x2]" 
         using A1 relat_1_def_1a by auto
  thus "(rng R) is non empty" using A1 A2 xtuple_0_def_13 xboole_0_def_1b by auto
qed

mtheorem relat_1_th_41:
  "dom R = {} or rng R = {} implies R = {}"
proof
  assume "dom R={} or rng R = {}"
  hence "not ((dom R) is non empty) or not ((rng R) is non empty)" by auto
  hence "not R be (non empty\<parallel>Relation)" using assms relat_1_cl_10[of R] relat_1_cl_11[of R] by blast
  thus "R={}" using assms by auto
qed
  
end