\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory relat_1
  imports zfmisc_1 subset_1
begin

reserve x for object

attr relat_1_def_1 ("Relation'_like")
  "attr Relation_like for set means (\<lambda>IT. \<forall>x.  x in IT \<longrightarrow> (ex y, z st x = [y, z]))"

mtheorem relat_1_cl_1[ty_cond_cluster]:
  "cluster empty \<rightarrow> Relation_like for set" using relat_1_def_1 xboole_0_def_1 by auto

theorem relat_1_cl_0[ex]:
"cluster Relation_like for set"
unfolding inhabited_def
proof
  show "{} be Relation_like\<bar>set" by mty simp
qed

abbreviation "Relation \<equiv> Relation_like\<bar> set"

reserve R,P for Relation

mtheorem relat_1_cl_5[ty_func_cluster]:
   mlet "P be Relation", "R be Relation"
  "cluster P \<union> R \<rightarrow> Relation_like"
proof-
  have A0: "\<forall>x.  x in P \<longrightarrow> (ex y, z st x = [y, z])" using relat_1_def_1 by mauto
  have "\<forall>x.  x in R \<longrightarrow> (ex y, z st x = [y, z])" using relat_1_def_1 by mauto
  hence "\<forall>x.  x in P\<union>R \<longrightarrow> (ex y, z st x = [y, z])" using A0 xboole_0_def_3 by auto
  thus "(P \<union> R) is Relation_like" using relat_1_def_1 by mauto
qed

mtheorem relat_1_cl_7[ty_func_cluster]:
   mlet "a be object", "b be object"
   "cluster {[a,b]} \<rightarrow> Relation_like"
proof-
   show "{[a,b]} is Relation_like" using relat_1_def_1 tarski_def_1 by auto
qed

abbreviation(input) relat_1_syn_1("dom _" [105] 105) where
  "dom R \<equiv> proj1 R"

abbreviation(input) relat_1_syn_2("rng _" [105] 105) where
  "rng R \<equiv> proj2 R"

mtheorem relat_1_th_3:
  "R = {[x,y]} \<longrightarrow> dom R = {x} \<and> rng R = {y}"
proof(intro impI, rule conjI)
  assume A1: "R = {[x,y]}"
  have "for z being object holds z in dom R \<longleftrightarrow> z in {x}"
  proof (rule ballI,rule iffI3)
     fix z
     assume "z be object"
     show "z in dom R \<longrightarrow> z in {x}"
       proof
         assume "z in dom R"
         then obtain b where
            [ty]: "b be object" and A2: "[z,b] in R" using xtuple_0_def_12 by auto
          have "[z,b] = [x,y]" using A1 A2 tarski_def_1 by simp
          hence "z=x" using xtuple_0_th_1[of z b] by simp
          thus "z in {x}" using tarski_def_1 by simp
       qed
     assume "z in {x}"
     hence "z=x" using tarski_def_1 by simp
     hence "[z,y] in R" using A1 tarski_def_1 by simp
     thus "z in dom R" using xtuple_0_def_12 by auto
  qed simp_all
  thus "dom R = {x}" by (intro tarski_th_2) auto
  have "for z being object holds z in rng R \<longleftrightarrow> z in {y}"
  proof (rule ballI,rule iffI3)
     fix z
     assume [ty]: "z be object"
     show "z in rng R \<longrightarrow> z in {y}"
       proof
         assume "z in rng R"
         then obtain b where
            T1: "b be object" and A2: "[b,z] in R" using xtuple_0_def_13 by auto
          have "[b,z] = [x,y]" using A1 A2 tarski_def_1 by simp
          hence "z=y" using xtuple_0_th_1[of b z] by simp
          thus "z in {y}" using tarski_def_1 by simp
       qed
     assume "z in {y}"
     hence "z=y" using tarski_def_1 by simp
     hence "[x,z] in R" using A1 tarski_def_1 by simp
     thus "z in rng R" using xtuple_0_def_13 by auto
  qed simp_all
  thus "rng R = {y}" by (intro tarski_th_2) auto
 qed

mtheorem relat_1_th_7:
  "R \<subseteq> [:dom R, rng R:]"
proof(rule tarski_def_3b,simp,simp)
  fix r
  assume A1: "r in R"
  then obtain x1 x2 where
     T0: "x1 be object" "x2 be object" and A2: "r = [x1,x2]"
         using A1 relat_1_def_1E[of R r] by mty auto
  have "x1 in dom R" "x2 in rng R" using A1 A2 xtuple_0_def_12 xtuple_0_def_13 by auto
  thus "r in [:proj1 R, proj2 R:]" using A2 zfmisc_1_th_87 by simp
qed

attr relat_1_def_18 ("_-defined" [110] 110)
     "X be set \<Longrightarrow> attr X-defined for Relation means (\<lambda>R. dom R c= X)"

attr relat_1_def_19 ("_-valued" [110] 110)
     "X be set \<Longrightarrow> attr X-valued for Relation means (\<lambda>R. rng R c= X)"

theorem relat_1_sch_1:
   "A be set \<Longrightarrow> B be set
       \<Longrightarrow> ex R being Relation st (for x,y holds
  [x,y] in R \<longleftrightarrow> (x in A \<and> y in B \<and> P (x,y) ))"
proof-
   assume [ty]:"A be set" "B be set"
   let ?Q = "\<lambda> it.  ex x,y st it=[x,y] \<and> P (x,y)"
   have T2: "[:A,B:] be set" by mauto
   obtain X where
     T1:"X be set" and
A1: "for p being object holds p in X \<longleftrightarrow> p in [:A , B:] \<and> ?Q(p)"
   using xboole_0_sch_1[OF T2, of ?Q] by auto
   show "ex R being Relation st (for x,y holds
           [x,y] in R \<longleftrightarrow> (x in A \<and> y in B \<and> P (x,y) ))"
   proof (intro bexI[of _ _ X] ballI)
       have "for p being object st p in X ex x,y st p=[x,y]"
      proof(intro ballI impI)
         fix p assume "p be object"
         assume "p in X"
        hence "ex x,y st p=[x,y] \<and> P (x,y)" using A1 by simp
        thus "ex x,y st p=[x,y]" by auto
      qed simp
      thus A2: "X be Relation" using T1 relat_1_def_1 by auto
      fix x y
      assume "x be object" "y be object"
      show "[x,y] in X \<longleftrightarrow> (x in A \<and> y in B \<and> P (x,y))"
          proof (intro iffI2)
             show "[x,y] in X \<longrightarrow> x in A \<and> y in B \<and> P (x, y)"
                proof
                   assume A3: "[x,y] in X"
                    then obtain xx yy where
                     "xx be object" "yy be object"
                   and A4: "[x,y]=[xx,yy]" and
                       A5: "P (xx,yy)" using A1 by auto
                   have A6: "[x,y] in [:A,B:]" using A1 A3 by auto
                   have "x=xx \<and> y=yy" using A4 xtuple_0_th_1a by auto
                   thus "x in A \<and> y in B \<and> P (x,y)"
                      using A5 A6 zfmisc_1_th_87 by auto
                qed
             show "x in A \<and> y in B \<and> P (x,y)  \<longrightarrow> [x,y] in X"
               proof (intro impI, elim conjE)
                 assume
                   A7: "x in A" "y in B" and A8: "P(x,y)"
                 have "[x,y] in [:A,B:]" using A7 zfmisc_1_th_87 by auto
                 thus "[x,y] in X" using A1 A8 by auto
               qed
   qed
   qed simp_all
qed

theorem relat_1_def_2[unfolded atomize_conjL[symmetric],rule_format]:
  "let P be Relation \<and> R be Relation
   redefine pred P = R means for a,b being object holds [a,b] in P \<longleftrightarrow> [a,b] in R"
proof-(*ule redefine_pred_means_property[of "P be Relation \<and> R be Relation"]*)
  assume [ty]: "P be Relation \<and> R be Relation"
  show "P = R \<longleftrightarrow> (for a,b being object holds ([a,b] in P \<longleftrightarrow> [a,b] in R))"
     proof (intro iffI2)
        show "P = R \<longrightarrow> (for a,b being object holds ([a,b] in P \<longleftrightarrow> [a,b] in R))" by auto
        show "(for a,b being object holds ([a,b] in P \<longleftrightarrow> [a,b] in R)) \<longrightarrow> P=R"
             proof
                assume A1: "for a,b being object holds ([a,b] in P \<longleftrightarrow> [a,b] in R)"
                have T2: "P be set" "R be set" by simp_all
                show "P = R"
                  proof (unfold xboole_0_def_10[OF T2], intro conjI)
                      show "P c= R"
                      proof (rule tarski_def_3b)
                            fix x
                            assume A2: "x in P"
                            hence "ex y,z being object st x = [y,z]" using relat_1_def_1 by mby simp
                            thus "x in R" using A1 A2 by auto
                        qed simp_all
                       show "R c= P"
                        proof (rule tarski_def_3b)
                            fix x
                            assume A2: "x in R"
                            hence "ex y,z being object st x = [y,z]" using relat_1_def_1 by mby simp
                            thus "x in P" using A1 A2 by auto
                        qed simp_all
                qed
            qed
     qed
qed

lemmas relat_1_def_2a=relat_1_def_2[THEN iffD2]

func relat_1_def_7:: "Set \<Rightarrow> Set" ("_~" [190] 190) where
  mlet "R be Relation"
  "func R~ \<rightarrow> Relation means \<lambda>it.(for x being object,y being object holds ([x,y] in it \<longleftrightarrow> ([y,x] in R)))"
proof-
      let ?Z = "\<lambda> x y.([y,x] in R)"
      obtain P where
        [ty]: "P be Relation" and
        A2: "for x,y holds [x,y] in P \<longleftrightarrow> x in rng R \<and> y in dom R \<and> ?Z (x,y)"
         using relat_1_sch_1[of "rng R" "dom R" "?Z"] by mauto
      show "ex P being Relation st
            for x,y holds ([x,y] in P \<longleftrightarrow> ([y,x] in R))"
       proof (intro bexI[of _ _ "P"])
         show "for x,y holds ([x,y] in P \<longleftrightarrow> ([y,x] in R))"
             proof (rule ballI,rule ballI,rule iffI3)
                fix x y
                assume "x be object" "y be object"
                show "[x , y] in P \<longrightarrow> [y , x] in R" using A2 by auto
                assume A3: "[x , y] in R"
                hence "x in dom R" " y in rng R" using xtuple_0_def_12 xtuple_0_def_13 by auto
                thus " [y , x] in P" using A3 A2 by simp
             qed simp_all
       qed simp_all
next
       fix P1 P2
      assume [ty]:"P1 be Relation " " P2 be Relation" and
             A2: "for x,y holds [x,y] in P1 \<longleftrightarrow> [y,x] in R" and
             A3: "for x,y holds [x,y] in P2 \<longleftrightarrow> [y,x] in R"
      show "P1=P2"
          proof (rule relat_1_def_2a,simp,simp,intro ballI impI )
            fix x y
            assume "x be object" "y be object"
            have "[x,y] in P1 \<longleftrightarrow> [y,x]  in R" using A2 by auto
            thus "[x,y] in P1 \<longleftrightarrow> [x,y] in P2" using A3 by auto
          qed simp_all
qed simp_all

text_raw \<open>\DefineSnippet{relat_1_def_7_involutiveness}{\<close>
theorem relat_1_def_7_involutiveness:
    "involutiveness Relation relat_1_def_7"
text_raw \<open>}%EndSnippet\<close>
proof
  fix R
  assume [ty]: "R be Relation"
  show "(R~)~ = R"
  proof (intro relat_1_def_2a ballI )
    show T1: "(R~)~ be Relation" by mauto
            show "R be Relation" by auto
            fix x y
            assume "x be object" "y be object"
            have "[x,y] in R~~ \<longleftrightarrow> [y,x]  in R~" using relat_1_def_7[of "R~" x y] by mauto
            thus "[x,y] in R~~ \<longleftrightarrow> [x,y] in R" using relat_1_def_7[of "R"  y x] by auto
          qed simp_all
qed simp_all


func relat_1_def_9:: "Set \<Rightarrow> Set \<Rightarrow> Set" (infix "*" 180) where
  mlet "P be Relation", "R be Relation"
  "func P * R \<rightarrow> Relation means \<lambda>it.(for x being object,y being object holds ([x,y] in it \<longleftrightarrow> (
ex z st [x,z] in P \<and> [z,y] in R)))"
proof-
     let ?Z = "\<lambda> x y.(ex z st [x,z] in P \<and> [z,y] in R)"
      obtain PR where
        [ty]: "PR be Relation" and
        A2: "for x,y holds [x,y] in PR \<longleftrightarrow> x in dom P \<and> y in rng R \<and> ?Z (x,y)"
        using relat_1_sch_1[of "dom P" "rng R" "?Z"] by mauto
      show "ex PR being Relation st
            for x,y holds ([x,y] in PR \<longleftrightarrow> (ex z st [x,z] in P \<and> [z,y] in R))"
       proof (intro bexI[of _ _ "PR"])
         show "for x,y holds ([x,y] in PR \<longleftrightarrow> (ex z st [x,z] in P \<and> [z,y] in R))"
             proof (rule ballI,rule ballI,rule iffI3)
                fix x y
                assume "x be object" "y be object"
                show "[x , y] in PR \<longrightarrow> (ex z st [x,z] in P \<and> [z,y] in R)" using A2 by auto
                assume A3: "ex z st [x,z] in P \<and> [z,y] in R"
                then obtain z where
                   "z be object" "[x,z] in P" "[z,y] in R" by auto
                hence "x in dom P" " y in rng R" using xtuple_0_def_12 xtuple_0_def_13 by auto
                thus " [x , y] in PR" using A3 A2 by simp
             qed simp_all
       qed simp_all
next
      fix P1 P2
      assume [ty]:"P1 be Relation " " P2 be Relation" and
             A2: "for x,y holds [x,y] in P1 \<longleftrightarrow> (ex z st [x,z] in P \<and> [z,y] in R)" and
             A3: "for x,y holds [x,y] in P2 \<longleftrightarrow> (ex z st [x,z] in P \<and> [z,y] in R)"
      show "P1=P2"
          proof (intro relat_1_def_2a ballI impI)
            fix x y
            assume "x be object" "y be object"
            have "[x,y] in P1 \<longleftrightarrow> (ex z st [x,z] in P \<and> [z,y] in R)" using A2 by auto
            thus "[x,y] in P1 \<longleftrightarrow> [x,y] in P2" using A3 by auto
          qed simp_all
qed simp

theorem relat_1_th_26:
  assumes [ty]:"P be Relation" "R be Relation"
  shows "rng (P*R) c= rng R"
proof(intro tarski_def_3b ballI impI)
  fix y assume "y in rng (P*R)"
  then obtain x where
     "x be object" "[x,y] in P*R" using xtuple_0_def_13[of "P*R"] by mauto
   then obtain z where
    "z be object" "[x,z] in P \<and> [z,y] in R" using relat_1_def_9 by auto
  thus "y in rng R" using xtuple_0_def_13 by auto
qed mauto

func relat_1_def_8 ("id _" [110] 110) where
mlet "X be set"
    "func id X \<rightarrow> Relation means \<lambda>it.(for x being object,y being object holds ([x,y] in it \<longleftrightarrow> (x in X \<and> x=y)))"
proof-
  let ?Z = "\<lambda> x y.(x = y)"
      obtain R where
        [ty]: "R be Relation" and
        A2: "for x,y holds [x,y] in R \<longleftrightarrow> x in X \<and> y in X \<and> ?Z (x,y)"
         using relat_1_sch_1[of "X" "X" "?Z"] by auto
      show "ex R being Relation st
            for x,y holds ([x,y] in R \<longleftrightarrow> (x in X \<and> x=y))"
       proof (intro bexI[of _ _ "R"])
         show "for x,y holds ([x,y] in R \<longleftrightarrow> (x in X \<and> x=y))" using A2 by auto
       qed simp_all
next
      fix P1 P2
      assume [ty]:"P1 be Relation " " P2 be Relation" and
             A2: "for x,y holds [x,y] in P1 \<longleftrightarrow> x in X \<and> x=y" and
             A3: "for x,y holds [x,y] in P2 \<longleftrightarrow> x in X \<and> x=y"
      show "P1=P2"
          proof (intro relat_1_def_2a ballI)
            fix x y
            assume "x be object" "y be object"
            have "[x,y] in P1 \<longleftrightarrow> x in X \<and> x=y" using A2 by auto
            thus "[x,y] in P1 \<longleftrightarrow> [x,y] in P2" using A3 by auto
          qed simp_all
qed simp

text_raw \<open>\DefineSnippet{reduce_id_dom}{\<close>
theorem relat_1_id_dom[rule_format]:
    "let X be set reduce dom (id X) to X"
text_raw \<open>}%EndSnippet\<close>
proof -
  assume [ty]: "X be set"
  show "dom (id X) = X"
  proof (intro xboole_0_def_10a conjI)
       show "proj1 (id X) is set" by mauto
       show "dom (id X) \<subseteq> X"
       proof (intro tarski_def_3b ballI impI)
         show "proj1 (id X) is set" by mauto
            fix x
            assume "x in dom (id X)"
            then obtain y where
              "y be object" " [x,y] in (id X)" using xtuple_0_def_12 by mauto
            thus "x in X" using relat_1_def_8 by auto
          qed simp_all
       show "X \<subseteq> dom (id X)"
       proof (intro tarski_def_3b ballI impI)
         show "proj1 id X is set" by mauto
            fix x
            assume "x in X"
            hence "[x,x] in id X" using relat_1_def_8 by auto
            thus "x in dom(id X)" using xtuple_0_def_12 by mauto
          qed simp_all
     qed simp_all
qed

text_raw \<open>\DefineSnippet{reduce_id_rng}{\<close>

theorem relat_1_id_rng[rule_format]:
  "let X be set reduce rng (id X) to X"
text_raw \<open>}%EndSnippet\<close>
proof-
  assume [ty]: "X be set"
 show "rng (id X) = X"
 proof (intro xboole_0_def_10a conjI)
            show "(proj2 id X) is set" by mauto
       show "rng (id X) \<subseteq> X"
       proof (intro tarski_def_3b ballI impI)
            show "(proj2 id X) is set" by mauto
            fix x
            assume "x in rng (id X)"
            then obtain y where
              "y be object" " [y,x] in (id X)" using xtuple_0_def_13 by mauto
            thus "x in X" using relat_1_def_8 by auto
          qed simp_all
       show "X \<subseteq> rng (id X)"
       proof (intro tarski_def_3b ballI impI)
                  show "(proj2 id X) is set" by mauto
            fix x
            assume "x in X"
            hence "[x,x] in id X" using relat_1_def_8 by auto
            thus "x in rng(id X)" using xtuple_0_def_13 by mauto
          qed simp_all
     qed simp_all
qed

func relat_1_def_11:: "Set \<Rightarrow> Set \<Rightarrow> Set" (infix "|" 190)
  where
mlet "R be Relation", "X be set"
     "func (R | X) \<rightarrow> Relation means \<lambda>it.(for x being object,y being object holds ([x,y] in it \<longleftrightarrow> (x in X \<and> [x,y] in R)))"
proof-
      let ?Z = "\<lambda> x y.(x in X \<and> [x,y] in R)"
      obtain S where
        [ty]: "S be Relation" and
        A2: "for x,y holds [x,y] in S \<longleftrightarrow> x in dom R \<and> y in rng R \<and> ?Z (x,y)"
         using relat_1_sch_1[of "dom R" "rng R" "?Z"] by mauto
       show "ex S being Relation st
            for x,y holds ([x,y] in S \<longleftrightarrow> (x in X \<and> [x,y] in R))"
       proof (intro bexI[of _ _ "S"])
         show "for x,y holds ([x,y] in S \<longleftrightarrow> (x in X \<and> [x,y] in R))"
           proof(intro ballI)
              fix x y
              have "[x , y] in R \<Longrightarrow> x in dom R" "[x,y] in R \<Longrightarrow> y in rng R" using xtuple_0_def_12 xtuple_0_def_13 by mauto
              hence "[x,y] in R \<and> x in X \<Longrightarrow> [x,y] in S" using A2 by auto
              thus "[x , y] in S \<longleftrightarrow> x in X \<and> [x , y] in R" using A2 by auto
           qed simp_all
       qed simp_all
next
      fix P1 P2
      assume [ty]:"P1 be Relation " " P2 be Relation" and
             A2: "for x,y holds [x,y] in P1 \<longleftrightarrow> x in X \<and> [x,y] in R" and
             A3: "for x,y holds [x,y] in P2 \<longleftrightarrow> x in X \<and> [x,y] in R"
      show "P1=P2"
          proof (intro relat_1_def_2a ballI)
            fix x y
            assume "x be object" "y be object"
            have "[x,y] in P1 \<longleftrightarrow> x in X \<and> [x,y] in R" using A2 by auto
            thus "[x,y] in P1 \<longleftrightarrow> [x,y] in P2" using A3 by auto
          qed simp_all
qed simp_all

abbreviation(input) relat_1_def_11_notation ("_ \<restriction> \<^bsub>_\<^esub>" 190) where
  "R\<restriction>\<^bsub>X\<^esub> \<equiv> R|X"  
  
mtheorem relat_1_th_51:
  "x in dom(R|X) \<longleftrightarrow> x in X \<and> x in dom R"
proof(rule iffI3)
  show "x in dom(R|X) \<longrightarrow> x in X \<and> x in dom R"
  proof
    assume "x in dom(R|X)"
    then obtain y where "y be object" and
    A1: "[x,y] in R|X" using xtuple_0_def_12[of "(R|X)"] by auto
    have "x in X" "[x,y] in R" using relat_1_def_11[of R X] A1 by auto
    thus "x in X \<and> x in dom R" using xtuple_0_def_12 by auto
  qed
  assume
A2: "x in X \<and> x in dom R"
  then obtain y where "y be object" and
A3: "[x,y] in R" using xtuple_0_def_12 by auto
  hence "[x,y] in R|X" using A2 relat_1_def_11 by auto
  thus "x in dom (R|X)" using xtuple_0_def_12 by auto
qed


mtheorem relat_1_th_55:
  "dom(R|X) = dom R \<inter> X"
proof-
  have "for x being object holds x in dom(R|X) \<longleftrightarrow> x in dom R \<inter> X"
  proof(rule ballI)
    fix x
    have "x in dom(R|X) \<longleftrightarrow> x in dom R \<and> x in X" using relat_1_th_51 by auto
    thus "x in dom(R|X) \<longleftrightarrow> x in dom R \<inter> X" using xboole_0_def_4 by auto
  qed simp_all
  thus ?thesis using tarski_th_2 all_set by auto
qed

mtheorem relat_1_th_56:
  "X \<subseteq> dom R \<longrightarrow> dom (R|X) = X"
proof
   assume A1: "X \<subseteq> dom R"
   hence A2: "dom R \<inter> X \<subseteq> X" using xboole_0_def_4 tarski_def_3b by mauto
   have "X \<subseteq> dom R \<inter> X" using xboole_0_def_4[of "proj1 R" X] A1 tarski_def_3a[of X "proj1 R"]
     by (intro tarski_def_3b) mauto
   hence "dom R \<inter> X = X" using xboole_0_def_10a A2 by mauto
   thus "dom (R|X) = X" using relat_1_th_55 by simp
qed


mtheorem relat_1_th75:
 "X \<subseteq> Y \<longrightarrow> R|X \<subseteq> R|Y"
proof
  assume A0:"X \<subseteq> Y"
  show "R|X \<subseteq> R|Y"
  proof(intro tarski_def_3b ballI impI)
    show "R|X is set " " R|Y is set" by auto
     fix x
    assume A2: "x in R|X"
    then obtain a b where
       A3:"a be object" "b be object" "x=[a,b]" using relat_1_def_1[of "R|X"] by auto
    have "a in X \<and> [a,b] in R" using relat_1_def_11 A2 A3 by auto
    hence "a in Y \<and> [a,b] in R" using A0 tarski_def_3a[of X Y] by auto
    thus "x in R|Y" using relat_1_def_11 A2 A3 by auto
  qed
qed

mtheorem relat_1_cl_10[ty_func_cluster]:
  mlet "R be non empty\<bar>Relation"
  "cluster dom R \<rightarrow> non empty"
proof-
  let ?E="the (Element-of R)"
  have A2: "?E in R" using subset_1_def_1[of R]  choice_ax[of "Element-of R"] by simp
  hence "ex x1,x2 be object st ?E=[x1,x2]" using relat_1_def_1 by mauto
  then obtain x1 x2 where
     "x1 be object" "x2 be object" and A3: "?E = [x1,x2]" by mauto
  thus "(dom R) is non empty" using A2 xboole_0_def_1 xtuple_0_def_12 by auto
qed


mtheorem relat_1_cl_11[ty_func_cluster]:
  mlet "R be non empty\<bar>Relation"
  "cluster rng R \<rightarrow> non empty"
proof-
  let ?E="the (Element-of R)"
  have A2: "?E in R" using subset_1_def_1[of R]  choice_ax[of "Element-of R"] by simp
  hence "ex x1,x2 be object st ?E =[x1,x2]" using relat_1_def_1E by mby auto
  then obtain x1 x2 where
     "x1 be object" "x2 be object" and A3: "?E = [x1,x2]" by auto
  thus "(rng R) is non empty" using A2 xtuple_0_def_13 xboole_0_def_1 by auto
qed

mtheorem relat_1_th_41:
  "dom R = {} \<or> rng R = {} \<longrightarrow> R = {}"
proof
  assume "dom R={} \<or> rng R = {}"
  hence "(dom R) is empty \<or> (rng R) is empty" by auto
  hence "R be empty"
    using relat_1_cl_10[of R] relat_1_cl_11[of R] by mauto
  thus "R={}" using empty1 by auto
qed

theorem relat_1_cl_20[ty_func_cluster]:
   "let X be empty \<bar> set
    cluster dom X \<rightarrow> empty" using xboole_0_def_1 xtuple_0_def_12_uniq by auto

theorem relat_1_cl_21[ty_func_cluster]:
   "let X be empty \<bar> set
    cluster rng X \<rightarrow> empty" using xboole_0_def_1 xtuple_0_def_13_uniq by auto

end