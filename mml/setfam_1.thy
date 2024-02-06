theory setfam_1
imports subset_1
begin


func setfam_1_def_1 ("meet _") where
  mlet "X be set"
  "func meet X \<rightarrow> set means \<lambda>it.
  ((for x being object holds x in it iff
     (\<forall>Y.  Y in X \<longrightarrow> x in Y)) if X\<noteq>{} otherwise it = {})"
proof-
     show "ex it be set st
        ((for x being object holds x in it iff
     (\<forall>Y.  Y in X \<longrightarrow> x in Y)) if X\<noteq>{} otherwise it = {})"
     proof(cases "X={}")
       case True
            thus "ex it be set st
                ((\<forall>x.  x in it iff
                 (\<forall>Y.  Y in X \<longrightarrow> x in Y)) if X\<noteq>{} otherwise it = {})" using bexI[of set _ "{}"] by mauto
       next
         case A1:False
             let ?P = "\<lambda>x. for Z st Z in X holds x in Z"
             obtain Y where
             T0[ty]:"Y be set" and A2:"(for x being object holds x in Y \<longleftrightarrow> x in union X \<and> ?P(x))"
               using xboole_0_sch_1[of "union X" ?P] by mauto
             show "ex it be set st
                ((\<forall>x.  x in it iff
                 (\<forall>Y.  Y in X \<longrightarrow> x in Y)) if X\<noteq>{} otherwise it = {})"
             proof(rule bexI[of _ _ Y],simp)
               have "\<forall>x.  x in Y iff
                           (\<forall>Z.  Z in X \<longrightarrow> x in Z)"
               proof(standard,rule iffI3)
                 fix x
                 show "x in Y \<longrightarrow> (\<forall>Z : set. Z in X \<longrightarrow> x in Z)" using A2 by mauto
                     (*for x being object holds x in Y \<longleftrightarrow> x in union X \<and> ?P(x)*)
                 assume A3:"\<forall>Z : set. Z in X \<longrightarrow> x in Z"
                 let ?y = "the Element-of X"
                 have Y: "?y in X" using Element_of_rule2 A1 by mauto
                 hence "x in ?y" using A3 all_set by auto
                 hence "x in union X" using A1 tarski_def_4 Y all_set by mauto
                 thus "x in Y" using A2 A3 by auto
               qed mauto
               thus "(\<forall>x.  x in Y iff
                           (\<forall>Z.  Z in X \<longrightarrow> x in Z)) if X \<noteq> {} otherwise Y = {}" using A1 by auto
             qed mauto
     qed
  next
   fix it1 it2 assume [ty]:"it1 is set" "it2 is set"
   assume A1:"(for x being object holds x in it1 iff
     (\<forall>Y.  Y in X \<longrightarrow> x in Y)) if X\<noteq>{} otherwise it1 = {}" and
      A2:"(for x being object holds x in it2 iff
     (\<forall>Y.  Y in X \<longrightarrow> x in Y)) if X\<noteq>{} otherwise it2 = {}"
   show "it1 =it2"
   proof (cases "X={}")
     case True
       thus "it1=it2" using A1 A2 by auto
     next
       case A3: False
           {
         fix x
      assume Z1[ty]: "x be object"
      have "x in it1 \<longleftrightarrow> (\<forall>Y.  Y in X \<longrightarrow> x in Y)" using A1 A3 by auto
      hence "x in it1 \<longleftrightarrow> x in it2" using A2 A3 by auto
    }
    thus "it1 = it2" using tarski_th_2 by mauto
  qed
qed mauto

mtheorem setfam_1_th_3:
  "Z in X \<longrightarrow> meet X \<subseteq> Z"
proof
  assume A1:"Z in X"
  hence A2: "X\<noteq>{}" using xb by auto
  show "meet X \<subseteq> Z"
  proof
    fix x assume "x in meet X"
    thus "x in Z" using A1 A2 setfam_1_def_1 by mauto
  qed mauto
qed

end