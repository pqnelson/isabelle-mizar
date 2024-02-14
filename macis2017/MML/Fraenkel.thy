\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Fraenkel
  imports Funct_2 "../Mizar/Mizar_Fraenkel_2"
begin

theorem Fraenkel_sch_1:
  assumes T0:"A be set" 
             "for x be object holds F(x) be object"
  assumes A1:"for v being Element-of A holds P(v) implies Q(v)"
  shows 
  "{F(v) where v be Element-of A : P(v) } \<subseteq>
   {F(u) where u be Element-of A : Q(u) }"
proof(unfold tarski_def_3,rule ballI, rule impI)
  fix x 
  assume "x be object"
  assume B1: "x in {F(v) where v be Element-of A : P(v) }"
  obtain v where 
    T2:"v be  Element-of A" and
    A2: "x = F(v)" and
    A3: "P(v)" using Fraenkel_A1_ex[OF _ B1] by auto
  have "Q(v)" using A1 A3 T2 by auto
  thus "x in {F(u) where u be Element-of A : Q(u) }"  
     using Fraenkel_A1_in T2 A2 by auto
qed

theorem Fraenkel_sch_2:
  assumes T0:"A1 be set" "A2 be set" 
             "for x1 be object,x2 be object holds F(x1,x2) be object"
  assumes A1:"for v1 being Element-of A1, v2 be Element-of A2 holds P(v1,v2) implies Q(v1,v2)"
  shows 
  "{F(v1,v2) where v1 be Element-of A1, v2 be Element-of A2 : P(v1,v2) } \<subseteq>
   {F(v1,v2) where v1 be Element-of A1, v2 be Element-of A2 : Q(v1,v2) }"
proof(unfold tarski_def_3,rule ballI, rule impI)
  fix x 
  assume "x be object"
  assume B1: "x in {F(v1,v2) where v1 be Element-of A1, v2 be Element-of A2 : P(v1,v2) }"
  obtain v1 v2 where 
    T2:"v1 be  Element-of A1" "v2 be Element-of A2" and
    A2: "x = F(v1,v2)" and
    A3: "P(v1,v2)" using Fraenkel_A2_ex[OF _ B1] by auto
  have "Q(v1,v2)" using A1 A3 T2 by auto
  thus "x in {F(v1,v2) where v1 be Element-of A1, v2 be Element-of A2 : Q(v1,v2) }"  
     using Fraenkel_A2_in T2 A2 by auto
qed

theorem Fraenkel_sch_3:
  assumes T0:"B be set" 
             "for x be object holds F(x) be object"
  assumes A1:"for v being Element-of B holds P(v) iff Q(v)"
  shows 
  "{F(v) where v be Element-of B : P(v) } =
   {F(u) where u be Element-of B : Q(u) }"
proof(unfold xboole_0_def_10[OF all_set all_set],rule conjI)
  let ?A = "{F(v) where v be Element-of B : P(v) }"
  let ?B = "{F(v) where v be Element-of B : Q(v) }"
  have A2: "for v being Element-of B holds P(v) implies Q(v)" using A1 by auto
  show "?A \<subseteq> ?B" using Fraenkel_sch_1[OF _ _ A2] T0 by auto
  have A3: "for v being Element-of B holds Q(v) implies P(v)" using A1 by auto
  show "?B \<subseteq> ?A" using Fraenkel_sch_1[OF _ _ A3] T0 by auto
qed

theorem Fraenkel_sch_4:
  assumes T0:"A be set" "B be set" 
             "for x1 be object, x2 be object holds F(x1,x2) be object"
  assumes A1:"for u being Element-of A, v be Element-of B holds P(u,v) iff Q(u,v)"
  shows 
  "{F(u1,v1) where u1 be Element-of A, v1 be  Element-of B : P(u1,v1) } =
    {F(u2,v2) where u2 be Element-of A, v2 be Element-of B : Q(u2,v2) }"
proof(unfold xboole_0_def_10[OF all_set all_set],rule conjI)
   let ?A = "{F(u1,v1) where u1 be Element-of A, v1 be  Element-of B : P(u1,v1) }"
  let ?B = "{F(u2,v2) where u2 be Element-of A, v2 be Element-of B : Q(u2,v2) }"
  have A2: "for u being Element-of A, v be Element-of B holds P(u,v) implies Q(u,v)" using A1 by auto
  show "?A \<subseteq> ?B" using Fraenkel_sch_2[OF _ _ _ A2] T0 by auto
  have A3: "for u being Element-of A, v be Element-of B holds Q(u,v) implies P(u,v)" using A1 by auto
  show "?B \<subseteq> ?A" using Fraenkel_sch_2[OF _ _ _ A3] T0 by auto
qed

theorem Fraenkel_sch_5:
  assumes T0:"B be set" 
             "for x be object holds F(x) be object"
             "for x be object holds G(x) be object"
  assumes A1:"for v being Element-of B holds F(v) = G(v)"
  shows 
  "{F(v1) where v1 be Element-of B : P(v1) } =
   {G(v2) where v2 be Element-of B : P(v2) }"
proof(unfold xboole_0_def_10[OF all_set all_set],rule conjI)
  let ?X = "{F(v1) where v1 be Element-of B : P(v1) }"
  let ?Y = "{G(v2) where v2 be Element-of B : P(v2) }"
  show "?X \<subseteq> ?Y"
    proof(unfold tarski_def_3,rule ballI, rule impI)
      fix x assume "x be object"
      assume B1: "x in ?X"
      obtain v1 where 
       T1: "v1 be Element-of B" and 
       A3: "x = F(v1)" and
       A4: "P(v1)" using Fraenkel_A1_ex[OF _ B1] by auto
      have "x = G(v1)" using A1 A3 T1 by auto
      thus "x in ?Y" using Fraenkel_A1_in A4 T1 by auto    
    qed
  show "?Y \<subseteq> ?X"
    proof(unfold tarski_def_3,rule ballI, rule impI)
      fix x assume "x be object"
      assume B1: "x in ?Y"
      obtain v1 where 
       T1: "v1 be Element-of B" and 
       A3: "x = G(v1)" and
       A4: "P(v1)" using Fraenkel_A1_ex[OF _ B1] by auto
      have "x = F(v1)" using A1 A3 T1 by auto
      thus "x in ?X" using Fraenkel_A1_in A4 T1 by auto    
   qed
qed  

theorem Fraenkel_sch_6:
  assumes T0:"B be set" 
             "for x be object holds F(x) be object"
             "for x be object holds G(x) be object"
  assumes A1:"for v being Element-of B st P(v) holds F(v) = G(v)"
  shows 
  "{F(v1) where v1 be Element-of B : P(v1) } =
   {G(v2) where v2 be Element-of B : P(v2) }"
proof(unfold xboole_0_def_10[OF all_set all_set],rule conjI)
  let ?X = "{F(v1) where v1 be Element-of B : P(v1) }"
  let ?Y = "{G(v2) where v2 be Element-of B : P(v2) }"
  show "?X \<subseteq> ?Y"
    proof(unfold tarski_def_3,rule ballI, rule impI)
      fix x assume "x be object"
      assume B1: "x in ?X"
      obtain v1 where 
       T1: "v1 be Element-of B" and 
       A3: "x = F(v1)" and
       A4: "P(v1)" using Fraenkel_A1_ex[OF _ B1] by auto
      have "x = G(v1)" using A1 A3 A4 T1 by auto
      thus "x in ?Y" using Fraenkel_A1_in A4 T1 by auto    
    qed
  show "?Y \<subseteq> ?X"
    proof(unfold tarski_def_3,rule ballI, rule impI)
      fix x assume "x be object"
      assume B1: "x in ?Y"
      obtain v1 where 
       T1: "v1 be Element-of B" and 
       A3: "x = G(v1)" and
       A4: "P(v1)" using Fraenkel_A1_ex[OF _ B1] by auto
      have "x = F(v1)" using A1 A3 A4 T1 by auto
      thus "x in ?X" using Fraenkel_A1_in A4 T1 by auto    
   qed
qed  

theorem Fraenkel_sch_7:
  assumes T0:"A be set" "B be set" 
             "for x1 be object, x2 be object holds F(x1,x2) be object"
             "for x1 be object, x2 be object holds G(x1,x2) be object"
  assumes A1:"for u being Element-of A, v be Element-of B holds F(u,v) = G(u,v)"
  shows 
  "{F(u1,v1) where u1 be Element-of A, v1 be Element-of B : P(u1,v1) } =
    {G(u2,v2) where u2 be Element-of A, v2 be Element-of B : P(u2,v2) }"
proof(unfold xboole_0_def_10[OF all_set all_set],rule conjI)
  let ?X = "{F(u1,v1) where u1 be Element-of A, v1 be Element-of B : P(u1,v1) }"
  let ?Y = "{G(u2,v2) where u2 be Element-of A, v2 be Element-of B : P(u2,v2) }"
 show "?X \<subseteq> ?Y"
  proof(unfold tarski_def_3,rule ballI, rule impI)
      fix x assume "x be object"
      assume B1: "x in ?X"
      obtain u1 v1 where 
       T1: "u1 be Element-of A" "v1 be Element-of B" and 
       A3: "x = F(u1,v1)" and
       A4: "P(u1,v1)" using Fraenkel_A2_ex[OF _ B1] by auto
     have "x = G(u1,v1)" using A1 A3 T1 by auto
     thus "x in ?Y" using A4 Fraenkel_A2_in T1 by auto
  qed    
  show "?Y \<subseteq> ?X"
  proof(unfold tarski_def_3,rule ballI, rule impI)
      fix x assume "x be object"
      assume B1: "x in ?Y"
      obtain u1 v1 where 
       T1: "u1 be Element-of A" "v1 be Element-of B" and 
       A3: "x = G(u1,v1)" and
       A4: "P(u1,v1)" using Fraenkel_A2_ex[OF _ B1] by auto
     have "x = F(u1,v1)" using A1 A3 T1 by auto
     thus "x in ?X" using A4 Fraenkel_A2_in T1 by auto
  qed    
qed

mtheorem Fraenkel_th_1:
  "for A,B being  set, F,G being Function-of A,B holds
     for X being set st F|X = G|X holds 
       for x being Element-of A st x in X holds F. x = G. x"
proof(intro ballI impI)
  fix A B F G X x
  assume T1:"A be set" "B be set" "F be Function-of A,B" "G be Function-of A,B" "X be set"
  have T2: "F be Function" using relset_1_cl_1 relset_1_def_1 all_set  T1 by auto 
  have T3: "G be Function" using relset_1_cl_1 relset_1_def_1 all_set  T1 by auto 
  assume A1:"F|X = G|X" "x be Element-of A"
  assume A2:"x in X"
  hence "F. x = (G|X).x" using A1 funct_1_th_49[of F X x] T2 T1 by simp
  also have "... =  G. x" using A2 funct_1_th_49[of G X x] T3 T1 by simp
  finally show "F. x = G. x" by simp
qed  

text_raw \<open>\DefineSnippet{fraenkelsch9}{\<close>
theorem Fraenkel_sch_9:
  assumes "A be set" "B be set" "X be set" 
          "f be Function-of A,B" "g be Function-of A,B"
          "(f | X) = (g | X)"
        "for u being Element-of A st u in X holds P(u) iff Q(u)"
  shows "{ f. u where u be Element-of A : P(u) & u in X } =
         { g. v where v be Element-of A : Q(v) & v in X }"
text_raw \<open>}%EndSnippet\<close>
proof-
  let ?F = "\<lambda>x1. f. x1"
  let ?G = "\<lambda>x1. g. x1"
  let ?PP = "\<lambda>x1. P(x1) & x1 in X"
  let ?QQ = "\<lambda>x1. Q(x1) & x1 in X"
  let ?C = "{?G(v) where  v be Element-of A : ?PP(v) }"     
  have A3: "for v be Element-of A holds ?PP(v) iff ?QQ(v)" using assms by auto
  have A4: "?C = { ?G(v) where  v be Element-of A : ?QQ(v) }" using Fraenkel_sch_3[OF _ _ A3] assms by simp
  have A5: "for v being Element-of A st ?PP(v) holds ?F(v) = ?G(v)" using assms Fraenkel_th_1[rule_format,of A B f g X] by auto
  have "{ ?F(u) where u be Element-of A : ?PP(u) } = ?C" using Fraenkel_sch_6[OF _ _ _ A5] assms by simp 
  thus ?thesis using A4 by simp
qed
  
theorem Fraenkel_sch_8:
  assumes T0:"A be set" "B be set" 
             "for x1 be object, x2 be object holds F(x1,x2) be object"
  assumes A1:"for u being Element-of A, v be Element-of B holds P(u,v) iff Q(u,v)"
    and   A2:"for u being Element-of A, v be Element-of B holds F(u,v) = F(v,u)"
  shows 
  "{F(u1,v1) where u1 be Element-of A, v1 be Element-of B : P(u1,v1) } =
    {F(v2,u2) where u2 be Element-of A, v2 be Element-of B : Q(u2,v2) }"
proof-
  have A3: "for u being Element-of A, v being Element-of B holds Q(u,v) implies P(u,v)" using A1 by simp
  have A4: "{ F(u1,v1) where u1 be Element-of A, v1 be Element-of B : Q(u1,v1)} \<subseteq> 
            { F(u2,v2) where u2 be Element-of A, v2 be Element-of B : P(u2,v2)}" using Fraenkel_sch_2[OF _ _ _ A3] T0 by auto 
  let ?H = "\<lambda>d1 d2. F(d2,d1)"
  have A5: "for u being Element-of A, v being Element-of B holds P(u,v) implies Q(u,v)" using A1 by simp
  have A6: "{F(u1,v1) where u1 be Element-of A, v1 be Element-of B : P(u1,v1)} \<subseteq> 
            {F(u2,v2) where u2 be Element-of A, v2 be Element-of B : Q(u2,v2)}" 
          using Fraenkel_sch_2[OF _ _ _ A5] T0 by auto 
  have A7: "for u be Element-of A, v being Element-of B holds F(u,v) = ?H(u,v)" using A2 by auto
  have A8: "{ F(u1,v1) where u1 be Element-of A, v1 be Element-of B : Q(u1,v1)} = 
            {?H(u2,v2) where u2 be Element-of A, v2 be Element-of B : Q(u2,v2)}" 
          using Fraenkel_sch_7[OF _ _ _ _ A7] T0 by auto 
  thus ?thesis using xboole_0_def_10[OF all_set all_set,THEN iffD2,rule_format,OF A4 A6] by simp 
qed
  
theorem Fraenkel_sch_10:
  assumes T0: "A be non empty\<parallel>set" 
  shows "{x where x be Element-of A: P(x) } \<subseteq> A"
proof(unfold tarski_def_3,rule ballI,rule impI)
  fix x assume "x be object"
  assume A0: "x in {x where x be Element-of A: P(x) }"
  obtain y where
    A1: "y be Element-of A" "x=y" "P(x)" using Fraenkel_A1_ex[OF _ A0] by auto
  show "x in A" using A1(1,2) T0 by auto
qed
  
theorem Fraenkel_sch_11:
  assumes T0: "A be set" "B be set"
              "for x1 be object, x2 be object holds F(x1,x2) be object" 
  assumes A1: "for st1 being set st st1 in {F(s1,t1) where s1 be Element-of A, t1 be Element-of B:
                                            P(s1,t1) } holds Q(st1)"
  shows "for s being Element-of A, t being Element-of B st P(s,t) holds Q(F(s,t))"
proof(rule ballI, rule ballI, rule impI)
  fix s t
  assume T0: "s be Element-of A" "t be Element-of B"
  assume "P(s,t)"
  then have "F(s,t) in { F(s1,t1) where s1 be Element-of A,t1 be Element-of B:P(s1,t1)}" using Fraenkel_A2_in T0 by auto 
  thus "Q(F(s,t))" using A1 all_set by simp
qed
  
theorem Fraenkel_sch_12:
  assumes T0: "A be set" "B be set"
              "for x1 be object, x2 be object holds F(x1,x2) be object" 
  assumes A1: "for s being Element-of A, t being Element-of B st P(s,t) holds Q(F(s,t))"

  shows "for st1 being set st st1 in { F(s1,t1) where s1 be Element-of A, t1 be Element-of B:
                                             P(s1,t1) } holds Q(st1)"
proof(rule ballI,rule impI)
  fix st1 assume "st1 be set"
  assume A2: "st1 in { F(s1,t1) where s1 be Element-of A, t1 be Element-of B:P(s1,t1) }"
  have "ex s1 be Element-of A,t1 be Element-of B st st1 = F(s1,t1) & P(s1,t1)" using Fraenkel_A2_ex[OF _ A2] by auto 
  thus "Q(st1)" using A1 by auto
qed
  
text_raw \<open>\DefineSnippet{fraenkelsch13}{\<close>
theorem Fraenkel_sch_13:
  assumes T0: "A be set" "B be set" "C be set"
   "for x1 be object,x2 be object holds F(x1,x2) be Element-of C"
  shows "{ st1 where st1 be Element-of C:
             st1 in {F(s1,t1) where s1 be Element-of A,
               t1 be Element-of B: P(s1,t1) } & Q(st1)} =
         { F(s2,t2) where s2 be Element-of A,t2 be Element-of B:
             P(s2,t2) & Q(F(s2,t2))}"
text_raw \<open>}%EndSnippet\<close>
proof(unfold xboole_0_def_10[OF all_set all_set],rule conjI)
  let ?T = "{F(s1,t1) where s1 be Element-of A,t1 be Element-of B:P(s1,t1)}"
  let ?X = "{st1 where st1 be Element-of C: st1 in ?T & Q(st1)}"
  let ?Y =  "{F(s2,t2) where s2 be Element-of A,t2 be Element-of B:
                                             P(s2,t2) & Q(F(s2,t2))}"
  show "?X \<subseteq> ?Y"
  proof(unfold tarski_def_3,rule ballI,rule impI)
    fix x assume "x be object"
    assume B1: "x in ?X"
    obtain st1 where
      A1: "st1 be Element-of C" "x = st1" and
      A2: "st1 in ?T" and
      A3: "Q(st1)" using Fraenkel_A1_ex[OF _ B1] by auto
    have "ex s1 be Element-of A,t1 be Element-of B st st1 = F(s1,t1) & P(s1,t1)" using Fraenkel_A2_ex[OF _ A2] by auto
    thus "x in ?Y" using A1 A3 Fraenkel_A2_in by auto  
   qed
  show "?Y \<subseteq> ?X"
    proof(unfold tarski_def_3,rule ballI,rule impI)
      fix x assume "x be object"
      assume B1: "x in ?Y"
      obtain s2 t2 where 
       A4:"s2 be Element-of A" "t2 be Element-of B" "x=F(s2,t2)" and
       A5:"P(s2,t2)" and
       A6:"Q(F(s2,t2))" using Fraenkel_A2_ex[OF _ B1] by auto
      have T2:"F(s2,t2) be Element-of C" using T0(4) by auto  
      have "F(s2,t2) in ?T" using A4 A5 Fraenkel_A2_in by auto 
      thus "x in ?X" using T2 A6 A4 Fraenkel_A1_in[OF _  T2, of "\<lambda>st1. st1 in ?T & Q(st1)"] by auto
    qed
 qed

end