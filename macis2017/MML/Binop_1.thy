\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Binop_1
  imports Funct_2
begin

definition binop_0_def_1_prefix (" _ . \<lparr> _ , _ \<rparr>"[90,90,90]) where
  "func f . \<lparr> a , b \<rparr> \<rightarrow> set equals 
        f.[a,b]"

schematic_goal binop_0_def_1:
  assumes "f be Function & a be object & b be object" shows "?X"
proof (rule equals_property[OF binop_0_def_1_prefix_def])    
  show "(f.[a,b]) be set" using assms funct_1_def_2 by simp
qed

theorem binop_0_def_2:
 "let A be non empty \<parallel> set & B be non empty \<parallel> set & C be set &
        f be (Function-of [:A,B:],C) & a be (Element-of A) & b be (Element-of B)
  redefine func f.\<lparr>a,b\<rparr>  \<rightarrow> Element-of C"
proof-
  assume A0: "A be non empty \<parallel> set &B be non empty \<parallel> set & C be set &
        f be (Function-of [:A,B:],C) & a be (Element-of A) & b be (Element-of B)"
 have "a in A & b in B " using A0 subset_1_def_1 by auto
  hence "[a,b] in [:A,B:]" by auto
  hence "[:A,B:] be non empty\<parallel>set" "[a,b] be Element-of [:A,B:]" using subset_1_def_1[of "[:A,B:]" "[a,b]"] all_set by auto
  hence A1: "(f.[a,b]) be Element-of C" using A0 funct_2_def_5[of "[:A,B:]" "C" "f" "[a,b]"]  by auto
  have "f be Function" using A0 relset_1_cl_ad all_set by auto
  thus "f.\<lparr> a, b \<rparr> be Element-of C" using A0 binop_0_def_1 all_set A1 by auto
qed

abbreviation  (input) binop_1_mode_1 ("UnOp-of _" 190) where 
  "UnOp-of X \<equiv> Function-of X , X"

definition binop_1_mode_2 ("BinOp-of _" 190) where 
  "BinOp-of X \<equiv> Function-of [:X,X:] , X"

theorem binop_0_def_20: 
  "let A be set & (f be BinOp-of A) & (a be Element-of A) & (b be Element-of A)
   redefine func  f.\<lparr>a,b\<rparr>  \<rightarrow> Element-of A"
proof-
  assume A0:"A be set & (f be BinOp-of A) & (a be Element-of A) & (b be Element-of A)"
  have W: "f be Function" using A0 relset_1_cl_ad all_set binop_1_mode_2_def by auto
   hence Z: "f.\<lparr> a,b \<rparr> = f.[a,b]" using binop_0_def_1 by simp 
   show "f.\<lparr>a,b\<rparr> be (Element-of A)"
    proof(cases "A={}")
      assume A1: "A={}"
       hence "f = {}" using funct_2_def_1a A0 all_set binop_1_mode_2_def by simp 
       hence "not [a,b] in dom f" using relat_1_cl_20 by simp
       hence "f.[a,b] = {}" using funct_1_def_2 W by simp
      thus  "f.\<lparr>a,b\<rparr> be (Element-of A)" using A1 Z by simp
    next
      assume A2: "A<>{} "
       hence "A is non empty" using xboole_0_lm_1 A0 by auto   
       hence "dom f = [:A,A:]" "a in A" "b in A" using A2 subset_1_def_1 funct_2_def_1a A0 binop_1_mode_2_def by auto
       hence "[a,b] in [:A,A:]" using all_set  by auto
       hence "[:A,A:] be non empty\<parallel>set" "[a,b] be Element-of [:A,A:]" using subset_1_def_1[of "[:A,A:]" "[a,b]"] all_set by auto
       hence "(f.[a,b]) be Element-of A" using A0 funct_2_def_5[of "[:A,A:]" "A" "f" "[a,b]"] binop_1_mode_2_def by auto   
      thus  "f.\<lparr>a,b\<rparr> be (Element-of A)" using Z by auto
    qed 
  qed

lemma BinOp_ex: "ex B be BinOp-of X st True"
proof-
  let ?Z = "\<lambda> x y. for x1,x2 be object st x=[x1,x2] holds y=x1"
  have T1:"X be set" using all_set by auto
  obtain R where
    T2: "R be Relation" and
    A1: "for x,y be object holds [x,y] in R iff x in [:X,X:] & y in X & ?Z(x,y)" 
         using relat_1_sch_1[of "[:X,X:]" "X" "?Z"] all_set by auto
  have T3: "R be Relation-of [:X,X:],X" 
    proof-
      have "R \<subseteq> [: [: X , X :] , X :]" unfolding tarski_def_3
        proof(rule ballI,rule impI)
          fix x
          assume A2: "x be object" "x in R"
          then obtain x1 x2 where
            A3: "x1 be object" "x2 be object" "x=[x1,x2]" using T2 relat_1_def_1a by auto
          hence "x1 in [:X,X:] & x2 in X" using A1 A2 by simp
          thus "x in [: [: X , X :] , X :]" using  A3 zfmisc_1_th_87[of "[:X,X:]" X] by simp
        qed
      hence "R in bool [: [: X , X :] , X :]" using zfmisc_1_def_1 all_set by auto
      thus "R be  Relation-of [:X,X:],X" using relset_1_def_1 subset_1_def_2 Element_of_rule by simp
    qed
  have W1: "R<>{} implies X<>{}"
     proof
        assume "R<>{}"
        then obtain x where
          A2:"x be object" "x in R" using xboole_0_def_1a all_set xboole_0_def_2c tarski_th_2[of R "{}"] by auto
        then obtain x1 x2 where
          "x1 be object" "x2 be object" "x=[x1,x2]" using T2 relat_1_def_1a by auto
        hence "x2 in X" using A1 A2 by simp
        thus "X<>{}" by simp
     qed 
  have "X<>{} \<Longrightarrow> [:X,X:] = dom R"
    proof-
      assume "X<>{}" 
      have B1:"[:X,X:] \<subseteq> dom R" unfolding tarski_def_3
         proof(rule ballI,rule impI)
            fix x 
            assume B2:"x be object" "x in [:X,X:]"
            then obtain x1 x2 where
              B3: "x1 be object" "x2 be object" "x=[x1,x2]" using T2 relat_1_def_1a by auto
            hence B4:"x1 in X" using B2 zfmisc_1_th_87 by simp
            have "?Z(x,x1)"
              proof(intro ballI,rule impI)
                 fix y1 y2
                 assume B5:"y1 be object" "y2 be object" "x=[y1,y2]"
                 show "x1=y1" using xtuple_0_th_1[of y1 y2 x1 x2] B3(3) B5(3) by auto
              qed 
            hence "[x,x1] in R" using A1[rule_format,of x x1, OF B2(1) B3(1)] B3 B2(2) B4 by iprover
            thus "x in dom R" using T2 xtuple_0_def_12 by auto 
         qed
      have "dom R \<subseteq> [:X,X:]" unfolding tarski_def_3
      proof(rule ballI, rule impI)
         fix x 
         assume "x in dom R"
         then obtain y where
           "y be object" "[x,y] in R" using xtuple_0_def_12 T2 by auto
         thus "x in [:X,X:]" using A1 by simp
      qed
      thus "[:X,X:] = dom R" using xboole_0_def_10 B1 all_set by auto
    qed
  hence T4: "R is [:X,X:],X :quasi-total" using W1 T3 funct_2_def_1a by auto
  have "for x,y1,y2 being object st [x,y1] in R & [x,y2] in R holds y1 = y2"
     proof(intro ballI impI)
        fix x y1 y2
        assume A2:"[x,y1] in R & [x,y2] in R"
        hence A3:"x in [:X,X:]" using A1 by auto
        then obtain x1 x2 where
          A3: "x1 be object" "x2 be object" "x=[x1,x2]" using zfmisc_1_def_1 by auto
        have A4: "?Z(x,y1)" "?Z(x,y2)" using A2 A1 by simp+
        show "y1 =y2" using A3(3) A4(1)[rule_format,of x1 x2] A4(2)[rule_format,of x1 x2]by auto
     qed
  hence "R is Function_like" using funct_1_def_1 all_set by simp
  thus ?thesis using binop_1_mode_2_def T4 by auto
qed

definition funct_5_def_4 ("op0") where
  "func op0 \<rightarrow> set equals
     {}"

schematic_goal funct_5_def_4:
   shows "?X"
by (rule equals_property [OF funct_5_def_4_def]) (simp add:all_set)  

definition funct_5_def_6 ("op2") where
  "func op2 \<rightarrow> set equals
     {[[ {},{} ],{}]}"

schematic_goal funct_5_def_6:
   shows "?X"
by (rule equals_property [OF funct_5_def_6_def]) (simp add:all_set)

theorem funct_5_def_7:
  "op0 be Element-of {{}}" using tarski_def_1b funct_5_def_4 by auto 

theorem funct_5_def_9:
  "op2 be BinOp-of {{}}" 
proof-
  have "op2 is Function_like" "op2 is Relation_like" 
    using funct_5_def_6[THEN conjunct2] funct_1_cl_3[of "[ {},{} ]" "{}"] relat_1_cl_7[of "[ {},{} ]" "{}"]
    by auto
  hence B1: "op2 be Function" using all_set by simp
  hence "dom op2=[:{{}},{{}}:]" "rng op2 = {{}}" using funct_5_def_6 
              relat_1_th_3[of "{}" "[{},{}]" op2] zfmisc_1_th_28 by auto
  thus B2: "op2 be BinOp-of {{}}" using funct_2_th_2[of op2,OF B1] binop_1_mode_2_def by auto  
qed

end