\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Zfmisc_1
  imports Xboole_0 Xfamily Xtuple_0
begin

reserve x,y,z,x1,x2,y1,y2 for object
reserve X,Y,Z for set

(* zfmisc1 *)

definition zfmisc_1_def_1_prefix ("bool _" 110) where
"func (bool X) \<rightarrow> set means \<lambda>it. (for Y holds Y in it iff Y c= X)"

schematic_goal  zfmisc_1_def_1:
  assumes "X be set" shows "?X"
proof (induct rule: means_property[OF  zfmisc_1_def_1_prefix_def, of X,case_names existence uniqueness])
   case existence
       let ?IT="\<lambda>x. x c= X"
       obtain M where
          A1: "M be set" "X in M" "(for X,Y holds X in M & Y c= X implies Y in M) &
            (for X st X in M ex Z st Z in M & (for Y st Y c= X holds Y in Z)) &
            (for X holds X c= M implies (X,M areequipotent or X in M))" using bspec[OF tarski_a_th_1 assms] by auto
       obtain IT where
          A2: "IT be set & (for Y being object holds (Y in IT iff Y in M & Y c= X))" using xboole_0_sch_1[OF A1(1),of ?IT] by auto
       (*take IT*)
       show "ex IT being set st (for Y being set holds (Y in IT iff Y c= X))" 
          proof (rule bexI[of _ IT])
            show "IT be set" using A2 by auto
            show "for Y being set holds (Y in IT iff Y c= X)" using A1 A2 assms by blast
          qed
   case uniqueness
       fix x y
       assume A1:"x be set" and A2:"y be set" and A3: "(for Z being set holds (Z in x iff Z c= X))"
          and A4: "(for Z being set holds (Z in y iff Z c= X))"       
       thus "x = y" using xfamily_sch_3[OF A1 A2 A3 A4] by auto
qed

definition cartesian_product ("[: _ , _ :]") where
  "func [: X1, X2 :] \<rightarrow> set means \<lambda>it. (for z holds z in it iff (ex x, y st x in X1 & y in X2 & z = [x, y]))"
schematic_goal zfmisc_1_def_2:
  assumes "X1 be set & X2 be set" shows "?X"
proof (induct rule: means_property[OF cartesian_product_def, of X1 X2, case_names existence uniqueness])
   case existence
      let ?X1="\<lambda>it1. ex x,y st x in X1 & y in X2 & it1 = [x,y]"
     have AA: "(bool(bool(X1 \<union> X2))) be set" using zfmisc_1_def_1 by auto
    obtain X where
    T2:" X be set " and A2: "for z being object holds z in X iff (z in (bool(bool(X1 \<union> X2))) & ?X1(z))" using
                     xboole_0_sch_1[OF AA, of ?X1] by blast
       show "ex X being set st (for z holds z in X iff (ex x, y st x in X1 & y in X2 & z = [x, y]))" 
          proof (rule bexI[of _ X])
             show "X be set" using T2 by simp
             show "for z holds z in X iff (ex x, y st x in X1 & y in X2 & z = [x, y])"
                proof (intro ballI, rule iffI2)
                  fix z
                  assume "z be object"
                  show "z in X implies (ex x, y st x in X1 & y in X2 & z = [x, y])" using A2 by simp
                  show "(ex x, y st x in X1 & y in X2 & z = [x, y]) implies z in X"
                     proof
                       assume "ex x, y st x in X1 & y in X2 & z = [x, y]"
                       then obtain x y where 
                          "x be object & y be object"  and A3: "x in X1" and A4:"y in X2" and A5:  "z = [x, y]" by auto   
                       have A5': "z = {{x,y},{x}}" using A5 tarski_def_5 by simp
                       have "{x,y} c= X1 \<union> X2"
                         proof (unfold tarski_def_3, intro ballI impI)
                           fix z
                           assume "z be object" "z in {x,y}"
                           thus "z in X1 \<union> X2" using A3 A4 xboole_0_def_3 by auto 
                         qed                  
                       hence A6: "{x,y} in bool(X1 \<union> X2)" using zfmisc_1_def_1 by auto
                       have "{x} c= X1 \<union> X2"
                         proof (unfold tarski_def_3, intro ballI impI)
                           fix z
                           assume "z be object" "z in {x}"
                           thus "z in X1 \<union> X2" using A3 A4 xboole_0_def_3 tarski_def_1b by auto
                         qed                  
                       hence A7: "{x} in bool(X1 \<union> X2)" using zfmisc_1_def_1 by auto
                       hence "{{x,y},{x}} c= bool(X1 \<union> X2)" using A6 tarski_def_2 by auto
                       hence "{{x,y},{x}} in bool(bool(X1 \<union> X2))" using zfmisc_1_def_1 by auto
                       thus "z in X" using A2[rule_format, of z,simplified] A3 A4 A5 A5' by auto
                     qed
                qed
          qed 
  case uniqueness then show ?case using xboole_0_sch_3 assms by auto
qed

lemmas zfmisc_1_def_2a[simp,type_infer] = zfmisc_1_def_2[unfolded atomize_conjL[symmetric],THEN conjunct1,THEN conjunct1,OF all_set all_set]
lemmas zfmisc_1_def_2b[simp] = zfmisc_1_def_2[THEN conjunct1,THEN conjunct2,unfolded atomize_conjL[symmetric],simplified all_set,simplified,rule_format]


definition cartesian_product3 ("[: _ , _ , _ :]") where
  "func [: X1,X2,X3 :] \<rightarrow> set equals [:[:X1,X2:],X3:]"
schematic_goal zfmisc_1_def_3:
   assumes "X1 be set & X2 be set & X3 be set"
   shows "?X"
proof (rule equals_property[OF cartesian_product3_def])    
  show "[:[:X1,X2:],X3:] be set" using all_set by simp
qed

abbreviation triple ("[ _ , _ , _]") where
  "[x,y,z] \<equiv> [[x,y],z]"
  
theorem zfmisc_3:
  "x in [: X1,X2,X3 :] \<Longrightarrow> ex x1,x2,x3 be object st x = [x1,x2,x3] & x1 in X1 & x2 in X2 & x3 in X3"
proof-
  assume "x in [: X1,X2,X3 :]"
  hence "x in [:[:X1,X2:],X3:]" using zfmisc_1_def_3 all_set by auto
  then obtain x12 x3 where
   A1:  "x12 be object" "x3 be object" "x12 in [:X1,X2:] & x3 in X3 & x = [x12,x3]"  using zfmisc_1_def_2 by auto  
  obtain x1 x2 where
     "x1 be object" "x2 be object" "x1 in X1 & x2 in X2 & x12 = [x1,x2]"  using A1 zfmisc_1_def_2 by auto   
  thus "ex x1,x2,x3 be object st x = [x1,x2,x3] & x1 in X1 & x2 in X2 & x3 in X3" using A1 by auto
qed  

definition trivial::Attr ("trivial")
where zfmisc_1_def_10a[THEN defattr_property,simp]: "trivial \<equiv> define_attr(\<lambda>X. X be set & (for x,y st x in X & y in X holds x=y))"

definition nontrivial :: Attr ("non trivial")
where zfmisc_1_def_10b[THEN defattr_property,simp]: "nontrivial\<equiv>  define_attr (\<lambda>X. X be set & (ex x,y st x in X & y in X & x<>y))"

mtheorem zfmisc_1_th_28:
  "[:{x},{y}:] = {[x,y]}"
proof(rule  tarski_0_2[simplified,rule_format])
  show "[:{x},{y}:] be set" "{[x,y]} be set" by auto
  fix z
  show "z in [:{x},{y}:] \<longleftrightarrow> z in {[x,y]}"
    proof (rule iffI3)
      show "z in [:{x},{y}:] implies z in {[x,y]}"
        proof
          assume "z in [:{x},{y}:]"
          then obtain x1 y1 where
            T1:"x1 be object" "y1 be object" and
            A1:"x1 in {x} & y1 in {y}" and
            A2:"z=[x1,y1]" using zfmisc_1_def_2 by simp auto
          have "x1=x & y1=y" using A1 tarski_def_1 by simp
          thus "z in {[x,y]}" using A2 tarski_def_1 by simp
       qed
        assume "z in {[x,y]}"
        hence A3: "z=[x,y]" using tarski_def_1 by simp
        have "x in {x} & y in {y}" using tarski_def_1 by simp
        thus  "z in  [:{x},{y}:]" using A3 zfmisc_1_def_2 tarski_def_1b by simp 
     qed
qed


theorem zfmisc_1_th_87:
  "for x,y holds [x,y] in [:X,Y:] iff x in X & y in Y"
proof (intro ballI)
  fix x y
  assume T0: "x be object" "y be object"
  show "[x,y] in [:X,Y:] iff x in X & y in Y"
     proof(rule iffI2)
        show "[x,y] in [:X,Y:] implies x in X & y in Y"
           proof
               assume "[x,y] in [:X,Y:]"
               hence "ex x1,y1 st x1 in X & y1 in Y & [x,y]=[x1,y1]" using zfmisc_1_def_2 by auto
               then obtain x1 y1 where
                  "x1 be object "  "y1 be object " and A1: "x1 in X & y1 in Y & [x,y]=[x1,y1]" by auto
               have "x=x1 & y=y1" using A1 xtuple_0_th_1 [of "x" "y"] by auto
               thus "x in X & y in Y" using A1 by simp 
           qed
       show "x in X & y in Y implies [x,y] in [:X,Y:]" using zfmisc_1_def_2 by auto
    qed
qed
reserve X1, X2,Y1,Y2 for set

mtheorem zfmisc_1_th_96:
  "X1 \<subseteq> Y1 & X2 \<subseteq> Y2 implies [:X1,X2:] \<subseteq> [:Y1,Y2:]"
proof
  assume A1: "X1 \<subseteq> Y1 & X2 \<subseteq> Y2"
  show "[:X1,X2:] \<subseteq> [:Y1,Y2:]"
     proof (unfold tarski_def_3,rule ballI, rule impI)
       fix x
       assume "x be object"
       assume A2: "x in [:X1,X2:]"
       then obtain x1 x2 where 
        T0: "x1 be object" "x2 be object" and A3: "x = [x1,x2]" by auto
       have "x1 in X1 & x2 in X2" using A2 A3 zfmisc_1_th_87 by simp
       hence "x1 in Y1 & x2 in Y2" using A1 tarski_def_3 by simp
       thus "x in [:Y1,Y2:]" using A3 zfmisc_1_th_87 by simp
    qed
qed

end