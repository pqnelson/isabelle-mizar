\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Relset_1
imports Relat_1 Subset_1
begin

reserve x,y,z for object
reserve X,Y for set


(*relset_1*)

definition relset_1_def_1_prefix ("( Relation-of _ , _  )" 105)
where relset_1_def_1: "Relation-of X,Y \<equiv> Subset-of [:X,Y:]"

mtheorem relset_1_lm_1:
  "for R being Relation-of X,Y holds R \<subseteq> [:X,Y:]" 
proof (rule ballI )
  fix R
  assume A1: "R be Relation-of X,Y"
  hence  A2: "R be Element-of (bool [:X,Y:])" using relset_1_def_1 subset_1_def_2 by auto
  hence "R in (bool [:X,Y:])" using A1 subset_1_cl_1 assms subset_1_def_1 by auto
  thus B1: "R \<subseteq> [:X,Y:]" using zfmisc_1_def_1 all_set by auto
qed


theorem relset_1_cl_1:
  "let X be set & Y be set 
   cluster \<rightarrow> Relation_like for Subset-of [:X,Y:]"
proof(intro impI ballI)
  assume "X be set & Y be set"
  fix IT
  assume A1: "IT be Subset-of [:X,Y:]"
  show "IT is Relation_like"
    proof (unfold relat_1_def_1a, intro conjI)
      show "IT be set" using all_set by simp
      show "for x st x in IT ex y,z st x=[y,z]"
        proof (intro ballI impI)
          fix x
          assume "x be object"
          have  A2: "IT be Element-of (bool [:X,Y:])" using A1 relset_1_def_1 subset_1_def_2 by auto
          hence "IT in (bool [:X,Y:])" using A1 subset_1_cl_1 all_set subset_1_def_1 by auto
          hence B1: "IT \<subseteq> [:X,Y:]" using zfmisc_1_def_1 all_set by auto
          assume "x in IT" 
          hence "x in [:X,Y:]" using B1 by auto  
          thus "ex y,z st x=[y,z]" using B1 zfmisc_1_def_2 all_set by auto  
        qed
    qed
qed

theorem relset_1_cl_ad:
  "let X be set & Y be set
   cluster \<rightarrow> Relation_like for Relation-of X,Y" 
proof(intro ballI impI)
  assume A: "X be set & Y be set"
  fix R
  assume "R be Relation-of X,Y" 
  hence "R be Subset-of ([:X,Y:])" using relset_1_def_1 by simp 
  thus "R is Relation_like"
    using A relset_1_cl_1[of "X"] by auto
qed

theorem relset_1_cl_2:
   "let X be set & Y be set
    cluster \<rightarrow> (X-defined) \<bar> (Y-valued) for (Relation-of X,Y)"
proof (intro impI ballI)
  assume A1:"X be set & Y be set"
  fix IT
  assume A2: "IT be (Relation-of X,Y)"
  hence B1: "IT \<subseteq> [:X,Y:]" using A1 relset_1_lm_1 by auto
  show "IT is  (X-defined) \<bar> (Y-valued)"
    proof (unfold attr_attr, intro conjI)
       show "IT is (X-defined)"
          proof (unfold relat_1_def_18a,intro conjI)            
            show T0: "IT be Relation" using A1 relset_1_cl_1 all_set relset_1_def_1 A2 by simp
            show "X be set" using A1 by simp  
            show "dom IT \<subseteq> X"
              proof(unfold tarski_def_3,intro ballI impI) 
                fix x 
                assume "x be object" "x in dom IT"
                then obtain y where
                  "y be object"  and A3: "[x,y] in IT" using T0 xtuple_0_def_12 by auto
                hence "[x,y] in [:X,Y:]" using A3 B1 by auto
                thus "x in X" using A2 zfmisc_1_th_87 by simp
              qed
          qed
       show "IT is (Y-valued)"
          proof (unfold relat_1_def_19a,intro conjI)
            show T0: "IT be Relation" using A1 relset_1_cl_1 all_set relset_1_def_1 A2 by simp
            show "Y be set" using A1 by simp  
            show "rng IT \<subseteq> Y"
              proof(unfold tarski_def_3,intro ballI impI) 
                fix x 
                assume "x be object" "x in rng IT"
                then obtain y where
                  "y be object"  "[y,x] in IT" using T0 xtuple_0_def_12 by auto
                hence "[y,x] in [:X,Y:]" using A2 B1 by auto
                thus "x in Y" using A2 zfmisc_1_th_87 by simp
              qed
          qed
     qed
qed

theorem relset_1_th_4:
  "for R being Relation st dom R \<subseteq> X & rng R \<subseteq> Y holds R be Relation-of X,Y"
proof(rule ballI,rule impI)
  fix R 
  assume A1: "R be Relation"
  assume "dom R \<subseteq> X & rng R \<subseteq> Y"
  hence "R c= [:dom R,rng R:] & [:dom R,rng R:] c= [:X,Y:]" using relat_1_th_7[of R] 
       zfmisc_1_th_96[of Y "rng R" X "dom R"] A1 all_set by auto
  thus "R be Relation-of X,Y" using zfmisc_1_def_1 all_set Element_of_rule subset_1_def_2 relset_1_def_1 by simp
qed

end