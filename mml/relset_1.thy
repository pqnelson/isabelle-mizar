\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory relset_1
  imports relat_1 subset_1
begin

reserve x,y,z for object
reserve X,Y for set

section "relset_1"

text_raw \<open>\DefineSnippet{relset1def1prefix}{\<close>
abbreviation relset_1_def_1 ("(Relation-of _,_)" 105)
where "Relation-of X,Y \<equiv> Subset-of [:X,Y:]"
text_raw \<open>}%EndSnippet\<close>

mtheorem relset_1_lm_1:
  "for R being Relation-of X,Y holds R \<subseteq> [:X,Y:]"
proof (rule ballI)
  fix R
  assume A1[ty]: "R be Relation-of X,Y"
  have [ty]:"R be set" by mauto
  have "R in (bool [:X,Y:])" using subset_1_def_1b[THEN iffD1] A1 by mauto
  thus B1: "R \<subseteq> [:X,Y:]" using zfmisc_1_def_1[of "[:X,Y:]" R] by auto
qed mauto

text_raw \<open>\DefineSnippet{relset_1_cl_1}{\<close>
theorem relset_1_cl_1[ty_cond_cluster]:
  "let X be set \<and> Y be set
   cluster \<rightarrow> Relation_like for Subset-of [:X,Y:]"
text_raw \<open>}%EndSnippet\<close>
proof-
  assume [ty]:"X be set \<and> Y be set"
  fix IT
  assume [ty]: "IT be Subset-of [:X,Y:]"
  show "IT is Relation_like"
    proof (intro relat_1_def_1I)
    (*  show "for x st x in IT ex y,z st x=[y,z]"
        proof (intro ballI impI)*)
          fix x
          have A2: "IT be Element-of (bool [:X,Y:])" by auto
          hence "IT in (bool [:X,Y:])" using subset_1_def_1b[THEN iffD1] by mauto
          hence B1: "IT \<subseteq> [:X,Y:]" using zfmisc_1_def_1 subset_1_def_1a[of _ IT ] by auto
          assume "x in IT"
          hence "x in [:X,Y:]" using B1 tarski_def_3a[of IT]  by auto
          thus "ex y,z st x=[y,z]" using B1 zfmisc_1_def_2 by auto
       qed mauto
qed

theorem relset_1_cl_2[ty_cond_cluster]:
   "let X be set \<and> Y be set
    cluster \<rightarrow> (X-defined) \<bar> (Y-valued) for (Relation-of X,Y)"
proof -
  assume A1[ty]:"X be set \<and> Y be set"
  fix IT
  assume A2[ty]: "IT be Relation-of X,Y"
  have B1: "IT \<subseteq> [:X,Y:]" using relset_1_lm_1 A2 by mauto
  show "IT is (X-defined) \<bar> (Y-valued)"
  proof (unfold ty_intersection, intro conjI)
    show "IT is (X-defined)"
    proof (intro relat_1_def_18I,simp,simp)
      show "dom IT \<subseteq> X"
      proof(intro tarski_def_3b)
        fix x
        assume "x in dom IT"
        then obtain y where
         "y be object" and A3: "[x,y] in IT" using xtuple_0_def_12 by auto
        hence "[x,y] in [:X,Y:]" using A3 B1 tarski_def_3 by auto
        thus "x in X" using A2 zfmisc_1_th_87 by simp
      qed mauto
    qed mauto
    show "IT is (Y-valued)"
    proof (intro relat_1_def_19I,simp,simp)
      show "rng IT \<subseteq> Y"
      proof(intro tarski_def_3b)
        fix x
        assume "x in rng IT"
        then obtain y where
          "y be object"  "[y,x] in IT" using xtuple_0_def_13 by auto
        hence "[y,x] in [:X,Y:]" using A2 B1 tarski_def_3 by auto
        thus "x in Y" using A2 zfmisc_1_th_87 by simp
      qed mauto
    qed mauto
  qed
qed

mtheorem relset_1_th_4:
  "for R being Relation st dom R \<subseteq> X \<and> rng R \<subseteq> Y holds R be Relation-of X,Y"
proof(rule ballI,rule impI)
  fix R
  assume A1[ty]: "R be Relation"
  assume "dom R \<subseteq> X \<and> rng R \<subseteq> Y"
  hence "R c= [:dom R,rng R:] \<and> [:dom R,rng R:] c= [:X,Y:]" using relat_1_th_7[of R]
       zfmisc_1_th_96[of Y "rng R" X "dom R"] A1 by mauto
  hence "R c= [:X,Y:]" using tarski_def_3 by mauto
  thus "R be Relation-of X,Y" using zfmisc_1_def_1 Element(6) by mauto
qed simp

end