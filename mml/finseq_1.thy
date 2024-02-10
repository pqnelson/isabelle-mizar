\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory finseq_1
  imports ordinal1 funct_1

begin
func finseq_1_def_1 ("Seg _") where
  mlet "n be Nat"
  "func Seg n \<rightarrow> set equals
     { i where i be Element-of NAT: i \<noteq> {} \<and> i c= n }"
    by mauto

reserve n,i for Nat

mtheorem finseq_1_th_1:
  "i in Seg n \<longleftrightarrow> (i\<noteq>{} \<and> i c= n)"
proof(rule iffI3)
  show "i in Seg n \<longrightarrow> i\<noteq>{} \<and> i c= n"
  proof
    assume "i in Seg n"
    hence B1: "i in {x where x be Element-of NAT: x \<noteq> {} \<and> x c= n}" using finseq_1_def_1 by mauto
    have J: " ex x be Element-of NAT st i = x \<and> x \<noteq> {} \<and> x c= n" using Fraenkel_A1_ex[OF _ _ B1] by auto
     obtain x where
      [ty]: "x be Element-of NAT"and
     A2: "i = x \<and> x \<noteq> {} \<and> x c= n" using bexE[OF J,of thesis] by auto
     thus " i\<noteq>{} \<and> i c= n" by mauto
   qed
  have [ty]:"i be Element-of NAT" using Element_of_NAT by mauto
  assume "i\<noteq>{} \<and> i c= n"
  hence "i in {x where x be Element-of NAT: x \<noteq> {} \<and> x c= n}" using Fraenkel_A1_in[of "Element-of NAT" i
           "\<lambda>x. x \<noteq> {} \<and> x c= n" ] by auto
  thus "i in Seg n" using finseq_1_def_1 by simp
qed


theorem finseq_1_cl_1:
  "Seg {} = {}"
proof(rule ccontr)
  assume "Seg {} \<noteq> {}"
  hence "ex x be object st x in Seg {}" using xboole_0_th_7 by mauto
  then obtain i where
     A1: "i in Seg {}" by auto
     hence B1: "i in {x where x be Element-of NAT: x \<noteq> {} \<and> x c= {}}" using finseq_1_def_1 by mauto
     have J: " ex x be Element-of NAT st i = x \<and> x \<noteq> {} \<and> x c= {}" using Fraenkel_A1_ex[OF _ _ B1] by auto
     obtain x where
      [ty]: "x be Element-of NAT"and
     A3: "i = x \<and> x \<noteq> {} \<and> x c= {}" using bexE[OF J,of thesis] by auto
     have "{} c= x" using tarski_def_3 xb by mauto
     thus "False" using A3 xboole_0_def_10 all_set by auto
qed


theorem finseq_1_cl:
  "n be Element-of NAT \<longrightarrow> Seg n c=  NAT"
proof(standard,standard)
  assume A1[ty]:"n be Element-of NAT"
  fix x
  assume "x in Seg n"
  hence B1: "x in { i where i be Element-of NAT: i \<noteq> {} \<and> i c= n }" using finseq_1_def_1 A1 by auto
   obtain i where
    T2[ty]:"i be Element-of NAT" and
    A2: "i = x" and
    A3: "i \<noteq>{} \<and> i c= n" using Fraenkel_A1_ex[OF _ _ B1] by auto
  show "x in NAT" using A2 ordinal1_def_12E by mauto
next show "n is Element-of omega \<Longrightarrow> Seg n is set"
  proof-
    assume [ty]:"n is Element-of omega"
    show "Seg n is set" by mauto
  qed
qed mauto


attr finseq_1_def_2 ("FinSequence-like")
 "attr FinSequence-like for Relation means (\<lambda>F. ex n be Element-of NAT st dom F = Seg n)"


theorem finseq_1_cl_2[ty_cond_cluster]:
  "cluster empty \<rightarrow> FinSequence-like for Relation"
proof
  fix X assume A1[ty]: "X be Relation" "X is empty"
  have "dom X is empty" by mauto
  hence H:"dom X={}" using xboole_0_lm_1 by mauto
  hence H:"dom X=Seg {}" using finseq_1_cl_1 by auto
  have "{} is Element-of NAT" using nat_0 Element_of_NAT by auto
  thus "ex n be Element-of NAT st dom X=Seg n" using H by mauto
qed mauto

theorem [ex]:
  "cluster FinSequence-like for Function"
proof
  show "{} is FinSequence-like \<bar> Function" by mauto
qed

abbreviation
  "FinSequence \<equiv> FinSequence-like\<bar> Function"


mdefinition finseq_1_def_4 ("FinSequence-of _")  where
  mlet "D be set"
  "mode FinSequence-of D \<rightarrow> FinSequence means
     (\<lambda>it. rng it c= D)" :mode_property
proof-
  have "inhabited(FinSequence)" by mauto
     have K: "{} c= D" using xb tarski_def_3 by mauto
  have "{} is empty" by mauto
  hence A1[ty]: "{} be FinSequence" by mauto
  have "rng {} is empty" by mauto
  hence "rng {}={}" using xboole_0_lm_1 by mauto
  hence "rng {} c= D" using K by auto
  thus "ex x be FinSequence st rng x \<subseteq> D" using bexI[of FinSequence] by mauto
qed mauto

lemma [ty_parent] :"D is set \<Longrightarrow> x is FinSequence-of D \<Longrightarrow> x is FinSequence" using finseq_1_def_4 by auto
lemmas [ex] = finseq_1_def_4(2)

func finseq_1_def_11 ("_*") where
  mlet "D be set"
  "func D* \<rightarrow> set means
     \<lambda>it. \<forall>x : object. 
         x in it \<longleftrightarrow> x be FinSequence-of D"
proof-
    let ?P = "\<lambda>p . p be FinSequence-of D"
    have A0: "bool [:NAT,D:] be set" using all_set by auto
    obtain IT where
   [ty]:"IT be set" and A1: "for x being object holds x in IT \<longleftrightarrow> x in bool [:NAT,D:] \<and> ?P(x)"
        using xboole_0_sch_1[OF A0, of ?P] by auto
     show "ex IT be set st \<forall>x : object.  x in IT \<longleftrightarrow> x be FinSequence-of D"
     proof(rule bexI[of _ _ IT],simp,rule ballI,rule iffI3)
       fix x assume "x be object"
       show "x in IT \<longrightarrow> x be FinSequence-of D" using A1 by mty auto
       assume A2[ty]: "x be FinSequence-of D"
         thm ty
       then obtain n where
         A3:"n be Element-of NAT" "dom x = Seg n" using finseq_1_def_2 by mauto
       have A4: "rng x c= D" using A2 finseq_1_def_4(1) by mauto
       have "dom x c= NAT" using A3 finseq_1_cl[of n] A3 by auto
       hence A5: "[:dom x,rng x:] c= [:NAT,D:]" using A4 A3(1) zfmisc_1_th_96[of D "rng x" NAT "dom x"] all_set by auto
       have A6: "x c= [:dom x,rng x:]" using relat_1_th_7[of x] A2 finseq_1_def_4 all_set by auto
       have "x c= [:NAT,D:]"
       proof(rule tarski_def_3b)
         fix a assume "a in x"
         hence "a in [:dom x,rng x:]" using A6 tarski_def_3a by mauto
         thus "a in [:NAT,D:]" using A5 tarski_def_3 by mauto
       qed mauto
       hence "x in bool [:NAT,D:]" using all_set zfmisc_1_def_1 by auto
       thus "x in IT" using A1 A2 by auto
     qed mauto
   next
  fix A1 A2
  assume A1:"A1 be set" "(\<forall>x : object. 
         x in A1 \<longleftrightarrow> x be FinSequence-of D)" and
        A2: "A2 be set" "\<forall>x : object. 
         x in A2 \<longleftrightarrow> x be FinSequence-of D"
    {
      fix x
      assume Z1: "x be object"
      have "x in A1 \<longleftrightarrow> (x be FinSequence-of D)" using Z1 A1 by auto
      then have "x in A1 \<longleftrightarrow> x in A2" using Z1 A2 by auto
    }
  thus "A1 = A2" using tarski_th_2[OF A1(1) A2(1)] by auto
qed mauto

reserve D for set

mtheorem finseq_1_th:
  "{} in D*"
proof-
  have A1[ty]:"{} be FinSequence" by mauto
  have "rng {} is empty" by mauto
  hence H:"rng {}={}" using xboole_0_lm_1 by mauto
  hence H:"rng {} \<subseteq> D" using xb tarski_def_3 by mauto
  thus "{} in D*" using finseq_1_def_11 finseq_1_def_4 by mauto
qed

end