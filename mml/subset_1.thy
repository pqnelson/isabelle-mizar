theory subset_1
imports zfmisc_1
begin

mtheorem subset_1_cl_1[ty_func_cluster]:
  mlet "X be set"
  "cluster bool X \<rightarrow> non empty"
using xboole_0_def_1 zfmisc_1_def_1[of "X" "X"] tarski_def_3c by mauto

theorem empty1:
  "x is empty \<Longrightarrow> x={}"
proof(rule xboole_0_def_10a)
  assume A1: "x is empty"
  show "x \<subseteq> {}" "{} \<subseteq> x"
  proof -
    show "x \<subseteq> {}" using A1 all_set tarski_def_3 xboole_0_def_1 by auto
    have "{} is empty" by mauto
    thus "{} \<subseteq> x" using all_set tarski_def_3 xboole_0_def_1 by auto
  qed
qed (simp add: all_set)+

theorem empty2:
  "x is non empty \<Longrightarrow> x\<noteq>{} " using empty1 by mauto

(*  :: "Set \<Rightarrow> Ty" *)
text_raw \<open>\DefineSnippet{subset_1_def_1}{\<close>
mdefinition subset_1_def_1      ("Element-of _" [105] 105) where
  mlet "X be set"
  "mode Element-of X \<rightarrow> set means
   (\<lambda>it. (it in X if X be non empty otherwise it be empty))" : mode_property
text_raw \<open>}%EndSnippet\<close>
proof(simp,cases "X={}")
  assume A1: "X={}"
  hence A2: "X is empty" by mty auto
  hence "not X is non empty" using xboole_0_def_1 by auto
  hence "{} in X if X is non empty otherwise {} is empty" using A1 A2 by auto
  thus "ex x be set st (x in X if X is non empty otherwise x is empty)" using bexI[of _ _ "{}"] by mauto
next
  assume A1: "X\<noteq>{}"
  hence [ty]: "X is non empty" using empty1 by auto
  then obtain x where
      "x be object" and A1: "x in X" using xboole_0_def_1I by mauto
   hence "x in X if X is non empty otherwise x is empty" by auto
  thus "ex x be set st (x in X if X is non empty otherwise x is empty)" using bexI[of _ _ "{}"] tarski_0_1 by auto
qed

lemmas subset_1_def_1a[ty_parent] = subset_1_def_1(1)[THEN iffD1,THEN conjunct1]
lemmas subset_1_def_1b = subset_1_def_1(1)
lemmas subset_1_def_1c[ex] = subset_1_def_1(2)

text_raw \<open>\DefineSnippet{ElementofP}{\<close>
abbreviation (input) ElementofS :: "(Set \<Rightarrow> Set) \<Rightarrow> (Set \<Rightarrow> Ty)" ("Element-of'' _") where
  "Element-of' F \<equiv> \<lambda>it. Element-of F(it)"
text_raw \<open>}%EndSnippet\<close>



lemma Element_of:
  "X is non empty \<Longrightarrow> (x be Element-of X) \<longleftrightarrow> x in X"
  "X is empty \<Longrightarrow> (x be Element-of X) \<longleftrightarrow> x is empty"
  using subset_1_def_1b all_set xboole_0_def_1(1) empty1 by auto

lemma Element_of1:
   "X is non empty \<Longrightarrow> x be Element-of X \<Longrightarrow> x in X" using Element_of(1) by auto

lemma Element_of_rule:
  "x be Element-of {} \<Longrightarrow> x={}" using Element_of empty1 by (intro empty1) mauto

lemma Element_of_rule1:
  "{} be Element-of {}" using Element_of empty1 by mauto

lemma Element_of_rule2:
  "X be set \<Longrightarrow> X\<noteq> {} \<Longrightarrow> x be Element-of X \<Longrightarrow> x in X"
proof-
  assume A1: "X \<noteq>{}" "x be Element-of X"
  hence "X is non empty" using xboole_0_def_1I empty1 by auto
  thus "x in X" using A1 Element_of by auto
qed

lemma Element_of_rule3:
  "X be set \<Longrightarrow> x in X \<Longrightarrow> x be Element-of X" using xb1[of x X] empty1 Element_of by auto


lemmas Element= Element_of Element_of_rule1 Element_of_rule2 Element_of_rule Element_of_rule3
Element_of(1)[THEN iffD1]
theorem sethood_of_Element_of[simp]:
  "sethood(Element-of X)"
proof(unfold sethood, cases "X={}")
   assume A1: "X={}"
   show "ex SH being set st (for x being object holds (x be (Element-of X) \<longleftrightarrow> x in SH))"
     proof(intro bexI[of _ _"{{}}"] ballI)
        show "{{}} be set" by mauto
        fix x
        assume "x be object"
        show "x be (Element-of X) \<longleftrightarrow> x in {{}}"
          proof(intro iffI2)
            show "x be (Element-of X) \<longrightarrow> x in {{}}"
              proof
                assume "x be Element-of X"
                hence "x={}" using A1 Element(5) by auto
                thus "x in {{}}" using tarski_def_1 by simp
              qed
            show "x in {{}} \<longrightarrow> x be (Element-of X)"
                 proof
                    assume "x in {{}}"
                    hence "x={}" using tarski_def_1 by simp
                    thus "x be Element-of X" using A1 Element(3) by auto
                 qed
          qed
     qed simp_all
next
assume A1: "X\<noteq>{}"
   show "ex SH being set st (for x being object holds (x be (Element-of X) \<longleftrightarrow> x in SH))"
     proof(intro bexI[of _ _ "X"] ballI impI)
        show "X be set" using all_set by simp
        fix x
        assume "x be object"
        have "X is non empty" using A1 empty1 by auto
        then show "x be (Element-of X) \<longleftrightarrow> x in X"
            using A1 Element(1) by auto
     qed simp_all
qed


abbreviation subset_1_def_2 ("Subset-of _" 105)
where "Subset-of X \<equiv> Element-of (bool X)"

mtheorem subset_1_cl_3[ex]:
  mlet "Y be non empty\<bar> set"
  "cluster non empty for Subset-of Y"
  unfolding inhabited_def
proof
  have "Y in bool Y" using zfmisc_1_def_1[of Y Y ] xboole_0_def_10[of Y Y] by auto
  hence "Y be Element-of (bool Y)" using Element(6) by mauto
  thus "Y be non empty\<bar>Subset-of Y" by auto
qed

lemma Subset_of_rule:
  "X \<subseteq> A \<Longrightarrow> X be Subset-of A" using zfmisc_1_def_1[OF all_set all_set]
        Element(6) all_set by auto


lemma Subset_in_rule:
  "X be Subset-of A \<Longrightarrow> X \<subseteq> A"
  using zfmisc_1_def_1 all_set subset_1_cl_1[of A] Element_of[of "bool A" X] by auto

text_raw \<open>\DefineSnippet{subset_0_def_4}{\<close>
func subset_0_def_4("'(_,_')`") where
    mlet "E be set","A be Subset-of E"
  "func (E,A)` \<rightarrow> Subset-of E equals
     E \\ A"
text_raw \<open>}%EndSnippet\<close>
proof-
   have "E\\A c= E" using xboole_0_def_5 tarski_def_3 by auto
    hence "E\\A in bool E" using zfmisc_1_def_1 by auto
  thus "(E\\A) be Subset-of E" using Element(6) by auto
qed

lemma Subset_trans:
  "A be Subset-of B \<Longrightarrow> B be Subset-of C \<Longrightarrow> A be Subset-of C"
proof-
  assume "A be Subset-of B" "B be Subset-of C"
  hence "A \<subseteq> B" " B\<subseteq> C" using Subset_in_rule by auto
  hence "A \<subseteq> C" using tarski_def_3 all_set by auto
  thus "A be Subset-of C" using Subset_of_rule by auto
qed

func subset_1_def_8 ("In '(_ , _')") where
  mlet "x be object","X be set"
  "assume x in X
   func In(x , X) \<rightarrow> Element-of X equals
     x"
proof-
  assume "x in X"
  thus "x be Element-of X" using Element_of_rule3 all_set by auto
qed mauto

abbreviation Subset_Family_prefix ("( Subset-Family-of _ )" 105)
where "Subset-Family-of X \<equiv> Subset-of (bool X)"



end
