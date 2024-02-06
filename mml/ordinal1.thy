theory ordinal1
imports zfmisc_1 subset_1
begin

reserve u,v,x,x1,x2,y,y1,y2,z,p,a for object
reserve A,B,X,X1,X2,X3,X4,X5,X6,Y,Y1,Y2,Z,N,M for set

section "ordinal1"

mtheorem ordinal1_th_1:"Y in X \<longrightarrow> \<not> X \<subseteq> Y"
proof (standard,standard)
  assume A1:"Y in X"
  assume "X \<subseteq> Y"
  hence "Y in Y" using A1 tarski_def_3 by mauto
  thus "False" using prefix_in_irreflexive by mauto
qed

func ordinal1_def_1 ("succ _" [90] 90) where
  "func succ X \<rightarrow> set equals X \<union> {X}"
proof -
  show "(X \<union> {X}) be set" by simp
qed

mtheorem ordinal1_th_2:"X in succ X"
proof -
  have "X in {X}" using tarski_def_1 by mauto
  thus ?thesis using xboole_0_def_3 ordinal1_def_1 by mauto
  qed

mtheorem ordinal1_th_4:"x in succ X \<longleftrightarrow> x in X \<or> x = X"
proof (rule iffI3)
  show "x in succ X \<longrightarrow> x in X \<or> x = X"
  proof
    assume "x in succ X"
    hence "x in X \<or> x in {X}" using xboole_0_def_3 ordinal1_def_1 by mauto
    thus "x in X \<or> x = X" using tarski_def_1[of X] by mauto
  qed
  assume "x in X \<or> x = X"
  hence "x in X \<or> x in {X}" using tarski_def_1 by mauto
  thus "x in succ X" using xboole_0_def_3 ordinal1_def_1 by mauto
qed

reserve a,b,c for object
reserve X,Y,Z,x,y,z for set

attr ordinal1_def_2 ("epsilon-transitive")
  "attr epsilon-transitive for set means
     (\<lambda>X. for x st x in X holds x c= X)"

attr ordinal1_def_3 ("epsilon-connected")
  "attr epsilon-connected for set means
     (\<lambda>X. for x,y st x in X \<and> y in X holds x in y \<or> x = y \<or> y in x)"

attr ordinal1_def_4 ("ordinal")
  "attr ordinal for object means
     (\<lambda>IT. IT is epsilon-transitive \<bar> epsilon-connected \<bar> set)"

attr ordinal1_def_6 ("limit'_ordinal")
  "attr limit_ordinal for set means (\<lambda>A. A = union A)"

abbreviation (input) "Number \<equiv> object"
abbreviation (input) "number \<equiv> set"
abbreviation "Ordinal \<equiv> ordinal \<bar> number"

lemma Lm1:"{} is epsilon-transitive \<bar> epsilon-connected"
  unfolding ty_intersection
  using xb1 by (intro conjI ordinal1_def_2I ordinal1_def_3I) mauto

theorem [ex]: "cluster ordinal for number"
proof
  show "{} is Ordinal" using Lm1 ordinal1_def_4I by mauto
qed

theorem [ex]: "cluster epsilon-transitive for number"
proof
  show "{} is epsilon-transitive \<bar> number" using Lm1 by mauto
qed

reserve A,B,C,D for Ordinal

declare ordinal1_def_4I[rotated,rotated,ty_cond_cluster]
declare ordinal1_def_4E[ty_cond_cluster]

(* Are similar? *)

mtheorem ordinal1_th_6:
  "\<forall>B : number. \<forall>A : number. \<forall>C : epsilon-transitive \<bar> number. A in B \<and> B in C \<longrightarrow> A in C"
proof (standard,standard,standard,standard,elim conjE)
  fix A B
  assume [ty]: "A is number" "B is number"
  fix C
  assume [ty]: "C is epsilon-transitive \<bar> number"
  assume A1:"A in B" and A2:"B in C"
  have "B \<subseteq> C" using A2 ordinal1_def_2 by mauto
  thus "A in C" using A1 tarski_def_3 by mauto
qed mauto

mtheorem ordinal1_th_7:
  "\<forall>x : epsilon-transitive \<bar> number. \<forall>A : Ordinal. x \<subset> A \<longrightarrow> x in A"
proof (standard,standard,standard)
  fix x
  assume [ty]: "x is epsilon-transitive \<bar> set"
  fix A
  assume [ty]: "A is Ordinal"
  let ?a = "the Element-of (A \\ x)"
  assume A1:"x \<subset> A"
  hence A2:"x \<subseteq> A" using xboole_0_def_8 by mauto
  have B2: "x \<noteq> A" using A1 xboole_0_def_8 by auto
  hence "not A c= x" using A2 xboole_0_def_10 by auto
  hence "ex y be object st y in A\\ x" using tarski_def_3 xboole_0_def_5 by auto
  hence "A \\ x \<noteq> {}" using xboole_0_def_1 by mauto
  hence "?a in A \\ x" using Element(4) by mauto
  then obtain y where [ty]: "y is number" and
A3: "y in A \\ x" and
A4: "not (ex a being object st a in A \\ x \<and> a in y)" using tarski_th_3[of ?a "A\\x"] by mauto
  have A5:"y in A" "\<not> y in x" using A3 xboole_0_def_5 by mauto
  {
    fix a
    assume "a in x"
    then obtain z where
    [ty]:"z be set" and
A6: "z = a" and
A7: "z in x" using all_set by auto
    have W1:  "z in A" using A2 A7 tarski_def_3a all_set by auto
    hence W3: "z in y \<or> z=y \<or> y in z" using A5 ordinal1_def_3E[of A] by auto
    have W2: "z \<noteq> y" using A5 A7 prefix_in_irreflexive by auto
    have A8: "z c= x" using A7 ordinal1_def_2 by mauto
    hence "\<not> y in z" using xboole_0_def_5 A3 tarski_def_3a all_set by auto
    hence "a in y" using W3 W2 A6 by auto
  }
  hence A8:"x \<subseteq> y" by (intro tarski_def_3b[of x y]) mauto
  have A9:"y \<subseteq> A" using A3 ordinal1_def_2E[of A y] xboole_0_def_5 by mauto
  {
    fix a
    assume [ty]: "a is Number"
    assume A10:"a in y"
    hence "\<not> a in A \\ x" using A4 by mauto
    hence "a in x" using A9 A10 xboole_0_def_5 tarski_def_3 by mauto
  }
  hence A11:"y \<subseteq> x" using tarski_def_3 by mauto
  thus "x in A" using A5 A8 xboole_0_def_10 by mauto
qed mauto


mtheorem ordinal1_th_8:
  "\<forall>A : epsilon-transitive \<bar> number. \<forall>C : Ordinal. \<forall>B : Ordinal. A \<subseteq> B \<and> B in C \<longrightarrow> A in C"
proof (standard,standard,standard,standard,elim conjE)
  fix A
  assume [ty]: "A is epsilon-transitive \<bar> number"
  fix B C
  assume [ty]: "B is Ordinal" "C is Ordinal"
  assume A1:"A \<subseteq> B" and A2:"B in C"
  have "B \<subseteq> C" using A2 ordinal1_def_2[of C] by mauto
  hence A3:"A \<subseteq> C" using A1 tarski_def_3 by mauto
  have "A \<noteq> C" using A1 A2 ordinal1_th_1 by mauto
  hence "A \<subset> C" using A3 xboole_0_def_8 by mauto
  thus "A in C" using ordinal1_th_7 by mauto
qed mauto


mtheorem xreagular_th_7:
  "for X1,X2,X3 be set holds
      \<not> (X1 in X2 \<and> X2 in X3 \<and> X3 in X1)"
proof (intro ballI notI impI)
  fix a b c
  assume T0[ty]:"a be set" "b be set" "c be set"
  assume A1:"a in b \<and> b in c \<and> c in a"
  let ?X = "{ a , b, c }"
  have "a in ?X" using enumset1_def_1 by mauto
  then obtain Y where
  T1[ty]: "Y be set" and A4:"Y in ?X \<and> \<not>(\<exists>z:object. z in ?X \<and> z in Y)"
    using tarski_th_3[of a ?X] by mauto
  have "Y=a \<or> Y=b\<or> Y=c " using A4 enumset1_def_1 by auto
  then show False using A1 A4 enumset1_def_1 by mauto
qed simp_all



mtheorem ordinal1_th_9:
  "a in A \<longrightarrow> a is Ordinal"
proof
  assume
A1: "a in A"
  have [ty]: "a is set" using tarski_0_1 by auto
  have A2: "a c= A " using ordinal1_def_2E A1 by auto
      {
    fix y assume [ty]: "y be set"
    assume
A3: "y in a"
    then have
A4: "y c= A" using A2 ordinal1_def_2E[of A y] tarski_def_3a by mauto
    assume "not y c= a"
    then obtain b where
A5: "b in y \<and> \<not> b in a" using tarski_def_3 by auto
    have "b in y \\ a" using A5 xboole_0_def_5 by auto
    then obtain z where
A6: "z in y \\ a" and
    "not (ex c being object st c in y \\ a \<and> c in z)" using tarski_th_3[of b "y\\a"] by mauto
    have A7: "z in y" "not z in a" using A6 xboole_0_def_5 by auto
    hence "z in A" using A4 tarski_def_3a by mauto
    then have W1: " (z = a) \<or> (a in z)" using A1 A4 A7 ordinal1_def_3E[of A z a] all_set by mauto
    have W2: "z = a \<Longrightarrow> False" using prefix_in_asymmetry[of y z] A7 A3 by auto
    have "a in z \<Longrightarrow>  False" using A3 A7 xreagular_th_7[of y a z] all_set by mauto
    hence False using W1 W2 by auto
  }
  then have
A7: "a is epsilon-transitive" using ordinal1_def_2I[of a] all_set by auto
  have "for y,z st y in a \<and> z in a holds y in z \<or> y = z \<or> z in y" using A2 ordinal1_def_3 tarski_def_3 by mauto
  hence "a is epsilon-connected" using ordinal1_def_3I by auto
  thus "a is Ordinal" using A7 ordinal1_def_4I by auto
qed

text_raw {*\DefineSnippet{ordinal1_th_10}{*}
mtheorem ordinal1_th_10:
  "\<not>A in B \<and> A \<noteq> B \<longrightarrow> B in A"
text_raw {*}%EndSnippet*}
proof(auto)
  assume
A1: "not A in B" and
A2: "A \<noteq> B"
  have "not A \<subset> B" using A1 ordinal1_th_7 by auto
  hence "not A c= B" using A2 xboole_0_def_8 by auto
  then obtain a where
A3: "a in A \<and> \<not> a in B" using tarski_def_3 by auto
  have "a in A \\ B" using A3 xboole_0_def_5 by auto
  then obtain X where
    [ty]: "X be set" and
A4: "X in A \\ B" and
A5: "not (ex a being object st a in A \\ B \<and> a in X)" using tarski_th_3[ of a "A\\B"] by mauto
have A6: "X c= A" using A4 ordinal1_def_2E xboole_0_def_5 by auto
  {
    fix b
    assume
A7: "b in X"
    hence "not b in A \\ B" using A5 by auto
    hence "b in B" using A6 A7 xboole_0_def_5 tarski_def_3 by mauto
  }
  hence "X c= B" using tarski_def_3 by auto
  then have
A8: "X c< B \<or> X = B" using xboole_0_def_8 by auto
   have"   B is ordinal" by auto
  have A9: "X in A" using A4 xboole_0_def_5 by auto
  hence "not X in B" and [ty]:"X is Ordinal" using A4 ordinal1_th_9[of A X]  xboole_0_def_5 by auto
  thus "B in A" using A8 ordinal1_th_7[of X B] A4 xboole_0_def_5 by mauto
qed

theorem ordinal1_def_5[simplified,rule_format]:
  "let A be Ordinal \<and> B be Ordinal
   redefine pred A c= B means
     for C be Ordinal st C in A holds C in B"
proof (rule iffI3)
  fix A B
  assume [ty]: "A is Ordinal \<and> B is Ordinal"
  show "A c= B \<longrightarrow>  (for C be Ordinal st C in A holds C in B)" using tarski_def_3 by auto
  assume A1:"for C be Ordinal st C in A holds C in B"
  show "A c= B"
    proof (intro tarski_def_3b)
      fix C
      assume A2:"C in A"
      hence [ty]:"C be Ordinal" using ordinal1_th_9[of A C]  by mauto
      show "C in B" using A1 A2 by mauto
    qed mauto
qed

lemmas ordinal1_def_5I = ordinal1_def_5[THEN iffD2,rule_format]
theorem ordinal1_def_5c:
  "A be Ordinal \<Longrightarrow> B be Ordinal \<Longrightarrow> \<not> A c= B \<longrightarrow> B c= A"
proof
  assume T[ty]: "A be Ordinal" "B be Ordinal"
  assume A1: "not A c= B"
  show "B c= A"
  proof(intro tarski_def_3b)
    obtain C where
       A2: "C in A \<and> \<not> C in B" using A1 tarski_def_3 by auto
    hence [ty]:"C is Ordinal" using A2(1) ordinal1_th_9[of A] by auto
    fix D assume A3: "D in B"
    hence [ty]: "D is Ordinal" using ordinal1_th_9[of B] by mty auto
    have "A in B \<or> B in A" using ordinal1_th_10[of A B] A1 xboole_0_def_10[of A B] by mauto
    hence "B in A" using ordinal1_th_6[of A] A2 by mauto (*szkoda ze mauto tego nie lapie bez instancji*)
    thus "D in A" using ordinal1_th_6[of B] A3 by mauto
  qed mauto
qed

lemma [intro?]: "x is a \<Longrightarrow> x is b \<Longrightarrow> x is a \<bar> b" by simp

mtheorem ordinal1_th_13:
  "x is Ordinal \<Longrightarrow> (succ x) is Ordinal"
proof
  assume
A3[ty]:"x is Ordinal"
  have E: "(succ x) = x \<union> {x}" using ordinal1_def_1 by auto
  have "(succ x) is epsilon-transitive"
  proof
    fix y
    have A4:"y = x \<longrightarrow> y c= (succ x)" using
      xboole_1_th_7[of "x\<union>{x}" x] E by mauto
    have A5: "y in x \<longrightarrow> y c= (succ x)"
      proof
        assume B: "y in x"
        hence [ty]:"y is Ordinal" using ordinal1_th_9[of x] by mauto
        have
A6:     "y c= x" using ordinal1_def_2E[of x y] B by mauto
        have "x c= x \<union> { x }" using xboole_1_th_7 by mauto
        thus "y c=  succ x" using A6 xboole_1_th_1[of "succ x" x y] E by mty auto
      qed

      assume "y in succ x"
      hence "y in x \<or> y =x " using E xboole_0_def_3 tarski_def_1 by mauto
      thus "y c= succ x" using A5 A4 by auto
    qed mauto
  then have
A7: "(succ x) is epsilon-transitive" by auto
  {
    fix y z assume [ty]: "y be set" "z be set"
    assume
A8: "y in succ x" and
A9: "z in succ x"
   have A10: "z in x \<or> z = x" using A9 E xboole_0_def_3 tarski_def_1 by mauto
   have "y in x \<or> y = x" using A8 xboole_0_def_3 tarski_def_1 E by mauto
   hence "y in z \<or> y = z \<or> z in y" using A10 ordinal1_def_3E[of x] by mauto
  }
  hence "(succ x) is epsilon-connected" using ordinal1_def_3I by auto
  thus "(succ x) is ordinal" using A7 ordinal1_def_4 by auto
qed mauto

mlemma [ty_func_cluster]: "cluster succ A \<rightarrow> non empty \<bar> ordinal"
proof
    have "A in succ A" using ordinal1_th_2 by auto
    thus "(succ A) is non empty" using xboole_0_def_1 by auto
    show "(succ A) is ordinal" using ordinal1_th_13 by auto
qed


mtheorem ordinal1_th_15:"(\<forall>x : set. x in X \<longrightarrow> x is ordinal \<bar> set \<and> x \<subseteq> X) \<longrightarrow>
               X is epsilon-transitive \<bar> epsilon-connected"
proof (standard,standard)
  assume A1:"\<forall>x : set. x in X \<longrightarrow> x is ordinal \<bar> set \<and> x \<subseteq> X"
  show "X is epsilon-transitive" using A1 ordinal1_def_2 by mauto
  show "X is epsilon-connected"
  proof
    fix x assume [ty]:"x is set"
    fix y assume [ty]:"y is set"
    assume "x in X" "y in X"
    hence [ty]: "x is ordinal \<bar> set \<and> y is ordinal \<bar> set" using A1 by mauto
    thus "x in y \<or> x = y \<or> y in x" using ordinal1_th_10 by mauto
  qed mauto
qed

mtheorem ordinal1_th_16:
  "X \<subseteq> A \<and> X \<noteq> {} \<longrightarrow> (\<exists>C : Ordinal. C in X \<and> (\<forall>B : Ordinal. B in X \<longrightarrow> C \<subseteq> B))"
proof (intro impI, elim conjE)
  let ?a = "the Element-of X"
  assume A1:"X \<subseteq> A" and A2:"X \<noteq> {}"
  have "?a in X" using A2 Element_of_rule2 by mauto
  then obtain Y where [ty]:"Y is set" and
  A3:"Y in X" and
  A4:"\<not> (\<exists>a : object. a in X \<and> a in Y)" using tarski_th_3[of _ X] by mauto
  have "Y in A" using A1 A3 tarski_def_3a by mauto
  hence "Y is Ordinal" using ordinal1_th_9[of A Y] by mauto
  then obtain C where [ty]:"C is Ordinal" and
  A5:"C = Y" by mauto
  show "\<exists>C : Ordinal. C in X \<and> (\<forall>B : Ordinal. B in X \<longrightarrow> C \<subseteq> B)"
  proof (intro bexI[of _ _ C] conjI ballI impI)
    show "C in X" using A3 A5 by mauto
    fix B
    assume [ty]:"B is Ordinal"
    assume "B in X"
    hence "\<not> B in C" using A4 A5 by mauto
    hence "B = C \<or> C in B" using ordinal1_th_10 by mauto
    thus "C \<subseteq> B" using ordinal1_def_2E[of B C,simplified] tarski_def_3_reflexive by mauto
  qed mauto
qed


mtheorem ordinal1_th_17:
  "A in B \<longleftrightarrow> succ A \<subseteq> B"
proof(rule iffI3)
  show "A in B \<longrightarrow> succ A c= B"
  proof
    assume
A1: "A in B"
    hence "\<forall>a : object.  a in { A } \<longrightarrow> a in B" using tarski_def_1 by auto
    hence
A2: "{ A } c= B" using tarski_def_3 by mauto
    have "A c= B" using A1 ordinal1_def_2 by mauto
    thus "succ A c= B" using A2 xboole_1_th_8[of "{A}" B A] ordinal1_def_1 by mauto
  qed
  assume
A3: "succ A c= B"
  have "A in succ A" using ordinal1_th_2 by mauto
  thus "A in B" using A3 tarski_def_3 by mauto
qed

theorem ordinal1_sch_1:
  assumes A1: "ex A st P(A)"
  shows "ex A st P(A) \<and> (\<forall>B. P(B) \<longrightarrow> A c= B)"
proof -
  obtain A where [ty]: "A is Ordinal" and
  A2: "P(A)" using A1 by mauto
  let ?R = "\<lambda>x. ex B st x = B \<and> P(B)"
  obtain X where [ty]: "X is set" and
  A3: "for x being object holds x in X \<longleftrightarrow> x in succ A \<and> ?R(x)"
    using xboole_0_sch_1[of "succ A" ?R] by mauto
  hence "\<forall>a : object.  a in X \<longrightarrow> a in succ A" by mauto
  hence A4: "X c= succ A" by (intro tarski_def_3[THEN iffD2]) mauto
  have [ty]: "(succ A) is ordinal" by mauto
  have "A in succ A" using ordinal1_th_2 by mauto
  hence "X \<noteq> {}" using A2 A3[THEN bspec,of A] xb1 by mauto
  then obtain C where [ty]: "C is ordinal" "C is set" and
  A5: "C in X" and
  A6: "for B st B in X holds C c= B" using ordinal1_th_16[of _ X,OF _ _ A4,simplified] by mauto
  have [ty]: "C is number" using ordinal1_def_4 by simp
  have "C in succ A" using A3 A5 by mauto
  hence A7: "C c= succ A" by (intro ordinal1_def_2E) mauto
  show ?thesis
  proof (intro bexI[of _ _ C] conjI ballI impI)
    have "ex B st C = B \<and> P(B)" using A3 A5 by mauto
    thus "P(C)" by mauto
    fix B assume [ty]: "B is Ordinal"
    assume A8: "P(B)"
    show "C c= B" proof (rule ccontr)
      assume A9: "\<not>C c= B"
      hence " B c= C" " B\<noteq>C" using ordinal1_def_5c xboole_0_def_10 by auto
      hence "B c< C" using xboole_0_def_8 by auto
      hence "B in C" using ordinal1_th_7 by mauto
      hence "B in X" unfolding A3[THEN bspec,of B,simplified] using A8 tarski_def_3a[OF _ _ A7,of B] by mauto
      thus False using A6 A9 by mauto
    qed
  qed mauto
qed

  (*::$N Transfinite induction*)
theorem ordinal1_sch_2:
  assumes A1:"for A st for C st C in A holds P(C) holds P(A)"
  shows "\<forall>A. P(A)"
proof
  let ?R = "\<lambda> x. ex B st x=B \<and> P(B)"
  fix A assume [ty]:"A is Ordinal"
  let ?Y = "succ A"
  obtain Z where
    [ty]:"Z be set" and
A2: "for x being object holds x in Z \<longleftrightarrow> x in ?Y \<and> ?R(x)" using xboole_0_sch_1[of ?Y ?R] by mauto
   have "?Y be Ordinal" by mauto
  have "?Y \\ Z \<noteq> {} \<longrightarrow> False"
   proof
    have B1:"?Y \\ Z \<subseteq> ?Y" using tarski_def_3 xboole_0_def_5 by mauto
    assume "?Y \\ Z \<noteq> {}"
    then obtain C where
    [ty]:"C be Ordinal" and
A3: "C in ?Y \\ Z" and
A4: "for B st B in ?Y \\ Z holds C c= B" using ordinal1_th_16[of ?Y "?Y \\ Z"] B1 by mauto
    have "for B st B in C holds P(B)"
      proof(standard,standard)
         fix B assume [ty]:"B be Ordinal" and
A5:   "B in C"
      have "C in ?Y" using A3 B1 tarski_def_3a by mauto
      hence
A6:   "C c= ?Y" using ordinal1_def_2 by mauto
      have "not B in Z \<longrightarrow> False"
      proof
        assume "not B in Z"
        then have "B in ?Y \\ Z" using A5 A6 xboole_0_def_5 tarski_def_3a[OF _ _ A6] by mauto
        then have
A7:     "C c= B" using A4 by mauto
        have "C \<noteq> B" using A5 prefix_in_irreflexive by mauto
        hence "C \<subset> B" using A7 xboole_0_def_8 by auto
        thus False using A5 ordinal1_th_7 prefix_in_asymmetry[of C B] by mauto
      qed
      then have "ex B9 being Ordinal st B = B9 \<and> P(B9)" using A2 by auto
      thus "P(B)" by auto
    qed mauto
    hence
A8: "P(C)" using A1 by auto
    have A9: "not C in Z" using A3 xboole_0_def_5 by mauto
    hence "C in succ A" using A3 xboole_0_def_5 by mauto
    thus False using A2 A8 A9 by auto
  qed mauto
  hence "?Y\\Z = {}" by auto
  hence "not A in ?Y \<or> A in Z" using xboole_0_def_5 xboole_0_def_1 by mauto
  hence "ex B st A = B \<and> P(B)" using A2 ordinal1_th_2 by auto
  thus "P(A)" by auto
qed mauto

mtheorem ordinal1_th_24:"\<forall>A : Ordinal. A is limit_ordinal \<longleftrightarrow> (\<forall>C : ordinal \<bar> set. C in A \<longrightarrow> succ C in A)"
proof (standard,standard)
  fix A assume [ty]:"A is Ordinal"
  show "A is limit_ordinal \<Longrightarrow> (\<forall>C : Ordinal. C in A \<longrightarrow> succ C in A)"
  proof (standard, standard)
    assume "A is limit_ordinal"
    hence A1:"A = union A" using ordinal1_def_6E by mauto
    fix C assume [ty]:"C is Ordinal"
    assume "C in A"
    then obtain z where [ty]:"z is set" and
    A2:"C in z" and
    A3:"z in A" using A1 tarski_def_4[of A C] by mauto
    have "\<forall>b : object. b in {C} \<longrightarrow> b in z" using A2 tarski_def_1 by mauto
    hence A4:"{C} \<subseteq> z" using tarski_def_3b by mauto
    have A5[ty]:"z is Ordinal" using ordinal1_th_9[OF _ _ A3] by auto
    hence "C \<subseteq> z" using A2 ordinal1_def_2E[OF _ _ _ A2] by mauto
    hence "succ C \<subseteq> z" using xboole_1_th_8[OF _ _ _ _ A4,of C] ordinal1_def_1 by mauto
    hence "succ C = z \<or> succ C \<subset> z" using xboole_0_def_8b by mauto
    hence A6:"succ C = z \<or> succ C in z" using A5 ordinal1_th_7 by mauto
    have "z \<subseteq> A" using A3 ordinal1_def_2 by mauto
    thus "succ C in A" using A3 A6 ordinal1_th_6[of _ "succ C" A] by mauto
  qed mauto
  assume A7:"\<forall>C : Ordinal. C in A \<longrightarrow> succ C in A"
  {
    fix a
    have [ty]:"a is set" using tarski_0_1 by mauto
    assume A8:"a in A"
    have "a is ordinal \<bar> set" using ordinal1_th_9[OF _ _ A8] by auto
    hence A9:"succ a in A" using A7 A8 by mauto
    have "a in succ a" using ordinal1_th_2 by mauto
    hence "a in union A" using A9 tarski_def_4[THEN iffD2,of A a,OF _ bexI] by mauto
  }
  hence A10:"A \<subseteq> union A" using tarski_def_3b by mauto
  {
    fix a
    assume "a in union A"
    then obtain z where [ty]:"z is set" and
    A11:"a in z" and
    A12:"z in A" using tarski_def_4 by mauto
    have "z \<subseteq> A" using A12 ordinal1_def_2 by mauto
    hence "a in A" using A11 tarski_def_3a by mauto
  }
  hence "union A \<subseteq> A" using tarski_def_3b by mauto
  hence "A = union A" using A10 xboole_0_def_10 by mauto
  thus "A is limit_ordinal" using ordinal1_def_6I by mauto
qed mauto

text_raw {*\DefineSnippet{ordinal1_th_24A}{*}
mtheorem ordinal1_th_24A:
  "\<forall>A : Ordinal. 
     A is limit_ordinal \<longleftrightarrow> (for C be set st C in A holds succ C in A)"
text_raw {*}%EndSnippet*}
proof(standard, rule iffI3)
  fix A assume [ty]:"A is Ordinal"
  show "A is limit_ordinal \<longrightarrow> (for C be set st C in A holds succ C in A)"
  proof(standard,standard,standard)
    fix C
    assume A1: "A is limit_ordinal" and [ty]: "C is set" and A2: "C in A"
    hence "C is Ordinal" using ordinal1_th_9[of A] by mty auto
    thus "succ C in A" using A1 A2 ordinal1_th_24[of A,THEN iffD1] by mauto
  qed mauto
  assume "for C be set st C in A holds succ C in A"
  thus "A is limit_ordinal" using ordinal1_th_24 by auto
qed mauto



mtheorem ordinal1_th_29:
  "not (A is limit_ordinal) \<longleftrightarrow> (ex B st A = succ B)"
proof(rule iffI3)
  show "not A is limit_ordinal \<longrightarrow> (ex B st A = succ B)"
  proof
    assume "not A is limit_ordinal"
    then obtain B where
      T[ty]:"B be Ordinal" and
A1: "B in A" and
A2: "not succ B in A" using ordinal1_th_24 by auto
    show "ex B st A=succ B"
      proof(intro bexI[of _ _ B])
        have "A\<noteq>succ B \<longrightarrow> False"
          proof
            assume
A3:           "A \<noteq> succ B"
            have "succ B \<subseteq> A" using A1 ordinal1_th_17 by auto
            hence "succ B \<subset> A" using A3 xboole_0_def_8 by mauto
            thus False using A2 ordinal1_th_7 by mauto
          qed
         thus "A=succ B" by auto
       qed mauto
     qed
  assume "ex B st A=succ B"
  then obtain B where
    [ty]: "B be Ordinal" and
    A4: "A = succ B" by auto
  have "B in A \<and> \<not> succ B in A" using A4 ordinal1_th_2 prefix_in_irreflexive by mauto
  thus "not (A is limit_ordinal)" using ordinal1_th_24 by mauto
qed

func ordinal1_def_9 ("On _") where
  "func On X \<rightarrow> set means
     (\<lambda>it. for x being object holds x in it \<longleftrightarrow> x in X \<and> x is Ordinal)"
proof -
  show "\<exists>x : set. \<forall>xa : object. xa in x \<longleftrightarrow> xa in X \<and> xa is ordinal \<bar> set"
    using xboole_0_sch_1 by mauto
  show "\<And>x y. x is set \<Longrightarrow>
           y is set \<Longrightarrow>
           \<forall>xa : object. xa in x \<longleftrightarrow> xa in X \<and> xa is ordinal \<bar> set \<Longrightarrow>
           \<forall>x : object. x in y \<longleftrightarrow> x in X \<and> x is ordinal \<bar> set \<Longrightarrow> x = y"
    by (intro xboole_0_sch_2[of _ _ "\<lambda>xa. xa in X \<and> xa is Ordinal"]) mauto
qed mauto

text_raw {*\DefineSnippet{ordinal1_th_32}{*}
mtheorem ordinal1_th_32:
  "\<forall>D : Ordinal.  ex A be Ordinal st D in A \<and> A is limit_ordinal"
text_raw {*}%EndSnippet*}

proof
  fix D
  assume [ty]: "D is Ordinal"
  obtain Field where [ty]:"Field is set" and
  A1:"D in Field" and
  A2:"\<forall>X : set. \<forall>Y : set. X in Field \<and> Y \<subseteq> X \<longrightarrow> Y in Field" and
  A3:"\<forall>X : set. X in Field \<longrightarrow> bool X in Field"
  "\<forall>X : set. X \<subseteq> Field \<longrightarrow> X,Field areequipotent \<or> X in Field"
    using zfmisc_1_th_112[of D,OF ty(4),THEN bexE,OF set_exists,of thesis] by blast
  have C: "\<forall>X : set. (X in On Field) \<longrightarrow> X is Ordinal \<and> X \<subseteq> On Field"
  proof (standard,standard,standard)
    fix X
    assume [ty]:"X is set"
    let ?A = X
    assume A4:"X in On Field"
    hence [ty]:"?A is Ordinal" using ordinal1_def_9 by mauto
    have A5:"?A in Field" using A4 ordinal1_def_9 by mauto
    show "X is Ordinal" using A4 ordinal1_def_9 by mauto
    show "X \<subseteq> On Field"
    proof
      fix y
      assume A6:"y in X"
      have B: "y in ?A" using A6 by mauto
      let ?B = y
      have [ty]:"?B is Ordinal" using ordinal1_th_9[OF _ _ B] by mauto
      have "?B \<subseteq> ?A" using A6 ordinal1_def_2 by mauto
      hence "?B in Field" using A2[THEN bspec,THEN bspec,of X _] A5 by mauto
      thus "y in On Field" using ordinal1_def_9 by mauto
    qed mauto
  qed mauto
  let ?ON = "On Field"
  show "\<exists>A : ordinal \<bar> set. D in A \<and> A is limit_ordinal"
  proof (intro bexI[of _ _ ?ON] conjI)
    have [ty]:"?ON is epsilon-transitive \<bar> epsilon-connected \<bar> set" using C ordinal1_th_15 by mauto
    show "D in ?ON" using A1 ordinal1_def_9 by mauto
    have "\<forall>A : ordinal \<bar> set. A in ?ON \<longrightarrow> succ A in ?ON"
    proof (standard,standard)
      fix A assume [ty]: "A is Ordinal"
      have A7:"succ A \<subseteq> bool A"
      proof
        fix x
        have [ty]:"x is set" using tarski_0_1 by mauto
        assume "x in succ A"
        hence "x in A \<or> x = A" using ordinal1_th_4 by mauto
        hence "x \<subseteq> A" using ordinal1_def_2 tarski_def_3_reflexive by mauto
        thus "x in bool A" using zfmisc_1_def_1 by mauto
      qed mauto
      assume "A in ?ON"
      hence "A in Field" using ordinal1_def_9 by mauto
      hence "bool A in Field" using A3 by mauto
      hence "succ A in Field" using A2[THEN bspec,THEN bspec,of _ "succ A"] A7 by mauto
      thus "succ A in ?ON" by (intro ordinal1_def_9[THEN iffD2]) mauto
    qed mauto
    thus "?ON is limit_ordinal" using ordinal1_th_24 by mauto
    thus "?ON is Ordinal" by simp
  qed mauto
qed mauto

func ordinal1_def_11 ("omega") where
  "func omega \<rightarrow> set means (\<lambda>it.
  {} in it \<and> it is limit_ordinal \<and> it is
  ordinal \<and> (for A st {} in A \<and> A is limit_ordinal holds it c= A))"
proof -
  have A: "{} is ordinal" using Lm1 by (intro ordinal1_def_4I) mauto
  show "\<exists>A : set. {} in A \<and>
              A is limit_ordinal \<and>
              A is ordinal \<and> (\<forall>B : ordinal \<bar> set. {} in B \<and> B is limit_ordinal \<longrightarrow> A \<subseteq> B)"
    using ordinal1_sch_1[OF ordinal1_th_32,OF A] by mauto
  show "\<And>x y. x is set \<Longrightarrow> y is set \<Longrightarrow>
       {} in x \<and> x is limit_ordinal \<and>
       x is ordinal \<and> (\<forall>A : ordinal \<bar> set. {} in A \<and> A is limit_ordinal \<longrightarrow> x \<subseteq> A) \<Longrightarrow>
       {} in y \<and> y is limit_ordinal \<and>
       y is ordinal \<and> (\<forall>A : ordinal \<bar> set. {} in A \<and> A is limit_ordinal \<longrightarrow> y \<subseteq> A) \<Longrightarrow> x = y"
    proof (elim conjE)
      fix x y
      assume [ty]: "x is set" "y is set" "x is limit_ordinal" "y is limit_ordinal" "x is ordinal" "y is ordinal"
      assume E: "{} in x" "{} in y"
      assume U: "\<forall>A : ordinal \<bar> set. {} in A \<and> A is limit_ordinal \<longrightarrow> x \<subseteq> A"
                "\<forall>A : ordinal \<bar> set. {} in A \<and> A is limit_ordinal \<longrightarrow> y \<subseteq> A"
      have "x c= y \<and> y c= x" using U(1)[THEN bspec,of y,simplified] U(2)[THEN bspec,of x,simplified] E by mauto
      thus "x = y" using xboole_0_def_10a by mauto
    qed
qed mauto

theorem [ty_func_cluster]:
   "cluster omega \<rightarrow> ordinal" using ordinal1_def_11 by mauto

attr ordinal1_def_12 ("natural")
  "attr natural for object means (\<lambda>A. A in omega)"

theorem [ty_func_cluster]:
   "cluster omega \<rightarrow> non empty" using ordinal1_def_11 xboole_0_def_1 by mauto


abbreviation (input) "NAT \<equiv> omega"

abbreviation "Nat \<equiv> natural \<bar> set"

lemma nat_0[ty_func]: "{} is Nat"
  using ordinal1_def_11 ordinal1_def_12I xboole_0_def_2_ty by simp

lemma Element_of_NAT:"x is natural \<Longrightarrow> x is Element-of NAT"
proof-
  assume "x is natural"
  hence "x in NAT" using ordinal1_def_12 by auto
  thus "x is Element-of NAT" using Element_of_rule3 by mauto
qed

lemma natural[ty_cond_cluster]: "x is Element-of NAT \<Longrightarrow> x is natural"
proof-
  have N: "NAT \<noteq> {}" using xb ordinal1_def_11 by mauto
  assume "x is Element-of NAT"
  hence "x in NAT" using N Element_of_rule2[of NAT x] by mauto
  thus "x is natural" using ordinal1_def_12 by mauto
qed



theorem [ex]:
  "cluster natural for set"
proof
  show "{} is Nat" using nat_0 by auto
qed

theorem [ty_cond_cluster]:
  "cluster natural \<rightarrow> ordinal for Number"
proof-
  fix x assume "x be natural"
  hence "x in omega" using ordinal1_def_12 by auto
  thus "x is ordinal" using ordinal1_th_9[of omega] by mty simp
qed

lemma "sethood(Nat)"
  unfolding sethood
  using ordinal1_def_12 all_set by (intro bexI[of _ _ omega]) mauto

attr ordinal1_def_16 ("with'_zero")
  "attr with_zero for set means (\<lambda>IT. {} in IT)"

theorem with_zero_cl[ty_parent]:
  "cluster with_zero \<rightarrow> non empty for set"
proof-
  fix X assume [ty]: "X be set" "X is with_zero"
  have "{} in X" using ordinal1_def_16 by mauto
  thus "X is non empty" using xboole_0_def_1 by auto
qed

theorem [ex]:
  "cluster with_zero for set"
proof
  show "{{}} is with_zero\<bar>set" using ordinal1_def_16 tarski_def_1 by mauto
qed

text_raw {*\DefineSnippet{ordinal2_sch_1}{*}
theorem ordinal2_sch_1:
  assumes A1: "P({})"
      and A2: "\<forall>A:Ordinal. P(A) \<longrightarrow> P(succ A)"
      and A3: "\<forall>A:Ordinal. A \<noteq> {} \<and> A be limit_ordinal \<and>
                 (\<forall>B:Ordinal. B in A \<longrightarrow> P(B)) \<longrightarrow> P(A)"
  shows "\<forall>A:Ordinal.  P(A)"
text_raw {*}%EndSnippet*}
proof-
have A4: "for A st for B st B in A holds P(B) holds P(A)"
  proof(standard,standard)
    fix A assume [ty]:"A be Ordinal" and
   A5: "for B st B in A holds P(B)"
    show "P(A)"
    proof(cases "A={}" )
      case True thus "P(A)" using A1 by auto
    next
      case C1: False
         show "P(A)"
         proof(cases "(\<forall>B.  A \<noteq> succ B)")
           case True
              hence "A is limit_ordinal" using ordinal1_th_29[of A] by auto
              thus "P(A)" using C1 A3 A5 by auto
           next
           case C2:False
              then obtain B where
              [ty]: "B is Ordinal" and
              A7:   "A = succ B" by auto
              have "B in A" using A7 ordinal1_def_1[of B] xboole_0_def_3 tarski_def_1 by mauto
              thus "P(A)" using A2 A5 A7 by mauto
         qed
       qed
 qed mauto
 thus "\<forall>A.  P(A)" using ordinal1_sch_2 by simp
qed


text_raw {*\DefineSnippet{OmegaInd}{*}
theorem ordinal_2_sch_19:
  assumes [ty]: "a be Nat"
    and A1: "P({})"
    and A2: "\<forall>n : Nat. P(n) \<longrightarrow> P(succ n)"
  shows "P(a)"
text_raw {*}%EndSnippet*}
proof-
  have [ty]:"a is set" using all_set by auto
  let ?P= "\<lambda>x . x is natural \<longrightarrow> P(x)"
  have
A3:"for A st ?P(A) holds ?P(succ A)"
  proof(standard,standard)
    fix A assume [ty]:"A be Ordinal" and
A4: "?P(A)"
    show "?P(succ A)"
    proof
      have "omega is set" by mauto
         assume "(succ A) is natural"
      hence
A5:     "(succ A) in omega" using ordinal1_def_12 by auto
       have B1: "A in succ A" using xboole_0_def_3 tarski_def_1 ordinal1_def_1[of A] by mauto
       hence "A in omega" using A5 prefix_in_asymmetry[of A "succ A"] A5 ordinal1_th_6[of "succ A" A omega] by mauto
      thus "P(succ A)" using A2 A4 ordinal1_def_12[of A] by auto
    qed
  qed mauto
  have
A6: "for A st A \<noteq> {} \<and> A is limit_ordinal \<and> (for B st B in A holds ?P(B))
           holds ?P(A)"
  proof(intro ballI, rule impI)
    fix A
    assume
    [ty]: "A is Ordinal" and
     A7:"A \<noteq> {} \<and> A is limit_ordinal \<and> (for B st B in A holds ?P(B))"
    have "{} c= A" using tarski_def_3b xb by mauto
    hence "{} \<subset> A" using A7 xboole_0_def_8 by mauto
    hence
A8: "{} in A" using ordinal1_th_7[of "{}" A] Lm1 by mauto
    have
A9: "not A in A" using prefix_in_irreflexive by auto
    have "omega c= A" using A8 A7 ordinal1_def_11 by auto
    hence "not A in omega" using A9 tarski_def_3a[of omega A] by mauto
    thus "?P(A)" using ordinal1_def_12 by auto
  qed mauto
  have A10: "?P({})" using A1 by auto
   have "a is Ordinal" using ty by mauto
 have "\<forall>A.  ?P(A)" using ordinal2_sch_1[of ?P, OF A10 A3 A6] by auto
 thus "P(a)" by mauto
qed

end
