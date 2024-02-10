\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory mizar_fraenkel
  imports "../mml/tarski"
begin

text_raw \<open>*\DefineSnippet{fraenkel_a1}{\<close>
definition Fraenkel1 where
   "func Fraenkel1 (F, D, P) \<rightarrow> set means \<lambda>it.
      \<forall>x : object. x in it \<longleftrightarrow> (\<exists>y : D. x = F(y) \<and> P(y))"
text_raw \<open>}%EndSnippet\<close>

syntax
  "_Fraenkel1" :: "Set \<Rightarrow> vs \<Rightarrow> Ty \<Rightarrow> o \<Rightarrow> Set" ("{ _ where _ be _ : _ }")
translations
 "{ f where x be D : P }" \<rightharpoonup> "CONST mizar_fraenkel.Fraenkel1((%x. f), D, (%x. P))"
 "mizar_fraenkel.Fraenkel1((%x. f), D, (%y. P))" \<rightharpoonup> "{ (%x. f)(y) where y be D : P }"

text_raw \<open>*\DefineSnippet{fraenkel_a1s}{\<close>
lemma Fraenkel_A1:
  fixes F :: "Set \<Rightarrow> Set" and P :: "Set \<Rightarrow> o"
  assumes [ex]:"inhabited(L)" "sethood(L)"
  shows "Fraenkel1(F, L, P) be set \<and>
    (\<forall>x : object. x in Fraenkel1(F, L, P) \<longleftrightarrow> (\<exists>y : L. x = F(y) \<and> P(y))) \<and>
    (x be set \<and> (\<forall>xa : object. xa in x \<longleftrightarrow> (\<exists>y : L. xa = F(y) \<and> P(y)))
                                \<longrightarrow> x = Fraenkel1(F, L, P))"
text_raw \<open>}%EndSnippet\<close>
proof (rule means_property[OF Fraenkel1_def])
text_raw \<open>*\DefineSnippet{fraenkel_a1p}{\<close>
  show "\<exists>x : set. \<forall>xa : object. xa in x \<longleftrightarrow> (\<exists>y : L. xa = F(y) \<and> P(y))"
text_raw \<open>}%EndSnippet\<close>
  proof -
    obtain Seth where SetH[ty]: "Seth be set" and
      Prop: "\<forall>x:object. x be L \<longleftrightarrow> x in Seth"
      using sethood assms by auto
    let ?R1 = "\<lambda>x y. x=y \<and> P(x)"
    have A1: "\<forall>x,y,z:object. ?R1 (x,y) \<and> ?R1 (x,z) \<longrightarrow> y = z" by simp
    obtain Sep where A2[ty]: "Sep be set" and
      A3:"\<forall>x:object. x in Sep \<longleftrightarrow> (\<exists>y:object. y in Seth \<and> ?R1 (y,x))"
      using tarski_sch_1[OF SetH A1] by auto
    let ?R = "\<lambda>x y. y = F (x)"
    have A4: "\<forall>x,y,z:object . ?R (x,y) \<and> ?R (x,z) \<longrightarrow> y = z" by simp
    obtain C where [ty]:"C be set" and
      A5: "\<forall>x:object. x in C \<longleftrightarrow>
        (\<exists> y: object. y in Sep \<and> ?R (y,x))"
        using tarski_sch_1[OF A2 A4] by auto
    show "\<exists>IT:set. \<forall>x:object. x in IT \<longleftrightarrow> (\<exists>y:L. x = F(y) \<and> P(y))"
    proof (intro bexI[of _ _ "C"],auto)
      fix x assume "x in C"
      then obtain y where "y be object" and
        "y in Sep \<and> ?R (y,x)" using A5 by auto
      thus "\<exists>\<^sub>L y . y is L \<and> (x = F (y)  \<and> P (y) )"
        using Prop A3 A5 by auto
    next
      show "\<And>y. y is L \<Longrightarrow> P(y) \<Longrightarrow> F(y) in C" using Prop A5 A3 by auto
    qed
  qed
next
  fix IT1 IT2
  assume B1: "IT1 be set" "IT2 be set" and
    B2: "\<forall>x:object. x in IT1 \<longleftrightarrow> (\<exists>y:L. x = F(y) \<and> P(y))" and
    B3: "\<forall>x:object. x in IT2 \<longleftrightarrow> (\<exists>y:L. x = F(y) \<and> P(y)) "
  hence "\<forall>x:object. x in IT1 \<longleftrightarrow>x in IT2" by simp
  thus "IT1=IT2" using B1 tarski_th_2 by auto
qed simp

lemmas Fraenkel_A1_ex =  Fraenkel_A1[THEN conjunct2,THEN conjunct1,THEN bspec,simplified,THEN iffD1]

lemma [ty_func]:  "Fraenkel1(P, L, Q)  be set" using all_set by auto

theorem Fraenkel_A1_in:
   "sethood(M) \<Longrightarrow> x be M \<Longrightarrow> Q(x) \<Longrightarrow> P(x) in {P(x) where x be M : Q(x)}"
proof-
  assume A:"sethood(M)" "x be M" "Q(x)"
  hence I:"inhabited(M)" using inhabited_def[of M]  by blast
    have "ex y be M st P(x) = P(y) \<and> Q(y)" using A I by auto
  thus "P(x) in {P(x) where x be M : Q(x)}" using Fraenkel_A1 A I
     by simp
 qed

abbreviation the_set_of_all
where "the_set_of_all (P, M) \<equiv> Fraenkel1(P, M, (\<lambda>x. True))"

syntax
  "_SetOfAll" :: "Set \<Rightarrow> vs \<Rightarrow> Ty \<Rightarrow> Set" ("the set-of-all _ where _ be _")
translations
 "the set-of-all f where x be D" \<rightleftharpoons> "CONST mizar_fraenkel.the_set_of_all((%x. f), D)"

term "the set-of-all {x} where x be set"

theorem Set_of_All_ex:
 "inhabited(M) \<Longrightarrow> sethood(M) \<Longrightarrow> x in the set-of-all P(x) where x be M \<Longrightarrow> ex y be M st x = P(y)"
proof-
  assume A1:"inhabited(M)" "sethood(M)" "x in the set-of-all P(x) where x be M"
  show "ex y be M st x = P(y)" using Fraenkel_A1_ex[OF A1] by auto
qed

theorem Set_of_All_in:
 "sethood(M) \<Longrightarrow> x be M \<Longrightarrow> P(x) in the set-of-all P(x) where x be M" using Fraenkel_A1_in by auto

end
