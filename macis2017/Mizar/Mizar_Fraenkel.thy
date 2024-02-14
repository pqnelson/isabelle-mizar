\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Mizar_Fraenkel
  imports "../MML/Tarski"
begin

  (* :: "(Set \<Rightarrow> Set) \<Rightarrow> Mode \<Rightarrow> (Set \<Rightarrow> o) \<Rightarrow> Set"  *)
text_raw \<open>\DefineSnippet{fraenkel_a1}{\<close>
definition Fraenkel1 where
   "func Fraenkel1 (F, D, P) \<rightarrow> set means \<lambda> it.
      for x being object holds
      x in it iff (ex y being D st x = F (y) & P (y))"
text_raw \<open>}%EndSnippet\<close>

syntax
  "_Fraenkel1" :: "Set \<Rightarrow> vs \<Rightarrow> Mode \<Rightarrow> o \<Rightarrow> Set" ("{ _ where _ be _ : _ }")
translations
 "{ f where x be D : P }" \<rightharpoonup> "CONST Mizar_Fraenkel.Fraenkel1((%x. f), D, (%x. P))"
 "Mizar_Fraenkel.Fraenkel1((%x. f), D, (%y. P))" \<rightharpoonup> "{ (%x. f)(y) where y be D : P }"

schematic_goal Fraenkel_A1:
  fixes P :: "Set \<Rightarrow> Set" and Q :: "Set => o"
  assumes "sethood-of L" shows "?X"
proof (induct rule :means_property[OF Fraenkel1_def,of L P Q, case_names existence uniqueness])
  case existence
      obtain X where 
        SetH: "X be set" and Prop: " for x being object holds (x be L iff x in X)" using sethood_def assms by auto 
      let ?QQ = "\<lambda>x y. x=y & Q(x)"
      have A1: "for x,y,z being object holds
          ?QQ (x,y) & ?QQ (x,z) implies y = z" by simp
      obtain XQ where
         A2:"XQ be set" and 
         A3:"for x being object holds x in XQ iff
                 (ex y being object st y in X & ?QQ (y,x))"
          using tarski_sch_1[OF SetH A1] by auto
      let ?R = "\<lambda>x y. y = P (x)"
      have A4: "for x,y,z being object holds
          ?R (x,y) & ?R (x,z) implies y = z" by simp
      obtain IT where
      A5:"IT be set" "for x being object holds (x in IT iff
         (ex y being object st y in XQ & ?R (y,x)))"
           using tarski_sch_1[OF A2 A4] by auto     
      show "ex IT being set st (for x being object holds (x in IT iff (ex y being L st (x = P (y)  & Q (y) ))))"
         proof (intro bexI[of _ "IT"] ballI)
            show "IT be set" using A5 by simp
            fix x
            assume "x be object"
            show "x in IT iff (ex y being L st (x = P (y) & Q (y)))"
              proof (intro iffI2)
                 show "x in IT implies (ex y being L st (x = P (y)  & Q (y) ))"
                    proof
                       assume "x in IT"
                       then obtain y where
                         "y be object" and A6: "y in XQ & ?R (y,x)" using A5 by auto
                       show "ex y being L st (x = P (y)  & Q (y) )"
                         proof (intro bexI[of _ "y"] conjI)
                           show "x = P (y)" using A6 by simp
                           obtain z where 
                               "z be object" and A7: "z in X & ?QQ (z,y)" using A3 A6 by auto
                           show "Q (y)"  "y be L" using A7 Prop by auto 
                         qed                        
                    qed
                 show "(ex y being L st (x = P (y)  & Q (y) )) implies x in IT"
                    proof
                      assume "ex y being L st (x = P (y) & Q (y))"
                      then obtain y where
                         A8: "y be L" and A9: "x = P (y)" and A10: "Q (y)" by auto
                      have "y in X" using Prop A8 by auto
                      hence "y in XQ" using A3 A10 by auto
                      thus "x in IT" using A5 A9 by auto
                    qed
              qed
         qed
    case uniqueness
    fix IT1 IT2
    assume B1: "IT1 be set" "IT2 be set" and
      B2: "for x being object holds (x in IT1 iff (ex y being L st (x = P (y) & Q (y))))" and 
      B3: "for x being object holds (x in IT2 iff (ex y being L st (x = P (y) & Q (y))))"
    {
        fix x
        assume "x be object"
        have "x in IT1 iff (ex y being L st (x = P (y) & Q (y)))" using B2 by simp
        hence "x in IT1 iff x in IT2" using B3 by simp
    }
    thus  "IT1=IT2" using B1 tarski_th_2 by auto
  qed 

lemmas Fraenkel_A1_ex =  Fraenkel_A1[THEN conjunct1,THEN conjunct2, rule_format, OF _ object_root,THEN iffD1]   
theorem Fraenkel_A1_in:
   "sethood-of M \<Longrightarrow> x be M \<Longrightarrow> Q(x) \<Longrightarrow> P(x) in {P(x) where x be M : Q(x)}"  using Fraenkel_A1 by auto

abbreviation the_set_of_all
where "the_set_of_all (P, M) \<equiv> Fraenkel1(P, M, (\<lambda>x. True))"

syntax
  "_SetOfAll" :: "Set \<Rightarrow> vs \<Rightarrow> Mode \<Rightarrow> Set" ("the set-of-all _ where _ be _")
translations
 "the set-of-all f where x be D" \<rightleftharpoons> "CONST Mizar_Fraenkel.the_set_of_all((%x. f), D)"

term "the set-of-all {x} where x be set"

theorem Set_of_All_ex:
 "sethood-of M \<Longrightarrow> x in the set-of-all P(x) where x be M \<Longrightarrow> ex y be M st x = P(y)"
proof-
  assume A1:"sethood-of M" "x in the set-of-all P(x) where x be M"
  show "ex y be M st x = P(y)" using Fraenkel_A1_ex[OF A1] by auto
qed 

theorem Set_of_All_in:
 "sethood-of M \<Longrightarrow> x be M \<Longrightarrow> P(x) in the set-of-all P(x) where x be M" using Fraenkel_A1_in by auto 

end