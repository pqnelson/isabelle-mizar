\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Tarski
imports Mizar Mizar_Defs
begin

(* HIDDEN *)

axiomatization
  object and set 
where
  (* object is the root of type hierarchy *)
  object_root[simp]: "x be object" and
  object_exists[simp]: "ex x being object st True" and
  hidden_mode[rule_format,simp,intro]: "x be set implies x be object"

abbreviation not_equal (infixl "<>" 50) where
  "x <> y \<equiv> not (x = y)"

abbreviation mizneq (infixl "\<noteq>" 50) where
  "a \<noteq> b \<equiv> not a = b"

(*TARSKI_0*)

reserve x,y,z,u,a for object
reserve M,N,X,Y,Z for set

consts
  prefix_in :: "Set \<Rightarrow> Set \<Rightarrow> o" (infixl "in" 50)

\<comment>\<open>Set axiom\<close>
axiomatization where tarski_0_1:
  "for x being object holds x be set"

\<comment>\<open>Extensionality axiom\<close>
axiomatization where tarski_0_2:
  "X be set \<Longrightarrow> Y be set \<Longrightarrow>
    (for x holds x in X iff x in Y) implies X = Y"

\<comment>\<open>Axiom of pair\<close>
axiomatization where tarski_0_3:
  "ex z being set st
     for a being object holds
       a in z iff a = x or a = y"

\<comment>\<open>Axiom of union\<close>
axiomatization where tarski_0_4:
  "X be set \<Longrightarrow>
     ex Z st for x holds x in Z iff (ex Y st x in Y & Y in X)"

\<comment>\<open>Axiom of regularity\<close>
axiomatization where tarski_0_5:
  "X be set \<Longrightarrow> x in X implies (ex Y st Y in X & not (ex z st z in X & z in Y))"

\<comment>\<open>Fraenkel's scheme\<close>
axiomatization where tarski_0_sch_1:
  "A be set \<Longrightarrow>
     for x,y,z st P (x,y) & P (x ,z) holds y = z \<Longrightarrow>
       ex X st for x holds
         x in X iff (ex y st y in A & P(y, x))"

(*TARSKI*)
theorem set_exists[simp]: "ex x being set st True"
using object_exists tarski_0_1 by auto

theorem all_set: "x be set"
using tarski_0_1 by auto

lemmas tarski_th_2 = tarski_0_2
lemmas [intro!] = tarski_0_2[simplified,rule_format]

definition tarski_def_1 ("{_}") where
   "func {y} \<rightarrow> set means \<lambda>it.
    for x holds x in it iff x = y"

schematic_goal tarski_def_1:
  assumes "y be object" shows "?X"
proof (induct rule: means_property[OF  tarski_def_1_def,of y, case_names existence uniqueness])
    case uniqueness
      fix X1 X2
      assume T0: "X1 be set" "X2 be set" and
         A1: "for x being object holds x in X1 iff x = y" and
         A2: "for x being object holds x in X2 iff x = y"
      {
         fix x
         assume "x be object"
         hence "x in X1 iff x = y" using A1 by auto
         hence "x in X1 iff x in X2" using A2 by auto
      }
      thus "X1 = X2" using tarski_th_2 A1 A2 T0 by auto
 next    
   case existence  
      obtain X where
      T1: "X be set " and A1: " (for x being object holds
        (x in X iff (x = y or x = y)))"
           using tarski_0_3 assms by blast
     (*take X*)
      show "ex X st for x being object holds x in X iff x = y"  
        proof (rule bexI[of _ X])
          show "X be set" 
               "for x being object holds x in X iff x = y" using T1 A1 by auto
        qed

qed

lemmas tarski_def_1a[simp] = tarski_def_1[THEN conjunct1,THEN conjunct1,simplified]
lemmas tarski_def_1b[simp] = tarski_def_1[THEN conjunct1,THEN conjunct2,simplified,rule_format]
lemmas tarski_def_1c = tarski_def_1[THEN conjunct2,rule_format,unfolded atomize_conjL[symmetric],simplified, rule_format]


definition tarski_def_2("{ _ , _ }") where
" func {y, z} \<rightarrow> set means \<lambda>it. (for x being object holds x in it iff (x = y or x = z))"

schematic_goal tarski_def_2:
  assumes "y be object & z be object" shows "?X"
proof (induct rule: means_property[OF tarski_def_2_def,of y z, case_names existence uniqueness])
  case existence  
    obtain X where
      A1: "X be set & (for x being object holds (x in X iff (x = y or x = z)))" using tarski_0_3 assms by blast
    thus "ex X be set st for x being object holds x in X iff (x = y or x = z)"  by auto
next
  case uniqueness
  fix IT1 IT2
  assume A: "IT1 be set" "for x being object holds (x in IT1 iff x = y or x = z)"
          "IT2 be set" "for x being object holds (x in IT2 iff x = y or x = z)"
  {
    fix x
    assume Z1: "x be object"
    have "x in IT1 iff x=y or x = z" using Z1 A(2) by auto
    hence "x in IT1 iff x in IT2" using Z1 A(4) by auto
  }
  thus "IT1 = IT2" using tarski_th_2 A by auto
qed

lemmas tarski_def_2b[simp] = tarski_def_2[THEN conjunct1,THEN conjunct2,simplified,rule_format]
lemmas tarski_def_2a[simp] = tarski_def_2[THEN conjunct1,THEN conjunct1,simplified,rule_format]

theorem tarski_def_2_commutativity[simp]:
  "commutativity object tarski_def_2"
proof(intro ballI)
  fix x y
  assume T0:"x be object" "y be object"
  have A1: "{x,y} be set" "{y,x} be set" using tarski_def_2 T0 by auto
  {fix z
   assume T1: "z be object"
   have "z in {x,y} iff z = x or z = y" using T0 T1 tarski_def_2 by auto
   hence "z in {x,y} iff z in {y,x}" using T0 T1 tarski_def_2 by auto
  }
  thus "{x,y}={y,x}" using tarski_th_2[OF A1] by auto
qed

definition tarski_def_3:: "Set \<Rightarrow> Set \<Rightarrow> o" (infixl "c=" 50)
where tarski_def_3_pre: "X be set \<Longrightarrow> Y be set \<Longrightarrow> X c= Y iff (for x holds x in X implies x in Y)"

lemmas tarski_def_3[simp] = tarski_def_3_pre[OF all_set all_set]
text_raw \<open>\DefineSnippet{tarski_def_3_reflexivity}{\<close>
theorem  tarski_def_3_reflexive:
  "reflexive set tarski_def_3"  by auto
text_raw \<open>}%EndSnippet\<close>
  
syntax "Tarski.tarski_def_3" :: "Set \<Rightarrow> Set \<Rightarrow> o" (infixl "\<subseteq>" 50)

definition tarski_def_4 ("union _" [90] 90) where
   "func union X \<rightarrow> set means \<lambda>it.
      for x holds
        x in it iff (ex Y st x in Y & Y in X)"

schematic_goal tarski_def_4:
  assumes "X be set" shows "?X"
proof (induct rule: means_property[OF tarski_def_4_def,of X,case_names existence uniquencess])
  case existence
    show "ex IT being set st for x being object holds x in IT iff (ex Y being set st x in Y & Y in X)" using tarski_0_4 assms by blast
  case uniquencess
  fix IT1 IT2
  assume T0: "IT1 be set" "IT2 be set"
  assume A1: "for x being object holds (x in IT1 iff (ex Y being set st (x in Y & Y in X)))" and
         A2: " for x being object holds (x in IT2 iff (ex Y being set st (x in Y & Y in X)))"
    {
     fix x
     assume T1:"x be object"
     have "x in IT1 iff (ex Y being set st (x in Y & Y in X))" using A1 T0 T1 by simp
     hence "x in IT1 iff x in IT2" using A2 T0 T1 by simp
    }
  thus "IT1 = IT2" using tarski_th_2 T0 by auto
qed

(* If we have "union X" we can assume the user wanted X to be a set *)
lemmas tarski_def_4a[simp] = tarski_def_4[THEN conjunct1,THEN conjunct1,OF all_set]
lemmas tarski_def_4b[simp] = tarski_def_4[THEN conjunct1,THEN conjunct2,simplified all_set,simplified,rule_format]
(*   setup "Config.put_global Blast.trace true" *)

lemmas tarski_th_3 = tarski_0_5

theorem prefix_in_asymmetry:
  "asymmetry set prefix_in"
proof (intro ballI notI impI)
  fix a b
  assume T0:"a be set" "b be set"
  assume A1:"a in b & b in a"
  let ?X = "{ a , b }"
  obtain Y where
  A4: "Y be set & Y in ?X & not(ex z being object st z in ?X & z in Y)"
    using tarski_0_5[of "?X"] T0 by auto
  have "Y=a or Y=b" using A4 T0 tarski_def_2 by auto
  then show False using A1 A4 T0 tarski_def_2 by auto
qed

lemmas[simp] = bspec[OF bspec[OF prefix_in_asymmetry all_set] all_set,rule_format]
lemmas tarski_sch_1 = tarski_0_sch_1

theorem prefix_in_irreflexive:
  "irreflexive set prefix_in" 
proof (intro ballI notI impI)
  fix a b
  assume T0:"a be set"
  assume A1:"a in a"
  let ?X = "{ a }"
  obtain Y where
  A4: "Y be set & Y in ?X & not(ex z being object st z in ?X & z in Y)"
    using tarski_0_5[of "?X"] T0 by auto
  have "Y=a" using A4 T0 tarski_def_1 by auto
  then show False using A1 A4 T0 tarski_def_1 by auto
qed



definition tarski_def_5 ("[_ , _]") where 
   "func [x,y] \<rightarrow> object equals
      {{x, y}, {x}}"


schematic_goal tarski_def_5:
  assumes "x be object & y be object" shows "?X"
proof (rule equals_property[OF tarski_def_5_def])
  show "{{x, y}, {x}} be object" using assms tarski_def_1 tarski_def_2 by auto
qed

definition
  are_equipotent_prefix :: "Set \<Rightarrow> Set \<Rightarrow> o" ("_,_ areequipotent" [100,100])
where
  tarski_def_6: "X be set \<Longrightarrow> Y be set \<Longrightarrow>
    X, Y areequipotent iff
    (ex Z st
     (for x st x in X ex y st y in Y & [x,y] in Z) &
     (for y st y in Y ex x st x in X & [x,y] in Z) &
     (for x,y,z,u st [x,y] in Z & [z,u] in Z holds x = z iff y = u))"

(*TARSKI_A*)

axiomatization where
tarski_a_th_1:
  "for N holds ex M st N in M &
     (for X,Y holds X in M & Y c= X implies Y in M) &
     (for X st X in M ex Z st Z in M & (for Y st Y c= X holds Y in Z)) &
     (for X holds X c= M implies X,M areequipotent or X in M)"

text_raw \<open>\DefineSnippet{redefine_func_mode_property}{\<close>        
lemma redefine_func_mode_property:
assumes lt: "lt"
assumes coherence: "for x be M holds x be M1"
assumes compatibility: "\<And> it. it be set \<Longrightarrow> ((it be M) \<longleftrightarrow> newCondition(it))"
shows "x be M \<Longrightarrow> (x be M1 & newCondition (x))" 
text_raw \<open>}%EndSnippet\<close>
proof
  assume A1: "x be M"
  thus "x be M1" using coherence by simp
  show "newCondition (x)" using compatibility[of x,OF all_set] A1 by simp
qed  
  
  
end



