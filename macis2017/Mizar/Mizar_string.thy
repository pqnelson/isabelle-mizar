\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Mizar_string
  imports "../MML/Xboole_0"
begin 
  
definition Succ ::"Set \<Rightarrow> Set" ("Succ _" 90) where
   "func Succ X \<rightarrow> set equals
          X \<union> {X}"
schematic_goal Succ:
  assumes "X be object" shows "?X"
proof (induct rule: equals_property[OF Succ_def,of X, case_names coherence])
  case coherence
    show "(X \<union> {X}) be set" by simp
qed

lemma Succ_1: "X<>Y \<Longrightarrow> Succ X <> Succ Y"
proof
  assume A1: "X<>Y" "Succ X = Succ Y"
  have "Y in Succ Y" using Succ tarski_def_1b by auto
  hence "Y in X \<union> { X }" using Succ A1(2) by auto
  hence A2: "Y in X" using A1(1) tarski_def_1b by auto
  have "X in Succ X" using tarski_def_1b Succ by auto
  hence "X in Y" using A1 Succ tarski_def_1b by auto 
  thus "False" using A2 prefix_in_asymmetry[rule_format,of X Y] all_set by auto
qed

lemma Succ_2: "x in Succ Y \<Longrightarrow> x in Succ Succ Y" using Succ by simp
lemma Succ_3: "x in Succ Y \<Longrightarrow> x <> Succ Y" using prefix_in_irreflexive all_set by auto
lemma Succ_4: "x in Succ Y \<Longrightarrow> Succ Y <> x" using prefix_in_irreflexive all_set by auto
lemma Succ_5: "X in Succ X" using Succ tarski_def_1b by auto
  
    
lemmas string = Succ_1 Succ_2 Succ_3 Succ_4 Succ_5 tarski_def_1b  
  
 
(*lemmas SUCC = Succ[simplified,THEN conjunct2]

theorem Succ_0:
  "not X in X" using prefix_in_irreflexive all_set by simp

theorem Succ_1x:
  "X in Succ X" using SUCC by auto

theorem Succ_2:
  "X in Y \<Longrightarrow> X in Succ Y" using SUCC by auto
*)
    
definition carrier:: "Set" ("carrier")
  where "carrier \<equiv> {}"

abbreviation ZeroF:: "Set" ("ZeroF")
  where "ZeroF \<equiv> Succ carrier"

abbreviation OneF:: "Set" ("OneF")
  where "OneF \<equiv> Succ ZeroF"

abbreviation multF:: "Set" ("multF")
  where "multF \<equiv> Succ OneF"    
    
abbreviation addF:: "Set" ("addF")
  where "addF \<equiv> Succ multF"    
    
abbreviation lmult:: "Set" ("lmult")
  where "lmult \<equiv> Succ addF"

abbreviation rmult:: "Set" ("rmult")
  where "rmult \<equiv> Succ lmult"    
    
abbreviation topology:: "Set" ("topology")
  where "topology \<equiv> Succ rmult"

abbreviation ObjectKind:: "Set" ("Object-Kind")
  where "Object-Kind \<equiv> Succ topology"

abbreviation ValuesF::  "Set" ("ValuesF")
  where "ValuesF \<equiv> Succ Object-Kind" 

abbreviation InstructionsF ::  "Set" ("InstructionsF")
  where "InstructionsF \<equiv> Succ ValuesF"     
  
abbreviation Execution ::  "Set" ("Execution")
  where "Execution \<equiv> Succ InstructionsF"     

(*test*)    
    
lemma "carrier <> OneF" by (simp add: string) 

lemma "ZeroF <> OneF" by (simp add: string) 

lemma "ZeroF <> multF" by (simp add: string) 

lemma "not ZeroF in {carrier}\<union>{OneF}" by (simp add: string)
    
end    