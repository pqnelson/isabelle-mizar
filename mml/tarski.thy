theory tarski
imports "../mizar/mizar_reserve"
begin

section "TARSKI_0"
reserve x for object
text_raw {*\DefineSnippet{tarski-axiom1}{*}
--"Set axiom"
theorem tarski_0_1:
  "\<forall>x. x be set" using SET_def by simp
(*axiomatization where tarski_0_1:
  "\<forall>x. x be set"*)
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{tarski-set-exists}{*}
theorem set_exists[ex]: "inhabited(set)"
  using tarski_0_1 inhabited_def by auto
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{tarski-reserve}{*}
reserve x,y,z,u,a for object
reserve M,N,X,Y,Z for set
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{tarski-axiom2}{*}
--"Extensionality axiom"
axiomatization where tarski_0_2:
  "\<forall>X. \<forall>Y. (\<forall>x. x in X \<longleftrightarrow> x in Y)
    \<longrightarrow> X = Y"
text_raw {*}%EndSnippet*}
  lemmas tarski_0_2a = tarski_0_2[THEN bspec,THEN bspec,rule_format,OF _ _ _ _ ballI,simplified]

text_raw {*\DefineSnippet{tarski-axiom3}{*}
--"Axiom of pair"
axiomatization where tarski_0_3:
  "\<forall>x. \<forall>y. \<exists>Z. \<forall>a.
      a in Z \<longleftrightarrow> a = x \<or> a = y"
text_raw {*}%EndSnippet*}

thm tarski_0_3
text_raw {*\DefineSnippet{tarski-axiom4}{*}
--"Axiom of union"
axiomatization where tarski_0_4:
  "\<forall>X. \<exists>Z. \<forall>x.
     x in Z \<longleftrightarrow> (\<exists>Y. x in Y \<and> Y in X)"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{tarski-axiom5}{*}
--"Axiom of regularity"
axiomatization where tarski_0_5:
  "\<forall>x. \<forall>X. x in X \<longrightarrow> (\<exists>Y. Y in X \<and>
     \<not>(\<exists>z. z in X \<and> z in Y))"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{tarski-axiom6}{*}
--"Fraenkel's scheme"
axiomatization where tarski_0_sch_1:
  "A be set \<Longrightarrow>
     \<forall>x,y,z. P(x,y) \<and> P(x,z) \<longrightarrow> y = z \<Longrightarrow>
       \<exists>X. \<forall>x.
   x in X \<longleftrightarrow> (\<exists>y. y in A \<and> P(y,x))"
text_raw {*}%EndSnippet*}

section "TARSKI"

theorem all_set: "x be set"
using tarski_0_1 object_root by mauto

lemmas tarski_sch_1 = tarski_0_sch_1
lemmas tarski_th_2 = tarski_0_2a[intro?]

(*lemmas tarski_th_2 = tarski_0_2[rule_format,OF _ _ ballI,simplified,intro?]*)

text_raw {*\DefineSnippet{tarski-def1}{*}
func tarski_def_1    ("{_}") where
  mlet "y be object"
  "func {y} \<rightarrow> set means \<lambda>it.
     \<forall>x. x in it \<longleftrightarrow> x = y"
text_raw {*}%EndSnippet*}
proof -
  fix X1 X2
  assume [ty]: "X1 be set" "X2 be set" and
    A1: "\<forall>x:object. x in X1 \<longleftrightarrow> x = y" and
    A2: "\<forall>x:object. x in X2 \<longleftrightarrow> x = y"
    {
      fix x
      assume [ty]: "x be object"
      hence "x in X1 \<longleftrightarrow> x = y" using A1 by auto
      hence "x in X1 \<longleftrightarrow> x in X2" using A2 by auto
    }
      thus "X1 = X2" by (intro tarski_th_2) auto
    next
  obtain X where
    [ty]: "X be set" and A1: "(\<forall>x:object.
       (x in X \<longleftrightarrow> (x = y \<or> x = y)))"
    using tarski_0_3[THEN bspec,THEN bspec] ex by mauto
      show "\<exists>Z:set. \<forall>x: object. x in Z \<longleftrightarrow> x = y"
        proof (rule bexI[of _ _ X])
          show "\<forall>x:object. x in X \<longleftrightarrow> x = y" using A1 by auto
        qed simp_all
qed simp

text_raw {*\DefineSnippet{tarski-def2}{*}
func tarski_def_2    ("{_ , _}") where
  mlet "y be object", "z be object"
  "func {y, z} \<rightarrow> set means \<lambda>it.
     \<forall>x. x in it \<longleftrightarrow> (x = y \<or> x = z)"
text_raw {*}%EndSnippet*}
proof-
  obtain X where
      "X be set" and A1: "(\<forall>x:object. (x in X \<longleftrightarrow> (x = y \<or> x = z)))"
       using tarski_0_3[THEN bspec,THEN bspec] by mauto
  thus "\<exists>X:set. \<forall>x:object. x in X \<longleftrightarrow> (x = y \<or> x = z)" using ex by auto
next
  fix IT1 IT2
  assume [ty]: "IT1 be set" and
         A1: "\<forall>x:object. (x in IT1 \<longleftrightarrow> x = y \<or> x = z)" and
         [ty]: "IT2 be set" and
         A2: "\<forall>x:object. (x in IT2 \<longleftrightarrow> x = y \<or> x = z)"
  {
    fix x
    assume [ty]: "x be object"
    have "x in IT1 \<longleftrightarrow> x=y \<or> x = z" using A1 by auto
    hence "x in IT1 \<longleftrightarrow> x in IT2" using A2 by auto
  }
  thus "IT1 = IT2" by (intro tarski_th_2) auto
qed simp

mtheorem tarski_def_2_commutativity[simplified]:
  "commutativity object tarski_def_2"
proof(intro ballI)
  fix x y
  assume T0[ty]:"x be object" "y be object"
  have "{x,y}  be set" by mauto
  {fix z
   assume T1[ty]: "z be object"
   have "z in {x,y} \<longleftrightarrow> z = x \<or> z = y" using tarski_def_2 by auto
   hence "z in {x,y} \<longleftrightarrow> z in {y,x}" using tarski_def_2 by auto
  }
  thus "{x,y}={y,x}" by (intro tarski_th_2) mauto
qed simp_all

definition tarski_def_3_pre:: "Set \<Rightarrow> Set \<Rightarrow> o" (infixl "c=" 50)
  where tarski_def_3:
"let X be set \<and> Y be set
  pred X c= Y means (\<forall>x:object. x in X \<longrightarrow> x in Y)"

lemmas tarski_def_3a = tarski_def_3[THEN iffD1,THEN bspec,simplified,rule_format]
lemmas tarski_def_3b[intro?] = tarski_def_3[THEN iffD2, rule_format,OF _ _ ballI, simplified,rule_format]
text_raw {*\DefineSnippet{tarski_def_3_reflexivity}{*}
theorem tarski_def_3_reflexive:
  "reflexive set tarski_def_3_pre" using tarski_def_3 by simp
text_raw {*}%EndSnippet*}



abbreviation tarski_def_3_notation (infixl "\<subseteq>" 50) where
  "X \<subseteq> Y \<equiv> X c= Y"


lemmas tarski_def_3c = tarski_def_3_reflexive[THEN bspec,simplified]

text_raw {*\DefineSnippet{tarski-def4}{*}
func tarski_def_4    ("union _" [90] 90) where
   mlet "X be set"
   "func union X \<rightarrow> set means \<lambda>it.
      \<forall>x. x in it \<longleftrightarrow> (\<exists>Y. x in Y \<and> Y in X)"
text_raw {*}%EndSnippet*}
proof-
  show "\<exists>IT:set. \<forall>x:object. x in IT \<longleftrightarrow> (\<exists>Y:set. x in Y \<and> Y in X)" using tarski_0_4 by auto
next
  fix IT1 IT2
  assume T0[ty]: "IT1 be set" "IT2 be set"
  assume A1: "\<forall>x:object. (x in IT1 \<longleftrightarrow> (\<exists>Y:set. (x in Y \<and> Y in X)))" and
         A2: " \<forall>x:object. (x in IT2 \<longleftrightarrow> (\<exists>Y:set. (x in Y \<and> Y in X)))"
    {
     fix x
     assume T1[ty]:"x be object"
     have "x in IT1 \<longleftrightarrow> (\<exists>Y:set. (x in Y \<and> Y in X))" using A1 by mauto
     hence "x in IT1 \<longleftrightarrow> x in IT2" using A2 by mauto
    }
  thus "IT1 = IT2" by (intro tarski_th_2) auto
qed simp

lemmas tarski_th_3 = tarski_0_5[THEN bspec,THEN bspec]

mtheorem prefix_in_asymmetry:
  "asymmetry set prefix_in"
proof (intro ballI notI impI)
  fix a b
  assume T0[ty]:"a be set" "b be set"
  assume A1:"a in b \<and> b in a"
  let ?X = "{ a , b }"
  have "a in ?X" using tarski_def_2 by mauto
  then obtain Y where
  T1[ty]: "Y be set" and A4:"Y in ?X \<and> \<not>(\<exists>z:object. z in ?X \<and> z in Y)"
    using tarski_0_5[THEN bspec,THEN bspec,of a ?X] by mauto
  have "Y=a \<or> Y=b" using A4 tarski_def_2 by auto
  then show False using A1 A4 tarski_def_2 by mauto
qed simp_all

theorem prefix_in_irreflexive:
  "irreflexive object prefix_in"
proof (intro ballI notI impI)
  fix a b
  assume [ty]:"a be object"
  assume A1:"a in a"
  let ?X = "{ a }"
  have "a in ?X" using tarski_def_1 by auto
  then obtain Y where
  A4: "Y be set \<and> Y in ?X \<and> \<not>(\<exists>z:object. z in ?X \<and> z in Y)"
    using tarski_0_5[THEN bspec,THEN bspec] by mauto
  have "Y=a" using A4 tarski_def_1 by auto
  then show False using A1 A4 tarski_def_1 by auto
qed simp_all

text_raw {*\DefineSnippet{tarski-def5}{*}
func tarski_def_5    ("[_ , _]") where
  mlet "x be object", "y be object"
  "func [x,y] \<rightarrow> object equals
     {{x, y} , {x}}"
text_raw {*}%EndSnippet*}
proof-
  show "{{x, y}, {x}} be object" by auto
qed

theorem [ty_func]:
  "x be object \<Longrightarrow> y be object \<Longrightarrow> [x,y] be set" using tarski_def_5 tarski_def_2_ty by mty auto  
  
  
definition
  are_equipotent :: "Set \<Rightarrow> Set \<Rightarrow> o" ("_,_ areequipotent" [100,100])
where
  tarski_def_6: "let X be set \<and> Y be set
   pred X, Y areequipotent means
    (ex Z st
     (for x st x in X ex y st y in Y \<and> [x,y] in Z) \<and>
     (for y st y in Y ex x st x in X \<and> [x,y] in Z) \<and>
     (for x,y,z,u st [x,y] in Z \<and> [z,u] in Z holds x = z \<longleftrightarrow> y = u))"

section "TARSKI_A"

axiomatization where
tarski_a_th_1:
  "\<forall>N.  ex M st N in M \<and>
     (for X,Y holds X in M \<and> Y c= X \<longrightarrow> Y in M) \<and>
     (for X st X in M ex Z st Z in M \<and> (for Y st Y c= X holds Y in Z)) \<and>
     (\<forall>X.  X c= M \<longrightarrow> X,M areequipotent \<or> X in M)"


 text_raw {*\DefineSnippet{redefine_func_mode_property}{*}
lemma redefine_func_mode_property:
assumes lt: "lt" and
  coherence: "\<forall>x : M.  x be M1" and
  mode_ex: "inhabited(M)" and
  compatibility: "\<And> it. it be set \<Longrightarrow> ((it be M) \<longleftrightarrow> newCondition(it))"
shows "x be M \<Longrightarrow> (x be M1 \<and> newCondition (x))"
text_raw {*}%EndSnippet*}
proof
  assume T0[ty]: "x be M"
  thus "x be M1" using coherence mode_ex by simp
  show "newCondition (x)" using compatibility[of x,OF all_set] by simp
qed

(* :: "Ty \<Rightarrow> o" *)
  
text_raw {*\DefineSnippet{sethood_def}{*}  
definition "sethood(M) \<equiv> \<exists>X:set. \<forall>x:object. x be M \<longrightarrow> x in X"
text_raw {*}%EndSnippet*}
  
text_raw {*\DefineSnippet{sethood}{*}  
theorem sethood:
  "sethood(M) \<longleftrightarrow> (\<exists>X:set. \<forall>x:object. x be M \<longleftrightarrow> x in X)"
text_raw {*}%EndSnippet*}
proof(rule iffI3)
  show "sethood(M) \<longrightarrow> (\<exists>X:set. \<forall>x:object. x be M \<longleftrightarrow> x in X)"
  proof
    assume "sethood(M)"
    then obtain X where
      [ty]:"X be set" and A1:"\<forall>x:object. x be M \<longrightarrow> x in X" using sethood_def by auto
    let ?P="\<lambda>x y. x=y & x be M"
    have  "\<forall>x,y,z:object. ?P(x,y) \<and> ?P(x,z) \<longrightarrow> y = z" by auto
    then obtain S where
       [ty]:"S be set" and "\<forall>x:object. x in S \<longleftrightarrow> (\<exists>y. y in X \<and> ?P(y,x))" using tarski_0_sch_1[of X ?P] by auto
    hence "\<forall>x:object. x be M \<longleftrightarrow> x in S" using A1 by auto
    thus "\<exists>S : set. \<forall>x : object. x is M \<longleftrightarrow> x in S" using bexI[of set _ S] by auto
  qed
  assume "\<exists>X:set. \<forall>x:object. x be M \<longleftrightarrow> x in X"
  thus "sethood(M)" using sethood_def by auto    
qed
      
abbreviation (input) setS :: "Set \<Rightarrow>Ty" ("set''")where
  "set' \<equiv> \<lambda>it. set"

end



