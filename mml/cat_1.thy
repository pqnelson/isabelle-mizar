theory cat_1
imports graph_1
begin

theorem [ex]:
  "let X be set \<and> Y be set
   cluster Function_like for Relation-of X,Y" unfolding inhabited_def
proof(rule exI[of _ "the (Function-of X,Y)"])
  assume [ty]:"X be set \<and> Y be set"
  show "(the Function-of X,Y) is Function_like\<bar> Relation-of X,Y" using choice_ax[of "Function-of X,Y"] by mauto
qed

mdefinition CatStr :: "Ty" ("CatStr") where
  "struct CatStr
      (#carrier \<rightarrow> (\<lambda>S. set);
        carrier` \<rightarrow> (\<lambda>S. set);
        Source \<rightarrow> (\<lambda>S. Function-of the carrier` of S, the carrier of S);
        Target \<rightarrow> (\<lambda>S. Function-of the carrier` of S, the carrier of S);
        Comp \<rightarrow> (\<lambda>S. PartFunc-of [:the carrier` of S, the carrier` of S:],the carrier` of S) #)"
  :well_defined_property[of _ _ "{carrier}\<union>{carrier`}\<union>{Source}\<union>{Target}\<union>{Comp}"]
  by (auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

lemmas CatStrA = CatStr(1)
lemmas [ex] = CatStr(2,3)
lemmas CatStrD = CatStr(4)
lemmas [ty_func] = CatStr(5)

theorem CatStr_inheritance[ty_parent]:
  "X be CatStr \<Longrightarrow> X be MultiGraphStruct" using CatStrA MultiGraphStructA by simp

theorem CatStr_inheritance1[ty_func]:
  "X be CatStr \<Longrightarrow> (the Comp of X) be PartFunc-of [:the carrier` of X, the carrier` of X:],the carrier` of X"
       using field CatStrA by auto

lemma CatStr_ag[ty_func]:
  "X be set \<Longrightarrow> Y be set \<Longrightarrow> S be Function-of Y,X \<Longrightarrow> T be Function-of Y,X \<Longrightarrow>
      C be PartFunc-of [:Y, Y:],Y \<Longrightarrow>
       [#carrier\<mapsto> X ; carrier`\<mapsto>Y; Source\<mapsto>S; Target\<mapsto>T ;  Comp \<mapsto>C #] be CatStr"
proof-
  assume A1[ty]: "X be set" "Y be set" "S be Function-of Y,X" "T be Function-of Y,X"
     "C be PartFunc-of [:Y, Y:],Y"
  let ?A= "[#carrier\<mapsto> X ; carrier`\<mapsto>Y; Source\<mapsto>S; Target\<mapsto>T; Comp \<mapsto>C #]"
  have [ty]: "?A be Struct" using Struct_5 by (simp add:string)
  have T:"the carrier of ?A=X" using the_selector_of_1[of ?A carrier "X"] Aggr by auto
  have T1:"the carrier` of ?A=Y" using the_selector_of_1[of ?A "carrier`" "Y"] Aggr by auto
  have [ty]:"?A is (carrier \<rightarrow> set')" using Field_1[of ?A carrier X ] Aggr by auto
  have [ty]:"?A is (carrier` \<rightarrow> set')" using Field_1[of ?A "carrier`" Y ] Aggr by auto
  have [ty]:"?A is (Source \<rightarrow> Function-of' the' carrier`, the' carrier)" using Field_1[of ?A Source S ] T T1 Aggr by auto
  have [ty]:"?A is (Target \<rightarrow> Function-of' the' carrier`, the' carrier)" using Field_1[of ?A Target T ] T T1 Aggr by auto
  have [ty]:"?A is (Comp \<rightarrow> (\<lambda>S. PartFunc-of [:the carrier` of S, the carrier` of S:],the carrier` of S))"
      using Field_1[of ?A Comp C ] T T1 Aggr by auto
  thus ?thesis using CatStrA by auto
qed

abbreviation cat_1_mode_1_prefix ("Object-of _" [150] 150)
  where "Object-of X \<equiv> Element-of (the carrier of X)"

abbreviation cat_1_mode_2_prefix ("Morphism-of _" [150] 150)
  where "Morphism-of X \<equiv> Element-of (the carrier` of X)"

text_raw {*\DefineSnippet{cat_1_def_1}{*}
func cat_1_def_1 ("_ *\<^sub>_ _") where
  mlet "C be CatStr", "f be Morphism-of C", "g be Morphism-of C"
 "assume [g,f] in dom (the Comp of C)
  func f *\<^sub>C g \<rightarrow> Morphism-of C equals
    ( the Comp of C ). \<lparr> g , f \<rparr>"
text_raw {*}%EndSnippet*}
proof-
  have A1: "( the Comp of C ). \<lparr> g , f \<rparr> = ( the Comp of C ). [g , f]" using binop_0_def_1 by auto
  assume "[g,f] in dom(the Comp of C)"
  hence "( the Comp of C ). [g , f] in (the carrier` of C)" using patfun1_th_4
    by mauto
 thus "( the Comp of C ). \<lparr> g , f \<rparr> is Morphism-of C" using Element_of_rule3 binop_0_def_1 by auto
qed mauto

theorem[ex]:
  "cluster non empty-struct\<bar> non void-struct for CatStr"
proof
  let ?X="[#carrier\<mapsto> {{}} ; carrier`\<mapsto>{{}}; Source\<mapsto>op1; Target\<mapsto>op1 ;  Comp \<mapsto>op2 #]"
  have [ty]: "?X be CatStr"
    using CatStr_ag by mauto
  have "the carrier of ?X = {{}}" using the_selector_of_1[of ?X "carrier" "{{}}"] Aggr by mauto
  hence [ty]: "?X is non empty-struct" using struct_0_def_1 by mauto
  have "the carrier` of ?X = {{}}" using the_selector_of_1[of ?X "carrier`" "{{}}"] Aggr by mauto
  hence [ty]: "?X is non void-struct" using struct_0_def_13 by mauto
  show "?X is non empty-struct\<bar> non void-struct \<bar>  CatStr" by auto
qed

text_raw {*\DefineSnippet{cat_1_def_4}{*}
func cat_1_def_4 ("Hom\<^bsub>_\<^esub>") where
  mlet "C be non empty-struct \<bar> non void-struct \<bar> CatStr",
          "a be Object-of C", "b be Object-of C"
 "func Hom\<^bsub>C\<^esub>(a,b) \<rightarrow> Subset-of the carrier` of C equals
    {f where f be Morphism-of C : dom\<^bsub>C\<^esub>f = a \<and> cod\<^bsub>C\<^esub>f = b}"
text_raw {*}%EndSnippet*}
proof-
  let ?X = "{f where f be Morphism-of C : dom\<^bsub>C\<^esub> f = a \<and> cod\<^bsub>C\<^esub> f = b}"
  have "?X \<subseteq>  the carrier` of C"
  proof
    fix x assume B1: "x in ?X"
      obtain f where
    [ty]:"f be Morphism-of C"and
    A2: "x = f" and
    A3: "dom\<^bsub>C\<^esub> f = a \<and> cod\<^bsub>C\<^esub> f = b" using Fraenkel_A1_ex[OF _ _ B1] by auto
    show "x in the carrier` of C" using Element_of1 A2 by mauto
  qed mauto
  thus "?X is Subset-of the carrier` of C" using Subset_of_rule by mauto
qed

reserve C for "non empty-struct\<bar> non void-struct\<bar> CatStr"
reserve f,g for "Morphism-of C"
reserve a,b,c,d for "Object-of C"

mtheorem cat_1_th_1:
  "f in Hom\<^bsub>C\<^esub>(a,b) \<longleftrightarrow> dom\<^bsub>C\<^esub>f=a \<and> cod\<^bsub>C\<^esub>f=b"
proof(rule iffI3)
  show "f in Hom\<^bsub>C\<^esub>(a,b) \<longrightarrow> dom\<^bsub>C\<^esub> f=a \<and> cod\<^bsub>C\<^esub>f=b"
  proof
    assume "f in Hom\<^bsub>C\<^esub>(a,b)"
    hence B1: "f in {g where g be Morphism-of C : dom\<^bsub>C\<^esub> g = a \<and> cod\<^bsub>C\<^esub> g = b}" using cat_1_def_4 by simp
    have J: " ex y be Morphism-of C st f = y \<and> dom\<^bsub>C\<^esub> y = a \<and> cod\<^bsub>C\<^esub> y = b" using Fraenkel_A1_ex[OF _ _ B1] by auto
     obtain g where
      [ty]: "g be Morphism-of C"and
     A2: "f = g \<and> dom\<^bsub>C\<^esub> g = a \<and> cod\<^bsub>C\<^esub> g = b" using bexE[OF J,of thesis] by auto (*CK ! ! dlaczego to nie idzie bez bexE*)
     thus "dom \<^bsub>C\<^esub> f=a \<and> cod \<^bsub>C\<^esub> f=b" by mauto
   qed
  assume "dom \<^bsub>C\<^esub> f=a \<and> cod \<^bsub>C\<^esub> f=b"
  hence "f in {g where g be Morphism-of C : dom \<^bsub>C\<^esub> g = a \<and> cod \<^bsub>C\<^esub> g = b}" using Fraenkel_A1_in[of "Morphism-of C" f
           "\<lambda>g. dom \<^bsub>C\<^esub> g = a \<and> cod \<^bsub>C\<^esub> g = b" ] by auto
  thus "f in Hom\<^bsub>C\<^esub>(a,b)" using cat_1_def_4 by simp
qed

text_raw {*\DefineSnippet{cat_1_def_5}{*}
mdefinition cat_1_def_5    ("Morphism-of") where
  mlet "C be non empty-struct \<bar> non void-struct \<bar> CatStr",
          "a be Object-of C", "b be Object-of C"
  "assume Hom\<^bsub>C\<^esub>(a,b) \<noteq> {}
  mode Morphism-of(a,b,C) \<rightarrow> Morphism-of C means
      (\<lambda>it. it in Hom\<^bsub>C\<^esub>(a,b))": assume_mode_property
text_raw {*}%EndSnippet*}
proof-
  assume "Hom\<^bsub>C\<^esub>(a,b) \<noteq> {}"
  hence "ex x be object st x in Hom\<^bsub>C\<^esub>(a,b)" using xboole_0_th_7 by auto
  then obtain x where
     A1: "x in Hom\<^bsub>C\<^esub>(a,b)" using bexI by auto
  have "Hom\<^bsub>C\<^esub>(a,b) \<subseteq> the carrier` of C" using Subset_in_rule by mauto
  hence "x is Element-of the carrier` of C" using Element_of_rule3 tarski_def_3 A1 by auto
  thus "ex x be Morphism-of C st x in Hom\<^bsub>C\<^esub>(a,b) " using A1 by mauto
qed mauto

lemmas cat_1_def_5a[ty_parent] = cat_1_def_5(1)[THEN conjunct1]
lemmas cat_1_def_5e = cat_1_def_5(1)[THEN conjunct2,rule_format]
lemmas cat_1_def_5i = cat_1_def_5(2)
lemmas cat_1_def_5c[ex] = cat_1_def_5(3)[simplified,rule_format]

mtheorem cat_1_th_4:
  "for f being Morphism-of C holds f is Morphism-of(dom \<^bsub>C\<^esub> f,cod \<^bsub>C\<^esub> f,C)"
proof
  fix f
  assume [ty]: "f be Morphism-of C"
  hence F: "f in Hom\<^bsub>C\<^esub>(dom \<^bsub>C\<^esub> f,cod \<^bsub>C\<^esub> f)" using cat_1_th_1 by mauto
  hence "Hom\<^bsub>C\<^esub>(dom \<^bsub>C\<^esub> f,cod \<^bsub>C\<^esub> f)\<noteq>{}" using xb by auto
  thus "f is Morphism-of (dom \<^bsub>C\<^esub> f,cod \<^bsub>C\<^esub> f,C)" using xb cat_1_def_5i F by mauto
qed mauto

text_raw {*\DefineSnippet{cat_1_th_5}{*}
mtheorem cat_1_th_5:
  "\<forall>f : Morphism-of (a,b,C). Hom\<^bsub>C\<^esub>(a,b) \<noteq> {} \<longrightarrow> dom\<^bsub>C\<^esub> f = a \<and> cod\<^bsub>C\<^esub> f = b"
text_raw {*}%EndSnippet*}
proof(standard,standard)
  fix f
  assume [ty]:"f be Morphism-of (a,b,C)"
  assume "Hom\<^bsub>C\<^esub>(a,b) \<noteq> {}"
  hence "f in Hom\<^bsub>C\<^esub>(a,b)" using cat_1_def_5e by mauto
  thus "dom \<^bsub>C\<^esub> f = a \<and> cod \<^bsub>C\<^esub> f = b" using cat_1_th_1 by mauto
qed mauto

text_raw {*\DefineSnippet{cat_1_th_6}{*}
mtheorem cat_1_th_6:
  "for f being Morphism-of (a,b,C), h being Morphism-of (c,d,C) st
     Hom\<^bsub>C\<^esub>(a,b) \<noteq> {} \<and> Hom\<^bsub>C\<^esub>(c,d) \<noteq> {} \<and> f = h holds a = c \<and> b = d"
text_raw {*}%EndSnippet*}
proof(standard,standard,standard)
  fix f h
  assume [ty]:"f be Morphism-of (a,b,C)" "h be Morphism-of (c,d,C)"
  assume A1:"Hom\<^bsub>C\<^esub>(a,b) \<noteq> {} \<and> Hom\<^bsub>C\<^esub>(c,d) \<noteq> {} \<and> f=h"
  have "dom\<^bsub>C\<^esub>f = a \<and> cod \<^bsub>C\<^esub> f = b" using A1 cat_1_th_5 by mauto
  thus "a = c \<and> b = d" using A1 cat_1_th_5 by mauto
qed mauto


text_raw {*\DefineSnippet{cat_1_def_6}{*}
attr cat_1_def_6 ("Category'_like")
"attr Category_like for non empty-struct \<bar> non void-struct \<bar> CatStr means
      (\<lambda>C. for f,g being Morphism-of C
            holds [g,f] in dom (the Comp of C) \<longleftrightarrow> dom \<^bsub>C\<^esub> g = cod \<^bsub>C\<^esub> f)"
text_raw {*}%EndSnippet*}


attr cat_1_def_7 ("transitive")
"attr transitive for non empty-struct \<bar> non void-struct \<bar> CatStr means
      (\<lambda>C. for f,g being Morphism-of C st dom \<^bsub>C\<^esub> g = cod \<^bsub>C\<^esub> f
         holds dom \<^bsub>C\<^esub> (g *\<^sub>C f) = dom \<^bsub>C\<^esub> f \<and> cod \<^bsub>C\<^esub> (g *\<^sub>C f) = cod \<^bsub>C\<^esub> g)"

attr cat_1_def_8 ("associative")
"attr associative for non empty-struct \<bar> non void-struct \<bar> CatStr means
      (\<lambda>C. for f,g,h being Morphism-of C
     st dom \<^bsub>C\<^esub> h = cod \<^bsub>C\<^esub> g \<and> dom \<^bsub>C\<^esub> g = cod \<^bsub>C\<^esub> f
    holds h *\<^sub>C (g *\<^sub>C f) = (h *\<^sub>C g) *\<^sub>C f)"

attr cat_1_def_9 ("reflexive")
"attr reflexive for non empty-struct \<bar> non void-struct \<bar> CatStr means
      (\<lambda>C. for b being Object-of C holds Hom\<^bsub>C\<^esub>(b,b) \<noteq> {})"

attr cat_1_def_10 ("with'_identities")
"attr with_identities for non empty-struct \<bar> non void-struct \<bar> CatStr means
      (\<lambda>C. for a being Object-of C holds
         ex i being Morphism-of(a,a,C) st
    for b being Object-of C holds
     (Hom\<^bsub>C\<^esub>(a,b)\<noteq>{} \<longrightarrow> (for g being Morphism-of(a,b,C) holds g *\<^sub>C i = g)) \<and>
     (Hom\<^bsub>C\<^esub>(b,a)\<noteq>{} \<longrightarrow> (for f being Morphism-of(b,a,C) holds i *\<^sub>C f = f)) )"


func cat_1_def_11("1Cat'(_,_')") where
  mlet "o be object", "m be object"
  "func 1Cat(o,m) \<rightarrow> CatStr equals
   [# carrier \<mapsto>{o};
     carrier`\<mapsto> {m};
     Source \<mapsto> (m .\<comment>> o);
     Target \<mapsto> (m .\<comment>> o);
     Comp \<mapsto> ([m,m].\<comment>>m) #]"
proof-
  have [ty]:"m .\<comment>> o be Function-of {m},{o}" by auto
  have [ty]:"[m,m] .\<comment>> o be Function-of [:{m},{m}:],{o}" by mauto
  thus "[# carrier \<mapsto>{o};
     carrier`\<mapsto> {m};
     Source \<mapsto> (m .\<comment>> o);
     Target \<mapsto> (m .\<comment>> o);
     Comp \<mapsto> ([m,m].\<comment>>m) #] be CatStr" by auto
qed

theorem cat_1_cl[ty_func_cluster,rule_format]:
  "let o be object \<and> m be object
   cluster 1Cat(o,m) \<rightarrow> non empty-struct\<bar> trivial-struct\<bar> non void-struct\<bar> trivial`-struct"
proof-
  let ?C = " [# carrier \<mapsto>{o};
     carrier`\<mapsto> {m};
     Source \<mapsto> (m .\<comment>> o);
     Target \<mapsto> (m .\<comment>> o);
     Comp \<mapsto> ([m,m].\<comment>>m) #]"
  have T1[ty]: "?C be CatStr" by mauto
  have T2: "the carrier of ?C = {o}"
     using the_selector_of_1[of ?C carrier "{o}"] Aggr by auto
  hence [ty]:"?C is trivial-struct" using struct_0_def_9[of ?C] by mauto
  have "the carrier of ?C is non empty" using T2 by mauto
  hence [ty]: "?C be non empty-struct" using struct_0_def_1 T2 by auto
  have T2: "the carrier` of ?C = {m}"
     using the_selector_of_1[of ?C "carrier`" "{m}"] Aggr by auto
  hence [ty]:"?C is trivial`-struct" using struct_0_def_21[of ?C] by mauto
  have "the carrier` of ?C is non empty" using T2 by mauto
  hence [ty]: "?C be non void-struct" using struct_0_def_13 T2 by auto
  show ?thesis using cat_1_def_11 by auto
qed

theorem [rule_format,ty_cond_cluster]:
 "cluster trivial-struct \<rightarrow> transitive \<bar>reflexive
    for non empty-struct\<bar> non void-struct\<bar> CatStr"
proof-
  fix C
  assume [ty]:"C is non empty-struct\<bar> non void-struct\<bar> CatStr"
              "C is trivial-struct"
  have [ty]:"C is transitive"
  proof
    fix f g assume T2[ty]: "f be Morphism-of C" "g be Morphism-of C"
    assume " dom \<^bsub>C\<^esub> g = cod \<^bsub>C\<^esub> f"
    show "dom \<^bsub>C\<^esub> (g *\<^sub>C f) = dom \<^bsub>C\<^esub> f \<and> cod \<^bsub>C\<^esub> (g *\<^sub>C f) = cod \<^bsub>C\<^esub> g" using
       struct_0_def_10[THEN iffD1,THEN bspec,THEN bspec,of C "dom \<^bsub>C\<^esub> (g *\<^sub>C f)"]
       struct_0_def_10[THEN iffD1,THEN bspec,THEN bspec,of C "cod \<^bsub>C\<^esub> (g *\<^sub>C f)"]
       by mby auto
   qed simp_all
  have [ty]:"C is reflexive"
   proof
     fix b
     assume [ty]:"b be Object-of C"
     let ?i =  "the Morphism-of C"
     have [ty]:"?i be Morphism-of C" by auto
     have "dom \<^bsub>C\<^esub> ?i = b" "cod \<^bsub>C\<^esub> ?i = b" using
        struct_0_def_10[THEN iffD1,THEN bspec,THEN bspec,of C _ b] by mauto
     hence "?i in Hom\<^bsub>C\<^esub>(b,b)" using cat_1_th_1 by mauto
     thus "Hom\<^bsub>C\<^esub>(b,b) \<noteq> {}" using xb by auto
   qed mauto
  show "C is transitive \<bar>reflexive" by mauto
qed

theorem [rule_format,ty_cond_cluster]:
 "cluster non void-struct\<bar> trivial`-struct \<rightarrow> associative \<bar>with_identities
    for non empty-struct\<bar> non void-struct\<bar> CatStr"
proof-
  fix C
  assume [ty]:"C is non empty-struct\<bar> non void-struct\<bar> CatStr"
              "C is non void-struct\<bar> trivial`-struct"
  have [ty]:"C is associative"
  proof
    fix f g h assume T2[ty]: "f be Morphism-of C" "g be Morphism-of C" "h be Morphism-of C"
    assume "dom \<^bsub>C\<^esub> h = cod \<^bsub>C\<^esub> g " "dom \<^bsub>C\<^esub> g = cod \<^bsub>C\<^esub> f"
    show "h *\<^sub>C (g *\<^sub>C f) = (h *\<^sub>C g) *\<^sub>C f " using
       struct_0_def_21R[THEN iffD1,THEN bspec,THEN bspec,of _ "h *\<^sub>C (g *\<^sub>C f)"]
      apply mby apply auto done
  qed mauto
  have [ty]:"C is with_identities"
  proof
    fix a assume T2[ty]: "a be Object-of C"
    let ?i = "the Morphism-of(a,a,C)"
    have [ty]:"?i be Morphism-of(a,a,C)" by mauto
    show "\<exists>i : Morphism-of (a , a , C). \<forall>b : Object-of C. (Hom\<^bsub>C\<^esub>(a,b)  \<noteq> {} \<longrightarrow> (\<forall>g : Morphism-of (a , b , C).  g *\<^sub>C i = g)) \<and>
                                                         (Hom\<^bsub>C\<^esub>(b,a)  \<noteq> {} \<longrightarrow> (\<forall>f : Morphism-of (b , a , C).  i *\<^sub>C f = f))"
    proof(rule bexI[of _ _ ?i],simp,standard,standard)
       fix b assume [ty]:"b be Object-of C"
       show "(Hom\<^bsub>C\<^esub>(a,b)  \<noteq> {} \<longrightarrow> (\<forall>g : Morphism-of (a , b , C).  g *\<^sub>C ?i = g))"
       proof(standard,standard)
         fix g assume [ty]:"g is Morphism-of (a , b , C)"
         show "g *\<^sub>C ?i = g" using
             struct_0_def_21R[THEN iffD1,THEN bspec,THEN bspec,of _ "g *\<^sub>C ?i"] by mauto
       qed mauto
       show "(Hom\<^bsub>C\<^esub>(b,a)  \<noteq> {} \<longrightarrow> (\<forall>g : Morphism-of (b , a , C).  ?i *\<^sub>C g = g))"
       proof(standard,standard)
         fix g assume [ty]:"g is Morphism-of (b , a , C)"
         show "?i *\<^sub>C g = g" using
             struct_0_def_21R[THEN iffD1,THEN bspec,THEN bspec,of _ g] by mauto
       qed mauto
     qed mauto
   qed mauto
   show "C be associative \<bar>with_identities" by mauto
 qed

theorem [rule_format,ty_func_cluster]:
  "let o be object \<and> m be object
   cluster 1Cat(o,m) \<rightarrow> Category_like"
proof
  let ?C="1Cat(o,m)"
  fix f g assume [ty]: "f be Morphism-of ?C" "g be Morphism-of ?C"
  show "[g,f] in dom the Comp of ?C \<longleftrightarrow> dom \<^bsub>?C\<^esub> g = cod \<^bsub>?C\<^esub> f"
   proof(rule iffI3)
     show "[g,f] in dom the Comp of ?C \<longrightarrow> dom \<^bsub>?C\<^esub> g = cod \<^bsub>?C\<^esub> f"
       using struct_0_def_10[THEN iffD1,THEN bspec,THEN bspec,of _ "dom \<^bsub>?C\<^esub> g"] by mauto
     assume "dom \<^bsub>?C\<^esub> g = cod \<^bsub>?C\<^esub> f"
     have "the Comp of 1Cat(o,m) = ([m,m].\<comment>>m)" using cat_1_def_11 the_selector_of_1[of ?C Comp "[m,m].\<comment>>m"]  Aggr by mauto
     hence
   A1: "dom the Comp of 1Cat(o,m) = {[m,m]}" using funcop_1_th_13 funcop_1_def_9 by mauto
     have "the carrier` of 1Cat(o,m) = {m}" using cat_1_def_11 the_selector_of_1[of ?C "carrier`" "{m}"]  Aggr by mauto
     hence "f in {m} \<and> g in {m}" using Element_of1 by mauto
     hence "f = m" "g = m" using tarski_def_1 by mauto
     thus "[g,f] in dom the Comp of ?C" using A1 tarski_def_1 by mauto
   qed mauto
qed mauto

theorem [ex]:
  "cluster reflexive \<bar>transitive \<bar>associative \<bar>with_identities\<bar>
      Category_like \<bar>non void-struct \<bar>non empty-struct for CatStr"
proof
  show "1Cat(the object,the object) is reflexive \<bar>transitive \<bar>associative \<bar>with_identities\<bar>
      Category_like \<bar>non void-struct \<bar>non empty-struct \<bar> CatStr" by mty auto
qed

abbreviation(input)
  "Category \<equiv> reflexive \<bar>transitive \<bar>associative \<bar>with_identities\<bar>
      Category_like \<bar>non void-struct \<bar>non empty-struct \<bar>CatStr"

reserve C for Category
reserve a,b,c for "Object-of C"
reserve f for "Morphism-of(a,b,C)"
reserve g for "Morphism-of (b,c,C)"

mtheorem cat_1_th_19:
  "Hom\<^bsub>C\<^esub>(a,b)\<noteq>{} \<and> Hom\<^bsub>C\<^esub>(b,c)\<noteq>{} \<longrightarrow> g *\<^sub>C f in Hom\<^bsub>C\<^esub>(a,c)"
proof(standard,auto)
  assume
A1: "Hom\<^bsub>C\<^esub>(a,b)\<noteq>{}" and A2: "Hom\<^bsub>C\<^esub>(b,c)\<noteq>{}"
  have A3:"f in Hom\<^bsub>C\<^esub>(a,b)" using A1 cat_1_def_5e by auto
  hence A4:"cod\<^bsub>C\<^esub>f=b" using cat_1_th_1 by auto
  have A5:"g in Hom\<^bsub>C\<^esub>(b,c)" using A2 cat_1_def_5e by auto
  hence A6: "dom\<^bsub>C\<^esub>g=b" using cat_1_th_1 by auto

  have "cod\<^bsub>C\<^esub>g=c" using A5 cat_1_th_1 by auto
  hence A7: "cod\<^bsub>C\<^esub> (g *\<^sub>C f) = c" using A6 A4 cat_1_def_7E by auto
  have "dom\<^bsub>C\<^esub>f=a" using A3 cat_1_th_1 by auto
  hence "dom\<^bsub>C\<^esub> (g *\<^sub>C f) = a" using A4 A6 cat_1_def_7E by auto
  thus "g *\<^sub>C f in Hom\<^bsub>C\<^esub>(a,c)" using A7 cat_1_th_1 by auto
qed

text_raw {*\DefineSnippet{cat_1_def_13}{*}
func cat_1_def_13   ("_ \<circ>\<^bsub>_,_,_,_\<^esub> _") where
  mlet "C be Category", "a be Object-of C", "b be Object-of C",
       "c be Object-of C", "f be Morphism-of (a,b,C)", "g be Morphism-of (b,c,C)"
  "assume Hom\<^bsub>C\<^esub>(a,b)\<noteq>{} \<and> Hom\<^bsub>C\<^esub>(b,c)\<noteq>{}
  func g \<circ>\<^bsub>C,a,b,c\<^esub> f \<rightarrow> Morphism-of(a,c,C) equals g *\<^sub>C f"
  text_raw {*}%EndSnippet*}
proof-
  assume "Hom\<^bsub>C\<^esub>(a,b)\<noteq>{} \<and> Hom\<^bsub>C\<^esub>(b,c)\<noteq>{}"
  hence E: "g *\<^sub>C f in Hom\<^bsub>C\<^esub>(a,c)" using cat_1_th_19 by mauto
  hence " Hom\<^bsub>C\<^esub>(a,c)\<noteq>{}" using xb by auto
  thus "g *\<^sub>C f is Morphism-of(a,c,C)" using cat_1_def_5i E by auto
qed mauto

end


