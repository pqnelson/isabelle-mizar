theory mizar_struct
imports "../mml/funct_1"
begin

nonterminal "Tys"
syntax
  ""       :: "Ty \<Rightarrow> Tys"  ("_")
  "_Attrs" :: "[Ty, Tys] \<Rightarrow> Tys"  ("_ ; _")
  "_Attr1" :: "Tys \<Rightarrow> Ty"         ("(# _ #)")

translations
  "(# x ; y; z #)"   \<rightharpoonup>  "(# (# x; y #); z #)"
  "(# x; y #)"    \<rightharpoonup>    " x \<bar> y"
  "(# x #)"  \<rightharpoonup> "x"

definition aggr(infixl "\<wrong>" 55) where
  "x \<wrong> y \<equiv> x \<union> y"

definition sel_t( "_ \<mapsto> _") where
  "x \<mapsto> y \<equiv> {[x,y]}"

nonterminal "Sets"
syntax
  ""       :: "Set \<Rightarrow> Sets"  ("_")
  "_Aggrs" :: "[Set, Sets] \<Rightarrow> Sets"  ("_ ; _" [100] 101)
  "_Aggr1" :: "Set \<Rightarrow> Set"         ("[# _ #]")
  "_TupleAggr" :: "[Set, Sets] \<Rightarrow> Ty" ("[# _;/ _ #]")

translations
  "[# x ; y; z #]"   ==  "[# [# x; y #]; z#] "
  "[# x; y #]"    ==    " x\<wrong>y"
  "[# x #]"  \<rightharpoonup> "x"

term "[# x\<mapsto>y #]"

term "[# x\<mapsto>y;w\<mapsto>u #]"
term "[# x\<mapsto>y;w\<mapsto>u;a\<mapsto>b #]"
term "[# x\<mapsto>y;w\<mapsto>u; a\<mapsto>b ; c\<mapsto>d #]"
lemma Aggr1:"[a,b] in X \<Longrightarrow> [a,b] in [# X ; c\<mapsto>d #]"
  using xboole_0_def_3 aggr_def all_set by auto
lemma Aggr2: "[c,d] in [# X ; c\<mapsto>d #]"
  using xboole_0_def_3 tarski_def_1 all_set aggr_def sel_t_def by auto
lemma Aggr3:"[a,b] in [# a\<mapsto>b #]"
  using xboole_0_def_3 tarski_def_1 all_set sel_t_def by auto

lemmas Aggr =Aggr1 Aggr2 Aggr3

text_raw {*\DefineSnippet{theselectorof}{*}
definition TheSelectorOf   ("the _ of _" [100,100] 190) where
   "func the selector of Str \<rightarrow> object means \<lambda>it.
      \<forall>T : object. [selector,T] in Str \<longrightarrow> it = T"
text_raw {*}%EndSnippet*}


text {*
\DefineSnippet{theselectorofdisplay}{
   @{thm [display] TheSelectorOf_def[no_vars]}
}%EndSnippet
*}

definition Struct where
  "Struct \<equiv> Function"

schematic_goal the_selector_of:
  assumes [ty]:"Str be Struct" and A:"selector in dom Str" shows "?X"
proof (induct rule: means_property[OF TheSelectorOf_def,of selector Str, case_names existence uniqueness])
  have [ty]:"Str be Function" using Struct_def by auto
  case existence
    obtain D where
      A1: "D be object" "[selector,D] in Str" using xtuple_0_def_12 A by auto
    show "ex x be object st for T be object st [selector,T] in Str holds x = T"
       proof(rule bexI[of _ _ D],simp,intro ballI)
          fix T
          show "[selector,T] in Str \<longrightarrow> D=T" using funct_1_def_1E A1 by mby auto
       qed simp_all
  case uniqueness
    fix x1 x2
    assume "for T be object st [selector,T] in Str holds x1 = T"
           "for T be object st [selector,T] in Str holds x2 = T"
    thus "x1=x2" using A1 by simp+
qed simp
text {*
\DefineSnippet{the_selector_of_prop}{
   @{thm [display] the_selector_of[no_vars]}
}%EndSnippet
*}

lemma the_selector_of_1:
  assumes[ty]: "Str be Struct" and
         "[selector,D] in Str"
  shows "the selector of Str = D"
proof-
  have [ty]:"Str be Function" using Struct_def by auto
  have "selector in dom Str" using assms(2) xtuple_0_def_12 by auto
  thus ?thesis using the_selector_of assms(2) by auto
qed

lemma the_selector_of_2:
  assumes[ty]: "Str be Struct"
          "Str1 be Struct" and
          "Str \<subseteq> Str1"
          "selector in dom Str"
  shows "the selector of Str = the selector of Str1"
proof-
   have [ty]:"Str be Function" "Str1 be Function" using Struct_def by auto
   obtain D where
    A1:"[selector,D] in Str" using assms(4) xtuple_0_def_12 by auto
   hence "[selector,D] in Str1" using assms(3) tarski_def_3 by simp
   thus ?thesis using the_selector_of_1 A1 by auto
qed


text_raw {*\DefineSnippet{structfield}{*}
definition field (infix "\<rightarrow>" 9) where
   "selector \<rightarrow> spec \<equiv> define_ty(object, \<lambda>_. True,\<lambda>it.
      the selector of it be spec(it) \<and> selector in dom it)"
text_raw {*}%EndSnippet*}



theorem field: "x is (selector \<rightarrow> spec) \<longleftrightarrow>  ((the selector of x) be spec(x) \<and> selector in dom x)"
  using def_ty_property_true field_def by auto

lemmas field_E = field[THEN iffD1,THEN conjunct1]


text_raw {*\DefineSnippet{TheS}{*}
abbreviation TheS   ("the'' _") where
   "TheS \<equiv> \<lambda>selector Str. the selector of Str"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{domainof}{*}
definition domain_of   ("domain'_of _" [100] 100) where
  "func domain_of M \<rightarrow> set means (\<lambda>it.
      (\<exists>X:M. it = dom X) \<and> (\<forall>X : M.  it \<subseteq> dom X))"
text_raw {*}%EndSnippet*}

(*  :: "Ty \<Rightarrow> Ty"  *)
text_raw {*\DefineSnippet{truct_strict}{*}
definition strict where
   "strict(M) \<equiv> define_ty(object,\<lambda>_.True, \<lambda>X. X be M \<and> dom X = domain_of M)"
text_raw {*}%EndSnippet*}
lemmas strict = strict_def[THEN def_ty_property,simplified]

theorem [ty_parent]:
  "X be strict(M) \<Longrightarrow> X be M" using strict[THEN conjunct1] by auto  
  
(*  :: "Set \<Rightarrow> Ty \<Rightarrow> Set" *)
text_raw {*\DefineSnippet{struct_restriction}{*}
definition the_restriction_of   ("the'_restriction'_of _ to _" [95,95] 95) where
   "func the_restriction_of X to Str \<rightarrow> strict(Str) 
      equals X\<restriction>\<^bsub>domain_of Str\<^esub>"
text_raw {*}%EndSnippet*}



lemma Field_1:
assumes [ty]:"Str be Struct" and
        "[selector,D] in Str" and
        [ty]:"D be specification(Str)"
shows "Str is (# selector \<rightarrow> specification #)"
proof-
  have [ty]:"Str be Function" using Struct_def by auto
  have "selector in dom (Str)" using assms(2) xtuple_0_def_12 by auto
  thus "Str is (#selector \<rightarrow> specification#)" using the_selector_of_1 assms(2) field by auto
qed

lemma Field_2:
  assumes "Str be Struct"
          "[selector,D] in Str"
          "Str is (# selector \<rightarrow> specification #)"
  shows "D be specification(Str)"
proof-
   have "the selector of Str = D" using the_selector_of_1 assms(1,2) by simp
  thus ?thesis using assms(3) field by auto
qed

theorem Struct_and_pair:
  assumes "not (selector in dom X)" and
          [ty]:"X be Struct"
  shows "[#X ; selector\<mapsto>S #] be Struct" "dom [#X ; selector\<mapsto>S #] = (dom X) \<union> {selector}"
proof-
  have X[ty]:"X be Function" using Struct_def by auto
  let ?F = "{[selector,S]}"
  have U:"X\<union> ?F = [#X ; selector\<mapsto>S#]" using aggr_def sel_t_def by auto
  have "for x,y1,y2 being object st [x,y1] in X\<union>?F \<and> [x,y2] in X\<union>?F holds y1 = y2"
     proof(intro ballI impI)
       fix x y1 y2
       assume "x be object" "y1 be object" "y2 be object"
       assume A: "[x , y1] in X\<union>?F \<and> [x , y2] in X\<union>?F"
       have A50:"[x,y1] in X \<or> [x , y1] in ?F" using A xboole_0_def_3 by mauto
       have A51:"[x , y2] in X \<or> [x , y2] in ?F" using A xboole_0_def_3 by mauto
       have A5: "[x,y1] in X \<or> [x,y1] =[selector,S]"  "[x,y2] in X \<or> [x,y2] =[selector,S]" using tarski_def_1 A50 A51 by auto
       show "y1 = y2"
       proof(rule disjE[OF A5(1)])
         assume C1:"[x,y1] in X"
           hence "x in dom X" using assms xtuple_0_def_12 by auto
           hence "x \<noteq> selector" using assms by auto
           hence "[x,y2] in X" using xtuple_0_th_1a A5 by mauto
           thus "y1=y2" using C1 assms X by (intro funct_1_def_1E) simp_all
       next
         assume C1:"[x,y1] = [selector,S]"
           hence C2: "x=selector" "y1=S" using xtuple_0_th_1a by auto
           hence "[x,y2] = [selector,S]" using A5 assms xtuple_0_def_12 by auto
           thus "y1=y2" using C2 xtuple_0_th_1a by auto
       qed
     qed simp_all
  hence A: "(X \<union> ?F) is Function_like" using funct_1_def_1 by mauto
  have "(X \<union> ?F) is Relation_like" using relat_1_cl_7 assms relat_1_cl_5[of X ?F] by mauto
  hence "(X \<union> ?F) is Function" using A by mauto
  thus W1: "[#X ; selector\<mapsto>S#] be Struct" using Struct_def U by auto
  have F: "?F be Relation" using relat_1_cl_7 by mauto
  hence "dom (?F) = {selector}" using relat_1_th_3[of S selector ?F] by auto
  hence "dom (X\<union> ?F) = (dom X) \<union> {selector}" using W1 F assms xtuple_th_23[of ?F X] by auto
  thus "dom [#X ; selector\<mapsto>S#] = (dom X) \<union> {selector}" using U by auto
qed

theorem fields_restriction:
  "X be Struct \<Longrightarrow> X is (s\<rightarrow>Typ) \<Longrightarrow> s in D \<Longrightarrow> tyeq(Typ(X),Typ(X|D)) \<Longrightarrow> (X|D) is (s\<rightarrow>Typ)"
proof-
  assume A[ty]:"X be Struct" "X is (s\<rightarrow>Typ)" and B: "s in D" "tyeq(Typ(X),Typ(X|D))"
  have [ty]:"X be Function" using Struct_def by auto
  have "s in dom X" using field A by simp
  then obtain T where
    "T be object" and A1:"[s,T] in X" using A xtuple_0_def_12 by auto
  have [ty]: "T be Typ(X)" using Field_2[OF A(1) A1 A(2)] by auto
  hence [ty]:"T be Typ(X|D)" using B(2) by simp
  have A3[ty]: "D be set" using all_set by auto
  have A4[ty]: "(X|D) be Relation" by mauto
  have A4a: "[s,T] in (X|D)" using relat_1_def_11[of X D] A1 A B by auto
  hence "(X|D) be Function" using funct_1_cl[of D X] A A3 by auto
  thus "(X|D) is (s\<rightarrow>Typ)" using Field_1[of "(X|D)"] A4a Struct_def by auto
qed

theorem the_selector_of_restriction:
 assumes [ty]:"X be Struct" and
         "selector in dom X" "selector in D"
 shows "(the' selector)(X) = (the' selector)(X|D)"
proof-
  have [ty]:"X be Function" using Struct_def by auto
  obtain T where
    "T be object" and A1:"[selector,T] in X" using assms(2) xtuple_0_def_12 by auto
  have [ty]: "D be set" using all_set by auto
  have [ty]: "(X|D) be Relation" using relat_1_def_11_ty[of X D] by auto
  have A4: "[selector,T] in (X|D)" using relat_1_def_11 A1 assms(3) by auto
  have "(X|D) be Function" by mauto
  hence "(X|D) be Struct" using Struct_def by simp
  hence "(the' selector)(X|D) = T" using the_selector_of_1 A4 by simp
  thus ?thesis using the_selector_of_1 A1 by simp
qed

(*  :: "Ty \<Rightarrow> Set \<Rightarrow> o" *)
text_raw {*\DefineSnippet{welldefined}{*}
definition well_defined_prefix (infix "well defined on" 50)
where
  "Fields well defined on D \<equiv>
    (\<exists>\<^sub>L X . X be Fields\<bar>Struct \<and> dom X=D) \<and>
    (\<forall>\<^sub>L X1. X1 be Fields\<bar>Struct \<longrightarrow> D \<subseteq> dom X1 \<and> X1\<restriction>\<^bsub>D\<^esub> be Fields) \<and>
    (\<forall>\<^sub>L X1 X2. X1 be Fields\<bar>Struct \<and>
                       X2 be Struct \<and> D \<subseteq> dom X1 \<and> X1 \<subseteq> X2 \<longrightarrow> X2 be Fields)"
text_raw {*}%EndSnippet*}

theorem First_0_arg_Mode:
  assumes [ex]:"inhabited(M)"
  shows "(#selector \<rightarrow> (\<lambda>S . M)#) well defined on {selector}"
proof(unfold well_defined_prefix_def, intro conjI)
  let ?Spec="\<lambda>S . M"
  obtain S where
    A2[ty]: "S be M" using inhabited_def assms by auto
  let ?F = "{[selector,S]}"
  have [ty]:"?F be Struct" unfolding Struct_def by mauto
  have A3: "?F is (#selector\<rightarrow>?Spec#)" using Field_1[of ?F selector S] tarski_def_1 by auto
  have "dom ?F = {selector}" using relat_1_th_3[of S selector "{[selector,S]}"] by mauto
  thus E:"\<exists>\<^sub>L X . X be (#selector\<rightarrow>?Spec#)\<bar>Struct \<and> dom X= {selector}" using bexI A3 by auto
  show "\<forall>\<^sub>L X1 X2 . X1 be (selector \<rightarrow> ?Spec) \<bar>  Struct \<and> X2 be Struct \<and>
       {selector} \<subseteq> (dom X1) \<and> (X1 \<subseteq> X2) \<longrightarrow> X2 is (selector \<rightarrow> ?Spec)"
  proof(intro allI impI)
    fix X1 X2
    assume B1: "X1 be (selector \<rightarrow> ?Spec)  \<bar>  Struct \<and>
                X2 be Struct \<and>
                {selector} \<subseteq> dom X1 \<and> X1 \<subseteq> X2"
       have B[ty]:"X1 be Function" "X2 be Function" using Struct_def B1 by auto
     have B5: "the selector of X1 be ?Spec(X2)" using field B1 by auto
     have B6: "dom X1 \<subseteq> dom X2" using xtuple_0_th_8[of X2 X1] B1 by auto
     have B70: "selector in dom X1" using B1 tarski_def_1 tarski_def_3 by mauto
     hence B7a: "the selector of X1 = the selector of X2"
       using B6 B1 tarski_def_3 by (intro the_selector_of_2[of X1 X2 selector]) mauto
     have B7b: "selector in dom X2" using B6 B1 tarski_def_3 B70 by mauto
     thus "X2 is (#selector \<rightarrow>?Spec#)" using B7a B5 field by auto
   qed
  show "\<forall>\<^sub>L X1. X1 be (#selector \<rightarrow>?Spec#)\<bar>Struct \<longrightarrow> {selector} \<subseteq> dom X1 \<and> X1| {selector} is (#selector \<rightarrow>?Spec#)"
  proof(intro allI impI conjI)
    fix X1 assume C1[ty]: "X1 be (#selector \<rightarrow>?Spec#)\<bar>Struct"
       have B[ty]:"X1 be Function" using Struct_def by auto
    have "selector in dom X1" using field C1 by auto
    thus "{selector} \<subseteq> dom X1" using tarski_def_1 tarski_def_3 by mauto
    have "X1| {selector} is (#selector \<rightarrow>?Spec#)" using fields_restriction[of X1 "selector" "?Spec" "{selector}"]
       tarski_def_1 by auto
    thus "X1| ({selector}) is (#selector \<rightarrow>?Spec#)" by simp
  qed
qed

text_raw {*\DefineSnippet{WellAddM0}{*}
theorem Fields_add_0_arg_Mode:
  assumes "Fields well defined on D"
          "not (selector in D)"
          "inhabited(M)"
  shows "Fields\<bar> (selector \<rightarrow> (\<lambda>S . M)) well defined on D\<union>{selector}"
text_raw {*}%EndSnippet*}
proof(unfold well_defined_prefix_def,intro conjI)
  have
   I0:"\<exists>\<^sub>L X . X be Fields\<bar>Struct \<and> dom X=D" and
   I1[rule_format]:"\<forall>\<^sub>L X1. X1 be Fields\<bar>Struct \<longrightarrow> D \<subseteq> dom X1 \<and> X1|D is Fields"and
   I2[rule_format]: "\<forall>\<^sub>L X1 X2. X1 be Fields\<bar>Struct \<and>  X2 be Struct \<and> D \<subseteq> dom X1 \<and> X1 \<subseteq> X2
       \<longrightarrow> X2 is Fields" using well_defined_prefix_def[of Fields D] assms(1) by auto
  let ?Spec="\<lambda>S . M"
  obtain X where
    T1[ty]: "X be Fields\<bar>Struct" and A1: "dom X=D" using I0(1) by auto
   have B[ty]:"X be Function" using Struct_def by auto
  obtain S where
    A2[ty]: "S be M" using assms inhabited_def by auto
  let ?F = "selector\<mapsto>S"
  show "\<exists>\<^sub>L X . (X be Fields\<bar>(selector\<rightarrow>?Spec)\<bar>Struct \<and> (dom X)=D\<union>{selector})"
  proof(intro exI conjI)
    have A3: "(X \<wrong> ?F) be Struct" "dom (X \<wrong> ?F) = (dom X) \<union> {selector}"
           using assms(2) A1 Struct_and_pair[of selector X] by auto
         have "X \<subseteq> X \<wrong> ?F" "D c= dom X" unfolding aggr_def
             using A1 tarski_def_3 xboole_0_def_3 all_set by auto
      hence A4: "(X \<wrong> ?F) is Fields" using A3 I2[of X "X \<wrong> ?F"]  by auto
      have A5: "S be ?Spec(X \<wrong>?F)" "[selector,S] in (X\<wrong>?F)"
          using A2 tarski_def_1 xboole_0_def_3 by (auto simp add:Aggr)
      have "(X \<wrong>?F) is (#selector \<rightarrow>?Spec#)" using Field_1 A3 A5 by auto
     thus "(X \<wrong> ?F) is Fields\<bar>(selector\<rightarrow>?Spec)\<bar>Struct"
           "dom (X \<wrong> ?F) = (D \<union> {selector})" using A4 A1 A3 by auto
    qed
  show "\<forall>\<^sub>L X1 X2. X1 be Fields \<bar>  (selector \<rightarrow> ?Spec)  \<bar>  Struct \<and> X2 be Struct \<and>
       (D\<union>{selector}) \<subseteq> (dom X1) \<and> (X1 \<subseteq> X2) \<longrightarrow> X2 is Fields \<bar>  (selector \<rightarrow> ?Spec)"
  proof(intro allI,rule impI)
    fix X1 X2
    assume B1: "X1 be Fields \<bar>  (selector \<rightarrow> ?Spec)  \<bar>  Struct \<and> X2 be Struct\<and> D \<union> {selector} \<subseteq> dom X1 \<and> X1 \<subseteq> X2"
    have B[ty]:"X1 be Function" "X2 be Function" using Struct_def B1 by auto
    have "D c= dom X1" using xboole_0_def_3 tarski_def_3 B1 all_set by auto
    hence B7: "X2 is Fields" using I2[rule_format,of X1 X2] B1 by auto
    have B5: "the selector of X1 be ?Spec(X2)" using B1 field by auto
    have B6: "dom X1 \<subseteq> dom X2" using xtuple_0_th_8[of X2 X1] B1 by auto
    have "selector in dom X1" using B1 tarski_def_1 xboole_0_def_3 tarski_def_3 all_set by auto
    hence "the selector of X1 = the selector of X2" "selector in dom X2"
        using B6 the_selector_of_2[of X1 X2 selector] B1 xboole_0_def_10 all_set tarski_def_3 by auto
    thus "X2 is Fields\<bar>(#selector \<rightarrow>?Spec#)" using B5 field B7 by auto
  qed

  show "\<forall>\<^sub>L X1. X1 be Fields\<bar>(#selector \<rightarrow>?Spec#)\<bar>Struct \<longrightarrow> D\<union>{selector} \<subseteq> dom X1 \<and> X1|(D\<union>{selector}) is Fields\<bar>(#selector \<rightarrow>?Spec#)"
  proof(intro allI impI conjI)
    fix X1 assume C1[ty]: "X1 be Fields\<bar>(#selector \<rightarrow>?Spec#)\<bar>Struct"
       have B[ty]:"X1 be Function" using Struct_def by auto
    have C5: "D \<subseteq> dom X1" using I1 C1 by auto
    have "selector in dom X1" using field C1 by auto
    thus "D\<union>{selector} \<subseteq> dom X1" using C5 tarski_def_1 xboole_0_def_3 tarski_def_3 all_set by auto
    hence T0:"X1 be Relation" by simp
    hence T1: "X1|(D\<union>{selector}) be Relation" "X1|D be Relation"
      using relat_1_def_11_ty[of X1 D] relat_1_def_11_ty[of X1 "D\<union>{selector}"] all_set by auto
    hence T2: "X1| (D\<union>{selector}) is Function_like"
      using funct_1_cl[of "D\<union>{selector}" X1,rule_format,OF all_set] C1 by auto
    hence "X1| D is Function_like"
       using funct_1_cl[of D X1,rule_format,OF all_set] C1 by auto
    hence C2: "X1| (D\<union>{selector}) be Struct" "X1|D be Struct"
       unfolding Struct_def using T2 T1 by auto
    have C3:"X1|D be Fields\<bar>Struct" using I1 C1 C2 C5 by auto
    have "dom (X1|D) = (dom X1)\<inter> D" using relat_1_th_55 T0 all_set by auto
    hence C4: "D \<subseteq> dom (X1|D)" using C5 all_set xboole_0_def_4 tarski_def_3 by auto
    have "X1|D \<subseteq> X1| (D\<union>{selector})" using relat_1_th75[of X1 "D\<union>{selector}" D] C1 xboole_0_def_3 tarski_def_3 all_set by auto
    hence C6: "X1| (D\<union>{selector}) is Fields" using C2 C3 I2[rule_format, OF C3 C2(1) C4] C4 by auto
    have "X1| (D\<union>{selector}) is (#selector \<rightarrow>?Spec#)" using fields_restriction[of X1 "selector" "?Spec" "D\<union>{selector}"]
       C1 tarski_def_1 xboole_0_def_3 all_set by auto
    thus "X1| (D\<union>{selector}) is Fields\<bar>(#selector \<rightarrow>?Spec#)" using C6 by simp
  qed

qed

text_raw {*\DefineSnippet{WellAddM1}{*}
theorem Fields_add_argM1:
assumes "Fields well defined on D"
 and "selector_1 in D"
 and "not (selector in D)"
 and "\<And> X1 . X1 be Fields\<bar>Struct \<Longrightarrow>
           inhabited (M1(the selector_1 of X1))"
shows
 "Fields \<bar> (selector \<rightarrow> (\<lambda>S. M1 (the selector_1 of S)))
         well defined on D \<union> {selector}"
text_raw {*}%EndSnippet*}
proof(unfold well_defined_prefix_def,intro conjI)
  have
   I0:"\<exists>\<^sub>L X . X be Fields\<bar>Struct \<and> dom X=D" and
   I1[rule_format]:"\<forall>\<^sub>L X1. X1 be Fields\<bar>Struct \<longrightarrow> D \<subseteq> dom X1 \<and> X1|D is Fields"and
   I2[rule_format]: "\<forall>\<^sub>L X1 X2. X1 be Fields\<bar>Struct \<and>  X2 be Struct \<and> D \<subseteq> dom X1 \<and> X1 \<subseteq> X2
       \<longrightarrow> X2 is Fields" using well_defined_prefix_def[of Fields D] assms(1) by auto
  let ?Spec="\<lambda>S . M1 (the selector_1 of S)"
  obtain X where
    [ty]: "X be Fields\<bar>Struct" and DD: "dom X=D" using I0 by blast
   have B[ty]:"X be Function" using Struct_def by auto
  obtain S where
    A2[ty]: "S be M1 (the selector_1 of X)" and "True" using assms(4)[of X] inhabited_def by auto
  let ?F = "selector\<mapsto>S"
  show "\<exists>\<^sub>L X . (X be Fields\<bar>(selector\<rightarrow>?Spec)\<bar>Struct \<and> (dom X)=D\<union>{selector})"
  proof(intro exI conjI)
     have A3: "(X \<wrong> ?F) be Struct" "dom (X \<wrong>?F) = (dom X) \<union> {selector}"
           using assms(3) DD Struct_and_pair[of selector X] by auto
         have X1: "X \<subseteq> X \<wrong> ?F" unfolding aggr_def using xboole_0_def_3[of X "selector \<mapsto> S"] all_set by (intro tarski_def_3b) auto
        have "proj1 X is set" by mauto
        hence [ty]: "D is set" using DD by simp
        have X2: "D c= dom X" using xboole_0_def_10[THEN iffD1,OF _ _ DD] DD by auto
      hence A4: "(X \<wrong>?F) is Fields" using A3 I2[of X "X \<wrong> ?F"]  aggr_def sel_t_def X1 by auto
      have "(the selector_1 of X)= (the selector_1 of (X\<wrong>?F))" using I1[of "X \<wrong>?F"]
           the_selector_of_2[of X "X \<wrong> ?F" "selector_1"] A3 DD X1 X2 assms(2)  aggr_def by auto
      hence A5: "S be ?Spec(X\<wrong>?F)" "[selector,S] in (X\<wrong>?F)"
            using A2 by (auto simp add:Aggr)
      have "(X\<wrong>?F) is (#selector \<rightarrow>?Spec#)" using Field_1 A3 A5 by auto
     thus "(X \<wrong>?F) is Fields\<bar>(selector\<rightarrow>?Spec)\<bar>Struct"
           "dom (X\<wrong> ?F) = (D \<union> {selector})" using A4 DD A3 by auto
       have "[selector,S] in (X\<wrong>?F)" by (auto simp add:Aggr)
   qed
  show "\<forall>\<^sub>L X1 X2. X1 be Fields \<bar>  (selector \<rightarrow> ?Spec)  \<bar>  Struct \<and> X2 be Struct \<and>
       (D\<union>{selector}) \<subseteq> (dom X1) \<and> (X1 \<subseteq> X2) \<longrightarrow> X2 is Fields \<bar>  (selector \<rightarrow> ?Spec)"
  proof(intro allI,rule impI,elim conjE)
    fix X1 X2
    assume B1t[ty]: "X1 be Fields \<bar>  (selector \<rightarrow> ?Spec)  \<bar>  Struct" "X2 be Struct"
      and B1: "D \<union> {selector} \<subseteq> dom X1" "X1 \<subseteq> X2"
    have [ty]:"X1 be Function" "X2 be Function" using Struct_def by auto
    have D:"D c= dom X1" using xboole_0_def_3 tarski_def_3 B1 all_set by auto
    hence B7: "X2 is Fields" using I2[rule_format,of X1 X2] B1 by auto
    have "selector_1 in dom X1" using D assms tarski_def_3 all_set by auto
    hence "the selector_1 of X1= the selector_1 of (X2)" using the_selector_of_2[of X1 X2 ] B1 by auto
    hence B5: "the selector of X1 be ?Spec(X2)" using B1 B1t field by auto
    have B6: "dom X1 \<subseteq> dom X2" using xtuple_0_th_8[of X2 X1] B1 by auto
    have "selector in dom X1" using B1 tarski_def_1 xboole_0_def_3 tarski_def_3 all_set by auto
    hence "the selector of X1 = the selector of X2" "selector in dom X2"
        using B6 the_selector_of_2[of X1 X2 selector] B1 xboole_0_def_10 all_set tarski_def_3 by auto
    thus "X2 is Fields\<bar>(#selector \<rightarrow>?Spec#)" using B5 field B7 by auto
  qed
      show "\<forall>\<^sub>L X1. X1 be Fields\<bar>(#selector \<rightarrow>?Spec#)\<bar>Struct \<longrightarrow> D\<union>{selector} \<subseteq> dom X1 \<and> X1|(D\<union>{selector}) is Fields\<bar>(#selector \<rightarrow>?Spec#)"
  proof(intro allI impI conjI)
    fix X1 assume C1[ty]: "X1 be Fields\<bar>(#selector \<rightarrow>?Spec#)\<bar>Struct"
      have [ty]:"X1 be Function" using Struct_def by auto
    have C5: "D \<subseteq> dom X1" using I1 C1 by auto
    have "selector in dom X1" using field C1 by auto
    thus "D\<union>{selector} \<subseteq> dom X1" using C5 tarski_def_1 xboole_0_def_3 tarski_def_3 all_set by auto
    hence T0:"X1 be Relation" by simp
    hence T1: "X1|(D\<union>{selector}) be Relation" "X1|D be Relation"
      using relat_1_def_11_ty[of X1 D] relat_1_def_11_ty[of X1 "D\<union>{selector}"] all_set by auto
    hence T2: "X1| (D\<union>{selector}) is Function_like"
      using funct_1_cl[of "D\<union>{selector}" X1,rule_format,OF all_set] C1 by auto
    hence "X1| D is Function_like"
       using funct_1_cl[of D X1,rule_format,OF all_set] C1 by auto
    hence C2: "X1| (D\<union>{selector}) be Struct" "X1|D be Struct"
       unfolding Struct_def using T2 T1 by auto
    have C3:"X1|D be Fields\<bar>Struct" using I1 C1 C2 C5 by auto
    have "dom (X1|D) = (dom X1)\<inter> D" using relat_1_th_55 T0 all_set by auto
    hence C4: "D \<subseteq> dom (X1|D)" using C5 all_set xboole_0_def_4 tarski_def_3 by auto
    have "X1|D \<subseteq> X1| (D\<union>{selector})" using relat_1_th75[of X1 "D\<union>{selector}" D] C1 xboole_0_def_3 tarski_def_3 all_set by auto
    hence C6: "X1| (D\<union>{selector}) is Fields" using C2 C3 I2[rule_format, OF C3 C2(1) C4] C4 by auto

      have X:"selector in D \<union> {selector}" using tarski_def_1 xboole_0_def_3 all_set by auto
     have "selector_1 in dom X1" "selector_1 in (D\<union>{selector})" using assms(2) C5 tarski_def_3 xboole_0_def_3 all_set by auto
     hence TS: "the selector_1 of X1 = the selector_1 of (X1|(D \<union> {selector}))"
      using C1 the_selector_of_restriction[of X1 selector_1 "D\<union>{selector}"] by auto
    hence "X1| (D\<union>{selector}) is (#selector \<rightarrow>?Spec#)" using fields_restriction[of X1 "selector" "?Spec" "D\<union>{selector}",OF ]
       C1 tarski_def_1 X all_set by auto
        have "X1| (D\<union>{selector}) is (#selector \<rightarrow>?Spec#)" using
     fields_restriction[of X1 "selector" "?Spec" "D\<union>{selector}"]
       C1 tarski_def_1 xboole_0_def_3 all_set TS by auto
    thus "X1| (D\<union>{selector}) is Fields\<bar>(#selector \<rightarrow>?Spec#)" using C6 by simp
  qed
qed

text_raw {*\DefineSnippet{WellAddM2}{*}
theorem Fields_add_2_arg_Mode:
  assumes "Fields well defined on D"
          "selector_1 in D"
          "selector_2 in D"
          "not (selector in D)"
           and "\<And> X1 . X1 be Fields\<bar>Struct \<Longrightarrow>
           inhabited (M1(the selector_1 of X1,the selector_2 of X1))"
  shows "Fields\<bar> (selector \<rightarrow> (\<lambda>S . M1 (the selector_1 of S,the selector_2 of S))) well defined on D\<union>{selector}"
text_raw {*}%EndSnippet*}
proof(unfold well_defined_prefix_def,intro conjI)
  have
   I0:"\<exists>\<^sub>L X . X be Fields\<bar>Struct \<and> dom X=D" and
   I1[rule_format]:"\<forall>\<^sub>L X1. X1 be Fields\<bar>Struct \<longrightarrow> D \<subseteq> dom X1 \<and> X1|D is Fields"and
   I2[rule_format]: "\<forall>\<^sub>L X1 X2. X1 be Fields\<bar>Struct \<and>  X2 be Struct \<and> D \<subseteq> dom X1 \<and> X1 \<subseteq> X2
       \<longrightarrow> X2 is Fields" using well_defined_prefix_def[of Fields D] assms(1) by auto
  let ?Spec="\<lambda>S . M1 (the selector_1 of S,the selector_2 of S)"

  obtain X where
    A1[ty]: "X be Fields\<bar>Struct" and DD: "dom X=D" using I0 by blast
   have [ty]:"X be Function" using Struct_def by auto
  obtain S where
    A2: "S be M1 (the selector_1 of X,the selector_2 of X)" using assms(5)[of X] inhabited_def by auto
  let ?F = "selector\<mapsto>S"
   show "\<exists>\<^sub>L X . (X be Fields\<bar>(selector\<rightarrow>?Spec)\<bar>Struct \<and> (dom X)=D\<union>{selector})"
  proof(intro exI conjI)
     have A3: "(X \<wrong>?F) be Struct" "dom (X \<wrong>?F) = (dom X) \<union> {selector}"
       using assms(4) DD Struct_and_pair[of selector X] aggr_def sel_t_def by auto
        have "(proj1 X) is set" by mauto
        hence [ty]: "D is set" using DD by simp
        have X1: "X \<subseteq> X \<wrong> ?F" unfolding aggr_def using xboole_0_def_3[of X "selector \<mapsto> S"] all_set by (intro tarski_def_3b) auto
        have X2: "D c= dom X" using xboole_0_def_10[THEN iffD1,OF _ _ DD] DD by auto
      hence A4: "(X \<wrong>?F) is Fields" using A3 I2[of X "X \<wrong> ?F"] aggr_def sel_t_def using X1 by auto
      have "(the selector_1 of X)= (the selector_1 of (X\<wrong>?F))"
           "(the selector_2 of X)= (the selector_2 of (X\<wrong>?F))"
           using I1[of "X \<wrong>?F"]
           the_selector_of_2[of X "X \<wrong> ?F" selector_1]
           the_selector_of_2[of X "X \<wrong> ?F" selector_2] A3 DD X1 X2 assms(2,3) aggr_def sel_t_def by auto
      hence A5: "S be ?Spec(X\<wrong>?F)" "[selector,S] in (X\<wrong>?F)"
            using A2 by (auto simp add:Aggr)
      have "(X\<wrong>?F) is (#selector \<rightarrow>?Spec#)" using Field_1 A3 A5 by auto
      thus "(X \<wrong>?F) is Fields\<bar>(selector\<rightarrow>?Spec)\<bar>Struct"
           "dom (X \<wrong> ?F) = (D \<union> {selector})" using A4 DD A3 by auto
   qed
  show "\<forall>\<^sub>L X1 X2. X1 be Fields \<bar>  (selector \<rightarrow> ?Spec)  \<bar>  Struct \<and> X2 be Struct \<and>
       (D\<union>{selector}) \<subseteq> (dom X1) \<and> (X1 \<subseteq> X2) \<longrightarrow> X2 is Fields \<bar>  (selector \<rightarrow> ?Spec)"
  proof(intro allI,rule impI,elim conjE)
    fix X1 X2
    assume B1t[ty]: "X1 be Fields \<bar>  (selector \<rightarrow> ?Spec)  \<bar>  Struct" "X2 be Struct"
       and B1: "D \<union> {selector} \<subseteq> dom X1" "X1 \<subseteq> X2"
    have [ty]:"X1 be Function" "X2 be Function" using Struct_def by auto
    have D:"D c= dom X1" using xboole_0_def_3 tarski_def_3 B1 all_set by auto
    hence B7: "X2 is Fields" using I2[rule_format,of X1 X2] B1 by auto
    have "selector_1 in dom X1" "selector_2 in dom X1" using D assms tarski_def_3 all_set by auto
    hence "the selector_1 of X1= the selector_1 of (X2)"
          "the selector_2 of X1= the selector_2 of (X2)" using the_selector_of_2[of X1 X2 ] B1 by auto
    hence B5: "the selector of X1 be ?Spec(X2)" using B1 B1t field by auto
    have B6: "dom X1 \<subseteq> dom X2" using xtuple_0_th_8[of X2 X1] B1 by auto
    have "selector in dom X1" using B1 tarski_def_1 xboole_0_def_3 tarski_def_3 all_set by auto
    hence "the selector of X1 = the selector of X2" "selector in dom X2"
        using B6 the_selector_of_2[of X1 X2 selector] B1 xboole_0_def_10 all_set tarski_def_3 by auto
    thus "X2 is Fields\<bar>(#selector \<rightarrow>?Spec#)" using B5 field B7 by auto
  qed
 show "\<forall>\<^sub>L X1. X1 be Fields\<bar>(#selector \<rightarrow>?Spec#)\<bar>Struct \<longrightarrow> D\<union>{selector} \<subseteq> dom X1 \<and> X1|(D\<union>{selector}) is Fields\<bar>(#selector \<rightarrow>?Spec#)"
  proof(intro allI impI conjI)
    fix X1 assume C1[ty]: "X1 be Fields\<bar>(#selector \<rightarrow>?Spec#)\<bar>Struct"
      have [ty]:"X1 be Function" using Struct_def by auto
    have C5: "D \<subseteq> dom X1" using I1 C1 by auto
    have "selector in dom X1" using field C1 by auto
    thus "D\<union>{selector} \<subseteq> dom X1" using C5 tarski_def_1 xboole_0_def_3 tarski_def_3 all_set by auto
    hence T0:"X1 be Relation" by simp
    hence T1: "X1|(D\<union>{selector}) be Relation" "X1|D be Relation"
      using relat_1_def_11_ty[of X1 D] relat_1_def_11_ty[of X1 "D\<union>{selector}"] all_set by auto
    hence T2: "X1| (D\<union>{selector}) is Function_like"
      using funct_1_cl[of "D\<union>{selector}" X1,rule_format,OF all_set] C1 by auto
    hence "X1| D is Function_like"
       using funct_1_cl[of D X1,rule_format,OF all_set] C1 by auto
    hence C2: "X1| (D\<union>{selector}) be Struct" "X1|D be Struct"
       unfolding Struct_def using T2 T1 by auto
    have C3:"X1|D be Fields\<bar>Struct" using I1 C1 C2 C5 by auto
    have "dom (X1|D) = (dom X1)\<inter> D" using relat_1_th_55 T0 all_set by auto
    hence C4: "D \<subseteq> dom (X1|D)" using C5 all_set xboole_0_def_4 tarski_def_3 by auto
    have "X1|D \<subseteq> X1| (D\<union>{selector})" using relat_1_th75[of X1 "D\<union>{selector}" D] C1 xboole_0_def_3 tarski_def_3 all_set by auto
    hence C6: "X1| (D\<union>{selector}) is Fields" using C2 C3 I2[rule_format, OF C3 C2(1) C4] C4 by auto

      have X:"selector in D \<union> {selector}" using tarski_def_1 xboole_0_def_3 all_set by auto
      have "selector_1 in dom X1" "selector_1 in (D\<union>{selector})"
           "selector_2 in dom X1" "selector_2 in (D\<union>{selector})" using assms(2,3) C5 tarski_def_3 xboole_0_def_3 all_set by auto
     hence TS: "the selector_1 of X1 = the selector_1 of (X1|(D \<union> {selector}))"
               "the selector_2 of X1 = the selector_2 of (X1|(D \<union> {selector}))"
       using C1 the_selector_of_restriction[of X1 selector_1 "D\<union>{selector}"]
                the_selector_of_restriction[of X1 selector_2 "D\<union>{selector}"]  by auto
    hence "X1| (D\<union>{selector}) is (#selector \<rightarrow>?Spec#)" using fields_restriction[of X1 "selector" "?Spec" "D\<union>{selector}",OF ]
       C1 tarski_def_1 X all_set by auto
        have "X1| (D\<union>{selector}) is (#selector \<rightarrow>?Spec#)" using
     fields_restriction[of X1 "selector" "?Spec" "D\<union>{selector}"]
       C1 tarski_def_1 xboole_0_def_3 all_set TS by auto
    thus "X1| (D\<union>{selector}) is Fields\<bar>(#selector \<rightarrow>?Spec#)" using C6 by simp
  qed
qed
text_raw {*\DefineSnippet{WellAddM3}{*}
theorem Fields_add_3_arg_Mode:
  assumes "Fields well defined on D"
        "sel_1 in D"    "sel_2 in D"    "sel_3 in D"    "\<not> sel in D"
     and "\<And>X1. X1 be Fields\<bar>Struct \<Longrightarrow>
        inhabited (M1(the sel_1 of X1, the sel_2 of X1, the sel_3 of X1))"
  shows "Fields \<bar> (sel \<rightarrow> (\<lambda>S. M1 (the sel_1 of S, the sel_2 of S, the sel_3 of S)))
        well defined on D \<union> {sel}"
text_raw {*}%EndSnippet*}
proof(unfold well_defined_prefix_def,intro conjI)
  have
   I0:"\<exists>\<^sub>L X . X be Fields\<bar>Struct \<and> dom X=D" and
   I1[rule_format]:"\<forall>\<^sub>L X1. X1 be Fields\<bar>Struct \<longrightarrow> D \<subseteq> dom X1 \<and> X1|D is Fields"and
   I2[rule_format]: "\<forall>\<^sub>L X1 X2. X1 be Fields\<bar>Struct \<and>  X2 be Struct \<and> D \<subseteq> dom X1 \<and> X1 \<subseteq> X2
       \<longrightarrow> X2 is Fields" using well_defined_prefix_def[of Fields D] assms(1) by auto
  let ?Spec="\<lambda>S . M1 (the sel_1 of S,the sel_2 of S,the sel_3 of S)"

  obtain X where
    A1[ty]: "X be Fields\<bar>Struct" and AA: "dom X=D" using I0 by blast
      have [ty]:"X be Function" using Struct_def by auto
  have B1:"X is Function_like" using A1 by simp
  obtain S where
    A2: "S be M1 (the sel_1 of X,the sel_2 of X,the sel_3 of X)" using assms(6)[of X] inhabited_def by auto
  let ?F = "sel\<mapsto>S"
  show "\<exists>\<^sub>L X . (X be Fields\<bar>(sel\<rightarrow>?Spec)\<bar>Struct \<and> (dom X)=D\<union>{sel})"
  proof(intro exI conjI)
     have A3: "(X \<wrong>?F) be Struct" "dom (X \<wrong>?F) = (dom X) \<union> {sel}"
           using assms(5) A1 Struct_and_pair[of sel X] AA by auto
      have X: "X \<subseteq> X \<wrong> ?F"  "D c= dom X" using A1 tarski_def_3b xboole_0_def_3 all_set AA xboole_0_def_10 aggr_def sel_t_def by auto
      hence A4: "(X \<wrong>?F) is Fields" using A3 I2[of X "X \<wrong> ?F"]  by auto
      have "(the sel_1 of X)= (the sel_1 of (X\<wrong>?F))"
           "(the sel_2 of X)= (the sel_2 of (X\<wrong>?F))"
           "(the sel_3 of X)= (the sel_3 of (X\<wrong>?F))"
           using I1[of "X \<union>?F"]
           the_selector_of_2[of X "X \<wrong> ?F" ] A3 AA X assms(2,3,4) by auto+
      hence A5: "S be ?Spec(X\<wrong>?F)" "[sel,S] in (X\<wrong>?F)"
            using A2 tarski_def_1 xboole_0_def_3 Aggr by auto
      have "(X\<wrong>?F) is (#sel \<rightarrow>?Spec#)" using Field_1 A3 A5 by auto
     thus "(X \<wrong>?F) is Fields\<bar>(sel\<rightarrow>?Spec)\<bar>Struct"
           "dom (X \<wrong> ?F) = (D \<union> {sel})" using A4 AA A3 by auto
   qed
  show "\<forall>\<^sub>L X1 X2. X1 be Fields \<bar>  (sel \<rightarrow> ?Spec)  \<bar>  Struct \<and> X2 be Struct \<and>
       (D\<union>{sel}) \<subseteq> (dom X1) \<and> (X1 \<subseteq> X2) \<longrightarrow> X2 is Fields \<bar>  (sel \<rightarrow> ?Spec)"
  proof(intro allI,rule impI,elim conjE)
    fix X1 X2
    assume B0[ty]: "X1 be Fields \<bar>  (sel \<rightarrow> ?Spec)  \<bar>  Struct" "X2 be Struct"
       and B1: "D \<union> {sel} \<subseteq> dom X1" "X1 \<subseteq> X2"
   have [ty]:"X1 be Function" "X2 be Function" using Struct_def by auto
    have D:"D c= dom X1" using xboole_0_def_3 tarski_def_3 B1 all_set by auto
    hence B7: "X2 is Fields" using I2[rule_format,of X1 X2] B1 by auto
    have "sel_1 in dom X1" "sel_2 in dom X1" "sel_3 in dom X1" using D assms tarski_def_3 all_set by auto
    hence "the sel_1 of X1= the sel_1 of (X2)"
          "the sel_2 of X1= the sel_2 of (X2)"
          "the sel_3 of X1= the sel_3 of (X2)" using the_selector_of_2[of X1 X2 ] B1 by auto
    hence B5: "the sel of X1 be ?Spec(X2)" using B0 B1 field by auto
    have B6: "dom X1 \<subseteq> dom X2" using xtuple_0_th_8[of X2 X1] B1 by auto
    have "sel in dom X1" using B1 tarski_def_1 xboole_0_def_3 tarski_def_3 all_set by auto
    hence "the sel of X1 = the sel of X2" "sel in dom X2"
        using B6 the_selector_of_2[of X1 X2 sel] B1 xboole_0_def_10 all_set tarski_def_3 by auto
    thus "X2 is Fields\<bar>(#sel \<rightarrow>?Spec#)" using B5 field B7 by auto
  qed
 show "\<forall>\<^sub>L X1. X1 be Fields\<bar>(#sel \<rightarrow>?Spec#)\<bar>Struct \<longrightarrow> D\<union>{sel} \<subseteq> dom X1 \<and> X1|(D\<union>{sel}) is Fields\<bar>(#sel \<rightarrow>?Spec#)"
  proof(intro allI impI conjI)
    fix X1 assume C1[ty]: "X1 be Fields\<bar>(#sel \<rightarrow>?Spec#)\<bar>Struct"
      have [ty]:"X1 be Function" using Struct_def by auto
    have C5: "D \<subseteq> dom X1" using I1 C1 by auto
    have "sel in dom X1" using field C1 by auto
    thus "D\<union>{sel} \<subseteq> dom X1" using C5 tarski_def_1 xboole_0_def_3 tarski_def_3 all_set by auto
    hence T0:"X1 be Relation" by simp
    hence T1: "X1|(D\<union>{sel}) be Relation" "X1|D be Relation"
      using relat_1_def_11_ty[of X1] all_set by mty auto
    hence T2: "X1| (D\<union>{sel}) is Function_like"
      using funct_1_cl[of "D\<union>{sel}" X1,rule_format,OF all_set] C1 by auto
    hence "X1| D is Function_like"
       using funct_1_cl[of D X1,rule_format,OF all_set] C1 by auto
    hence C2: "X1| (D\<union>{sel}) be Struct" "X1|D be Struct"
       unfolding Struct_def using T2 T1 by auto
    have C3:"X1|D be Fields\<bar>Struct" using I1 C1 C2 C5 by auto
    have "dom (X1|D) = (dom X1)\<inter> D" using relat_1_th_55 T0 all_set by auto
    hence C4: "D \<subseteq> dom (X1|D)" using C5 all_set xboole_0_def_4 tarski_def_3 by auto
    have "X1|D \<subseteq> X1| (D\<union>{sel})" using relat_1_th75[of X1 "D\<union>{sel}" D] C1 xboole_0_def_3 tarski_def_3 all_set by auto
    hence C6: "X1| (D\<union>{sel}) is Fields" using C2 C3 I2[rule_format, OF C3 C2(1) C4] C4 by auto

      have X:"sel in D \<union> {sel}" using tarski_def_1 xboole_0_def_3 all_set by auto
      have "sel_1 in dom X1" "sel_1 in (D\<union>{sel})"
           "sel_2 in dom X1" "sel_2 in (D\<union>{sel})"
           "sel_3 in dom X1" "sel_3 in (D\<union>{sel})" using assms(2,3,4) C5 tarski_def_3 xboole_0_def_3 all_set by auto
     hence TS: "the sel_1 of X1 = the sel_1 of (X1|(D \<union> {sel}))"
               "the sel_2 of X1 = the sel_2 of (X1|(D \<union> {sel}))"
               "the sel_3 of X1 = the sel_3 of (X1|(D \<union> {sel}))"
       using C1 the_selector_of_restriction[of X1 sel_1 "D\<union>{sel}"]
                the_selector_of_restriction[of X1 sel_2 "D\<union>{sel}"]
                the_selector_of_restriction[of X1 sel_3 "D\<union>{sel}"] by auto
    hence "X1| (D\<union>{sel}) is (#sel \<rightarrow>?Spec#)" using fields_restriction[of X1 "sel" "?Spec" "D\<union>{sel}",OF ]
       C1 tarski_def_1 X all_set by auto
        have "X1| (D\<union>{sel}) is (#sel \<rightarrow>?Spec#)" using
     fields_restriction[of X1 "sel" "?Spec" "D\<union>{sel}"]
       C1 tarski_def_1 xboole_0_def_3 all_set TS by auto
    thus "X1| (D\<union>{sel}) is Fields\<bar>(#sel \<rightarrow>?Spec#)" using C6 by simp
  qed
qed



theorem well_defined_order_1:
  assumes "\<And>X. X is Fields1 \<longleftrightarrow> X is Fields2"
          "D1=D2"
          "Fields1 well defined on D1"
 shows "Fields2 well defined on D2"
proof(unfold well_defined_prefix_def,intro conjI)
   have
   I0:"\<exists>\<^sub>L X . X be Fields1\<bar>Struct \<and> dom X=D1" and
   I1[rule_format]:"\<forall>\<^sub>L X1. X1 be Fields1\<bar>Struct \<longrightarrow> D1 \<subseteq> dom X1 \<and> X1|D1 is Fields1"and
   I2[rule_format]: "\<forall>\<^sub>L X1 X2. X1 be Fields1\<bar>Struct \<and>  X2 be Struct \<and> D1 \<subseteq> dom X1 \<and> X1 \<subseteq> X2
       \<longrightarrow> X2 is Fields1" using well_defined_prefix_def[of Fields1 D1] assms(3) by auto
   obtain X where
      "X be Fields1\<bar>Struct \<and> dom X=D1" using I0 by auto
   thus "\<exists>\<^sub>L X . X be Fields2\<bar>Struct \<and> dom X=D2" using assms(1,2) by auto

   show "\<forall>\<^sub>L X1. X1 be Fields2\<bar>Struct \<longrightarrow> D2 \<subseteq> dom X1 \<and> X1|D2 is Fields2" using assms I1 by auto
   show "\<forall>\<^sub>L X1 X2. X1 be Fields2\<bar>Struct \<and>  X2 be Struct \<and> D2 \<subseteq> dom X1 \<and> X1 \<subseteq> X2
       \<longrightarrow> X2 is Fields2"
   proof(intro allI impI) fix X1 X2
     assume A: "X1 be Fields2\<bar>Struct \<and>  X2 be Struct \<and> D2 \<subseteq> dom X1 \<and> X1 \<subseteq> X2"
     hence "X2 be Fields1" using I2[of X1 X2] assms by auto
     thus "X2 is Fields2" using assms by auto
   qed

  qed

text_raw {*\DefineSnippet{WellOrder}{*}
theorem well_defined_order:
  assumes "\<And>X. X is Fields1 \<longleftrightarrow> X is Fields2"
     and "Fields1 well defined on D1"
  shows "Fields2 well defined on D1"
text_raw {*}%EndSnippet*}
proof(unfold well_defined_prefix_def,intro conjI)
   have
   I0:"\<exists>\<^sub>L X . X be Fields1\<bar>Struct \<and> dom X=D1" and
   I1[rule_format]:"\<forall>\<^sub>L X1. X1 be Fields1\<bar>Struct \<longrightarrow> D1 \<subseteq> dom X1 \<and> X1|D1 is Fields1"and
   I2[rule_format]: "\<forall>\<^sub>L X1 X2. X1 be Fields1\<bar>Struct \<and>  X2 be Struct \<and> D1 \<subseteq> dom X1 \<and> X1 \<subseteq> X2
       \<longrightarrow> X2 is Fields1" using well_defined_prefix_def[of Fields1 D1] assms(2) by auto
   obtain X where
      "X be Fields1\<bar>Struct \<and> dom X=D1" using I0 by auto
   thus "\<exists>\<^sub>L X . X be Fields2\<bar>Struct \<and> dom X=D1" using assms(1,2) by auto

   show "\<forall>\<^sub>L X1. X1 be Fields2\<bar>Struct \<longrightarrow> D1 \<subseteq> dom X1 \<and> X1|D1 is Fields2" using assms I1 by auto
   show "\<forall>\<^sub>L X1 X2. X1 be Fields2\<bar>Struct \<and>  X2 be Struct \<and> D1 \<subseteq> dom X1 \<and> X1 \<subseteq> X2
       \<longrightarrow> X2 is Fields2"
   proof(intro allI impI) fix X1 X2
     assume A: "X1 be Fields2\<bar>Struct \<and>  X2 be Struct \<and> D1 \<subseteq> dom X1 \<and> X1 \<subseteq> X2"
     hence "X2 be Fields1" using I2[of X1 X2] assms by auto
     thus "X2 is Fields2" using assms by auto
   qed
  qed



text_raw {*\DefineSnippet{struct}{*}
abbreviation(input) struct ("struct _ _" [10,10] 10)
  where "struct Name Fields \<equiv>
     (Name \<equiv> define_ty(object,\<lambda>_.True,\<lambda>it. it be Struct \<and> it be Fields))"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{structScheme}{*}
lemma struct_scheme:
  assumes df: "struct S Fields"
    and exist: "\<exists>\<^sub>L X . X be Fields\<bar>Struct \<and> dom X = D"
    and monotone: "\<forall>\<^sub>L X1. X1 be Fields\<bar>Struct \<longrightarrow> D \<subseteq> dom X1"
    and restriction: "\<forall>\<^sub>L X1. X1 be Fields\<bar>Struct \<longrightarrow> X1\<restriction>\<^bsub>D\<^esub> be Fields"
  shows "(x be S \<longleftrightarrow> x be Fields\<bar>Struct) \<and>
       inhabited(S) \<and> inhabited(strict(S)) \<and>
       domain_of S = D \<and>
       (E be S \<longrightarrow> the_restriction_of E to S be strict(S))"
text_raw {*}%EndSnippet*}
proof(intro conjI)
   show "x be S \<longleftrightarrow> x be Fields\<bar>Struct" using def_ty_property_true df by auto
   obtain X where
     "X be Struct" and
     fields: "X is Fields" and
     dom:   "dom X=D" using exist by auto
   hence A1: "X be S" using def_ty_property_true df by auto
   thus I: "inhabited(S)" using inhabited_def by auto

   let ?P="\<lambda>it. (ex X be S st it = dom X) \<and>
            (\<forall>X : S.  it \<subseteq> dom X)"
   let ?D = "domain_of S"
   have "?D be set \<and> ?P(?D) \<and> (x be set \<and> ?P(x) \<longrightarrow> x = ?D)"
    proof(induct rule: means_property[OF domain_of_def, case_names existence uniqueness])
       case existence
         show "ex x be set st ?P(x)"
             proof(intro bexI[of _ _ D])
               show "(ex X be S st D=dom X)\<and>(\<forall>X : S.  D \<subseteq> dom X)"
                   using A1 dom bexI def_ty_property_true df monotone I by auto
             qed (simp_all add:all_set)
        case uniqueness
      show "\<And>x y. x be set \<Longrightarrow>
          y be set \<Longrightarrow> ?P(x) \<Longrightarrow> ?P(y) \<Longrightarrow>x=y"
        proof-
          fix x y
          assume [ty]:"x be set" "y be set" and A2:"?P(x)" "?P(y)"
          then obtain X1 where
            [ty]: "X1 be S" and A3:"x = dom X1" using I by auto
          obtain X2 where
            [ty]: "X2 be S" and A4: "y = dom X2" using I A2 by auto
          have "x \<subseteq> y" "y \<subseteq> x" using A2 A3 A4 I
             by auto
          thus "x=y" using A2 xboole_0_def_10 by simp
        qed
    qed simp_all
   hence A2:"?P(?D)" by auto
   then obtain X1 where
     A3:"X1 be S" "?D=dom X1" using I by auto
   hence "X1 be Struct" "X1 is Fields" using def_ty_property_true df by auto
   hence "D c= dom X1" "dom X1 c= D" using monotone[rule_format, of X1]
            A2[THEN conjunct2,THEN bspec, OF I A1] dom A3(2) by auto
   thus A4: "?D = D" using A3(2) xboole_0_def_10[of D "dom X1",simplified all_set] by auto
   hence "X is strict(S)" using A1 dom strict[THEN conjunct2] by auto    
   thus "inhabited(strict(S))" using inhabited_def by auto
   show "E be S \<longrightarrow> (the_restriction_of E to S) be strict (S) "
    proof(rule impI)
      assume B0[ty]: "E be S"
      hence B1[ty]: "E be Struct" "E is Fields" "?D be set" "E be Function"
        using def_ty_property_true df all_set Struct_def by auto
      have B2: "E|?D be Relation" "E|?D is Function_like" using
         funct_1_cl by mauto
      hence B22:"E|?D be Struct" unfolding Struct_def by auto
      have "E|?D is Fields" using restriction B1(1,2) A4 by simp
      hence B3: "E|?D be S" using def_ty_property[OF df,THEN conjunct2] B22 by simp 
      have "?D \<subseteq> dom E" using A2[THEN conjunct2] B0 I by auto
      hence "dom (E|?D) = ?D" using relat_1_th_56[of E ?D] all_set B1 by auto
      hence "E|?D be strict (S)" using B3 strict[THEN conjunct2] by auto
      thus "(the_restriction_of E to S) be strict (S)"
         using equals_property[OF the_restriction_of_def,of E S] by auto
    qed
qed

theorem Equal_strict:
  assumes [ty]:"A1 be Struct" "A2 be Struct"
          "A1 is strict(M)" "A2 is strict(M)" and
          "\<And>selector. selector in domain_of M \<Longrightarrow>
             the selector of A1 = the selector of A2"
  shows "A1=A2"
proof(intro xboole_0_def_10a conjI)
  have [ty]:"A1 be Function" "A2 be Function" using Struct_def by auto
  show "A1 be set" "A2 be set" by auto
  have D: "dom A1 = domain_of M" "dom A2 = domain_of M"
    using assms(3,4) strict[THEN conjunct1,rule_format,of _ M] by auto
  show "A1 c= A2"
    proof(rule tarski_def_3b)
        fix x
        assume A0: "x in A1"
        then obtain a b where
          A1: "a be object" "b be object" "x=[a,b]"
          using relat_1_def_1E[of A1 x] by auto
        hence A2: "the a of A1 = b" using the_selector_of_1 A0 by auto
        have A3: "a in dom A1" using A0 A1 xtuple_0_def_12 by auto
        hence "a in dom A2" using D by auto
        hence A4: "[a,A2. a] in A2"
          using assms(2) funct_1_th_1[of A2 "A2. a"] by auto
        hence "the a of A2 = A2. a" using the_selector_of_1 A0
           by auto
        thus "x in A2" using A1 A2 A3 assms(5) D A4 by auto
    qed simp_all
     show "A2 c= A1"
    proof(rule tarski_def_3b)
        fix x
        assume A0: "x in A2"
        then obtain a b where
          A1: "a be object" "b be object" "x=[a,b]"
          using relat_1_def_1E[of A2 x] by auto
        hence A2: "the a of A2 = b" using the_selector_of_1 A0 assms(2) by auto
        have A3: "a in dom A2" using A0 A1 xtuple_0_def_12 by auto
        hence "a in dom A1" using D by auto
        hence A4: "[a,A1. a] in A1"
          using assms(2) funct_1_th_1[of A1 "A1. a"] by auto
        hence "the a of A1 = A1. a" using the_selector_of_1 A0
           by auto
        thus "x in A1" using A1 A2 A3 assms(5) D A4 by auto
    qed simp_all
qed


text_raw {*\DefineSnippet{structSchemeWell}{*}
lemma well_defined_property:
  assumes df: "struct S Fields"
    and well: "Fields well defined on D"
  shows "(x be S \<longleftrightarrow> x be Fields\<bar>Struct) \<and>
       inhabited(S) \<and> inhabited(strict(S)) \<and>
       domain_of S = D \<and>
       (E be S \<longrightarrow> the_restriction_of E to S be strict(S)) \<and>
       (Fields well defined on D)"
text_raw {*}%EndSnippet*}
proof-
  have A0: "\<exists>\<^sub>L X . X be Fields\<bar>Struct \<and> dom X=D"
  "\<forall>\<^sub>L X1. X1 be Fields\<bar>Struct \<longrightarrow> D \<subseteq> dom X1 \<and> X1|D is Fields"
  "\<forall>\<^sub>L X1 X2. X1 be Fields\<bar>Struct \<and>  X2 be Struct \<and> D \<subseteq> dom X1 \<and> X1 \<subseteq> X2
       \<longrightarrow> X2 is Fields" using well_defined_prefix_def[of Fields D] well by auto
  have monotone: "\<And> X1. X1 be Struct \<and> X1 is Fields \<longrightarrow> D \<subseteq> dom X1" using A0(2) by auto
  have restriction: "\<And> X1. X1 be Struct \<and> X1 is Fields \<longrightarrow> X1|D is Fields" using A0(2) by auto
  thus ?thesis using monotone struct_scheme[OF df A0(1),of x] well by auto
qed

theorem Struct_1:
  "[#s \<mapsto> D#] be Struct" unfolding Struct_def sel_t_def using funct_1_cl_3 relat_1_cl_7 by mauto

theorem Struct_2:
  "s1 \<noteq> s2 \<Longrightarrow> [# s1\<mapsto>D1 ; s2\<mapsto> D2#] be Struct"
proof-
  assume A1:"s1\<noteq>s2"
  let ?F1 = "{[s1,D1]}"
  let ?F2 = "{[s2,D2]}"
  have "for x,y1,y2 being object st [x,y1] in ?F1\<union>?F2 \<and> [x,y2] in ?F1\<union>?F2 holds y1 = y2"
     proof(intro ballI impI)
       fix x y1 y2
       assume "[x , y1] in ?F1\<union>?F2 \<and> [x , y2] in ?F1\<union>?F2"
       hence "[x,y1] in ?F1 \<or> [x , y1] in ?F2" "[x , y2] in ?F1 \<or> [x , y2] in ?F2" using xboole_0_def_3 by mauto
       hence "[x,y1] = [s1,D1] \<or> [x,y1] =[s2,D2]"  "[x,y2] = [s1,D1] \<or> [x,y2] =[s2,D2]" using tarski_def_1 by simp+
       hence "(x=s1 \<and> y1=D1) \<or> (x=s2 \<and> y1=D2)" "(x=s1 \<and> y2=D1) \<or> (x=s2 \<and> y2=D2)"
          using xtuple_0_th_1a by auto
       thus "y1=y2" using A1 by auto
     qed simp_all
  hence A: "(?F1 \<union> ?F2) is Function_like" using funct_1_def_1 by mauto
  have "(?F1 \<union> ?F2) is Relation_like" using relat_1_cl_7 relat_1_cl_5[of ?F1 ?F2] by mauto
  thus "[# s1\<mapsto>D1 ; s2\<mapsto> D2#] be Struct" unfolding Struct_def aggr_def sel_t_def using A by mauto
qed

theorem Struct_3:
  "s1 \<noteq> s2 \<and> s1\<noteq>s3 \<and> s2\<noteq>s3 \<Longrightarrow> [# s1\<mapsto> D1 ; s2\<mapsto>D2 ; s3\<mapsto>D3#] be Struct"
proof-
  assume A1:"s1\<noteq>s2 \<and> s1\<noteq>s3 \<and> s2\<noteq>s3"
  let ?F1 = "{[s1,D1]}"
  let ?F2 = "{[s2,D2]}"
  let ?F3 = "{[s3,D3]}"
  have "for x,y1,y2 being object st [x,y1] in ?F1\<union>?F2\<union>?F3 \<and> [x,y2] in ?F1\<union>?F2\<union>?F3 holds y1 = y2"
     proof(intro ballI impI)
       fix x y1 y2
       assume "[x , y1] in ?F1\<union>?F2\<union>?F3 \<and> [x , y2] in ?F1\<union>?F2\<union>?F3"
       hence "[x,y1] in ?F1 \<or> [x , y1] in ?F2 \<or> [x , y1] in ?F3" "[x , y2] in ?F1 \<or> [x , y2] in ?F2 \<or> [x , y2] in ?F3" using xboole_0_def_3 by mauto
       hence "[x,y1] = [s1,D1] \<or> [x,y1] =[s2,D2] \<or> [x,y1] =[s3,D3]"  "[x,y2] = [s1,D1] \<or> [x,y2] =[s2,D2] \<or> [x,y2] =[s3,D3]"
           using tarski_def_1 by simp+
       hence "(x=s1 \<and> y1=D1) \<or> (x=s2 \<and> y1=D2) \<or> (x=s3 \<and> y1=D3)" "(x=s1 \<and> y2=D1) \<or> (x=s2 \<and> y2=D2) \<or> (x=s3 \<and> y2=D3)"
          using xtuple_0_th_1a by auto
       thus "y1=y2" using A1 by auto
     qed simp_all
  hence A: "(?F1 \<union> ?F2 \<union> ?F3) is Function_like" using funct_1_def_1 by mauto
  have "(?F1 \<union> ?F2 \<union> ?F3) is Relation_like" using relat_1_cl_7 relat_1_cl_5[of ?F1 ?F2] relat_1_cl_5[of "?F1\<union>?F2" ?F3] by mauto
  thus "[# s1\<mapsto> D1 ; s2\<mapsto>D2 ; s3\<mapsto>D3#] be Struct" unfolding Struct_def aggr_def sel_t_def using A by mauto
qed

theorem Struct_4:
  "s1 \<noteq> s2 \<and> s1\<noteq>s3 \<and> s1\<noteq> s4 \<and> s2\<noteq>s3 \<and> s2\<noteq>s4 \<and> s3\<noteq>s4 \<Longrightarrow> [# s1\<mapsto> D1 ; s2\<mapsto>D2 ; s3\<mapsto>D3 ;s4\<mapsto>D4#] be Struct"
proof-
  assume A1:"s1 \<noteq> s2 \<and> s1\<noteq>s3 \<and> s1\<noteq> s4 \<and> s2\<noteq>s3 \<and> s2\<noteq>s4 \<and> s3\<noteq>s4"
  let ?F1 = "{[s1,D1]}"
  let ?F2 = "{[s2,D2]}"
  let ?F3 = "{[s3,D3]}"
  let ?F4 = "{[s4,D4]}"
  have "for x,y1,y2 being object st [x,y1] in ?F1\<union>?F2\<union>?F3\<union>?F4 \<and> [x,y2] in ?F1\<union>?F2\<union>?F3\<union>?F4 holds y1 = y2"
     proof(intro ballI impI)
       fix x y1 y2
       assume "[x , y1] in ?F1\<union>?F2\<union>?F3\<union>?F4 \<and> [x , y2] in ?F1\<union>?F2\<union>?F3\<union>?F4"
       hence "[x,y1] in ?F1 \<or> [x , y1] in ?F2 \<or> [x , y1] in ?F3 \<or> [x , y1] in ?F4"
             "[x , y2] in ?F1 \<or> [x , y2] in ?F2 \<or> [x , y2] in ?F3 \<or> [x , y2] in ?F4" using xboole_0_def_3 by mty auto
       hence "[x,y1] = [s1,D1] \<or> [x,y1] =[s2,D2] \<or> [x,y1] =[s3,D3] \<or> [x,y1] =[s4,D4]"  "[x,y2] = [s1,D1] \<or> [x,y2] =[s2,D2] \<or> [x,y2] =[s3,D3] \<or> [x,y2] =[s4,D4]"
           using tarski_def_1 by simp+
       hence "(x=s1 \<and> y1=D1) \<or> (x=s2 \<and> y1=D2) \<or> (x=s3 \<and> y1=D3) \<or> (x=s4 \<and> y1=D4)" "(x=s1 \<and> y2=D1) \<or> (x=s2 \<and> y2=D2) \<or> (x=s3 \<and> y2=D3)  \<or> (x=s4 \<and> y2=D4)"
          using xtuple_0_th_1a by auto
       thus "y1=y2" using A1 by auto
     qed simp_all
  hence A: "(?F1 \<union> ?F2 \<union> ?F3\<union>?F4) is Function_like" using funct_1_def_1 all_set by simp
  have "(?F1 \<union> ?F2 \<union> ?F3\<union>?F4) is Relation_like" using relat_1_cl_7 relat_1_cl_5[of ?F1 ?F2] relat_1_cl_5[of "?F1\<union>?F2" ?F3]
     relat_1_cl_5[of "?F1\<union>?F2\<union>?F3" ?F4] by mauto
  thus "[# s1\<mapsto> D1 ; s2\<mapsto>D2 ; s3\<mapsto>D3 ;s4\<mapsto>D4#] be Struct" unfolding Struct_def aggr_def sel_t_def using A all_set by auto
qed

theorem Struct_5:
  "s1 \<noteq> s2 \<and> s1\<noteq>s3 \<and> s1\<noteq> s4 \<and> s1\<noteq> s5 \<and> s2\<noteq>s3 \<and> s2\<noteq>s4 \<and> s2\<noteq> s5 \<and> s3\<noteq>s4 \<and> s3\<noteq> s5 \<and> s4\<noteq> s5
       \<Longrightarrow> [# s1\<mapsto> D1 ; s2\<mapsto>D2 ; s3\<mapsto>D3 ;s4\<mapsto>D4 ;s5\<mapsto>D5 #] be Struct"
proof-
  assume A1:"s1 \<noteq> s2 \<and> s1\<noteq>s3 \<and> s1\<noteq> s4 \<and> s1\<noteq> s5 \<and> s2\<noteq>s3 \<and> s2\<noteq>s4 \<and> s2\<noteq> s5 \<and> s3\<noteq>s4 \<and> s3\<noteq> s5 \<and> s4\<noteq> s5"
  let ?F1 = "{[s1,D1]}"
  let ?F2 = "{[s2,D2]}"
  let ?F3 = "{[s3,D3]}"
  let ?F4 = "{[s4,D4]}"
  let ?F5 = "{[s5,D5]}"
  have "for x,y1,y2 being object st [x,y1] in ?F1\<union>?F2\<union>?F3\<union>?F4\<union>?F5 \<and> [x,y2] in ?F1\<union>?F2\<union>?F3\<union>?F4\<union>?F5 holds y1 = y2"
     proof(intro ballI impI)
       fix x y1 y2
       assume "[x , y1] in ?F1\<union>?F2\<union>?F3\<union>?F4\<union>?F5 \<and> [x , y2] in ?F1\<union>?F2\<union>?F3\<union>?F4\<union>?F5"
       hence "[x,y1] in ?F1 \<or> [x , y1] in ?F2 \<or> [x , y1] in ?F3 \<or> [x , y1] in ?F4 \<or> [x , y1] in ?F5"
             "[x , y2] in ?F1 \<or> [x , y2] in ?F2 \<or> [x , y2] in ?F3 \<or> [x , y2] in ?F4 \<or> [x , y2] in ?F5"
           using xboole_0_def_3 all_set by auto
       hence "[x,y1] = [s1,D1] \<or> [x,y1] =[s2,D2] \<or> [x,y1] =[s3,D3] \<or> [x,y1] =[s4,D4] \<or> [x,y1] =[s5,D5]"
               "[x,y2] = [s1,D1] \<or> [x,y2] =[s2,D2] \<or> [x,y2] =[s3,D3] \<or> [x,y2] =[s4,D4] \<or> [x,y2] =[s5,D5]"
           using tarski_def_1 by simp_all
         hence "(x=s1 \<and> y1=D1) \<or> (x=s2 \<and> y1=D2) \<or> (x=s3 \<and> y1=D3) \<or> (x=s4 \<and> y1=D4) \<or> (x=s5 \<and> y1=D5)"
                "(x=s1 \<and> y2=D1) \<or> (x=s2 \<and> y2=D2) \<or> (x=s3 \<and> y2=D3)  \<or> (x=s4 \<and> y2=D4) \<or> (x=s5 \<and> y2=D5)"
          using xtuple_0_th_1a by auto
       thus "y1=y2" using A1 by auto
     qed simp_all
  hence A: "(?F1 \<union> ?F2 \<union> ?F3\<union>?F4\<union>?F5) is Function_like" using funct_1_def_1 all_set by auto
  have "(?F1 \<union> ?F2 \<union> ?F3\<union>?F4\<union>?F5) is Relation_like" using relat_1_cl_7 relat_1_cl_5[of ?F1 ?F2] relat_1_cl_5[of "?F1\<union>?F2" ?F3]
     relat_1_cl_5[of "?F1\<union>?F2\<union>?F3" ?F4] relat_1_cl_5[of "?F1\<union>?F2\<union>?F3\<union>?F4" ?F5] all_set by simp
  thus "[# s1\<mapsto> D1 ; s2\<mapsto>D2 ; s3\<mapsto>D3 ;s4\<mapsto>D4 ;s5\<mapsto>D5 #] be Struct" unfolding Struct_def aggr_def sel_t_def using A all_set by auto
qed

theorem Struct_6:
  "s1 \<noteq> s2 \<and> s1\<noteq>s3 \<and> s1\<noteq> s4 \<and> s1\<noteq> s5 \<and> s1\<noteq> s6 \<and>
   s2\<noteq>s3 \<and> s2\<noteq>s4 \<and> s2\<noteq> s5 \<and> s2\<noteq> s6 \<and>
  s3\<noteq>s4 \<and> s3\<noteq> s5 \<and> s3\<noteq> s6 \<and> s4\<noteq> s5 \<and> s4\<noteq> s6 \<and> s5\<noteq> s6
       \<Longrightarrow> [# s1\<mapsto> D1 ; s2\<mapsto>D2 ; s3\<mapsto>D3 ;s4\<mapsto>D4 ;s5\<mapsto>D5;s6\<mapsto>D6 #] be Struct"
proof-
  assume A1:"s1 \<noteq> s2 \<and> s1\<noteq>s3 \<and> s1\<noteq> s4 \<and> s1\<noteq> s5 \<and> s1\<noteq> s6 \<and>
   s2\<noteq>s3 \<and> s2\<noteq>s4 \<and> s2\<noteq> s5 \<and> s2\<noteq> s6 \<and>
  s3\<noteq>s4 \<and> s3\<noteq> s5 \<and> s3\<noteq> s6 \<and> s4\<noteq> s5 \<and> s4\<noteq> s6 \<and> s5\<noteq> s6"
  let ?F1 = "{[s1,D1]}"
  let ?F2 = "{[s2,D2]}"
  let ?F3 = "{[s3,D3]}"
  let ?F4 = "{[s4,D4]}"
  let ?F5 = "{[s5,D5]}"
  let ?F6 = "{[s6,D6]}"
  have "for x,y1,y2 being object st [x,y1] in ?F1\<union>?F2\<union>?F3\<union>?F4\<union>?F5\<union>?F6 \<and> [x,y2] in ?F1\<union>?F2\<union>?F3\<union>?F4\<union>?F5\<union>?F6 holds y1 = y2"
     proof(intro ballI impI)
       fix x y1 y2
       assume "[x , y1] in ?F1\<union>?F2\<union>?F3\<union>?F4\<union>?F5\<union>?F6 \<and> [x , y2] in ?F1\<union>?F2\<union>?F3\<union>?F4\<union>?F5\<union>?F6"
       hence "[x,y1] in ?F1 \<or> [x , y1] in ?F2 \<or> [x , y1] in ?F3 \<or> [x , y1] in ?F4 \<or> [x , y1] in ?F5 \<or> [x , y1] in ?F6"
             "[x , y2] in ?F1 \<or> [x , y2] in ?F2 \<or> [x , y2] in ?F3 \<or> [x , y2] in ?F4 \<or> [x , y2] in ?F5 \<or> [x , y2] in ?F6"
           using xboole_0_def_3 all_set by auto
       hence "[x,y1] = [s1,D1] \<or> [x,y1] =[s2,D2] \<or> [x,y1] =[s3,D3] \<or> [x,y1] =[s4,D4] \<or> [x,y1] =[s5,D5] \<or> [x,y1] =[s6,D6]"
               "[x,y2] = [s1,D1] \<or> [x,y2] =[s2,D2] \<or> [x,y2] =[s3,D3] \<or> [x,y2] =[s4,D4] \<or> [x,y2] =[s5,D5] \<or> [x,y2] =[s6,D6]"
           using tarski_def_1 by simp_all
         hence "(x=s1 \<and> y1=D1) \<or> (x=s2 \<and> y1=D2) \<or> (x=s3 \<and> y1=D3) \<or> (x=s4 \<and> y1=D4) \<or> (x=s5 \<and> y1=D5)  \<or> (x=s6 \<and> y1=D6) "
                "(x=s1 \<and> y2=D1) \<or> (x=s2 \<and> y2=D2) \<or> (x=s3 \<and> y2=D3)  \<or> (x=s4 \<and> y2=D4) \<or> (x=s5 \<and> y2=D5) \<or> (x=s6 \<and> y2=D6)"
          using xtuple_0_th_1a by auto
       thus "y1=y2" using A1 by auto
     qed simp_all
  hence A: "(?F1 \<union> ?F2 \<union> ?F3\<union>?F4\<union>?F5\<union>?F6) is Function_like" using funct_1_def_1 all_set by auto
  have "(?F1 \<union> ?F2 \<union> ?F3\<union>?F4\<union>?F5\<union>?F6) is Relation_like" using relat_1_cl_7 relat_1_cl_5[of ?F1 ?F2] relat_1_cl_5[of "?F1\<union>?F2" ?F3]
     relat_1_cl_5[of "?F1\<union>?F2\<union>?F3" ?F4] relat_1_cl_5[of "?F1\<union>?F2\<union>?F3\<union>?F4" ?F5]
     relat_1_cl_5[of "?F1\<union>?F2\<union>?F3\<union>?F4\<union>?F5" ?F6] all_set by simp
  thus "[# s1\<mapsto> D1 ; s2\<mapsto>D2 ; s3\<mapsto>D3 ;s4\<mapsto>D4 ;s5\<mapsto>D5;s6\<mapsto>D6 #] be Struct" unfolding Struct_def aggr_def sel_t_def using A all_set by auto
qed



theorem Dom_1:
  "dom [# s \<mapsto> D #]={s}"
proof-
  have "{[s,D]} be Relation" using relat_1_cl_7 by mauto
  thus ?thesis using relat_1_th_3[of D s "{[s,D]}"] sel_t_def by auto
qed


thm relat_1_cl_5
theorem Dom_2:
  "dom [# s1 \<mapsto> D1 ; s2\<mapsto> D2 #] = {s1}\<union>{s2}"
proof-
  have A1[ty]:"{[s1,D1]} be Relation \<and> {[s2,D2]} be Relation" using relat_1_cl_7 by mauto
  have "({[s1,D1]} \<union> {[s2,D2]}) be Relation" using relat_1_cl_5 A1 by mauto
  hence "dom ({[s1,D1]} \<union> {[s2,D2]}) = (dom {[s1,D1]}) \<union> (dom {[s2,D2]})" using xtuple_th_23 relat_1_def_1I by simp
  thus ?thesis using Dom_1 sel_t_def aggr_def by auto
qed

theorem Dom_3:
  "dom [# s1 \<mapsto> D1 ; s2\<mapsto> D2 ; s3 \<mapsto> D3 #] = {s1}\<union>{s2}\<union>{s3}"
proof-
  have A2:"{[s1,D1]} be Relation \<and> {[s2,D2]} be Relation" using relat_1_cl_7 by mauto
  have A3: "({[s1,D1]} \<union> {[s2,D2]}) be Relation \<and>  {[s3,D3]} be Relation" using relat_1_cl_7 relat_1_cl_5 A2 by mauto
  have A4: "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) be Relation" using relat_1_cl_7 relat_1_cl_5 A3 by mauto
  hence "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) be Relation" using relat_1_cl_5[of "{[s1,D1]} \<union> {[s2,D2]}" "{[s3,D3]}"] by simp
  hence "dom ({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) = (dom ({[s1,D1]}\<union>{[s2,D2]})) \<union> (dom {[s3,D3]})" using xtuple_th_23 relat_1_def_1I
      by mty auto
  thus ?thesis using Dom_1 Dom_2 sel_t_def aggr_def by auto
qed

theorem Dom_4:
  "dom [# s1 \<mapsto> D1 ; s2\<mapsto> D2 ; s3 \<mapsto> D3 ; s4 \<mapsto> D4 #] = {s1}\<union>{s2}\<union>{s3}\<union>{s4}"
proof-
  have A2:"{[s1,D1]} be Relation \<and> {[s2,D2]} be Relation" using relat_1_cl_7 by mauto
  have A3: "({[s1,D1]} \<union> {[s2,D2]}) be Relation \<and>  {[s3,D3]} be Relation" using relat_1_cl_7 relat_1_cl_5 A2 by mauto
   have A4: "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) be Relation \<and>  {[s4,D4]} be Relation " using relat_1_cl_7 relat_1_cl_5 A3 by mauto
  have A5: "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}) be Relation " using relat_1_cl_7 relat_1_cl_5 A4 all_set by simp
  hence "dom ({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}) = (dom ({[s1,D1]}\<union>{[s2,D2]}\<union>{[s3,D3]})) \<union> (dom {[s4,D4]})"
     using xtuple_th_23 relat_1_def_1I by mty auto
  thus ?thesis using Dom_1 Dom_3 sel_t_def aggr_def by auto
qed


theorem Dom_5:
  "dom[# s1 \<mapsto> D1 ; s2\<mapsto> D2 ; s3 \<mapsto> D3 ; s4 \<mapsto> D4 ;s5\<mapsto>D5 #] = {s1}\<union>{s2}\<union>{s3}\<union>{s4}\<union>{s5}"
proof-
  have A5: "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}\<union>{[s5,D5]}) be Relation " using relat_1_cl_7 relat_1_cl_5 all_set by auto
  hence "dom ({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}\<union>{[s5,D5]}) = (dom ({[s1,D1]}\<union>{[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]})) \<union> (dom {[s5,D5]})"
    using xtuple_th_23 relat_1_def_1I all_set by simp
  thus ?thesis using Dom_1 Dom_4 sel_t_def aggr_def by auto
qed

theorem Dom_6:
  "dom[# s1 \<mapsto> D1 ; s2\<mapsto> D2 ; s3 \<mapsto> D3 ; s4 \<mapsto> D4 ;s5\<mapsto>D5;s6\<mapsto>D6 #] = {s1}\<union>{s2}\<union>{s3}\<union>{s4}\<union>{s5}\<union>{s6}"
proof-
  have "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}\<union>{[s5,D5]}\<union>{[s5,D5]}) be Relation " using relat_1_cl_7 relat_1_cl_5 all_set by auto
  hence "dom ({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}\<union>{[s5,D5]}\<union>{[s6,D6]}) = (dom ({[s1,D1]}\<union>{[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}\<union>{[s5,D5]})) \<union> (dom {[s6,D6]})"
    using xtuple_th_23 relat_1_def_1I all_set by simp
  thus ?thesis using Dom_1 Dom_5 sel_t_def aggr_def by auto
qed

end
