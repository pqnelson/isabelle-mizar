theory algstr_0
imports struct_0
begin

abbreviation "addMagma_fields \<equiv> (#carrier \<rightarrow> set';addF\<rightarrow> BinOp-of' the' carrier #)"

mdefinition addMagma :: "Ty" ("addMagma") where
  "struct addMagma(#carrier \<rightarrow> set';addF\<rightarrow> BinOp-of' the' carrier #)"
:well_defined_property[of _ _ "{carrier}\<union>{addF}"]
  by (auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)


lemmas addMagmaA = addMagma(1)
lemmas [ex] = addMagma(2,3)
lemmas addMagmaD = addMagma(4)
lemmas [ty_func] = addMagma(5)

theorem addMagma_inheritance[ty_parent]:
  "X be addMagma \<Longrightarrow> X be 1-sorted" using addMagmaA one_sortedA by simp

theorem addMagma_inheritance1[ty_func]:
  "X be addMagma \<Longrightarrow> (the addF of X) be BinOp-of (the carrier of X)" using field addMagmaA by auto

lemma addMagma_ag[ty_func]:
  "X be set \<Longrightarrow> B be BinOp-of X \<Longrightarrow> [#carrier\<mapsto> X ; addF\<mapsto>B#] be addMagma"
proof-
  assume A1[ty]: "X be set" "B be BinOp-of X"
  let ?A= "[#carrier\<mapsto> X ; addF\<mapsto>B#]"
  have [ty]: "?A be Struct" using Struct_2[of carrier addF] by (simp add:string)
  have T:"the carrier of ?A=X" using the_selector_of_1[of ?A carrier "X"] Aggr by auto
  have [ty]:"?A is (carrier \<rightarrow> set')" using Field_1[of ?A carrier X ] Aggr by auto
  have [ty]:"?A is (addF \<rightarrow> BinOp-of' the' carrier)" using Field_1[of ?A addF B ] T Aggr by auto
  thus ?thesis using addMagmaA by auto
qed

theorem algstr_0_cl_1[rule_format,ty_func_cluster]:
  "let D be non empty\<bar>set \<and> o be BinOp-of D
   cluster [#carrier\<mapsto> D ; addF\<mapsto>o#] \<rightarrow> non empty-struct"
proof-
  assume T0[ty]:"D be non empty\<bar>set \<and> o be BinOp-of D"
  let ?X = "[#carrier\<mapsto> D ; addF\<mapsto>o#]"
  have T1[ty]: "?X be addMagma" by mauto
  have "the carrier of ?X = D" using Aggr by (intro the_selector_of_1) auto
  thus "?X is non empty-struct" using struct_0_def_1 addMagmaA one_sortedA T1 by auto
qed

theorem algstr_0_cl_2[rule_format,ty_func_cluster]:
  "let T be trivial\<bar>set \<and> f be BinOp-of T
   cluster [#carrier\<mapsto> T ; addF\<mapsto>f#] \<rightarrow> trivial-struct"
proof-
  assume T0[ty]:"T be trivial\<bar>set \<and> f be BinOp-of T"
  let ?X = "[#carrier\<mapsto> T ; addF\<mapsto>f#]"
  have T1[ty]: "?X be addMagma" by mauto
  hence T2: "the carrier of ?X = T" "?X be 1-sorted" using the_selector_of_1[of ?X carrier T] Aggr by auto
  show "?X is trivial-struct" using struct_0_def_9[of ?X] T2 by auto
qed

theorem algstr_0_cl_3[rule_format,ty_func_cluster]:
  "let N be non trivial\<bar>set \<and> b be BinOp-of N
   cluster [#carrier\<mapsto>N ; addF\<mapsto>b#] \<rightarrow> non trivial-struct"
proof-
  assume T0[ty]:"N be non trivial\<bar>set \<and> b be BinOp-of N"
  let ?X = "[#carrier\<mapsto>N ; addF\<mapsto>b#]"
  have [ty]: "?X be addMagma" by mauto
  hence "the carrier of ?X = N" using the_selector_of_1[of ?X carrier N]  Aggr by auto
  thus "?X is non trivial-struct" using struct_0_def_9[of ?X] by auto
qed

text_raw {*\DefineSnippet{algstr0def1}{*}
func algstr_0_def_1 ("_ \<oplus>\<^sub>_ _" [66,1000,67] 66) where
  mlet "M be addMagma", "x be Element-of-struct M",
       "y be Element-of-struct M"
  "func x \<oplus>\<^sub>M y \<rightarrow> Element-of-struct M equals
     (the addF of M) . \<lparr> x , y \<rparr>"
text_raw {*}%EndSnippet*}
proof-
  let ?A = "the carrier of M"
   have A1: "(the addF of M) be BinOp-of ?A" "?A be set" using ty by auto
   thus " (the addF of M) .  \<lparr> x , y \<rparr> be Element-of ?A"
          using binop_0_def_20A by auto
qed

abbreviation algstr_0_def_2 ("Trivial-addMagma") where
  "Trivial-addMagma \<equiv> [# carrier\<mapsto>{{}} ; addF \<mapsto> op2 #]"

theorem algstr_0_cl_4[rule_format,ty_func_cluster]:
  "cluster Trivial-addMagma \<rightarrow> 1-element-struct\<bar> strict (addMagma)"
proof(unfold ty_intersection,intro conjI)
  let ?T ="Trivial-addMagma"
  have T0[ty]: "?T be addMagma" by mauto

  have "[carrier,{{}}] in [# carrier\<mapsto>{{}} ; addF \<mapsto> op2 #]" using Aggr by auto
  hence T1: "the carrier of ?T={{}}"
    using the_selector_of_1[of ?T carrier "{{}}"] by auto
  thus T2: "Trivial-addMagma is 1-element-struct" using T0 struct_0_def_19_a by auto
  have "domain_of addMagma = dom ?T" using addMagmaD Dom_2 by auto
  thus "Trivial-addMagma is strict (addMagma)" using T2 strict[THEN conjunct2] T0 by auto
qed

theorem algstr_0_cl_5[ex]:
  "cluster strict (addMagma)\<bar>1-element-struct for addMagma"
  unfolding inhabited_def
proof(intro exI)
  show "Trivial-addMagma is strict (addMagma)\<bar>1-element-struct\<bar> addMagma" by mauto
qed


attr algstr_0_def_3 ("left-add-cancelable\<^sub>_" [200] 200)
   "M be addMagma \<Longrightarrow> attr left-add-cancelable\<^sub>M for Element-of-struct M means
     (\<lambda> x. for y,z be Element-of-struct M st x \<oplus>\<^sub>M y = x \<oplus>\<^sub>M z holds y = z)"


attr algstr_0_def_4 ("right-add-cancelable\<^sub>_" [200] 200)
   " M be addMagma \<Longrightarrow> attr right-add-cancelable\<^sub>M for Element-of-struct M means (\<lambda> x.
                                       (for y,z be Element-of-struct M st y \<oplus>\<^sub>M x = z \<oplus>\<^sub>M x holds y = z))"

attr algstr_0_def_5 ("add-cancelable\<^sub>_" [200] 200)
   "M be addMagma \<Longrightarrow> attr add-cancelable\<^sub>M for Element-of-struct M means (\<lambda> x.
                                       x is right-add-cancelable\<^sub>M \<bar> left-add-cancelable\<^sub>M)"

theorem algstr_0_cl_6[ty_cond_cluster]:
  "let M be addMagma
   cluster right-add-cancelable\<^sub>M \<bar> left-add-cancelable\<^sub>M \<rightarrow> add-cancelable\<^sub>M for Element-of-struct M" using algstr_0_def_5 by auto

theorem algstr_0_cl_7[ty_cond_cluster]:
  "let M be addMagma
   cluster add-cancelable\<^sub>M \<rightarrow> right-add-cancelable\<^sub>M \<bar> left-add-cancelable\<^sub>M for Element-of-struct M" using algstr_0_def_5 by auto

attr algstr_0_def_6 ("left-add-cancelable")
   "attr left-add-cancelable for addMagma means (\<lambda> M.  (for x be Element-of-struct M holds x is left-add-cancelable\<^sub>M))"


attr algstr_0_def_7 ("right-add-cancelable")
   "attr right-add-cancelable for addMagma means (\<lambda> M.
                                       (for x be Element-of-struct M holds x is right-add-cancelable\<^sub>M))"

attr algstr_0_def_8 ("add-cancelable")
   "attr add-cancelable for addMagma means (\<lambda> M.
                                       M is right-add-cancelable \<bar> left-add-cancelable)"

theorem algstr_0_cl_8[rule_format,ty_cond_cluster]:
  "cluster right-add-cancelable \<bar> left-add-cancelable \<rightarrow> add-cancelable for addMagma" using algstr_0_def_8 by auto


theorem algstr_0_cl_9[rule_format,ty_cond_cluster]:
  "cluster add-cancelable \<rightarrow> right-add-cancelable \<bar> left-add-cancelable for addMagma" using algstr_0_def_8 by auto


theorem algstr_0_cl_10[rule_format,ty_func_cluster]:
  "cluster Trivial-addMagma \<rightarrow> add-cancelable"
proof
  let ?T ="Trivial-addMagma"
  have [ty]: "?T be addMagma" by mauto
  have T1: "the carrier of ?T={{}}"
    using Aggr by (auto intro: the_selector_of_1)
  show "?T is right-add-cancelable"
    proof
      fix x assume T2[ty]: "x be Element-of-struct ?T"
      show "x is right-add-cancelable\<^sub>?T"
      proof
        fix y z assume T3[ty]: "y be Element-of-struct ?T" "z be Element-of-struct ?T"
        assume "y \<oplus>\<^sub>?T x = z \<oplus>\<^sub>?T x"
        show "y = z" using struct_0_def_10[THEN iffD1,THEN bspec,THEN bspec,of ?T y z] by auto
      qed simp_all
    qed simp_all
  show "?T is left-add-cancelable"
    proof
      fix x assume T2[ty]: "x be Element-of-struct ?T"
      show "x is left-add-cancelable\<^sub>?T"
      proof
        fix y z assume T3[ty]: "y be Element-of-struct ?T" "z be Element-of-struct ?T"
        assume "x \<oplus>\<^sub>?T y = x \<oplus>\<^sub>?T z"
        show "y = z" using struct_0_def_10[THEN iffD1,THEN bspec,THEN bspec,of ?T y z] by auto
      qed simp_all
    qed simp_all
qed mauto

theorem algstr_0_cl_11[ex]:
  "cluster add-cancelable\<bar>strict (addMagma)\<bar>1-element-struct for addMagma"
  unfolding inhabited_def
proof(intro exI,simp,intro conjI)
  show "Trivial-addMagma is add-cancelable "
        "Trivial-addMagma is strict (addMagma)"
        "Trivial-addMagma is 1-element-struct" by mauto
  show "Trivial-addMagma be addMagma" by mauto
qed



theorem algstr_0_cl_12[ty_cond_cluster]:
  "let M be left-add-cancelable \<bar> addMagma
   cluster \<rightarrow> left-add-cancelable\<^sub>M for Element-of-struct M"
proof-
  fix X assume T[ty]:"M be left-add-cancelable \<bar> addMagma" "X be Element-of-struct M"
  show "X be left-add-cancelable\<^sub>M" using algstr_0_def_6E[of M X] by mauto
qed

theorem algstr_0_cl_13[ty_cond_cluster]:
  "let M be right-add-cancelable \<bar> addMagma
   cluster \<rightarrow> right-add-cancelable\<^sub>M for Element-of-struct M"
proof-
  fix X assume T[ty]:"M be right-add-cancelable \<bar> addMagma" "X be Element-of-struct M"
  show "X be right-add-cancelable\<^sub>M" using algstr_0_def_7E[of M X] by auto
qed

abbreviation "addLoopStr_fields\<equiv>(#carrier \<rightarrow> set';  addF\<rightarrow> BinOp-of' the' carrier ;ZeroF \<rightarrow> Element-of' the' carrier#)"

mdefinition addLoopStr_d ("addLoopStr") where
"struct addLoopStr
  (# carrier \<rightarrow> set';
     addF \<rightarrow> BinOp-of' the' carrier;
     ZeroF \<rightarrow> Element-of' the' carrier #)"
:well_defined_property[of _ _ "{carrier}\<union>{addF}\<union>{ZeroF}"]
  by (auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)
(*proof (rule Fields_add_argM1[OF addMagma_d(5)],simp add:string,simp add:string )
    fix X1 assume [ty]:"X1 be addMagma_fields\<bar>Struct"
    hence "the carrier of X1 be set" using field by auto
    thus "inhabited(Element-of-struct X1)" by auto
  qed
*)

lemmas addLoopStrA = addLoopStr_d(1)
lemmas [ex] = addLoopStr_d(2,3)
lemmas addLoopStrD = addLoopStr_d(4)
lemmas addLoopStrR = addLoopStr_d(5)


text_raw {*\DefineSnippet{addLoopStrEx1}{*}
term "{[carrier, the set]} \<union>
      {[addF, the BinOp-of (the set)]} \<union>
      {[ZeroF, the Element-of (the set)]}"
text_raw {*}%EndSnippet*}




text_raw {*\DefineSnippet{addLoopStrEx2}{*}
term "[#carrier \<mapsto> (the set);
      addF\<mapsto> the BinOp-of (the set);
      ZeroF\<mapsto> the Element-of (the set)#]"
text_raw {*}%EndSnippet*}


text_raw {*\DefineSnippet{addLoopStrInheritance}{*}
theorem addLoopStr_inheritance[ty_cond_cluster]:
  assumes "X be addLoopStr"
  shows "X be addMagma \<and> X be ZeroStr"
    using addLoopStrA addMagmaA ZeroStrA assms
    by simp
text_raw {*}%EndSnippet*}





lemma addLoopStr_AG[ty_func]: "X be set \<Longrightarrow> B be BinOp-of X \<Longrightarrow> E be Element-of X \<Longrightarrow>
   [#carrier \<mapsto> X ; addF\<mapsto>B ; ZeroF\<mapsto>E#] be addLoopStr"
proof-
  assume A1[ty]: "X be set" "B be BinOp-of X" "E be Element-of X"
  let ?A= "[#carrier \<mapsto> X ; addF\<mapsto>B ; ZeroF\<mapsto>E#]"
  have T1[ty]: "?A be Struct" using Struct_3[of carrier addF ZeroF] by (simp add:string)
  have T: "the carrier of ?A=X" using the_selector_of_1[OF T1, of carrier X] Aggr by auto
  have [ty]:"?A is (carrier \<rightarrow> set')" using Field_1[of ?A carrier X ] Aggr by auto
  have [ty]:"?A is (addF \<rightarrow> BinOp-of' the' carrier)" using Field_1[of ?A addF B ] T Aggr by auto
  have [ty]:"?A is (ZeroF \<rightarrow> Element-of' the' carrier)" using Field_1[of ?A ZeroF E ] T Aggr by auto
  thus ?thesis using T1 addLoopStrA by auto
qed

theorem algstr_0_cl_14[ty_func_cluster]:
  "let (D be non empty\<bar>set \<and> o be BinOp-of D \<and> d be Element-of D)
   cluster [#carrier \<mapsto> D ; addF\<mapsto>o ; ZeroF\<mapsto>d#] \<rightarrow> non empty-struct"
proof-
  assume T0[ty]:"D be non empty\<bar>set \<and> o be BinOp-of D \<and> d be Element-of D"
  let ?X = "[#carrier \<mapsto> D ; addF\<mapsto>o ; ZeroF\<mapsto>d#]"
  have T1[ty]: "?X be addLoopStr" by mauto
  have "the carrier of ?X = D" using the_selector_of_1[of ?X carrier D] Aggr by auto
  thus "?X is non empty-struct" using struct_0_def_1 by mby auto
qed

theorem algstr_0_cl_15[ty_func_cluster]:
  "let T be trivial\<bar>set \<and> f be BinOp-of T \<and> t be Element-of T
   cluster [#carrier\<mapsto>T;addF\<mapsto>f;ZeroF\<mapsto>t#] \<rightarrow> trivial-struct"
proof-
  assume T0[ty]:"T be trivial\<bar>set \<and> f be BinOp-of T \<and> t be Element-of T"
  let ?X = "[#carrier\<mapsto>T;addF\<mapsto>f;ZeroF\<mapsto>t#]"
  have T1[ty]: "?X be addLoopStr" by mauto
  have T2: "the carrier of ?X = T" using the_selector_of_1[of ?X carrier T] Aggr by auto
  show "?X is trivial-struct" using struct_0_def_9[of ?X,rule_format] T2(1) by auto
qed

theorem algstr_0_cl_16[ty_func_cluster]:
  "let N be non trivial\<bar>set \<and> b be BinOp-of N \<and> m be Element-of N
   cluster [#carrier \<mapsto> N ; addF\<mapsto>b ; ZeroF\<mapsto>m#] \<rightarrow> non trivial-struct"
proof-
  assume T0[ty]:"N be non trivial\<bar>set \<and> b be BinOp-of N \<and> m be Element-of N"
  let ?X = "[#carrier \<mapsto> N ; addF\<mapsto>b ; ZeroF\<mapsto>m#]"
  have T1[ty]: "?X be addLoopStr" by mauto
  hence "the carrier of ?X = N" using the_selector_of_1[of ?X carrier N] Aggr by auto
  thus "?X is non trivial-struct" using struct_0_def_9 by auto
qed

abbreviation algstr_0_def_9 ("Trivial-addLoopStr") where
(* "Trivial-addLoopStr \<equiv>
     [#carrier\<mapsto>{op0};addF\<mapsto>op2;ZeroF\<mapsto>op0#]"*)
   "Trivial-addLoopStr \<equiv>
     [# Trivial-addMagma; ZeroF \<mapsto> {} #]"

theorem algstr_0_cl_17[ty_func_cluster]:
  "cluster Trivial-addLoopStr \<rightarrow> 1-element-struct\<bar> strict (addLoopStr)"
proof(unfold ty_intersection,intro conjI)
  let ?T ="Trivial-addLoopStr"
  have T0[ty]: "?T be addLoopStr" by mauto
  have T1: "the carrier of ?T={{}}"
    using the_selector_of_1[of ?T carrier "{{}}"] using Aggr by auto
  thus T2: "?T is 1-element-struct" using T0 struct_0_def_19_a by auto
  have "domain_of addLoopStr = dom ?T" using addLoopStrD Dom_3 by auto
  thus "Trivial-addLoopStr is strict (addLoopStr)" using strict[THEN conjunct2] by auto
qed

theorem algstr_0_cl_18[ex]:
  "cluster strict (addLoopStr)\<bar>1-element-struct for addLoopStr"
  unfolding inhabited_def
proof(intro exI[of _ "Trivial-addLoopStr"],simp,intro conjI)
  show "Trivial-addLoopStr is strict (addLoopStr)" "Trivial-addLoopStr be 1-element-struct"
    by mauto
qed mauto

attr algstr_0_def_10 ("left-complementable\<^sub>_" [200] 200)
   "M be addLoopStr \<Longrightarrow> attr left-complementable\<^sub>M for Element-of-struct M means (\<lambda> x.
                                       (ex y be Element-of-struct M st y \<oplus>\<^sub>M x =0\<^sub>M))"

attr algstr_0_def_11 ("right-complementable\<^sub>_" [200] 200)
   "M be addLoopStr \<Longrightarrow> attr right-complementable\<^sub>M for Element-of-struct M means (\<lambda> x.
                                       (ex y be Element-of-struct M st x \<oplus>\<^sub>M y =0\<^sub>M))"
text_raw {*\DefineSnippet{algstr_0_def_12}{*}
attr algstr_0_def_12 ("add-complementable\<^sub>_" [200] 200)
   " M be addLoopStr\<Longrightarrow>attr add-complementable\<^sub>M for Element-of-struct M means (\<lambda> x.
                                       x is right-complementable\<^sub>M \<bar> left-complementable\<^sub>M)"
text_raw {*}%EndSnippet*}


text_raw {*\DefineSnippet{algstr_0_cl_19}{*}
theorem algstr_0_cl_19[ty_cond_cluster]:
  "let M be addLoopStr
   cluster right-complementable\<^sub>M \<bar> left-complementable\<^sub>M \<rightarrow> add-complementable\<^sub>M for Element-of-struct M"
  using algstr_0_def_12I by auto
text_raw {*}%EndSnippet*}


text_raw {*\DefineSnippet{algstr_0_cl_20}{*}
theorem algstr_0_cl_20[ty_cond_cluster]:
  "let M be addLoopStr
   cluster add-complementable\<^sub>M \<rightarrow> right-complementable\<^sub>M \<bar> left-complementable\<^sub>M for Element-of-struct M"
    using algstr_0_def_12E by auto
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{algstr0def13}{*}
func algstr_0_def_13 ("\<ominus>\<^sub>_ _" [1000, 86] 87) where
 mlet "M be addLoopStr",
          "x be Element-of-struct M"
  "assume x is left-complementable\<^sub>M \<bar> right-add-cancelable\<^sub>M
   func \<ominus>\<^sub>M x \<rightarrow> Element-of-struct M means
     (\<lambda>it. it \<oplus>\<^sub>M x = 0\<^sub>M)"
text_raw {*}%EndSnippet*}
proof-
      assume [ty]:"x is left-complementable\<^sub>M \<bar>right-add-cancelable\<^sub>M"
      thus "ex y be Element-of-struct M st y \<oplus>\<^sub>M x= 0\<^sub>M" using algstr_0_def_10 by mauto
  next
     assume A1[ty]: "x is left-complementable\<^sub>M \<bar>right-add-cancelable\<^sub>M"
     fix y1 y2

     assume T0[ty]: "y1 be Element-of-struct M"
                "y2 be Element-of-struct M"
     assume A2: " y1 \<oplus>\<^sub>M x= 0\<^sub>M" and
    A3: " y2 \<oplus>\<^sub>M x= 0\<^sub>M"
     thus "y1=y2" using algstr_0_def_4E by mauto
  next
     show "inhabited( Element-of-struct M)" by auto
qed

func algstr_0_def_14 ("_ \<ominus>\<^sub>_ _" [66,1000, 67] 66) where
  mlet "M be addLoopStr","x be Element-of-struct M","y be Element-of-struct M"
  "func x \<ominus>\<^sub>M y \<rightarrow> Element-of-struct M equals
     x \<oplus>\<^sub>M \<ominus>\<^sub>M y"
proof-
   show "(x \<oplus>\<^sub>M \<ominus>\<^sub>M y) be Element-of-struct M" using algstr_0_def_1[of M x "\<ominus>\<^sub>M y"] by mauto
qed

theorem algstr_0_cl_21[ty_func_cluster]:
  "cluster Trivial-addLoopStr \<rightarrow> add-cancelable"
proof
  let ?T ="Trivial-addLoopStr"
  have [ty]:"?T be addLoopStr" by mauto
  show T: "?T be addMagma" by simp
       have T1: "the carrier of ?T={{}}"
      using Aggr by (auto intro:the_selector_of_1)
      show "?T is right-add-cancelable"
    proof
      fix x assume T2[ty]: "x be Element-of-struct ?T"
      show "x is right-add-cancelable\<^sub>?T"
      proof
        fix y z assume T3[ty]: "y be Element-of-struct ?T" "z be Element-of-struct ?T"
        assume "y \<oplus>\<^sub>?T x = z \<oplus>\<^sub>?T x"
        show "y = z" by (auto intro: struct_0_def_10a[of ?T])
      qed simp_all
    qed simp_all
  show "?T is left-add-cancelable"
    proof
      fix x assume T2[ty]: "x be Element-of-struct ?T"
      show "x is left-add-cancelable\<^sub>?T"
      proof
        fix y z assume T3[ty]: "y be Element-of-struct ?T" "z be Element-of-struct ?T"
        assume "x \<oplus>\<^sub>?T y = x \<oplus>\<^sub>?T z"
        show "y = z" by (auto intro: struct_0_def_10a[of ?T])
      qed simp_all
    qed simp_all
qed

attr algstr_0_def_15 ("left-complementable")
   "attr left-complementable for addLoopStr means (\<lambda> M. (for x be Element-of-struct M holds x is left-complementable\<^sub>M))"


attr algstr_0_def_16 ("right-complementable")
   "attr right-complementable for addLoopStr means (\<lambda> M.
                                       (for x be Element-of-struct M holds x is right-complementable\<^sub>M))"

attr algstr_0_def_17 ("complementable")
   "attr complementable for addLoopStr means (\<lambda> M.
                                       M is right-complementable \<bar> left-complementable)"

theorem algstr_0_cl_22[ty_cond_cluster]:
  "cluster right-complementable \<bar> left-complementable \<rightarrow> complementable for addLoopStr" using algstr_0_def_17 by auto


theorem algstr_0_cl_23[ty_cond_cluster]:
  "cluster complementable \<rightarrow> right-complementable \<bar> left-complementable for addLoopStr" using algstr_0_def_17 by auto


theorem algstr_0_cl_24[ty_func_cluster]:
  "cluster Trivial-addLoopStr \<rightarrow> complementable"
proof
  let ?T ="Trivial-addLoopStr"
  have [ty]:"?T be addLoopStr" by mauto
  have T1: "the carrier of ?T={{}}"
    using Aggr by (auto intro: the_selector_of_1)

  show "?T is right-complementable"
    proof
      fix x assume T2[ty]: "x be Element-of-struct ?T"
      show "x is right-complementable\<^sub>?T"
      proof
        show "x be Element-of-struct ?T" using T2 by simp
        have "x \<oplus>\<^sub>?T x = 0\<^sub>?T" by (intro struct_0_def_10a[of ?T]) mauto
        thus "ex y be Element-of-struct ?T st x \<oplus>\<^sub>?T y = 0\<^sub>?T" using bexI[of _ _ x] by mauto
      qed simp_all
    qed simp_all
  show "?T is left-complementable"
    proof
      fix x assume T2[ty]: "x be Element-of-struct ?T"
      show "x is left-complementable\<^sub>?T"
      proof
        show "x be Element-of-struct ?T" using T2 by simp
        have "x \<oplus>\<^sub>?T x =0\<^sub>?T" by (intro struct_0_def_10a[of ?T]) mauto
        thus "ex y be Element-of-struct ?T st y \<oplus>\<^sub>?T x = 0\<^sub>?T" using bexI[of _ _ x] by mauto
      qed simp_all
    qed simp_all
  qed mauto

theorem algstr_0_cl_25[ex]:
  "cluster complementable\<bar>add-cancelable\<bar>strict (addLoopStr)\<bar>1-element-struct for addLoopStr"
unfolding inhabited_def
proof(intro exI)
  show "Trivial-addLoopStr be complementable\<bar>add-cancelable\<bar>strict (addLoopStr)\<bar>1-element-struct\<bar>addLoopStr"
    by mty auto
qed



theorem algstr_0_cl_26[ty_cond_cluster]:
  "let M be left-complementable \<bar> addLoopStr
   cluster \<rightarrow> left-complementable\<^sub>M for Element-of-struct M"
proof (rule algstr_0_def_15E, simp_all, elim conjE)
  fix X
  assume [ty]:"M is left-complementable" "M is addLoopStr" "X is Element-of-struct M"
  show "inhabited(Element-of-struct M)" by simp
qed


theorem algstr_0_cl_27[ty_cond_cluster]:
  "let M be right-complementable \<bar> addLoopStr
   cluster \<rightarrow> right-complementable\<^sub>M for Element-of-struct M"
proof (rule algstr_0_def_16E, simp_all, elim conjE)
  fix X
  assume [ty]:"M is right-complementable" "M is addLoopStr" "X is Element-of-struct M"
  then show "inhabited(Element-of-struct M)" by simp
qed

section "Multiplicative structures"


abbreviation "multMagma_fields \<equiv> (#carrier \<rightarrow> set';multF\<rightarrow> BinOp-of' the' carrier #)"

text_raw {*\DefineSnippet{multMagma}{*}
mdefinition multMagma_d ("multMagma") where
  "struct multMagma (#
  carrier \<rightarrow> set';
  multF\<rightarrow> BinOp-of' the' carrier #)"
  :well_defined_property[of _ _ "{carrier}\<union>{multF}"]
  by (auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)
text_raw {*}%EndSnippet*}
(*  :struct_well_defined
proof(rule Fields_add_argM1[OF one_sorted(5)],simp add:string,simp add:string)
   fix X1 assume "X1 be one_sorted_fields\<bar>Struct"
    hence "the carrier of X1 be set" using field by auto
    thus "inhabited(BinOp-of-struct X1)" using BinOp_ex by auto
  qed (simp_all add:string)
*)

lemmas multMagmaA = multMagma_d(1)
lemmas [ex] = multMagma_d(2,3)
lemmas multMagmaD = multMagma_d(4)
lemmas multMagmaR = multMagma_d(5)

theorem multMagma_inheritance[ty_parent]:
  "X be multMagma \<Longrightarrow> X be 1-sorted" using multMagmaA one_sortedA by simp

theorem multMagma_inheritance1[ty_func]:
  "X be multMagma \<Longrightarrow> (the multF of X) be BinOp-of (the carrier of X)" using field multMagmaA by auto

lemma multMagma_AG[rule_format,ty_func]: "X be set \<Longrightarrow> B be BinOp-of X \<Longrightarrow>
   [#carrier\<mapsto>X;multF\<mapsto>B#] be multMagma"
proof-
  assume [ty]: "X be set" "B be BinOp-of X"
  let ?A= "[#carrier\<mapsto>X;multF\<mapsto>B#]"
  have [ty]:"?A be Struct" using Struct_2[of carrier multF] by (simp add:string)
  have T: "the carrier of ?A=X" using the_selector_of_1[of ?A carrier "X"] Aggr by auto
  have [ty]:"?A is (carrier \<rightarrow> set')" using Field_1[of ?A carrier X ] Aggr by auto
  have [ty]:"?A is (multF \<rightarrow> BinOp-of' the' carrier)" using Field_1[of ?A multF B ] T Aggr by auto
  thus ?thesis using multMagmaA by auto
qed

theorem algstr_0_cl_28[rule_format,ty_func_cluster]:
  "let D be non empty\<bar>set \<and> o be BinOp-of D
   cluster [#carrier\<mapsto>D;multF\<mapsto>o#] \<rightarrow> non empty-struct"
proof-
  assume [ty]:"D be non empty\<bar>set \<and> o be BinOp-of D"
  let ?X = "[#carrier\<mapsto>D;multF\<mapsto>o#]"
  have [ty]: "?X be multMagma" by mauto
  have "the carrier of ?X = D" using the_selector_of_1[of ?X carrier D] Aggr by auto
  thus "?X is non empty-struct" using struct_0_def_1 by auto
qed

theorem algstr_0_cl_29[ty_func_cluster]:
  "let T be trivial\<bar>set \<and> f be BinOp-of T
   cluster [#carrier\<mapsto>T;multF\<mapsto>f#] \<rightarrow> trivial-struct"
proof-
  assume T0[ty]:"T be trivial\<bar>set \<and> f be BinOp-of T"
  let ?X = "[#carrier\<mapsto>T;multF\<mapsto>f#]"
  have T2: "the carrier of ?X = T" "?X be 1-sorted" using the_selector_of_1[of ?X carrier T] Aggr by mauto
  thus "?X is trivial-struct" using struct_0_def_9 by auto
qed

theorem algstr_0_cl_30[ty_func_cluster]:
  "let N be non trivial\<bar>set \<and> b be BinOp-of N
   cluster [#carrier\<mapsto>N;multF\<mapsto>b#] \<rightarrow> non trivial-struct"
proof-
  assume T0[ty]:"N be non trivial\<bar>set \<and> b be BinOp-of N"
  let ?X = "[#carrier\<mapsto>N;multF\<mapsto>b#]"
  have T1[ty]: "?X be multMagma" by mauto
  hence T2: "the carrier of ?X = N" using the_selector_of_1[of ?X carrier N] Aggr by auto
  show "?X is non trivial-struct" using struct_0_def_9[of ?X] T2(1) by auto
qed

text_raw {*\DefineSnippet{algstr0def18}{*}
func algstr_0_def_18 ("_ \<otimes>\<^sub>_ _" [96, 1000, 97] 96) where
mlet "M be multMagma "," x be Element-of-struct M","
         y be Element-of-struct M"
  "func x \<otimes>\<^sub>M y \<rightarrow> Element-of-struct M equals
     (the multF of M) . \<lparr> x , y \<rparr>"
text_raw {*}%EndSnippet*}
proof-
   let ?A = "the carrier of M"
   have A1: "(the multF of M) be BinOp-of ?A" "?A be set" using multMagmaA field one_sortedA by auto
   thus " (the multF of M) .  \<lparr> x , y \<rparr> be Element-of ?A"
           using binop_0_def_20A by auto
qed

abbreviation algstr_0_def_19 ("Trivial-multMagma") where
  "Trivial-multMagma \<equiv> [#carrier\<mapsto>{{}};multF\<mapsto>op2#]"

theorem algstr_0_cl_31[rule_format,ty_func_cluster]:
  "cluster Trivial-multMagma \<rightarrow> 1-element-struct\<bar> strict (multMagma)"
proof(unfold ty_intersection,intro conjI)
  let ?T ="Trivial-multMagma"
  have T0[ty]: "?T be multMagma" by mauto
  hence T1: "the carrier of ?T={{}}"
    using the_selector_of_1[of ?T carrier "{{}}"] using Aggr by auto
  thus T2: "Trivial-multMagma is 1-element-struct" using T0 struct_0_def_19_a by auto
  have "domain_of multMagma = dom ?T" using multMagmaD Dom_2 by auto
  thus "Trivial-multMagma is strict (multMagma)" using T2 strict[THEN conjunct2] T0 by auto
qed

theorem algstr_0_cl_32[ex]:
  "cluster strict (multMagma)\<bar>1-element-struct for multMagma"
   unfolding inhabited_def
proof
  show "Trivial-multMagma is strict(multMagma) \<bar> 1-element-struct \<bar> multMagma" by mauto
qed


attr algstr_0_def_20 ("left-mult-cancelable\<^sub>_" [200] 200)
   "M be multMagma \<Longrightarrow> attr left-mult-cancelable\<^sub>M for Element-of-struct M means
(\<lambda> x.
                                       (for y,z be Element-of-struct M st x \<otimes>\<^sub>M y = x \<otimes>\<^sub>M z holds y = z))"


attr algstr_0_def_21 ("right-mult-cancelable\<^sub>_" [200] 200)
   " M be multMagma\<Longrightarrow>attr right-mult-cancelable\<^sub>M for Element-of-struct M means (\<lambda> x.
                                       (for y,z be Element-of-struct M st y \<otimes>\<^sub>M x = z \<otimes>\<^sub>M x holds y = z))"

attr algstr_0_def_22 ("mult-cancelable\<^sub>_" [200] 200)
   " M be multMagma\<Longrightarrow>attr mult-cancelable\<^sub>M for Element-of-struct M means (\<lambda> x.
                                       x is right-mult-cancelable\<^sub>M \<bar> left-mult-cancelable\<^sub>M)"

theorem algstr_0_cl_33[ty_cond_cluster]:
  "let M be multMagma
   cluster right-mult-cancelable\<^sub>M \<bar> left-mult-cancelable\<^sub>M \<rightarrow> mult-cancelable\<^sub>M for Element-of-struct M" using algstr_0_def_22 by auto

theorem algstr_0_cl_34[ty_cond_cluster]:
  "let M be multMagma
   cluster mult-cancelable\<^sub>M \<rightarrow> right-mult-cancelable\<^sub>M \<bar> left-mult-cancelable\<^sub>M for Element-of-struct M" using algstr_0_def_22 by auto

attr algstr_0_def_23 ("left-mult-cancelable")
   "attr left-mult-cancelable for multMagma means (\<lambda> M.  (for x be Element-of-struct M holds x is left-mult-cancelable\<^sub>M))"

attr algstr_0_def_24 ("right-mult-cancelable")
   "attr right-mult-cancelable for multMagma means (\<lambda> M.
                                       (for x be Element-of-struct M holds x is right-mult-cancelable\<^sub>M))"

attr algstr_0_def_25 ("mult-cancelable")
   "attr mult-cancelable for multMagma means (\<lambda>M.
                                       M is right-mult-cancelable \<bar> left-mult-cancelable)"

theorem algstr_0_cl_35[ty_cond_cluster]:
  "cluster right-mult-cancelable \<bar> left-mult-cancelable \<rightarrow> mult-cancelable for multMagma" using algstr_0_def_25 by auto

theorem algstr_0_cl_36[ty_cond_cluster]:
  "cluster mult-cancelable \<rightarrow> right-mult-cancelable \<bar> left-mult-cancelable for multMagma" using algstr_0_def_25 by auto

mtheorem algstr_0_cl_37[rule_format,ty_func_cluster]:
  "cluster Trivial-multMagma \<rightarrow> mult-cancelable"
proof
  let ?T ="Trivial-multMagma"
  have [ty]: "?T be multMagma" by auto
  have T1: "the carrier of ?T={{}}"
    using Aggr by (auto intro: the_selector_of_1)

  show "?T is right-mult-cancelable"
    proof
      fix x assume T2[ty]: "x be Element-of-struct ?T"
      show "x is right-mult-cancelable\<^sub>?T"
      proof
        fix y z assume T3[ty]: "y be Element-of-struct ?T" "z be Element-of-struct ?T"
        assume "y \<otimes>\<^sub>?T x = z \<otimes>\<^sub>?T x"
        show "y = z" by (auto intro: struct_0_def_10a[of ?T])
      qed simp_all
    qed simp_all
  show "?T is left-mult-cancelable"
    proof
      fix x assume T2[ty]: "x be Element-of-struct ?T"
      show "x is left-mult-cancelable\<^sub>?T"
      proof
        fix y z assume T3[ty]: "y be Element-of-struct ?T" "z be Element-of-struct ?T"
        assume "x \<otimes>\<^sub>?T y = x \<otimes>\<^sub>?T z"
        show "y = z" by (auto intro: struct_0_def_10a[of ?T])
      qed simp_all
    qed simp_all
qed mauto


theorem algstr_0_cl_38[ex]:
  "cluster mult-cancelable\<bar>strict (multMagma)\<bar>1-element-struct for multMagma"
  unfolding inhabited_def
proof(intro exI)
  show "Trivial-multMagma is mult-cancelable\<bar>strict (multMagma)\<bar>1-element-struct\<bar>multMagma"
     by mauto
qed



theorem algstr_0_cl_39[ty_cond_cluster]:
  "let M be left-mult-cancelable \<bar> multMagma
   cluster \<rightarrow> left-mult-cancelable\<^sub>M for Element-of-struct M"
proof-
  fix X assume [ty]:"M be left-mult-cancelable \<bar> multMagma" "X be Element-of-struct M"
  show "X be left-mult-cancelable\<^sub>M"
        using algstr_0_def_23E[of M X] by auto
qed

theorem algstr_0_cl_40[ty_cond_cluster]:
  "let M be right-mult-cancelable \<bar> multMagma
   cluster \<rightarrow> right-mult-cancelable\<^sub>M for Element-of-struct M"
proof-
  fix X assume [ty]:"M be right-mult-cancelable \<bar> multMagma" "X be Element-of-struct M"
  show "X be right-mult-cancelable\<^sub>M"
        using algstr_0_def_24E[of M X] by auto
    qed

abbreviation "multLoopStr_fields \<equiv> (#carrier \<rightarrow> set'; OneF \<rightarrow> Element-of' the' carrier; multF\<rightarrow> BinOp-of' the' carrier #)"

mdefinition multLoopStr_d ("multLoopStr") where
  "struct multLoopStr multLoopStr_fields"
:well_defined_property[of _ _ "{carrier}\<union>{OneF}\<union>{multF}"]
  by (auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)
(*:struct_well_defined
proof(rule Fields_add_argM1[OF OneStr_d(5)],simp add:string,simp add:string)
    fix X1 assume "X1 be OneStr_fields\<bar>Struct"
    hence "the carrier of X1 be set" using field by auto
    thus "inhabited(BinOp-of the carrier of X1)" by auto
  qed*)


lemmas multLoopStrA =  multLoopStr_d(1)
lemmas [ex] =  multLoopStr_d(2,3)
lemmas multLoopStrD =  multLoopStr_d(4)
lemmas multLoopStrR =  multLoopStr_d(5)

theorem multLoopStr_inheritance[ty_parent]:
  "X be multLoopStr \<Longrightarrow> X be multMagma \<and>  X be OneStr" using multLoopStrA multMagmaA OneStrA by auto

lemma multLoopStr_AG[ty_func]: "X be set \<Longrightarrow> B be BinOp-of X \<Longrightarrow> E be Element-of X \<Longrightarrow>
   [#carrier\<mapsto>X ; multF\<mapsto> B;OneF\<mapsto>E#] be multLoopStr"
proof-
  assume [ty]: "X be set" "B be BinOp-of X" "E be Element-of X"
  let ?A= "[#carrier\<mapsto>X ; multF\<mapsto> B;OneF\<mapsto>E#]"
  have [ty]: "?A be Struct" using Struct_3[of carrier multF OneF] by (simp add:string)
  have T:"the carrier of ?A=X" using the_selector_of_1[of ?A carrier X] Aggr by auto
  have [ty]:"?A is (carrier \<rightarrow> set')" using Field_1[of ?A carrier X ] Aggr by auto
  have [ty]:"?A is (multF \<rightarrow> BinOp-of' the' carrier)" using Field_1[of ?A multF B ] T Aggr by auto
  have [ty]:"?A is (OneF \<rightarrow> Element-of' the' carrier)" using Field_1[of ?A OneF E ] T Aggr by auto
  thus ?thesis using multLoopStrA by auto
qed

theorem algstr_0_cl_41[ty_func_cluster]:
  "let D be non empty\<bar>set \<and> o be BinOp-of D \<and> d be Element-of D
   cluster [#carrier\<mapsto>D ; multF\<mapsto> o;OneF\<mapsto>d#] \<rightarrow> non empty-struct"
proof-
  assume T0[ty]:"D be non empty\<bar>set \<and> o be BinOp-of D \<and> d be Element-of D"
  let ?X = "[#carrier\<mapsto>D ; multF\<mapsto> o;OneF\<mapsto>d#]"
  have T1[ty]:"?X be multLoopStr" by mauto
  have "the carrier of ?X = D" using the_selector_of_1[of ?X carrier D]  Aggr by auto
  thus "?X is non empty-struct" using struct_0_def_1 by simp
qed

theorem algstr_0_cl_42[ty_func_cluster]:
  "let T be trivial\<bar>set \<and> f be BinOp-of T \<and> t be Element-of T
   cluster [#carrier\<mapsto>T ; multF\<mapsto> f;OneF\<mapsto>t#] \<rightarrow> trivial-struct"
proof-
  assume T0[ty]:"T be trivial\<bar>set \<and> f be BinOp-of T \<and> t be Element-of T"
  let ?X = "[#carrier\<mapsto>T ; multF\<mapsto> f;OneF\<mapsto>t#]"
  have T1[ty]: "?X be multLoopStr" by mauto
  hence T2: "the carrier of ?X = T" "?X be 1-sorted" using the_selector_of_1[of ?X carrier T]
    Aggr by auto
  thus "?X is trivial-struct" using struct_0_def_9[of ?X,THEN iffD2,rule_format] T0 T1 by auto
qed



theorem algstr_0_cl_43[ty_func_cluster]:
  "let N be non trivial\<bar>set \<and> b be BinOp-of N \<and> m be Element-of N
   cluster [#carrier\<mapsto>N ; multF\<mapsto> b;OneF\<mapsto>m#] \<rightarrow> non trivial-struct"
proof-
  assume T0[ty]:"N be non trivial\<bar>set \<and> b be BinOp-of N \<and> m be Element-of N"
  let ?X = "[#carrier\<mapsto>N ; multF\<mapsto> b;OneF\<mapsto>m#]"
  have T1[ty]: "?X be multLoopStr" by mauto
  hence T2: "the carrier of ?X = N" using the_selector_of_1[of ?X carrier N] Aggr by auto
  show "?X is non trivial-struct" using struct_0_def_9 T2(1) by auto
qed

abbreviation algstr_0_def_26 ("Trivial-multLoopStr") where
(* "Trivial-multLoopStr \<equiv> [#carrier\<mapsto>{{}} ; multF\<mapsto> op2;OneF\<mapsto>op0#]" *)
   "Trivial-multLoopStr \<equiv> [# Trivial-multMagma; OneF \<mapsto> {} #]"

theorem algstr_0_cl_44[ty_func_cluster]:
  "cluster Trivial-multLoopStr \<rightarrow> 1-element-struct\<bar> strict (multLoopStr)"
proof(unfold ty_intersection,intro conjI)
  let ?T ="Trivial-multLoopStr"
  have T0[ty]: "?T be multLoopStr" by mauto
  hence T1: "the carrier of ?T={{}}"
    using Aggr by (auto intro: the_selector_of_1)
  thus T2: "Trivial-multLoopStr is 1-element-struct" using T0 struct_0_def_19_a by auto
  have "domain_of multLoopStr = dom ?T" unfolding multLoopStrD Dom_3 using string by (intro tarski_th_2) mauto
  thus "Trivial-multLoopStr is strict (multLoopStr)" using T2 strict[THEN conjunct2] T0 by auto
qed

theorem algstr_0_cl_45[ex]:
  "cluster strict (multLoopStr)\<bar>1-element-struct for multLoopStr"
 unfolding inhabited_def
proof(intro exI)
  show "Trivial-multLoopStr is strict (multLoopStr)\<bar>1-element-struct \<bar> multLoopStr" by mty auto
qed

theorem algstr_0_cl_46[ty_func_cluster]:
  "cluster Trivial-multLoopStr \<rightarrow> mult-cancelable"
proof
  let ?T ="Trivial-multLoopStr"
  show [ty]:"?T be multMagma" by mty auto
  have T1: "the carrier of ?T={{}}"
    using Aggr by (auto intro: the_selector_of_1)
  show "?T is right-mult-cancelable"
  proof
      fix x assume T2[ty]: "x be Element-of-struct ?T"
      show "x is right-mult-cancelable\<^sub>?T"
      proof
        fix y z assume T3[ty]: "y be Element-of-struct ?T" "z be Element-of-struct ?T"
        assume "y \<otimes>\<^sub>?T x = z \<otimes>\<^sub>?T x"
        show "y = z" by (auto intro: struct_0_def_10a[of ?T])
      qed simp_all
    qed simp_all
  show "?T is left-mult-cancelable"
    proof
      fix x assume T2[ty]: "x be Element-of-struct ?T"
      show "x is left-mult-cancelable\<^sub>?T"
      proof
        fix y z assume T3[ty]: "y be Element-of-struct ?T" "z be Element-of-struct ?T"
        assume "x \<otimes>\<^sub>?T y = x \<otimes>\<^sub>?T z"
        show "y = z" by (auto intro: struct_0_def_10a[of ?T])
      qed simp_all
    qed simp_all
qed


attr algstr_0_def_27 ("left-invertible\<^sub>_" [200] 200)
   "M be multLoopStr\<Longrightarrow>attr left-invertible\<^sub>M for Element-of-struct M means (\<lambda> x.
                                       (ex y be Element-of-struct M st y \<otimes>\<^sub>M x =1\<^sub>M))"

attr algstr_0_def_28 ("right-invertible\<^sub>_" [200] 200)
   "M be multLoopStr\<Longrightarrow>attr right-invertible\<^sub>M for Element-of-struct M means (\<lambda> x.
                                       (ex y be Element-of-struct M st x \<otimes>\<^sub>M y =1\<^sub>M))"

attr algstr_0_def_29 ("mult-invertible\<^sub>_" [200] 200)
   "M be multLoopStr\<Longrightarrow> attr mult-invertible\<^sub>M for Element-of-struct M means (\<lambda> x.
                                       x is right-invertible\<^sub>M \<bar> left-invertible\<^sub>M)"

theorem algstr_0_cl_47[ty_cond_cluster]:
  "let M be multLoopStr
   cluster right-invertible\<^sub>M \<bar> left-invertible\<^sub>M \<rightarrow> mult-invertible\<^sub>M for Element-of-struct M"
     using algstr_0_def_29 by auto

theorem algstr_0_cl_48[ty_cond_cluster]:
  "let M be multLoopStr
   cluster mult-invertible\<^sub>M \<rightarrow> right-invertible\<^sub>M \<bar> left-invertible\<^sub>M for Element-of-struct M"
  using algstr_0_def_29 by auto

text_raw {*\DefineSnippet{algstr0def30}{*}
func algstr_0_def_30 ("'/\<^sub>_ _" [1000, 99] 98) where
  mlet "M be multLoopStr",
          "x be Element-of-struct M"
  "assume x is left-invertible\<^sub>M \<bar> right-mult-cancelable\<^sub>M
   func /\<^sub>M x \<rightarrow> Element-of-struct M means
     (\<lambda>it. it \<otimes>\<^sub>M x = 1\<^sub>M)"
text_raw {*}%EndSnippet*}
proof-
     assume[ty]: "x is left-invertible\<^sub>M \<bar>right-mult-cancelable\<^sub>M"
     show "ex y be Element-of-struct M st y \<otimes>\<^sub>M x= 1\<^sub>M" using algstr_0_def_27[THEN iffD1] by mauto
  next
     assume A1[ty]: "x is (left-invertible\<^sub>M \<bar>right-mult-cancelable\<^sub>M)"
     fix y1 y2
        have I:"inhabited(Element-of-struct M)" by auto
     assume T0[ty]: "y1 be Element-of-struct M"
                "y2 be Element-of-struct M"
     assume
    A2: " y1 \<otimes>\<^sub>M x= 1\<^sub>M" and
    A3: " y2 \<otimes>\<^sub>M x= 1\<^sub>M"
    thus "y1=y2" using algstr_0_def_21E by mauto (* Example for the need of mby *)
qed simp_all


attr algstr_0_def_31 ("left-invertible")
   "attr left-invertible for multLoopStr means (\<lambda> M.  (for x be Element-of-struct M holds x is left-invertible\<^sub>M))"


attr algstr_0_def_32 ("right-invertible")
   "attr right-invertible for multLoopStr means (\<lambda> M.
                                       (for x be Element-of-struct M holds x is right-invertible\<^sub>M))"

attr algstr_0_def_33 ("invertible")
   "attr invertible for multLoopStr means (\<lambda> M.
                                       M is right-invertible \<bar> left-invertible)"

theorem algstr_0_cl_49[ty_cond_cluster]:
  "cluster right-invertible \<bar> left-invertible \<rightarrow> invertible for multLoopStr" using algstr_0_def_33 by auto

theorem algstr_0_cl_50[ty_cond_cluster]:
  "cluster invertible \<rightarrow> right-invertible \<bar> left-invertible for multLoopStr" using algstr_0_def_33 by auto

theorem algstr_0_cl_51[ty_func_cluster]:
  "cluster Trivial-multLoopStr \<rightarrow> invertible"
proof
  let ?T ="Trivial-multLoopStr"
  have [ty]:"?T be multLoopStr" by mauto
  have T1: "the carrier of ?T={{}}"
    using Aggr by (auto intro: the_selector_of_1)
  have Z: "1\<^sub>?T be Element-of-struct ?T" by mauto
  show "?T is right-invertible"
    proof
      fix x assume T2[ty]:"x be Element-of-struct ?T"
      hence T3: "(x \<otimes>\<^sub>?T x) be Element-of-struct ?T" by mauto
      show "x is right-invertible\<^sub>?T"
      proof
        show "x be Element-of-struct ?T" by simp
        have "x \<otimes>\<^sub>?T x =1\<^sub>?T" by mty (auto intro: struct_0_def_10a[of ?T])
        thus "ex y be Element-of-struct ?T st x \<otimes>\<^sub>?T y =1\<^sub>?T" using bexI[of _ _ x] by mauto
      qed simp_all
    qed simp_all
  show "?T is left-invertible"
    proof
      fix x assume T2[ty]: "x be Element-of-struct ?T"
      show "x is left-invertible\<^sub>?T"
      proof
        show "x be Element-of-struct ?T" by simp
        have "x \<otimes>\<^sub>?T x =1\<^sub>?T" by mty (auto intro: struct_0_def_10a[of ?T])
        thus "ex y be Element-of-struct ?T st y \<otimes>\<^sub>?T x =1\<^sub>?T" using bexI[of _ _ x] by mauto
      qed simp_all
    qed simp_all
qed mauto

theorem algstr_0_cl_52[ex]:
  "cluster invertible\<bar>mult-cancelable\<bar>strict (multLoopStr)\<bar>1-element-struct for multLoopStr"
 unfolding inhabited_def
proof(intro exI)
     show "Trivial-multLoopStr is invertible\<bar>mult-cancelable\<bar>strict (multLoopStr)\<bar>1-element-struct\<bar> multLoopStr"
        by mty auto
qed


theorem algstr_0_cl_53[ty_cond_cluster]:
  "let M be left-invertible \<bar> multLoopStr
   cluster \<rightarrow> left-invertible\<^sub>M for Element-of-struct M"
proof-
  fix X assume T[ty]:"M be left-invertible \<bar> multLoopStr" "X be Element-of-struct M"
  show "X be left-invertible\<^sub>M" using algstr_0_def_31E by auto
qed



theorem algstr_0_cl_54[ty_cond_cluster]:
  "let M be right-invertible \<bar> multLoopStr
   cluster \<rightarrow> right-invertible\<^sub>M for Element-of-struct M"
proof-
  fix X assume T[ty]:"M be right-invertible \<bar> multLoopStr" "X be Element-of-struct M"
  show "X be right-invertible\<^sub>M" using algstr_0_def_32E by auto
qed


(*begin :: Almost*)
abbreviation "multLoopStr_0_fields \<equiv> (#carrier \<rightarrow> set';  multF\<rightarrow> BinOp-of' the' carrier; ZeroF \<rightarrow> Element-of' the' carrier;
      OneF \<rightarrow> Element-of' the' carrier #)"

mdefinition multLoopStr_0_d ("multLoopStr'_0") where
  "struct multLoopStr_0 multLoopStr_0_fields"
:well_defined_property[of _ _ "{carrier} \<union>{multF}\<union>{ZeroF}\<union>{OneF}"]
  by (auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)
(*:struct_well_defined
proof-
  have multLoopStr_0_well_pre: "multLoopStr_fields \<bar>(# ZeroF \<rightarrow> Element-of' the' carrier #)
                           well defined on {carrier} \<union>{OneF}\<union>{multF}\<union>{ZeroF} "
  proof(rule Fields_add_argM1[OF multLoopStr_d(5)],simp add:string,simp add:string)
   fix X1 assume "X1 be multLoopStr_fields\<bar>Struct"
    hence "the carrier of X1 be set" using field by auto
    thus "inhabited(Element-of the carrier of X1)" using subset_1_def_1 by auto
  qed
  have A0: "{carrier} \<union>{OneF}\<union>{multF}\<union>{ZeroF} = {carrier} \<union>{multF}\<union>{ZeroF}\<union>{OneF}"
      using string(7) by mty (auto intro: tarski_0_2a)
  have A1: "\<And>X. X is multLoopStr_fields \<bar>(# ZeroF \<rightarrow> Element-of' the' carrier #)
            \<longleftrightarrow> X is multLoopStr_0_fields"
     by auto
  show "multLoopStr_0_fields well defined on {carrier} \<union>{multF}\<union>{ZeroF}\<union>{OneF} " using
      well_defined_order[OF A1 multLoopStr_0_well_pre] A0 by auto
qed *)


lemmas multLoopStr_0A = multLoopStr_0_d(1)
lemmas [ex] = multLoopStr_0_d(2,3)
lemmas multLoopStr_0D = multLoopStr_0_d(4)
lemmas multLoopStr_0R = multLoopStr_0_d(5)

theorem multLoopStr_0_inheritance[ty_parent]:
  "X be multLoopStr_0 \<Longrightarrow> X be multLoopStr \<and> X be ZeroOneStr" using multLoopStr_0A multLoopStrA ZeroOneStrA by simp

lemma multLoopStr_0_AG[ty_func]: "X be set \<Longrightarrow> B be BinOp-of X \<Longrightarrow> Z be Element-of X \<Longrightarrow> E be Element-of X \<Longrightarrow>
   [#carrier\<mapsto>X ; multF\<mapsto>B ; ZeroF\<mapsto>Z ; OneF\<mapsto>E#] be multLoopStr_0"
proof-
  assume A1[ty]: "X be set" "B be BinOp-of X" "Z be Element-of X"   "E be Element-of X"
  let ?A= "[#carrier\<mapsto>X ; multF\<mapsto>B ; ZeroF\<mapsto>Z ; OneF\<mapsto>E#]"
  have T1[ty]: "?A be Struct" using Struct_4[of carrier multF ZeroF OneF] string by simp
  have T: "the carrier of ?A=X" using Aggr by (auto intro: the_selector_of_1)
  have [ty]:"?A is (carrier \<rightarrow> set')" using Field_1[of ?A carrier X ] Aggr by auto
  have [ty]:"?A is (multF \<rightarrow> BinOp-of' the' carrier)" using Field_1[of ?A multF B ] T Aggr by auto
  have [ty]:"?A is (ZeroF \<rightarrow> Element-of' the' carrier)" using Field_1[of ?A ZeroF Z ] T Aggr by auto
  have [ty]:"?A is (OneF \<rightarrow> Element-of' the' carrier)" using Field_1[of ?A OneF E ] T Aggr by auto
  show ?thesis using multLoopStr_0A by auto
qed

theorem algstr_0_cl_55[ty_func_cluster]:
  "let D be non empty\<bar>set \<and> o be BinOp-of D \<and> d be Element-of D \<and> e be Element-of D
   cluster [#carrier\<mapsto>D ; multF\<mapsto>o ; ZeroF\<mapsto>d ; OneF\<mapsto>e#] \<rightarrow> non empty-struct"
proof-
  assume T0[ty]:"D be non empty\<bar>set \<and> o be BinOp-of D \<and> d be Element-of D \<and> e be Element-of D"
  let ?X = "[#carrier\<mapsto>D ; multF\<mapsto>o ; ZeroF\<mapsto>d ; OneF\<mapsto>e#]"
  have T1[ty]: "?X be multLoopStr_0" by mauto
  have "the carrier of ?X = D" using the_selector_of_1[of ?X carrier D] Aggr by auto
  thus "?X is non empty-struct" using struct_0_def_1 by auto
qed

theorem algstr_0_cl_56[ty_func_cluster]:
  "let T be trivial\<bar>set \<and> f be BinOp-of T \<and> s be Element-of T \<and> t be Element-of T
   cluster [#carrier\<mapsto>T ; multF\<mapsto>f ; ZeroF\<mapsto>s ; OneF\<mapsto>t#] \<rightarrow> trivial-struct"
proof-
  assume T0[ty]:"T be trivial\<bar>set \<and> f be BinOp-of T \<and> s be Element-of T \<and> t be Element-of T"
  let ?X = "[#carrier\<mapsto>T ; multF\<mapsto>f ; ZeroF\<mapsto>s ; OneF\<mapsto>t#]"
  have T1[ty]: "?X be multLoopStr_0" by mauto
  hence T2: "the carrier of ?X = T" using the_selector_of_1[of ?X carrier T] Aggr by auto
  show "?X is trivial-struct" using struct_0_def_9 T0 T2(1) by auto
qed

theorem algstr_0_cl_57[ty_func_cluster]:
  "let N be non trivial\<bar>set \<and> b be BinOp-of N \<and> m be Element-of N \<and> n be Element-of N
   cluster [#carrier\<mapsto>N ; multF\<mapsto>b ; ZeroF\<mapsto>m ; OneF\<mapsto>n#] \<rightarrow> non trivial-struct"
proof-
  assume T0[ty]:"N be non trivial\<bar>set \<and> b be BinOp-of N \<and> m be Element-of N \<and> n be Element-of N"
  let ?X = "[#carrier\<mapsto>N ; multF\<mapsto>b ; ZeroF\<mapsto>m ; OneF\<mapsto>n#]"
  have T1[ty]: "?X be multLoopStr_0" by mauto
  hence T2: "the carrier of ?X = N" using the_selector_of_1[of ?X carrier N] Aggr by auto
  show "?X is non trivial-struct" using struct_0_def_9 T2(1) by auto
qed

abbreviation algstr_0_def_34 ("Trivial-multLoopStr'_0") where
(*  "Trivial-multLoopStr_0 \<equiv>
     [#carrier\<mapsto>{{}} ; multF\<mapsto>op2 ; ZeroF\<mapsto>op0 ; OneF\<mapsto>op0#]"*)
  "Trivial-multLoopStr_0 \<equiv>
     [# Trivial-multMagma; ZeroF \<mapsto> {} ; OneF \<mapsto> {} #]"

theorem algstr_0_cl_58[ty_func_cluster]:
  "cluster Trivial-multLoopStr_0 \<rightarrow> 1-element-struct\<bar> strict (multLoopStr_0)"
proof(unfold ty_intersection,intro conjI)
  let ?T ="Trivial-multLoopStr_0"
  have T0[ty]: "?T be multLoopStr_0" by mauto
  hence T1: "the carrier of ?T={{}}"
    using Aggr by (auto intro: the_selector_of_1)
  thus T2: "Trivial-multLoopStr_0 is 1-element-struct" using struct_0_def_19_a by auto
  have "domain_of multLoopStr_0 = dom ?T" using multLoopStr_0D Dom_4 by auto
  thus "Trivial-multLoopStr_0 is strict (multLoopStr_0)" using strict[THEN conjunct2] by auto
qed

theorem algstr_0_cl_59[ex]:
  "cluster strict (multLoopStr_0)\<bar>1-element-struct for multLoopStr_0"
unfolding inhabited_def
proof(intro exI)
  show "Trivial-multLoopStr_0 is strict (multLoopStr_0)\<bar>1-element-struct\<bar>multLoopStr_0" by mauto
qed

attr algstr_0_def_36 ("almost-left-cancelable")
   "attr almost-left-cancelable for multLoopStr_0 means (\<lambda> M.
                                       (for x be Element-of-struct M st x \<noteq> 0\<^sub>M holds x is left-mult-cancelable\<^sub>M))"

attr algstr_0_def_37 ("almost-right-cancelable")
   "attr almost-right-cancelable for multLoopStr_0 means (\<lambda> M.
                                       (for x be Element-of-struct M st x \<noteq> 0\<^sub>M holds x is right-mult-cancelable\<^sub>M))"

attr algstr_0_def_38 ("almost-cancelable")
   "attr almost-cancelable for multLoopStr_0 means (\<lambda> M.  M is almost-right-cancelable \<bar> almost-left-cancelable)"

theorem algstr_0_cl_60[ty_cond_cluster]:
  "cluster almost-right-cancelable \<bar> almost-left-cancelable \<rightarrow> almost-cancelable for multLoopStr_0" using algstr_0_def_38 by auto

theorem algstr_0_cl_61[ty_cond_cluster]:
  "cluster almost-cancelable \<rightarrow> almost-right-cancelable \<bar> almost-left-cancelable for multLoopStr_0" using algstr_0_def_38 by auto

theorem algstr_0_cl_62[ty_func_cluster]:
  "cluster Trivial-multLoopStr_0 \<rightarrow> almost-cancelable"
proof
  let ?T ="Trivial-multLoopStr_0"
  show [ty]: "?T be multLoopStr_0" by mauto
       show "?T is almost-right-cancelable"
        proof
          fix x assume T2[ty]: "x be Element-of-struct ?T"
          assume "x \<noteq>0\<^sub>?T"
          thus "x is right-mult-cancelable\<^sub>?T"
            by mty (auto intro: struct_0_def_10a[of ?T])
        qed simp_all
       show "?T is almost-left-cancelable"
        proof
          fix x assume T2[ty]: "x be Element-of-struct ?T"
          assume "x \<noteq>0\<^sub>?T"
          thus "x is left-mult-cancelable\<^sub>?T"
            by mty (auto intro: struct_0_def_10a[of ?T])
        qed simp_all
   qed

theorem algstr_0_cl_63[ex]:
  "cluster almost-cancelable\<bar>strict (multLoopStr_0)\<bar>1-element-struct for multLoopStr_0"
unfolding inhabited_def
proof(intro exI)
  show "Trivial-multLoopStr_0 is almost-cancelable\<bar>strict (multLoopStr_0)\<bar>1-element-struct\<bar>multLoopStr_0"
  by mauto
qed

attr algstr_0_def_39 ("almost-left-invertible")
   "attr almost-left-invertible for multLoopStr_0 means (\<lambda> M.
                                       (for x be Element-of-struct M st x \<noteq> 0\<^sub>M holds x is left-invertible\<^sub>M))"

attr algstr_0_def_40 ("almost-right-invertible")
   "attr almost-right-invertible for multLoopStr_0 means (\<lambda> M.
                                       (for x be Element-of-struct M st x \<noteq> 0\<^sub>M holds x is right-invertible\<^sub>M))"

attr algstr_0_def_41 ("almost-invertible")
   "attr almost-invertible for multLoopStr_0 means (\<lambda> M.  M is almost-right-invertible \<bar> almost-left-invertible)"

theorem algstr_0_cl_64[ty_cond_cluster]:
  "cluster almost-right-invertible \<bar> almost-left-invertible \<rightarrow> almost-invertible for multLoopStr_0" using algstr_0_def_41 by auto

theorem algstr_0_cl_65[ty_cond_cluster]:
  "cluster almost-invertible \<rightarrow> almost-right-invertible \<bar> almost-left-invertible for multLoopStr_0" using algstr_0_def_41 by auto

theorem algstr_0_cl_66[ty_func_cluster]:
  "cluster Trivial-multLoopStr_0 \<rightarrow> almost-invertible"
proof
  let ?T ="Trivial-multLoopStr_0"
  show [ty]: "?T be multLoopStr_0" by mauto
       have Z: "0\<^sub>?T be Element-of-struct ?T" using struct_0_def_6[of ?T] by mauto
       show "?T is almost-right-invertible"
        proof
          fix x assume T2[ty]: "x be Element-of-struct ?T"
          assume "x \<noteq>0\<^sub>?T"
          thus "x is right-invertible\<^sub>?T" by mty (auto intro: struct_0_def_10a[of ?T])
        qed simp_all
       show "?T is almost-left-invertible"
        proof
          fix x assume T2[ty]: "x be Element-of-struct ?T"
          assume "x \<noteq>0\<^sub>?T"
          thus "x is left-invertible\<^sub>?T" by mty (auto intro: struct_0_def_10a[of ?T])
        qed simp_all
   qed

theorem algstr_0_cl_67[ex]:
  "cluster almost-invertible\<bar>almost-cancelable\<bar>strict (multLoopStr_0)\<bar>1-element-struct for multLoopStr_0"
 unfolding inhabited_def
proof(intro exI)
  show "Trivial-multLoopStr_0 is almost-invertible\<bar>almost-cancelable\<bar>strict (multLoopStr_0)\<bar>1-element-struct\<bar>multLoopStr_0"
    by mauto
qed

(*begin :: Double*)
abbreviation "doubleLoopStr_fields \<equiv>
 (# carrier \<rightarrow> (\<lambda>S. set);
   addF \<rightarrow> (\<lambda>S. BinOp-of the carrier of S);
   ZeroF \<rightarrow> (\<lambda>S. Element-of the carrier of S);
   multF \<rightarrow> (\<lambda>S. BinOp-of the carrier of S);
   OneF \<rightarrow> (\<lambda>S. Element-of the carrier of S) #)"

text_raw {*\DefineSnippet{doubleLoopStr_ex}{*}
term "{[carrier, the set]} \<union>
      {[addF, the BinOp-of (the set)]} \<union>
      {[ZeroF, the Element-of (the set)]} \<union>
      {[multF, the BinOp-of (the set)]} \<union>
      {[OneF, the Element-of (the set)]}"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{doubleLoopStr}{*}
mdefinition doubleLoopStr_d("doubleLoopStr") where
"struct doubleLoopStr (#
   carrier \<rightarrow> (\<lambda>S. set);
   addF \<rightarrow> (\<lambda>S. BinOp-of the carrier of S);
   ZeroF \<rightarrow> (\<lambda>S. Element-of the carrier of S);
   multF \<rightarrow> (\<lambda>S. BinOp-of the carrier of S);
   OneF \<rightarrow> (\<lambda>S. Element-of the carrier of S)
#)" : well_defined_property[of _ _ "{carrier}\<union>{addF}\<union>{ZeroF}\<union>{multF}\<union>{OneF}"]
text_raw {*}%EndSnippet*}
  by (auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

lemmas doubleLoopStrA = doubleLoopStr_d(1)
lemmas [ex] = doubleLoopStr_d(2,3)
lemmas doubleLoopStrD = doubleLoopStr_d(4)
lemmas doubleLoopStrR = doubleLoopStr_d(5)

text_raw {*\DefineSnippet{doubleLoopStr_strict}{*}
term "strict (doubleLoopStr) \<bar> doubleLoopStr"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{doubleLoopStr_inheritance}{*}
theorem doubleLoopStr_inheritance[ty_parent]:
  assumes "X be doubleLoopStr"
  shows "X be multLoopStr_0 \<and> X be addLoopStr"
using assms doubleLoopStrA addLoopStrA multLoopStr_0A by auto
text_raw {*}%EndSnippet*}


text_raw {*\DefineSnippet{doubleLoopStr_dom}{*}
lemma "domain_of doubleLoopStr =
     {carrier} \<union> {addF} \<union> {ZeroF} \<union> {multF} \<union> {OneF}"
text_raw {*}%EndSnippet*}
using doubleLoopStr_d(4) by simp


text_raw {*\DefineSnippet{doubleLoopStr_agg_e}{*}
theorem
  "[#carrier\<mapsto>X;addF\<mapsto>A;ZeroF\<mapsto>Z;multF\<mapsto>M;OneF\<mapsto>E#] =
    {[carrier,X]}\<union>{[addF,A]}\<union>{[ZeroF,Z]}\<union>{[multF,M]}\<union>{[OneF,E]}" using aggr_def sel_t_def by simp
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{doubleLoopStr_agg}{*}
lemma doubleLoopStr_AG[ty_func]:
  assumes "X be set"   "A be BinOp-of X"   "Z be Element-of X"
   "M be BinOp-of X"   "E be Element-of X"
  shows
   "[#carrier\<mapsto>X; addF\<mapsto>A; ZeroF\<mapsto>Z; multF\<mapsto>M; OneF\<mapsto>E#] be doubleLoopStr"
text_raw {*}%EndSnippet*}
using assms proof-
  assume A1[ty]: "X be set" "A be BinOp-of X" "M be BinOp-of X" "E be Element-of X" "Z be Element-of X"
  let ?A= "[#carrier\<mapsto>X;addF\<mapsto>A;ZeroF\<mapsto>Z;multF\<mapsto>M;OneF\<mapsto>E#]"
  have T1[ty]: "?A be Struct" using Struct_5 by (simp add:string)
  have T:"the carrier of ?A=X" using Aggr by (auto intro: the_selector_of_1)
   have [ty]:"?A is (carrier \<rightarrow> set')" using Field_1[of ?A carrier X ] Aggr by auto
  have [ty]:"?A is (multF \<rightarrow> BinOp-of' the' carrier)" using Field_1[of ?A multF M ] T Aggr by auto
  have [ty]:"?A is (ZeroF \<rightarrow> Element-of' the' carrier)" using Field_1[of ?A ZeroF Z ] T Aggr by auto
  have [ty]:"?A is (OneF \<rightarrow> Element-of' the' carrier)" using Field_1[of ?A OneF E ] T Aggr by auto
   have [ty]:"?A is (addF \<rightarrow> BinOp-of' the' carrier)" using Field_1[of ?A addF A ] T Aggr by auto
  show "[#carrier\<mapsto>X;addF\<mapsto>A;ZeroF\<mapsto>Z;multF\<mapsto>M;OneF\<mapsto>E#] be doubleLoopStr" using doubleLoopStrA by auto
qed

theorem algstr_0_cl_68[ty_func_cluster]:
  "let D be non empty\<bar>set \<and> o be BinOp-of D \<and> o1 be BinOp-of D \<and> d be Element-of D \<and> e be Element-of D
   cluster [#carrier\<mapsto>D;addF\<mapsto>o;ZeroF\<mapsto>d;multF\<mapsto>o1;OneF\<mapsto>e#] \<rightarrow> non empty-struct"
proof-
  assume T0[ty]:"D be non empty\<bar>set \<and> o be BinOp-of D \<and> o1 be BinOp-of D \<and> d be Element-of D \<and> e be Element-of D"
  let ?X = " [#carrier\<mapsto>D;addF\<mapsto>o;ZeroF\<mapsto>d;multF\<mapsto>o1;OneF\<mapsto>e#]"
  have T1[ty]: "?X be doubleLoopStr" by mauto
  have "the carrier of ?X = D" using the_selector_of_1[of ?X carrier D] Aggr by auto
  thus "?X is non empty-struct" using struct_0_def_1 by auto
qed


theorem algstr_0_cl_69[rule_format,ty_func_cluster]:
  "let T be trivial\<bar>set \<and> f be BinOp-of T \<and> f1 be BinOp-of T \<and> s be Element-of T \<and> t be Element-of T
   cluster [#carrier\<mapsto>T;addF\<mapsto>f;ZeroF\<mapsto>t;multF\<mapsto>f1;OneF\<mapsto>s#] \<rightarrow> trivial-struct"
proof-
  assume [ty]:"T be trivial\<bar>set \<and> f be BinOp-of T \<and> f1 be BinOp-of T \<and> s be Element-of T \<and> t be Element-of T"
  let ?X = "[#carrier\<mapsto>T;addF\<mapsto>f;ZeroF\<mapsto>t;multF\<mapsto>f1;OneF\<mapsto>s#]"
  have [ty]: "?X be doubleLoopStr" by mauto
  hence "the carrier of ?X = T" using Aggr by (auto intro: the_selector_of_1)
  thus "?X is trivial-struct" using struct_0_def_9 by mauto
qed

theorem algstr_0_cl_70:
  "let N be non trivial\<bar>set \<and> b be BinOp-of N \<and> b1 be BinOp-of N \<and> n be Element-of N \<and> m be Element-of N
   cluster [#carrier\<mapsto>N;addF\<mapsto>b;ZeroF\<mapsto>m;multF\<mapsto>b1;OneF\<mapsto>n#] \<rightarrow> non trivial-struct"
proof-
  assume [ty]:"N be non trivial\<bar>set \<and> b be BinOp-of N \<and> b1 be BinOp-of N \<and> n be Element-of N \<and> m be Element-of N"
  let ?X = "[#carrier\<mapsto>N;addF\<mapsto>b;ZeroF\<mapsto>m;multF\<mapsto>b1;OneF\<mapsto>n#]"
  have [ty]: "?X be doubleLoopStr" by mauto
  hence "the carrier of ?X = N" using Aggr by (auto intro: the_selector_of_1)
  thus "?X is non trivial-struct" using struct_0_def_9 by auto
qed

abbreviation algstr_0_def_42 ("Trivial-doubleLoopStr") where
(*  "Trivial-doubleLoopStr \<equiv>
     [#carrier\<mapsto>{{}};addF\<mapsto>op2;ZeroF\<mapsto>op0;multF\<mapsto>op2;OneF\<mapsto>op0#]"*)
  "Trivial-doubleLoopStr \<equiv>
     [# Trivial-addLoopStr; multF \<mapsto> op2 ; OneF \<mapsto> {} #]"

theorem algstr_0_cl_71[ty_func_cluster]:
  "cluster Trivial-doubleLoopStr \<rightarrow> 1-element-struct\<bar> strict (doubleLoopStr)"
proof(unfold ty_intersection,intro conjI)
  let ?T ="Trivial-doubleLoopStr"
  have T0[ty]: "?T be doubleLoopStr" by mauto
  hence T1: "the carrier of ?T={{}}"
    using Aggr by (auto intro: the_selector_of_1)
  thus T2: "Trivial-doubleLoopStr is 1-element-struct" using T0 struct_0_def_19_a by auto
  have "domain_of doubleLoopStr = dom ?T" using doubleLoopStrD Dom_5 by auto
  thus "Trivial-doubleLoopStr is strict (doubleLoopStr)" using T2 strict[THEN conjunct2] by auto
qed

theorem algstr_0_cl_72[ex]:
  "cluster strict (doubleLoopStr)\<bar>non empty-struct\<bar>1-element-struct for doubleLoopStr"
unfolding inhabited_def
proof(intro exI)
  show "Trivial-doubleLoopStr is strict (doubleLoopStr)\<bar>non empty-struct\<bar>1-element-struct\<bar>doubleLoopStr" by mty auto
qed

theorem algstr_0_cl_72_add[ex]:
  "cluster non empty-struct for doubleLoopStr"
unfolding inhabited_def
proof(intro exI)
  show "Trivial-doubleLoopStr is non empty-struct\<bar>doubleLoopStr" by mty auto
qed

func algstr_0_def_43 ("_ '/\<^sub>_ _" [66,1000, 67] 66) where
  mlet "M be multLoopStr","x be Element-of-struct M","y be Element-of-struct M"
  "func x /\<^sub>M y \<rightarrow> Element-of-struct M equals
     x \<otimes>\<^sub>M /\<^sub>M y"
proof-
    show "(x \<otimes>\<^sub>M /\<^sub>M y) be Element-of-struct M" by auto
qed

end
