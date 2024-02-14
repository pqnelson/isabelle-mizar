\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Algstr_0
  imports Struct_0
begin

abbreviation "addMagma_fields \<equiv> (#carrier \<rightarrow> set';addF\<rightarrow> BinOp-of' the' carrier #)"

definition "struct addMagma(#carrier \<rightarrow> set';addF\<rightarrow> BinOp-of' the' carrier #)"

lemma addMagma_well:"addMagma_fields well defined on {carrier} \<union>{addF}"
proof(rule Fields_add_argM1[OF one_sorted_well],simp add:string,simp add:string)
  show "for X1 be one_sorted_fields\<parallel>Function holds ex it be BinOp-of-struct X1 st True"
  proof(rule ballI)
    fix X1 assume "X1 be one_sorted_fields\<parallel>Function"
    hence "the carrier of X1 be set" using field by auto
    thus "ex it be BinOp-of the carrier of X1 st True"  using BinOp_ex by auto
  qed
qed

schematic_goal addMagma:
   shows ?X by (rule struct_well_defined[OF addMagma_def addMagma_well])

theorem addMagma_inheritance:
  "X be addMagma \<Longrightarrow> X be one-sorted" using addMagma one_sorted by simp

lemma addMagma_ag[rule_format]: "X be set \<Longrightarrow> B be BinOp-of X \<Longrightarrow> ({[carrier,X]}\<union>{[addF,B]}) be addMagma & ({[carrier,X]}\<union>{[addF,B]}) be Function"
proof-
  assume A1: "X be set" "B be BinOp-of X"
  let ?A= "{[carrier,X]}\<union>{[addF,B]}"
  have T1: "?A be Function" using Function_2[of carrier addF] by (simp add:string)
  have "the carrier of ?A=X" using the_selector_of_1[OF T1, of carrier "X"] tarski_def_1 by auto
  thus ?thesis using T1 addMagma Field_1[OF T1,of addF B] Field_1[of ?A carrier "X" ] A1 string by auto
qed

theorem algstr_0_cl_1:
  "let D be non empty\<parallel>set & o be BinOp-of D
   cluster {[carrier,D]}\<union>{[addF,o]} \<rightarrow> non empty-struct"
proof-
  assume T0:"D be non empty\<parallel>set & o be BinOp-of D"
  let ?X = "{[carrier,D]}\<union>{[addF,o]}"
  have T1: "?X be addMagma" "?X be Function" using addMagma_ag T0 by auto
  have "the carrier of ?X = D" using the_selector_of_1[of ?X carrier D] T1(2) string by auto
  thus "?X is non empty-struct" using  struct_0_def_1_b addMagma one_sorted T1 T0 by auto
qed

theorem algstr_0_cl_2:
  "let T be trivial\<parallel>set & f be BinOp-of T
   cluster {[carrier,T]}\<union>{[addF,f]} \<rightarrow> trivial-struct"
proof-
  assume T0:"T be trivial\<parallel>set & f be BinOp-of T"
  let ?X = "{[carrier,T]}\<union>{[addF,f]}"
  have T1: "?X be addMagma" "?X be Function" using addMagma_ag T0 by auto
  hence T2: "the carrier of ?X = T" "?X be one-sorted" using the_selector_of_1[of ?X carrier T]  addMagma one_sorted string by auto
  show "?X is  trivial-struct" using  struct_0_def_9_a[of ?X,THEN iffD2,rule_format, OF T2(2)] T0 T2(1) by auto
qed

theorem algstr_0_cl_3:
  "let N be non trivial\<parallel>set & b be BinOp-of N
   cluster {[carrier,N]}\<union>{[addF,b]} \<rightarrow> non trivial-struct"
proof-
  assume T0:"N be non trivial\<parallel>set & b be BinOp-of N"
  let ?X = "{[carrier,N]}\<union>{[addF,b]}"
  have T1: "?X be addMagma" "?X be Function" using addMagma_ag T0 by auto
  hence T2: "the carrier of ?X = N" "?X be one-sorted" using the_selector_of_1[of ?X carrier N]  addMagma one_sorted string by auto
  show "?X is  non trivial-struct" using  struct_0_def_9_b[of ?X,THEN iffD2,rule_format, OF T2(2)] T0 T2(1) by auto
qed

text_raw \<open>\DefineSnippet{algstr0def1}{\<close>
definition algstr_0_def_1 ("_ \<oplus>\<^sub>_ _" [66,1000,67] 66) where
  "func x \<oplus>\<^sub>M y \<rightarrow> Element-of-struct M equals
     (the addF of M) . \<lparr> x , y \<rparr>"
schematic_goal algstr_0_def_1:
  assumes "M be addMagma & x be Element-of-struct M
         & y be Element-of-struct M" shows "?X"
text_raw \<open>}%EndSnippet\<close>
proof (rule equals_property [OF algstr_0_def_1_def,of M x y])
   let ?A = "the carrier of M"
   have A1: "(the addF of M) be BinOp-of ?A" "?A be set" using assms addMagma field one_sorted by auto
   thus " (the addF of M) .  \<lparr> x , y \<rparr> be Element-of ?A"  using binop_0_def_20[of "the carrier of M" "the addF of M" x y]
           assms by auto
qed


definition algstr_0_def_2 ("Trivial-addMagma") where
  "func Trivial-addMagma \<rightarrow> addMagma equals
     {[carrier,{{}}]}\<union>{[addF,op2]}"

schematic_goal algstr_0_def_2:
  shows "?X"
proof (rule equals_property [OF algstr_0_def_2_def])
  show "({[carrier,{{}}]} \<union>{[addF,op2]}) be addMagma" using addMagma_ag funct_5_def_9 all_set by auto
qed

lemmas [simp] = algstr_0_def_2[THEN conjunct2]


lemma algstr_0_def_2_t:"Trivial-addMagma is trivial-struct"
proof-
  have A1: "{{}} is trivial" using zfmisc_1_def_10a all_set tarski_def_1b by auto
  have "op2 be  BinOp-of {{}}" using funct_5_def_9 by simp
  thus ?thesis using  algstr_0_cl_2 all_set A1 by auto
qed

theorem algstr_0_cl_4:
  "cluster Trivial-addMagma \<rightarrow> 1-element-struct\<bar> strict addMagma"
proof(rule attr_attr[THEN iffD2],rule conjI)
  let ?T ="Trivial-addMagma"
  have T0: "?T be addMagma" "?T be one-sorted" "?T be Function" using algstr_0_def_2 addMagma one_sorted by auto
  hence T1: "the carrier of ?T={{}}"
    using the_selector_of_1[OF T0(3),of carrier "{{}}"] string by auto
  thus T2: "Trivial-addMagma is 1-element-struct" using T0 struct_0_def_19_a by auto
  have  "domain_of addMagma = dom ?T"  using addMagma Dom_2 by auto
  thus "Trivial-addMagma is strict addMagma" using T2 strict T0 by auto
qed

theorem algstr_0_cl_5:
  "cluster strict addMagma\<bar>1-element-struct for addMagma"
proof
  show "Trivial-addMagma is strict addMagma\<bar>1-element-struct" using algstr_0_cl_4 by auto
  show "Trivial-addMagma be addMagma" using algstr_0_def_2 by auto
qed


definition left_add_cancelable ("left-add-cancelable\<^sub>_") where algstr_0_def_3 [THEN defattr_property]:
   "attr left-add-cancelable\<^sub>M means (\<lambda> x. M be addMagma & x be Element-of-struct M &
                                       (for y,z be Element-of-struct M st x \<oplus>\<^sub>M y = x \<oplus>\<^sub>M z holds y = z))"

lemmas algstr_0_def_3a = algstr_0_def_3[THEN iffD1,THEN conjunct2,rule_format]

definition right_add_cancelable ("right-add-cancelable\<^sub>_") where algstr_0_def_4 [THEN defattr_property]:
   "attr right-add-cancelable\<^sub>M means (\<lambda> x. M be addMagma & x be Element-of-struct M &
                                       (for y,z be Element-of-struct M st y \<oplus>\<^sub>M x = z \<oplus>\<^sub>M x holds y = z))"
lemmas algstr_0_def_4a = algstr_0_def_4[THEN iffD1,THEN conjunct2,rule_format]

definition add_cancelable ("add-cancelable\<^sub>_") where algstr_0_def_5 [THEN defattr_property]:
   "attr add-cancelable\<^sub>M means (\<lambda> x. M be addMagma & x be Element-of-struct M &
                                       x is  right-add-cancelable\<^sub>M \<bar> left-add-cancelable\<^sub>M)"
lemmas algstr_0_def_5a = algstr_0_def_5[THEN iffD1,THEN conjunct2,rule_format]


(*Przykład na to że klastry zapentlają simp*)

theorem algstr_0_cl_6:
  "let M be addMagma
   cluster right-add-cancelable\<^sub>M \<bar> left-add-cancelable\<^sub>M \<rightarrow> add-cancelable\<^sub>M  for Element-of-struct M" using  algstr_0_def_5 by auto

theorem algstr_0_cl_7:
  "let M be addMagma
   cluster add-cancelable\<^sub>M \<rightarrow> right-add-cancelable\<^sub>M \<bar> left-add-cancelable\<^sub>M for Element-of-struct M" using  algstr_0_def_5 by auto

definition left_add_cancelable_M ("left-add-cancelable") where algstr_0_def_6 [THEN defattr_property]:
   "attr left-add-cancelable means (\<lambda> M. M be addMagma & (for x be Element-of-struct M holds x is left-add-cancelable\<^sub>M))"
lemmas algstr_0_def_6a = algstr_0_def_3[THEN iffD1,THEN conjunct2,rule_format]


definition right_add_cancelable_M ("right-add-cancelable") where algstr_0_def_7 [THEN defattr_property]:
   "attr right-add-cancelable means (\<lambda> M. M be addMagma &
                                       (for x be Element-of-struct M holds x is right-add-cancelable\<^sub>M))"
lemmas algstr_0_def_7a = algstr_0_def_7[THEN iffD1,THEN conjunct2,rule_format]

definition add_cancelable_M ("add-cancelable") where algstr_0_def_8 [THEN defattr_property]:
   "attr add-cancelable means (\<lambda> M. M be addMagma &
                                       M is  right-add-cancelable \<bar> left-add-cancelable)"

lemmas algstr_0_def_8a = algstr_0_def_8[THEN iffD1,THEN conjunct2,rule_format]


theorem algstr_0_cl_8:
  "cluster right-add-cancelable \<bar> left-add-cancelable \<rightarrow> add-cancelable  for addMagma" using  algstr_0_def_8 by auto


theorem algstr_0_cl_9:
  "cluster add-cancelable \<rightarrow> right-add-cancelable \<bar> left-add-cancelable for addMagma" using  algstr_0_def_8 by auto


theorem algstr_0_cl_10:
  "cluster Trivial-addMagma \<rightarrow> add-cancelable"
proof(unfold algstr_0_def_8,rule conjI,rule algstr_0_def_2[THEN conjunct1],rule attr_attr[THEN iffD2],rule conjI)
  let ?T ="Trivial-addMagma"
  have T0: "?T be Function" "?T be one-sorted" using algstr_0_def_2 addMagma one_sorted by auto
  have T1: "the carrier of ?T={{}}"
    using the_selector_of_1[OF T0(1),of carrier "{{}}"] string by auto

  show "?T is right-add-cancelable"
    proof(unfold algstr_0_def_7,rule conjI,rule algstr_0_def_2[THEN conjunct1],rule ballI)
      fix x assume T2: "x be Element-of-struct ?T"
      show "x is right-add-cancelable\<^sub>?T"
      proof(unfold algstr_0_def_4,intro conjI,rule algstr_0_def_2[THEN conjunct1],rule T2,intro ballI impI)
        fix y z assume T3: "y be Element-of-struct ?T" "z be Element-of-struct ?T"
        assume "y \<oplus>\<^sub>?T x = z \<oplus>\<^sub>?T x"
        show "y = z" using struct_0_def_10[OF T0(2),THEN iffD1,OF algstr_0_def_2_t,rule_format,OF T3] by simp
      qed
    qed
  show "?T is left-add-cancelable"
    proof(unfold algstr_0_def_6,rule conjI,rule algstr_0_def_2[THEN conjunct1],rule ballI)
      fix x assume T2: "x be Element-of-struct ?T"
      show "x is left-add-cancelable\<^sub>?T"
      proof(unfold algstr_0_def_3,intro conjI,rule algstr_0_def_2[THEN conjunct1],rule T2,intro ballI impI)
        fix y z assume T3: "y be Element-of-struct ?T" "z be Element-of-struct ?T"
        assume "x \<oplus>\<^sub>?T y = x \<oplus>\<^sub>?T z"
        show "y = z"  using struct_0_def_10[OF T0(2),THEN iffD1,OF algstr_0_def_2_t,rule_format,OF T3] by simp
      qed
    qed
qed

theorem algstr_0_cl_11:
  "cluster add-cancelable\<bar>strict addMagma\<bar>1-element-struct for addMagma"
proof
  show "Trivial-addMagma is add-cancelable\<bar>strict addMagma\<bar>1-element-struct" using algstr_0_cl_4 algstr_0_cl_10 by auto
  show "Trivial-addMagma be addMagma" using algstr_0_def_2 by auto
qed

theorem algstr_0_cl_12:
  "let M be left-add-cancelable \<parallel> addMagma
   cluster \<rightarrow> left-add-cancelable\<^sub>M for Element-of-struct M"
  using algstr_0_def_6 by auto

theorem algstr_0_cl_13:
  "let M be right-add-cancelable \<parallel> addMagma
   cluster \<rightarrow> right-add-cancelable\<^sub>M for Element-of-struct M"
  using algstr_0_def_7 by auto

abbreviation "addLoopStr_fields\<equiv>(#carrier \<rightarrow> set';  addF\<rightarrow> BinOp-of' the' carrier ;ZeroF \<rightarrow> Element-of' the' carrier#)"


text_raw \<open>\DefineSnippet{addLoopStr1}{\<close>
definition "struct addLoopStr
  (# carrier \<rightarrow> set';
     addF \<rightarrow> BinOp-of' the' carrier;
     ZeroF \<rightarrow> Element-of' the' carrier #)"
text_raw \<open>}%EndSnippet\<close>


text_raw \<open>\DefineSnippet{addLoopStrEx1}{\<close>
term "{[carrier, the set]}\<union>
      {[addF, the BinOp-of the set]}\<union>
      {[ZeroF, the Element-of the set]}"
text_raw \<open>}%EndSnippet\<close>

lemma addLoopStr_well_1:"(#carrier \<rightarrow> set';  ZeroF \<rightarrow> Element-of' the' carrier ; addF\<rightarrow> BinOp-of' the' carrier #)
          well defined on {carrier} \<union>{ZeroF}\<union>{addF}"
proof(rule Fields_add_argM1[OF ZeroStr_well],simp add:string,simp add:string)
  show "for X1 be ZeroStr_fields\<parallel>Function holds ex it be BinOp-of the carrier of X1 st True"
  proof(rule ballI)
    fix X1 assume "X1 be ZeroStr_fields\<parallel>Function"
    hence "the carrier of X1 be set" using field by auto
    thus "ex it be BinOp-of the carrier of X1 st True" using BinOp_ex by auto
  qed
qed

lemma addLoopStr_well_2:"
(#carrier \<rightarrow> set';  addF \<rightarrow> BinOp-of' the' carrier ;ZeroF \<rightarrow> Element-of' the' carrier#)
   well defined on {carrier}\<union>{addF}\<union>{ZeroF} "
proof-
  have A0: "{carrier} \<union>{ZeroF}\<union>{addF} = {carrier} \<union>{addF}\<union>{ZeroF}"  by auto
  have A1: "\<And>X. X is ZeroStr_fields \<bar>(# addF \<rightarrow> BinOp-of' the' carrier #)
            iff X is addLoopStr_fields"
     by auto
  show ?thesis using  well_defined_order[OF A1 addLoopStr_well_1] A0 by auto
qed
text_raw \<open>\DefineSnippet{addLoopStrWell}{\<close>
lemma addLoopStr_well:"
   (# carrier \<rightarrow> set';
       addF \<rightarrow> BinOp-of' the' carrier;
       ZeroF \<rightarrow> Element-of' the' carrier #)
   well defined on {carrier} \<union> {addF} \<union> {ZeroF}"
proof (rule Fields_add_argM1[OF addMagma_well])
  show "carrier in {carrier} \<union> {addF}"
    by (simp add:string)
  show "not ZeroF in {carrier} \<union> {addF}"
    by (simp add:string)
  show "for X1 be addMagma_fields\<parallel>Function holds
          ex it be Element-of-struct X1 st True"
  proof
    fix X1 assume "X1 be addMagma_fields\<parallel>Function"
    hence "the carrier of X1 be set" using field by auto
    thus "ex it be Element-of-struct X1 st True"
      using subset_1_def_1 by blast
  qed
qed
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{addLoopStr2}{\<close>
schematic_goal addLoopStr:
  shows ?X by (rule struct_well_defined[OF
                 addLoopStr_def addLoopStr_well])
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{addLoopStrEx2}{\<close>
term "{[carrier, the set]}\<union>
      {[addF, the BinOp-of the set]}\<union>
      {[ZeroF, the Element-of the set]}"
text_raw \<open>}%EndSnippet\<close>


text_raw \<open>\DefineSnippet{addLoopStrInheritance}{\<close>
theorem addLoopStr_inheritance:
  assumes "X be addLoopStr"
  shows "X be addMagma & X be ZeroStr"
    using addLoopStr addMagma ZeroStr assms
    by simp
text_raw \<open>}%EndSnippet\<close>


    (*
lemma ZeroStr_well:"ZeroStr_fields well defined on {carrier} \<union>{ZeroF}"
proof(rule Fields_add_argM1[OF one_sorted_well],simp add:string,simp add:string)
  show "for X1 be  one_sorted_fields \<parallel>Function holds ex it be Element-of-struct X1 st True"
  proof(rule ballI)
    fix X1 assume "X1 be one_sorted_fields\<parallel>Function"
    hence "the carrier of X1 be set" using field by auto
    thus "ex it be Element-of the carrier of X1 st True"  using subset_1_def_1[THEN conjunct2] by auto
  qed
qed  *)



lemma addLoopStr_ag[rule_format]: "X be set \<Longrightarrow> B be BinOp-of X \<Longrightarrow> E be Element-of X \<Longrightarrow>
   ({[carrier,X]}\<union>{[addF,B]}\<union>{[ZeroF,E]}) be addLoopStr & ({[carrier,X]}\<union>{[addF,B]}\<union>{[ZeroF,E]}) be Function"
proof-
  assume A1: "X be set" "B be BinOp-of X" "E be Element-of X"
  let ?A= "{[carrier,X]}\<union>{[addF,B]}\<union>{[ZeroF,E]}"
  have T1: "?A be Function" using Function_3[of carrier addF ZeroF] by (simp add:string)
  have "the carrier of ?A=X" using the_selector_of_1[OF T1, of carrier X] tarski_def_1 by auto
  thus ?thesis using T1  addLoopStr Field_1[OF T1,of addF B] Field_1[of ?A carrier X ] Field_1[of ?A ZeroF E ] A1 string by auto
qed

  theorem algstr_0_cl_14:
  "let D be non empty\<parallel>set & o be BinOp-of D & d be Element-of D
   cluster {[carrier,D]}\<union>{[addF,o]}\<union>{[ZeroF,d]} \<rightarrow> non empty-struct"
proof-
  assume T0:"D be non empty\<parallel>set & o be BinOp-of D & d be Element-of D"
  let ?X = "{[carrier,D]}\<union>{[addF,o]}\<union>{[ZeroF,d]}"
  have T1: "?X be addLoopStr" "?X be Function" using addLoopStr_ag T0 by auto
  have "the carrier of ?X = D" using the_selector_of_1[of ?X carrier D] T1(2) string by auto
  thus "?X is non empty-struct" using  struct_0_def_1_b addLoopStr one_sorted T1 T0 by auto
qed

theorem algstr_0_cl_15:
  "let T be trivial\<parallel>set & f be BinOp-of T & t be Element-of T
   cluster {[carrier,T]}\<union>{[addF,f]}\<union>{[ZeroF,t]} \<rightarrow> trivial-struct"
proof-
  assume T0:"T be trivial\<parallel>set & f be BinOp-of T & t be Element-of T"
  let ?X = "{[carrier,T]}\<union>{[addF,f]}\<union>{[ZeroF,t]}"
  have T1: "?X be addLoopStr" "?X be Function" using addLoopStr_ag T0 by auto
  hence T2: "the carrier of ?X = T" "?X be one-sorted" using the_selector_of_1[of ?X carrier T]
    addLoopStr one_sorted string by auto
  show "?X is  trivial-struct" using  struct_0_def_9_a[of ?X,THEN iffD2,rule_format, OF T2(2)] T0 T2(1) by auto
qed

theorem algstr_0_cl_16:
  "let N be non trivial\<parallel>set & b be BinOp-of N & m be Element-of N
   cluster {[carrier,N]}\<union>{[addF,b]}\<union>{[ZeroF,m]} \<rightarrow> non trivial-struct"
proof-
  assume T0:"N be non trivial\<parallel>set & b be BinOp-of N & m be Element-of N"
  let ?X = "{[carrier,N]}\<union>{[addF,b]}\<union>{[ZeroF,m]}"
  have T1: "?X be addLoopStr" "?X be Function" using addLoopStr_ag T0 by auto
  hence T2: "the carrier of ?X = N" "?X be one-sorted" using the_selector_of_1[of ?X carrier N]  addLoopStr one_sorted string by auto
  show "?X is  non trivial-struct" using  struct_0_def_9_b[of ?X,THEN iffD2,rule_format, OF T2(2)] T0 T2(1) by auto
qed

definition algstr_0_def_9 ("Trivial-addLoopStr") where
  "func Trivial-addLoopStr \<rightarrow> addLoopStr equals
     {[carrier,{{}}]}\<union>{[addF,op2]}\<union>{[ZeroF,op0]}"

schematic_goal algstr_0_def_9:
  shows "?X"
proof (rule equals_property [OF algstr_0_def_9_def])
  show "({[carrier,{{}}]} \<union>{[addF,op2]}\<union>{[ZeroF,op0]}) be addLoopStr" using addLoopStr_ag funct_5_def_9 funct_5_def_7 all_set by auto
qed

lemmas [simp] = algstr_0_def_9[THEN conjunct2]

lemma algstr_0_def_9_t:"Trivial-addLoopStr is trivial-struct"
proof-
  have A1: "{{}} is trivial" using zfmisc_1_def_10a all_set tarski_def_1b by auto
  have "op2 be  BinOp-of {{}}" "op0 be Element-of {{}}" using funct_5_def_9 funct_5_def_7 funct_5_def_4 by simp+
  thus ?thesis using  algstr_0_cl_15[of "{{}}" op2 op0] all_set A1 by auto
qed

theorem algstr_0_cl_17:
  "cluster Trivial-addLoopStr \<rightarrow> 1-element-struct\<bar> strict addLoopStr"
proof(rule attr_attr[THEN iffD2],rule conjI)
  let ?T ="Trivial-addLoopStr"
  have T0: "?T be addLoopStr" "?T be one-sorted" "?T be Function" using algstr_0_def_9 addLoopStr one_sorted by auto
  hence T1: "the carrier of ?T={{}}"
    using the_selector_of_1[OF T0(3),of carrier "{{}}"] string by auto
  thus T2: "Trivial-addLoopStr is 1-element-struct" using T0 struct_0_def_19_a by auto
  have  "domain_of addLoopStr = dom ?T"  using addLoopStr Dom_3 tarski_th_2[of "domain_of addLoopStr" "dom ?T"] by auto
  thus "Trivial-addLoopStr is strict addLoopStr" using T2 strict T0 by auto
qed

theorem algstr_0_cl_18:
  "cluster strict addLoopStr\<bar>1-element-struct for addLoopStr"
proof
  show "Trivial-addLoopStr is strict addLoopStr\<bar>1-element-struct" using algstr_0_cl_17 by auto
  show "Trivial-addLoopStr be addLoopStr" using algstr_0_def_9 by auto
qed

definition left_complementable ::"Set \<Rightarrow>Attr" ("left-complementable\<^sub>_") where algstr_0_def_10 [THEN defattr_property]:
   "attr left-complementable\<^sub>M means (\<lambda> x. M be addLoopStr & x be Element-of-struct M &
                                       (ex y be Element-of-struct M st y \<oplus>\<^sub>M x =0\<^sub>M))"
lemmas algstr_0_def_10a = algstr_0_def_10[THEN iffD1,THEN conjunct2,rule_format]

definition right_complementable ("right-complementable\<^sub>_") where algstr_0_def_11 [THEN defattr_property]:
   "attr right-complementable\<^sub>M means (\<lambda> x. M be addLoopStr & x be Element-of-struct M &
                                       (ex y be Element-of-struct M st x \<oplus>\<^sub>M y =0\<^sub>M))"
lemmas algstr_0_def_11a = algstr_0_def_11[THEN iffD1,THEN conjunct2,rule_format]

definition add_complementable ("add-complementable\<^sub>_") where algstr_0_def_12 [THEN defattr_property]:
   "attr add-complementable\<^sub>M means (\<lambda> x. M be addLoopStr & x be Element-of-struct M &
                                       x is  right-complementable\<^sub>M \<bar> left-complementable\<^sub>M)"
lemmas algstr_0_def_12a = algstr_0_def_12[THEN iffD1,THEN conjunct2,rule_format]

theorem algstr_0_cl_19:
  "let M be addLoopStr
   cluster right-complementable\<^sub>M \<bar> left-complementable\<^sub>M \<rightarrow> add-complementable\<^sub>M  for Element-of-struct M"
     using  algstr_0_def_12 by auto

theorem algstr_0_cl_20:
  "let M be addLoopStr
   cluster add-complementable\<^sub>M \<rightarrow> right-complementable\<^sub>M \<bar> left-complementable\<^sub>M for Element-of-struct M"
    using  algstr_0_def_12 by auto

text_raw \<open>\DefineSnippet{algstr0def13}{\<close>
definition algstr_0_def_13 ("\<ominus>\<^sub>_ _" [1000, 86] 87) where
  "assume x is left-complementable\<^sub>M \<bar> right-add-cancelable\<^sub>M
   func \<ominus>\<^sub>M x \<rightarrow> Element-of-struct M means
     (\<lambda>it. it \<oplus>\<^sub>M x = 0\<^sub>M)"
schematic_goal algstr_0_def_13:
  assumes "M be addLoopStr"
          "x be Element-of-struct M" shows "?X"
text_raw \<open>}%EndSnippet\<close>
proof (induct rule: assume_means_property[OF algstr_0_def_13_def conjI[OF assms], of x M,  case_names existence uniqueness coherence])
  case existence
      assume "x is left-complementable\<^sub>M \<bar>right-add-cancelable\<^sub>M"
      thus "ex y be Element-of-struct M st y \<oplus>\<^sub>M x= 0\<^sub>M" using algstr_0_def_10a by auto
  next
   case uniqueness
     assume A1: "x is left-complementable\<^sub>M \<bar>right-add-cancelable\<^sub>M"
     fix y1 y2
     assume T0: "y1 be Element-of-struct M"
                "y2 be Element-of-struct M" and
    A2: " y1 \<oplus>\<^sub>M x= 0\<^sub>M" and
    A3: " y2 \<oplus>\<^sub>M x= 0\<^sub>M"
    thus "y1=y2" using A1 algstr_0_def_4a[of x M y1 y2] by auto
  next
   case coherence
     show "ex x being Element-of-struct M st True" using subset_1_def_1[THEN conjunct2] all_set by auto
qed

definition algstr_0_def_14 ("_ \<ominus>\<^sub>_ _" [66,1000, 67] 66) where
  "func x \<ominus>\<^sub>M y \<rightarrow> Element-of-struct M equals
     x  \<oplus>\<^sub>M \<ominus>\<^sub>M y"

schematic_goal algstr_0_def_14:
   assumes " M be addLoopStr & x be Element-of-struct M & y be Element-of-struct M" shows "?X"
proof (rule equals_property [OF algstr_0_def_14_def,of x M y])
    have T0:"M be addMagma" using assms addMagma addLoopStr by auto
    have "(\<ominus>\<^sub>M y)  be Element-of-struct M"  using assms algstr_0_def_13 by simp
    thus "(x  \<oplus>\<^sub>M \<ominus>\<^sub>M y) be Element-of-struct M" using  algstr_0_def_1[of M x "\<ominus>\<^sub>M y"] T0 assms by auto
qed

theorem algstr_0_cl_21:
  "cluster Trivial-addLoopStr \<rightarrow> add-cancelable"
proof(unfold algstr_0_def_8,rule conjI)
  let ?T ="Trivial-addLoopStr"
  show T: "?T be addMagma" using algstr_0_def_9[THEN conjunct1] addLoopStr addMagma by simp
  show "?T is right-add-cancelable  \<bar>  left-add-cancelable"
    proof(rule attr_attr[THEN iffD2],rule conjI)
       have T0: "?T be Function" "?T be one-sorted" using algstr_0_def_9 addLoopStr one_sorted by auto
       have T1: "the carrier of ?T={{}}"
      using the_selector_of_1[OF T0(1),of carrier "{{}}"] string by auto
      show "?T is right-add-cancelable"
    proof(unfold algstr_0_def_7,rule conjI,rule T,rule ballI)
      fix x assume T2: "x be Element-of-struct ?T"
      show "x is right-add-cancelable\<^sub>?T"
      proof(unfold algstr_0_def_4,intro conjI,rule T,rule T2,intro ballI impI)
        fix y z assume T3: "y be Element-of-struct ?T" "z be Element-of-struct ?T"
        assume "y \<oplus>\<^sub>?T x = z \<oplus>\<^sub>?T x"
        show "y = z" using struct_0_def_10[OF T0(2),THEN iffD1,OF algstr_0_def_9_t,rule_format,OF T3] by simp
      qed
    qed
  show "?T is left-add-cancelable"
    proof(unfold algstr_0_def_6,rule conjI,rule T,rule ballI)
      fix x assume T2: "x be Element-of-struct ?T"
      show "x is left-add-cancelable\<^sub>?T"
      proof(unfold algstr_0_def_3,intro conjI,rule T,rule T2,intro ballI impI)
        fix y z assume T3: "y be Element-of-struct ?T" "z be Element-of-struct ?T"
        assume "x \<oplus>\<^sub>?T y = x \<oplus>\<^sub>?T z"
        show "y = z"  using struct_0_def_10[OF T0(2),THEN iffD1,OF algstr_0_def_9_t,rule_format,OF T3] by simp
      qed
    qed
qed
qed

definition left_complementable_M ("left-complementable") where algstr_0_def_15 [THEN defattr_property]:
   "attr left-complementable means (\<lambda> M. M be addLoopStr & (for x be Element-of-struct M holds x is left-complementable\<^sub>M))"
lemmas algstr_0_def_15a = algstr_0_def_3[THEN iffD1,THEN conjunct2,rule_format]


definition right_complementable_M ("right-complementable") where algstr_0_def_16 [THEN defattr_property]:
   "attr right-complementable means (\<lambda> M. M be addLoopStr &
                                       (for x be Element-of-struct M holds x is right-complementable\<^sub>M))"
lemmas algstr_0_def_16a = algstr_0_def_16[THEN iffD1,THEN conjunct2,rule_format]

definition complementable_M ("complementable") where algstr_0_def_17 [THEN defattr_property]:
   "attr complementable means (\<lambda> M. M be addLoopStr &
                                       M is  right-complementable \<bar> left-complementable)"

lemmas algstr_0_def_17a = algstr_0_def_17[THEN iffD1,THEN conjunct2,rule_format]


theorem algstr_0_cl_22:
  "cluster right-complementable \<bar> left-complementable \<rightarrow> complementable  for addLoopStr" using  algstr_0_def_17 by auto


theorem algstr_0_cl_23:
  "cluster complementable \<rightarrow> right-complementable \<bar> left-complementable for addLoopStr" using  algstr_0_def_17 by auto

theorem algstr_0_cl_24:
  "cluster Trivial-addLoopStr \<rightarrow> complementable"
proof(unfold algstr_0_def_17,rule conjI,rule algstr_0_def_9[THEN conjunct1],rule attr_attr[THEN iffD2],rule conjI)
  let ?T ="Trivial-addLoopStr"
  have T0: "?T be Function" "?T be ZeroStr" "?T be one_sorted" "?T be addMagma"
      using algstr_0_def_9 addLoopStr ZeroStr one_sorted addMagma by auto
  have T1: "the carrier of ?T={{}}"
    using the_selector_of_1[OF T0(1),of carrier "{{}}"] string by auto
  have Z: "0\<^sub>?T be Element-of-struct ?T" using struct_0_def_6[of ?T] T0 by auto

  show "?T is right-complementable"
    proof(unfold algstr_0_def_16,rule conjI,rule  algstr_0_def_9[THEN conjunct1],rule ballI)
      fix x assume T2: "x be Element-of-struct ?T"
      hence T3: "(x \<oplus>\<^sub>?T x) be Element-of-struct ?T"  using algstr_0_def_1[of ?T x x] T0(4) by auto
      show "x is right-complementable\<^sub>?T"
      proof(unfold algstr_0_def_11,intro conjI,rule algstr_0_def_9[THEN conjunct1],rule T2,rule bexI[of _ x])
        show "x be Element-of-struct ?T" using T2 by simp
        show "x \<oplus>\<^sub>?T x =0\<^sub>?T" using struct_0_def_10[OF T0(3),THEN iffD1,OF algstr_0_def_9_t,rule_format,OF Z T3] by simp
      qed
    qed
  show "?T is left-complementable"
    proof(unfold algstr_0_def_15,rule conjI,rule  algstr_0_def_9[THEN conjunct1],rule ballI)
      fix x assume T2: "x be Element-of-struct ?T"
      hence T3: "(x \<oplus>\<^sub>?T x) be Element-of-struct ?T"  using algstr_0_def_1[of ?T x x] T0(4) by auto
      show "x is left-complementable\<^sub>?T"
      proof(unfold algstr_0_def_10,intro conjI,rule algstr_0_def_9[THEN conjunct1],rule T2,rule bexI[of _ x])
        show "x be Element-of-struct ?T" using T2 by simp
        show "x \<oplus>\<^sub>?T x =0\<^sub>?T" using struct_0_def_10[OF T0(3),THEN iffD1,OF algstr_0_def_9_t,rule_format,OF Z T3] by simp
      qed
    qed
qed

theorem algstr_0_cl_25:
  "cluster complementable\<bar>add-cancelable\<bar>strict addLoopStr\<bar>1-element-struct for addLoopStr"
proof
  show "Trivial-addLoopStr is  complementable\<bar>add-cancelable\<bar>strict addLoopStr\<bar>1-element-struct"
       using algstr_0_cl_17 algstr_0_cl_21 algstr_0_cl_24 by auto
  show "Trivial-addLoopStr be addLoopStr" using algstr_0_def_9 by auto
qed

theorem algstr_0_cl_26:
  "let M be left-complementable \<parallel> addLoopStr
   cluster \<rightarrow> left-complementable\<^sub>M for Element-of-struct M"
  using algstr_0_def_15 by auto

theorem algstr_0_cl_27:
  "let M be right-complementable \<parallel> addLoopStr
   cluster \<rightarrow> right-complementable\<^sub>M for Element-of-struct M"
  using algstr_0_def_16 by auto

(*begin :: Multiplicative structures*)

abbreviation "multMagma_fields \<equiv> (#carrier \<rightarrow> set';multF\<rightarrow> BinOp-of' the' carrier #)"

text_raw \<open>\DefineSnippet{multMagma}{\<close>
definition "struct multMagma (#
  carrier \<rightarrow> set';
  multF\<rightarrow> BinOp-of' the' carrier #)"
text_raw \<open>}%EndSnippet\<close>
lemma multMagma_well:"multMagma_fields
                    well defined on {carrier} \<union>{multF}"
proof(rule Fields_add_argM1[OF one_sorted_well],simp add:string,simp add:string)
  show "for X1 be one_sorted_fields\<parallel>Function holds ex it be BinOp-of-struct X1 st True"
  proof(rule ballI)
    fix X1 assume "X1 be one_sorted_fields\<parallel>Function"
    hence "the carrier of X1 be set" using field by auto
    thus "ex it be BinOp-of the carrier of X1 st True"  using BinOp_ex by auto
  qed
qed

schematic_goal multMagma:
   shows ?X by (rule struct_well_defined[OF multMagma_def multMagma_well])

theorem multMagma_inheritance:
  "X be multMagma \<Longrightarrow> X be one-sorted" using multMagma one_sorted by simp

lemma multMagma_ag[rule_format]: "X be set \<Longrightarrow> B be BinOp-of X \<Longrightarrow>
   ({[carrier,X]}\<union>{[multF,B]}) be multMagma & ({[carrier,X]}\<union>{[multF,B]}) be Function"
proof-
  assume A1: "X be set" "B be BinOp-of X"
  let ?A= "{[carrier,X]}\<union>{[multF,B]}"
  have T1: "?A be Function" using Function_2[of carrier multF] by (simp add:string)
  have "the carrier of ?A=X" using the_selector_of_1[OF T1, of carrier "X"] tarski_def_1 by auto
  thus ?thesis using T1 multMagma Field_1[OF T1,of multF B] Field_1[of ?A carrier "X" ] A1 string by auto
qed

theorem algstr_0_cl_28:
  "let D be non empty\<parallel>set & o be BinOp-of D
   cluster {[carrier,D]}\<union>{[multF,o]} \<rightarrow> non empty-struct"
proof-
  assume T0:"D be non empty\<parallel>set & o be BinOp-of D"
  let ?X = "{[carrier,D]}\<union>{[multF,o]}"
  have T1: "?X be multMagma" "?X be Function" using multMagma_ag T0 by auto
  have "the carrier of ?X = D" using the_selector_of_1[of ?X carrier D] T1(2) string by auto
  thus "?X is non empty-struct" using  struct_0_def_1_b multMagma one_sorted T1 T0 by auto
qed

theorem algstr_0_cl_29:
  "let T be trivial\<parallel>set & f be BinOp-of T
   cluster {[carrier,T]}\<union>{[multF,f]} \<rightarrow> trivial-struct"
proof-
  assume T0:"T be trivial\<parallel>set & f be BinOp-of T"
  let ?X = "{[carrier,T]}\<union>{[multF,f]}"
  have T1: "?X be multMagma" "?X be Function" using multMagma_ag T0 by auto
  hence T2: "the carrier of ?X = T" "?X be one-sorted" using the_selector_of_1[of ?X carrier T]  multMagma one_sorted string by auto
  show "?X is  trivial-struct" using  struct_0_def_9_a[of ?X,THEN iffD2,rule_format, OF T2(2)] T0 T2(1) by auto
qed

theorem algstr_0_cl_30:
  "let N be non trivial\<parallel>set & b be BinOp-of N
   cluster {[carrier,N]}\<union>{[multF,b]} \<rightarrow> non trivial-struct"
proof-
  assume T0:"N be non trivial\<parallel>set & b be BinOp-of N"
  let ?X = "{[carrier,N]}\<union>{[multF,b]}"
  have T1: "?X be multMagma" "?X be Function" using multMagma_ag T0 by auto
  hence T2: "the carrier of ?X = N" "?X be one-sorted" using the_selector_of_1[of ?X carrier N]  multMagma one_sorted string by auto
  show "?X is  non trivial-struct" using  struct_0_def_9_b[of ?X,THEN iffD2,rule_format, OF T2(2)] T0 T2(1) by auto
qed

text_raw \<open>\DefineSnippet{algstr0def18}{\<close>
definition algstr_0_def_18 ("_ \<otimes>\<^sub>_ _" [96, 1000, 97] 96) where
  "func x \<otimes>\<^sub>M y \<rightarrow> Element-of-struct M equals
     (the multF of M) . \<lparr> x , y \<rparr>"
text_raw \<open>}%EndSnippet\<close>
schematic_goal algstr_0_def_18:
  assumes "M be multMagma & x be Element-of-struct M
         & y be Element-of-struct M" shows "?X"

proof (rule equals_property [OF algstr_0_def_18_def,of M x y])
   let ?A = "the carrier of M"
   have A1: "(the multF of M) be BinOp-of ?A" "?A be set" using assms multMagma field one_sorted by auto
   thus " (the multF of M) .  \<lparr> x , y \<rparr> be Element-of ?A"  using binop_0_def_20[of "the carrier of M" "the multF of M" x y]
           assms by auto
qed

definition algstr_0_def_19 ("Trivial-multMagma") where
  "func Trivial-multMagma \<rightarrow> multMagma equals
     {[carrier,{{}}]}\<union>{[multF,op2]}"

schematic_goal algstr_0_def_19:
  shows "?X"
proof (rule equals_property [OF algstr_0_def_19_def])
  show "({[carrier,{{}}]} \<union>{[multF,op2]}) be multMagma" using multMagma_ag funct_5_def_9 all_set by auto
qed

lemmas [simp] = algstr_0_def_19[THEN conjunct2]


lemma algstr_0_def_19_t:"Trivial-multMagma is trivial-struct"
proof-
  have A1: "{{}} is trivial" using zfmisc_1_def_10a all_set tarski_def_1b by auto
  have "op2 be  BinOp-of {{}}" using funct_5_def_9 by simp
  thus ?thesis using  algstr_0_cl_29 all_set A1 by auto
qed

theorem algstr_0_cl_31:
  "cluster Trivial-multMagma \<rightarrow> 1-element-struct\<bar> strict multMagma"
proof(rule attr_attr[THEN iffD2],rule conjI)
  let ?T ="Trivial-multMagma"
  have T0: "?T be multMagma" "?T be one-sorted" "?T be Function" using algstr_0_def_19 multMagma one_sorted by auto
  hence T1: "the carrier of ?T={{}}"
    using the_selector_of_1[OF T0(3),of carrier "{{}}"] string by auto
  thus T2: "Trivial-multMagma is 1-element-struct" using T0 struct_0_def_19_a by auto
  have  "domain_of multMagma = dom ?T"  using multMagma Dom_2 by auto
  thus "Trivial-multMagma is strict multMagma" using T2 strict T0 by auto
qed

theorem algstr_0_cl_32:
  "cluster strict multMagma\<bar>1-element-struct for multMagma"
proof
  show "Trivial-multMagma is strict multMagma\<bar>1-element-struct" using algstr_0_cl_31 by auto
  show "Trivial-multMagma be multMagma" using algstr_0_def_19 by auto
qed


definition left_mult_cancelable ("left-mult-cancelable\<^sub>_") where algstr_0_def_20 [THEN defattr_property]:
   "attr left-mult-cancelable\<^sub>M means (\<lambda> x. M be multMagma & x be Element-of-struct M &
                                       (for y,z be Element-of-struct M st x \<otimes>\<^sub>M y = x \<otimes>\<^sub>M z holds y = z))"

lemmas algstr_0_def_20a = algstr_0_def_20[THEN iffD1,THEN conjunct2,rule_format]

definition right_mult_cancelable ("right-mult-cancelable\<^sub>_") where algstr_0_def_21 [THEN defattr_property]:
   "attr right-mult-cancelable\<^sub>M means (\<lambda> x. M be multMagma & x be Element-of-struct M &
                                       (for y,z be Element-of-struct M st y \<otimes>\<^sub>M x = z \<otimes>\<^sub>M x holds y = z))"
lemmas algstr_0_def_21a = algstr_0_def_21[THEN iffD1,THEN conjunct2,rule_format]

definition mult_cancelable ("mult-cancelable\<^sub>_") where algstr_0_def_22 [THEN defattr_property]:
   "attr mult-cancelable\<^sub>M means (\<lambda> x. M be multMagma & x be Element-of-struct M &
                                       x is  right-mult-cancelable\<^sub>M \<bar> left-mult-cancelable\<^sub>M)"
lemmas algstr_0_def_22a = algstr_0_def_22[THEN iffD1,THEN conjunct2,rule_format]


(*Przykład na to że klastry zapentlają simp*)

theorem algstr_0_cl_33:
  "let M be multMagma
   cluster right-mult-cancelable\<^sub>M \<bar> left-mult-cancelable\<^sub>M \<rightarrow> mult-cancelable\<^sub>M  for Element-of-struct M" using  algstr_0_def_22 by auto

theorem algstr_0_cl_34:
  "let M be multMagma
   cluster mult-cancelable\<^sub>M \<rightarrow> right-mult-cancelable\<^sub>M \<bar> left-mult-cancelable\<^sub>M for Element-of-struct M" using  algstr_0_def_22 by auto

definition left_mult_cancelable_M ("left-mult-cancelable") where algstr_0_def_23 [THEN defattr_property]:
   "attr left-mult-cancelable means (\<lambda> M. M be multMagma & (for x be Element-of-struct M holds x is left-mult-cancelable\<^sub>M))"
lemmas algstr_0_def_23a = algstr_0_def_23[THEN iffD1,THEN conjunct2,rule_format]

definition right_mult_cancelable_M ("right-mult-cancelable") where algstr_0_def_24 [THEN defattr_property]:
   "attr right-mult-cancelable means (\<lambda> M. M be multMagma &
                                       (for x be Element-of-struct M holds x is right-mult-cancelable\<^sub>M))"
lemmas algstr_0_def_24a = algstr_0_def_24[THEN iffD1,THEN conjunct2,rule_format]

definition mult_cancelable_M ("mult-cancelable") where algstr_0_def_25 [THEN defattr_property]:
   "attr mult-cancelable means (\<lambda> M. M be multMagma &
                                       M is  right-mult-cancelable \<bar> left-mult-cancelable)"

lemmas algstr_0_def_25a = algstr_0_def_8[THEN iffD1,THEN conjunct2,rule_format]

theorem algstr_0_cl_35:
  "cluster right-mult-cancelable \<bar> left-mult-cancelable \<rightarrow> mult-cancelable  for multMagma" using  algstr_0_def_25 by auto

theorem algstr_0_cl_36:
  "cluster mult-cancelable \<rightarrow> right-mult-cancelable \<bar> left-mult-cancelable for multMagma" using  algstr_0_def_25 by auto

theorem algstr_0_cl_37:
  "cluster Trivial-multMagma \<rightarrow> mult-cancelable"
proof(unfold algstr_0_def_25,rule conjI,rule algstr_0_def_19[THEN conjunct1],rule attr_attr[THEN iffD2],rule conjI)
  let ?T ="Trivial-multMagma"
  have T0: "?T be Function" "?T be one-sorted" using algstr_0_def_19 multMagma one_sorted by auto
  have T1: "the carrier of ?T={{}}"
    using the_selector_of_1[OF T0(1),of carrier "{{}}"] string by auto
  show "?T is right-mult-cancelable"
    proof(unfold algstr_0_def_24,rule conjI,rule algstr_0_def_19[THEN conjunct1],rule ballI)
      fix x assume T2: "x be Element-of-struct ?T"
      show "x is right-mult-cancelable\<^sub>?T"
      proof(unfold algstr_0_def_21,intro conjI,rule algstr_0_def_19[THEN conjunct1],rule T2,intro ballI impI)
        fix y z assume T3: "y be Element-of-struct ?T" "z be Element-of-struct ?T"
        assume "y \<otimes>\<^sub>?T x = z \<otimes>\<^sub>?T x"
        show "y = z" using struct_0_def_10[OF T0(2),THEN iffD1,OF algstr_0_def_19_t,rule_format,OF T3] by simp
      qed
    qed
  show "?T is left-mult-cancelable"
    proof(unfold algstr_0_def_23,rule conjI,rule algstr_0_def_19[THEN conjunct1],rule ballI)
      fix x assume T2: "x be Element-of-struct ?T"
      show "x is left-mult-cancelable\<^sub>?T"
      proof(unfold algstr_0_def_20,intro conjI,rule algstr_0_def_19[THEN conjunct1],rule T2,intro ballI impI)
        fix y z assume T3: "y be Element-of-struct ?T" "z be Element-of-struct ?T"
        assume "x \<otimes>\<^sub>?T y = x \<otimes>\<^sub>?T z"
        show "y = z"  using struct_0_def_10[OF T0(2),THEN iffD1,OF algstr_0_def_19_t,rule_format,OF T3] by simp
      qed
    qed
qed

theorem algstr_0_cl_38:
  "cluster mult-cancelable\<bar>strict multMagma\<bar>1-element-struct for multMagma"
proof
  show "Trivial-multMagma is mult-cancelable\<bar>strict multMagma\<bar>1-element-struct" using algstr_0_cl_31 algstr_0_cl_37 by auto
  show "Trivial-multMagma be multMagma" using algstr_0_def_19 by auto
qed

theorem algstr_0_cl_39:
  "let M be left-mult-cancelable \<parallel> multMagma
   cluster \<rightarrow> left-mult-cancelable\<^sub>M for Element-of-struct M"
  using algstr_0_def_23 by auto

theorem algstr_0_cl_40:
  "let M be right-mult-cancelable \<parallel> multMagma
   cluster \<rightarrow> right-mult-cancelable\<^sub>M for Element-of-struct M"
  using algstr_0_def_24 by auto

abbreviation "multLoopStr_fields \<equiv> (#carrier \<rightarrow> set'; OneF \<rightarrow> Element-of' the' carrier; multF\<rightarrow> BinOp-of' the' carrier #)"

definition "struct multLoopStr multLoopStr_fields"

lemma multLoopStr_well:"multLoopStr_fields  well defined on {carrier} \<union>{OneF}\<union>{multF}"
proof(rule Fields_add_argM1[OF OneStr_well],simp add:string,simp add:string)
  show "for X1 be OneStr_fields\<parallel>Function holds ex it be BinOp-of-struct X1 st True"
  proof(rule ballI)
    fix X1 assume "X1 be OneStr_fields\<parallel>Function"
    hence "the carrier of X1 be set" using field by auto
    thus "ex it be BinOp-of the carrier of X1 st True"  using BinOp_ex by auto
  qed
qed

schematic_goal multLoopStr:
   shows ?X by (rule struct_well_defined[OF multLoopStr_def multLoopStr_well])

theorem multLoopStr_inheritance:
  "X be multLoopStr \<Longrightarrow> X be multMagma &  X be OneStr" using multLoopStr multMagma OneStr by auto

lemma multLoopStr_ag[rule_format]: "X be set \<Longrightarrow> B be BinOp-of X \<Longrightarrow> E be Element-of X \<Longrightarrow>
   ({[carrier,X]}\<union>{[multF,B]}\<union>{[OneF,E]}) be multLoopStr & ({[carrier,X]}\<union>{[multF,B]}\<union>{[OneF,E]}) be Function"
proof-
  assume A1: "X be set" "B be BinOp-of X" "E be Element-of X"
  let ?A= "{[carrier,X]}\<union>{[multF,B]}\<union>{[OneF,E]}"
  have T1: "?A be Function" using Function_3[of carrier multF OneF] by (simp add:string)
  have "the carrier of ?A=X" using the_selector_of_1[OF T1, of carrier X] tarski_def_1 by auto
  thus ?thesis using T1  multLoopStr Field_1[OF T1,of multF B] Field_1[of ?A carrier X ] Field_1[of ?A OneF E ] A1 string by auto
qed

theorem algstr_0_cl_41:
  "let D be non empty\<parallel>set & o be BinOp-of D & d be Element-of D
   cluster {[carrier,D]}\<union>{[multF,o]}\<union>{[OneF,d]} \<rightarrow> non empty-struct"
proof-
  assume T0:"D be non empty\<parallel>set & o be BinOp-of D & d be Element-of D"
  let ?X = "{[carrier,D]}\<union>{[multF,o]}\<union>{[OneF,d]}"
  have T1: "?X be multLoopStr" "?X be Function" using multLoopStr_ag T0 by auto
  have "the carrier of ?X = D" using the_selector_of_1[of ?X carrier D] T1(2) string by auto
  thus "?X is non empty-struct" using  struct_0_def_1_b multLoopStr one_sorted T1 T0 by auto
qed

theorem algstr_0_cl_42:
  "let T be trivial\<parallel>set & f be BinOp-of T & t be Element-of T
   cluster {[carrier,T]}\<union>{[multF,f]}\<union>{[OneF,t]} \<rightarrow> trivial-struct"
proof-
  assume T0:"T be trivial\<parallel>set & f be BinOp-of T & t be Element-of T"
  let ?X = "{[carrier,T]}\<union>{[multF,f]}\<union>{[OneF,t]}"
  have T1: "?X be multLoopStr" "?X be Function" using multLoopStr_ag T0 by auto
  hence T2: "the carrier of ?X = T" "?X be one-sorted" using the_selector_of_1[of ?X carrier T]
    multLoopStr one_sorted string by auto
  show "?X is  trivial-struct" using  struct_0_def_9_a[of ?X,THEN iffD2,rule_format, OF T2(2)] T0 T2(1) by auto
qed

theorem algstr_0_cl_43:
  "let N be non trivial\<parallel>set & b be BinOp-of N & m be Element-of N
   cluster {[carrier,N]}\<union>{[multF,b]}\<union>{[OneF,m]} \<rightarrow> non trivial-struct"
proof-
  assume T0:"N be non trivial\<parallel>set & b be BinOp-of N & m be Element-of N"
  let ?X = "{[carrier,N]}\<union>{[multF,b]}\<union>{[OneF,m]}"
  have T1: "?X be multLoopStr" "?X be Function" using multLoopStr_ag T0 by auto
  hence T2: "the carrier of ?X = N" "?X be one-sorted" using the_selector_of_1[of ?X carrier N]  multLoopStr one_sorted string by auto
  show "?X is  non trivial-struct" using  struct_0_def_9_b[of ?X,THEN iffD2,rule_format, OF T2(2)] T0 T2(1) by auto
qed

definition algstr_0_def_26 ("Trivial-multLoopStr") where
  "func Trivial-multLoopStr \<rightarrow> multLoopStr equals
     {[carrier,{{}}]}\<union>{[multF,op2]}\<union>{[OneF,op0]}"

schematic_goal algstr_0_def_26:
  shows "?X"
proof (rule equals_property [OF algstr_0_def_26_def])
  show "({[carrier,{{}}]} \<union>{[multF,op2]}\<union>{[OneF,op0]}) be multLoopStr" using multLoopStr_ag funct_5_def_9 funct_5_def_7 all_set by auto
qed

lemmas [simp] = algstr_0_def_26[THEN conjunct2]

lemma algstr_0_def_26_t:"Trivial-multLoopStr is trivial-struct"
proof-
  have A1: "{{}} is trivial" using zfmisc_1_def_10a all_set tarski_def_1b by auto
  have "op2 be  BinOp-of {{}}" "op0 be Element-of {{}}" using funct_5_def_9 funct_5_def_7 funct_5_def_4 by simp+
  thus ?thesis using  algstr_0_cl_42[of "{{}}" op2 op0] all_set A1 by auto
qed

theorem algstr_0_cl_44:
  "cluster Trivial-multLoopStr \<rightarrow> 1-element-struct\<bar> strict multLoopStr"
proof(rule attr_attr[THEN iffD2],rule conjI)
  let ?T ="Trivial-multLoopStr"
  have T0: "?T be multLoopStr" "?T be one-sorted" "?T be Function" using algstr_0_def_26 multLoopStr one_sorted by auto
  hence T1: "the carrier of ?T={{}}"
    using the_selector_of_1[OF T0(3),of carrier "{{}}"] string by auto
  thus T2: "Trivial-multLoopStr is 1-element-struct" using T0 struct_0_def_19_a by auto
  have  "domain_of multLoopStr = dom ?T"  using multLoopStr Dom_3 tarski_th_2[of "domain_of multLoopStr" "dom ?T"] by auto
  thus "Trivial-multLoopStr is strict multLoopStr" using T2 strict T0 by auto
qed

theorem algstr_0_cl_45:
  "cluster strict multLoopStr\<bar>1-element-struct for multLoopStr"
proof
  show "Trivial-multLoopStr is strict multLoopStr\<bar>1-element-struct" using algstr_0_cl_44 by auto
  show "Trivial-multLoopStr be multLoopStr" using algstr_0_def_26 by auto
qed

theorem algstr_0_cl_46:
  "cluster Trivial-multLoopStr \<rightarrow> mult-cancelable"
proof(unfold algstr_0_def_25,rule conjI)
  let ?T ="Trivial-multLoopStr"
  show T: "?T be multMagma" using  algstr_0_def_26 multLoopStr multMagma by auto
  show "?T is right-mult-cancelable  \<bar>  left-mult-cancelable"
    proof (rule attr_attr[THEN iffD2],rule conjI)
       have T0: "?T be Function" "?T be one-sorted" using T multMagma one_sorted by auto
       have T1: "the carrier of ?T={{}}"
         using the_selector_of_1[OF T0(1),of carrier "{{}}"] string by auto
      show "?T is right-mult-cancelable"
        proof(unfold algstr_0_def_24,rule conjI,rule T,rule ballI)
          fix x assume T2: "x be Element-of-struct ?T"
          show "x is right-mult-cancelable\<^sub>?T"
             proof(unfold algstr_0_def_21,intro conjI,rule T,rule T2,intro ballI impI)
               fix y z assume T3: "y be Element-of-struct ?T" "z be Element-of-struct ?T"
               assume "y \<otimes>\<^sub>?T x = z \<otimes>\<^sub>?T x"
               show "y = z" using struct_0_def_10[OF T0(2),THEN iffD1,OF algstr_0_def_26_t,rule_format,OF T3] by simp
             qed
        qed
      show "?T is left-mult-cancelable"
        proof(unfold algstr_0_def_23,rule conjI,rule T,rule ballI)
          fix x assume T2: "x be Element-of-struct ?T"
          show "x is left-mult-cancelable\<^sub>?T"
             proof(unfold algstr_0_def_20,intro conjI,rule T,rule T2,intro ballI impI)
               fix y z assume T3: "y be Element-of-struct ?T" "z be Element-of-struct ?T"
               assume "x \<otimes>\<^sub>?T y = x \<otimes>\<^sub>?T z"
               show "y = z"  using struct_0_def_10[OF T0(2),THEN iffD1,OF algstr_0_def_26_t,rule_format,OF T3] by simp
            qed
          qed
   qed
qed

definition left_invertible ::"Set \<Rightarrow>Attr" ("left-invertible\<^sub>_") where algstr_0_def_27 [THEN defattr_property]:
   "attr left-invertible\<^sub>M means (\<lambda> x. M be multLoopStr & x be Element-of-struct M &
                                       (ex y be Element-of-struct M st y \<otimes>\<^sub>M x =1\<^sub>M))"
lemmas algstr_0_def_27a = algstr_0_def_27[THEN iffD1,THEN conjunct2,rule_format]

definition right_invertible ("right-invertible\<^sub>_") where algstr_0_def_28 [THEN defattr_property]:
   "attr right-invertible\<^sub>M means (\<lambda> x. M be multLoopStr & x be Element-of-struct M &
                                       (ex y be Element-of-struct M st x \<otimes>\<^sub>M y =1\<^sub>M))"
lemmas algstr_0_def_28a = algstr_0_def_11[THEN iffD1,THEN conjunct2,rule_format]

definition mult_invertible ("mult-invertible\<^sub>_") where algstr_0_def_29 [THEN defattr_property]:
   "attr mult-invertible\<^sub>M means (\<lambda> x. M be multLoopStr & x be Element-of-struct M &
                                       x is  right-invertible\<^sub>M \<bar> left-invertible\<^sub>M)"
lemmas algstr_0_def_29a = algstr_0_def_29[THEN iffD1,THEN conjunct2,rule_format]

theorem algstr_0_cl_47:
  "let M be multLoopStr
   cluster right-invertible\<^sub>M \<bar> left-invertible\<^sub>M \<rightarrow> mult-invertible\<^sub>M  for Element-of-struct M"
     using  algstr_0_def_29 by auto

theorem algstr_0_cl_48:
  "let M be multLoopStr
   cluster mult-invertible\<^sub>M \<rightarrow> right-invertible\<^sub>M \<bar> left-invertible\<^sub>M for Element-of-struct M"
  using  algstr_0_def_29 by auto
text_raw \<open>\DefineSnippet{algstr0def30}{\<close>
definition algstr_0_def_30 ("'/\<^sub>_ _" [1000, 99] 98) where
  "assume x is left-invertible\<^sub>M \<bar> right-mult-cancelable\<^sub>M
   func /\<^sub>M x \<rightarrow> Element-of-struct M means
     (\<lambda>it. it \<otimes>\<^sub>M x = 1\<^sub>M)"
schematic_goal algstr_0_def_30[rule_format]:
  assumes "M be multLoopStr"
          "x be Element-of-struct M" shows "?X"
text_raw \<open>}%EndSnippet\<close>
proof (induct rule: assume_means_property[OF algstr_0_def_30_def conjI[OF assms], of x M,  case_names existence uniqueness coherence])
  case existence
      assume "x is left-invertible\<^sub>M \<bar>right-mult-cancelable\<^sub>M"
      thus "ex y be Element-of-struct M st y \<otimes>\<^sub>M x= 1\<^sub>M" using algstr_0_def_27a by auto
  next
   case uniqueness
     assume A1: "x is left-invertible\<^sub>M \<bar>right-mult-cancelable\<^sub>M"
     fix y1 y2
     assume T0: "y1 be Element-of-struct M"
                "y2 be Element-of-struct M" and
    A2: " y1 \<otimes>\<^sub>M x= 1\<^sub>M" and
    A3: " y2 \<otimes>\<^sub>M x= 1\<^sub>M"
    thus "y1=y2" using A1 algstr_0_def_21a[of x M y1 y2] by auto
  next
   case coherence
     show "ex x being Element-of-struct M st True" using subset_1_def_1[THEN conjunct2] all_set by auto
qed

definition left_invertible_M ("left-invertible") where algstr_0_def_31 [THEN defattr_property]:
   "attr left-invertible means (\<lambda> M. M be multLoopStr & (for x be Element-of-struct M holds x is left-invertible\<^sub>M))"
lemmas algstr_0_def_31a = algstr_0_def_3[THEN iffD1,THEN conjunct2,rule_format]


definition right_invertible_M ("right-invertible") where algstr_0_def_32 [THEN defattr_property]:
   "attr right-invertible means (\<lambda> M. M be multLoopStr &
                                       (for x be Element-of-struct M holds x is right-invertible\<^sub>M))"
lemmas algstr_0_def_32a = algstr_0_def_16[THEN iffD1,THEN conjunct2,rule_format]

definition invertible_M ("invertible") where algstr_0_def_33 [THEN defattr_property]:
   "attr invertible means (\<lambda> M. M be multLoopStr &
                                       M is  right-invertible \<bar> left-invertible)"

lemmas algstr_0_def_33a = algstr_0_def_17[THEN iffD1,THEN conjunct2,rule_format]

theorem algstr_0_cl_49:
  "cluster right-invertible \<bar> left-invertible \<rightarrow> invertible  for multLoopStr" using  algstr_0_def_33 by auto

theorem algstr_0_cl_50:
  "cluster invertible \<rightarrow> right-invertible \<bar> left-invertible for multLoopStr" using  algstr_0_def_33 by auto

theorem algstr_0_cl_51:
  "cluster Trivial-multLoopStr \<rightarrow> invertible"
proof(unfold algstr_0_def_33,rule conjI,rule algstr_0_def_26[THEN conjunct1],rule attr_attr[THEN iffD2],rule conjI)
  let ?T ="Trivial-multLoopStr"
  have T0: "?T be Function" "?T be OneStr" "?T be one_sorted" "?T be multMagma"
      using algstr_0_def_26 multLoopStr OneStr one_sorted multMagma by auto
  have T1: "the carrier of ?T={{}}"
    using the_selector_of_1[OF T0(1),of carrier "{{}}"] string by auto
  have Z: "1\<^sub>?T be Element-of-struct ?T" using struct_0_def_7[of ?T] T0 by auto
  show "?T is right-invertible"
    proof(unfold algstr_0_def_32,rule conjI,rule  algstr_0_def_26[THEN conjunct1],rule ballI)
      fix x assume T2: "x be Element-of-struct ?T"
      hence T3: "(x \<otimes>\<^sub>?T x) be Element-of-struct ?T"  using algstr_0_def_18[of ?T x x] T0(4) by auto
      show "x is right-invertible\<^sub>?T"
      proof(unfold algstr_0_def_28,intro conjI,rule algstr_0_def_26[THEN conjunct1],rule T2,rule bexI[of _ x])
        show "x be Element-of-struct ?T" using T2 by simp
        show "x \<otimes>\<^sub>?T x =1\<^sub>?T" using struct_0_def_10[OF T0(3),THEN iffD1,OF algstr_0_def_26_t,rule_format,OF Z T3] by simp
      qed
    qed
  show "?T is left-invertible"
    proof(unfold algstr_0_def_31,rule conjI,rule  algstr_0_def_26[THEN conjunct1],rule ballI)
      fix x assume T2: "x be Element-of-struct ?T"
      hence T3: "(x \<otimes>\<^sub>?T x) be Element-of-struct ?T"  using algstr_0_def_18[of ?T x x] T0(4) by auto
      show "x is left-invertible\<^sub>?T"
      proof(unfold algstr_0_def_27,intro conjI,rule algstr_0_def_26[THEN conjunct1],rule T2,rule bexI[of _ x])
        show "x be Element-of-struct ?T" using T2 by simp
        show "x \<otimes>\<^sub>?T x =1\<^sub>?T" using struct_0_def_10[OF T0(3),THEN iffD1,OF algstr_0_def_26_t,rule_format,OF Z T3] by simp
      qed
    qed
qed

theorem algstr_0_cl_52:
  "cluster invertible\<bar>mult-cancelable\<bar>strict multLoopStr\<bar>1-element-struct for multLoopStr"
proof
  show "Trivial-multLoopStr is  invertible\<bar>mult-cancelable\<bar>strict multLoopStr\<bar>1-element-struct"
       using algstr_0_cl_44 algstr_0_cl_46 algstr_0_cl_51 by auto
  show "Trivial-multLoopStr be multLoopStr" using algstr_0_def_26 by auto
qed

theorem algstr_0_cl_53:
  "let M be left-invertible \<parallel> multLoopStr
   cluster \<rightarrow> left-invertible\<^sub>M for Element-of-struct M"
  using algstr_0_def_31 by auto

theorem algstr_0_cl_54:
  "let M be right-invertible \<parallel> multLoopStr
   cluster \<rightarrow> right-invertible\<^sub>M for Element-of-struct M"
  using algstr_0_def_32 by auto

(*begin :: Almost*)
abbreviation  "multLoopStr_0_fields \<equiv> (#carrier \<rightarrow> set';  multF\<rightarrow> BinOp-of' the' carrier; ZeroF \<rightarrow> Element-of' the' carrier;
      OneF \<rightarrow> Element-of' the' carrier #)"

definition "struct  multLoopStr_0 multLoopStr_0_fields"

lemma multLoopStr_0_well_pre:" multLoopStr_fields \<bar>(# ZeroF \<rightarrow> Element-of' the' carrier #)
                           well defined on {carrier} \<union>{OneF}\<union>{multF}\<union>{ZeroF} "
proof(rule Fields_add_argM1[OF multLoopStr_well],simp add:string,simp add:string)
  show "for X1 be multLoopStr_fields\<parallel>Function holds ex it be Element-of-struct X1 st True"
  proof(rule ballI)
    fix X1 assume "X1 be multLoopStr_fields\<parallel>Function"
    hence "the carrier of X1 be set" using field by auto
    thus "ex it be Element-of the carrier of X1 st True"  using subset_1_def_1[THEN conjunct2] by auto
  qed
qed

lemma multLoopStr_0_well:"multLoopStr_0_fields well defined on {carrier} \<union>{multF}\<union>{ZeroF}\<union>{OneF} "
proof-
  have A0: "{carrier} \<union>{OneF}\<union>{multF}\<union>{ZeroF} = {carrier} \<union>{multF}\<union>{ZeroF}\<union>{OneF}"
      using tarski_0_2[of "{carrier} \<union>{OneF}\<union>{multF}\<union>{ZeroF}" "{carrier} \<union>{multF}\<union>{ZeroF}\<union>{OneF}"] by auto
  have A1: "\<And>X. X is multLoopStr_fields \<bar>(# ZeroF \<rightarrow> Element-of' the' carrier #)
            iff X is multLoopStr_0_fields"
     by auto
 show ?thesis using  well_defined_order[OF A1 multLoopStr_0_well_pre] A0 by auto
qed

schematic_goal multLoopStr_0:
   shows ?X by (rule struct_well_defined[OF multLoopStr_0_def multLoopStr_0_well])

theorem multLoopStr_0_inheritance:
  "X be multLoopStr_0 \<Longrightarrow> X be multLoopStr & X be ZeroOneStr" using multLoopStr_0 multLoopStr ZeroOneStr by simp

lemma multLoopStr_0_ag[rule_format]: "X be set \<Longrightarrow> B be BinOp-of X \<Longrightarrow> Z be Element-of X \<Longrightarrow> E be Element-of X \<Longrightarrow>
   ({[carrier,X]}\<union>{[multF,B]}\<union>{[ZeroF,Z]}\<union>{[OneF,E]}) be multLoopStr_0 & ({[carrier,X]}\<union>{[multF,B]}\<union>{[ZeroF,Z]}\<union>{[OneF,E]}) be Function"
proof-
  assume A1: "X be set" "B be BinOp-of X" "Z be Element-of X"   "E be Element-of X"
  let ?A= "{[carrier,X]}\<union>{[multF,B]}\<union>{[ZeroF,Z]}\<union>{[OneF,E]}"
  have T1: "?A be Function" using Function_4[of carrier multF ZeroF OneF] by (simp add:string)
  have "the carrier of ?A=X" using the_selector_of_1[OF T1, of carrier X] tarski_def_1 by auto
  thus ?thesis using T1  multLoopStr_0 Field_1[OF T1,of multF B] Field_1[of ?A carrier X ] Field_1[of ?A OneF E ] Field_1[of ?A ZeroF Z ] A1 string by auto
qed

theorem algstr_0_cl_55:
  "let D be non empty\<parallel>set & o be BinOp-of D & d be Element-of D & e be Element-of D
   cluster {[carrier,D]}\<union>{[multF,o]}\<union>{[ZeroF,d]}\<union>{[OneF,e]} \<rightarrow> non empty-struct"
proof-
  assume T0:"D be non empty\<parallel>set & o be BinOp-of D & d be Element-of D & e be Element-of D"
  let ?X = "{[carrier,D]}\<union>{[multF,o]}\<union>{[ZeroF,d]}\<union>{[OneF,e]}"
  have T1: "?X be multLoopStr_0" "?X be Function" using multLoopStr_0_ag T0 by auto
  have "the carrier of ?X = D" using the_selector_of_1[of ?X carrier D] T1(2) string by auto
  thus "?X is non empty-struct" using  struct_0_def_1_b multLoopStr_0 one_sorted T1 T0 by auto
qed

theorem algstr_0_cl_56:
  "let T be trivial\<parallel>set & f be BinOp-of T & s be Element-of T & t be Element-of T
   cluster {[carrier,T]}\<union>{[multF,f]}\<union>{[ZeroF,s]}\<union>{[OneF,t]} \<rightarrow> trivial-struct"
proof-
  assume T0:"T be trivial\<parallel>set & f be BinOp-of T & s be Element-of T & t be Element-of T"
  let ?X = "{[carrier,T]}\<union>{[multF,f]}\<union>{[ZeroF,s]}\<union>{[OneF,t]}"
  have T1: "?X be multLoopStr_0" "?X be Function" using multLoopStr_0_ag T0 by auto
  hence T2: "the carrier of ?X = T" "?X be one-sorted" using the_selector_of_1[of ?X carrier T]
    multLoopStr_0 one_sorted string by auto
  show "?X is  trivial-struct" using  struct_0_def_9_a[of ?X,THEN iffD2,rule_format, OF T2(2)] T0 T2(1) by auto
qed

theorem algstr_0_cl_57:
  "let N be non trivial\<parallel>set & b be BinOp-of N & m be Element-of N & n be Element-of N
   cluster {[carrier,N]}\<union>{[multF,b]}\<union>{[ZeroF,m]}\<union>{[OneF,n]} \<rightarrow> non trivial-struct"
proof-
  assume T0:"N be non trivial\<parallel>set & b be BinOp-of N & m be Element-of N & n be Element-of N"
  let ?X = "{[carrier,N]}\<union>{[multF,b]}\<union>{[ZeroF,m]}\<union>{[OneF,n]}"
  have T1: "?X be multLoopStr_0" "?X be Function" using multLoopStr_0_ag T0 by auto
  hence T2: "the carrier of ?X = N" "?X be one-sorted" using the_selector_of_1[of ?X carrier N]  multLoopStr_0 one_sorted string by auto
  show "?X is  non trivial-struct" using  struct_0_def_9_b[of ?X,THEN iffD2,rule_format, OF T2(2)] T0 T2(1) by auto
qed

definition algstr_0_def_34 ("Trivial-multLoopStr'_0") where
  "func Trivial-multLoopStr_0 \<rightarrow> multLoopStr_0 equals
     {[carrier,{{}}]}\<union>{[multF,op2]}\<union>{[ZeroF,op0]}\<union>{[OneF,op0]}"

schematic_goal algstr_0_def_34:
  shows "?X"
proof (rule equals_property [OF algstr_0_def_34_def])
  show "({[carrier,{{}}]} \<union>{[multF,op2]}\<union>{[ZeroF,op0]}\<union>{[OneF,op0]}) be multLoopStr_0" using multLoopStr_0_ag funct_5_def_9 funct_5_def_7 all_set by auto
qed

lemmas [simp] = algstr_0_def_34[THEN conjunct2]

lemma algstr_0_def_34_t:"Trivial-multLoopStr_0 is trivial-struct"
proof-
  have A1: "{{}} is trivial" using zfmisc_1_def_10a all_set tarski_def_1b by auto
  have "op2 be  BinOp-of {{}}" "op0 be Element-of {{}}" using funct_5_def_9 funct_5_def_7 funct_5_def_4 by simp+
  thus ?thesis using  algstr_0_cl_56[of "{{}}" op2 op0] all_set A1 by auto
qed

theorem algstr_0_cl_58:
  "cluster Trivial-multLoopStr_0 \<rightarrow> 1-element-struct\<bar> strict multLoopStr_0"
proof(rule attr_attr[THEN iffD2],rule conjI)
  let ?T ="Trivial-multLoopStr_0"
  have T0: "?T be multLoopStr_0" "?T be one-sorted" "?T be Function" using algstr_0_def_34 multLoopStr_0 one_sorted by auto
  hence T1: "the carrier of ?T={{}}"
    using the_selector_of_1[OF T0(3),of carrier "{{}}"] string by auto
  thus T2: "Trivial-multLoopStr_0 is 1-element-struct" using T0 struct_0_def_19_a by auto
  have  "domain_of multLoopStr_0 = dom ?T"  using multLoopStr_0 Dom_4 by auto
  thus "Trivial-multLoopStr_0 is strict multLoopStr_0" using T2 strict T0 by auto
qed

theorem algstr_0_cl_59:
  "cluster strict multLoopStr_0\<bar>1-element-struct for multLoopStr_0"
proof
  show "Trivial-multLoopStr_0 is strict multLoopStr_0\<bar>1-element-struct" using algstr_0_cl_58 by auto
  show "Trivial-multLoopStr_0 be multLoopStr_0" using algstr_0_def_34 by auto
qed


definition almost_left_cancelable_M ("almost-left-cancelable") where algstr_0_def_36 [THEN defattr_property]:
   "attr almost-left-cancelable means (\<lambda> M. M be multLoopStr_0 &
                                       (for x be Element-of-struct M st x <> 0\<^sub>M holds x is left-mult-cancelable\<^sub>M))"
lemmas algstr_0_def_36a = algstr_0_def_36[THEN iffD1,THEN conjunct2,rule_format]

definition almost_right_cancelable_M ("almost-right-cancelable") where algstr_0_def_37 [THEN defattr_property]:
   "attr almost-right-cancelable means (\<lambda> M. M be multLoopStr_0 &
                                       (for x be Element-of-struct M st x <> 0\<^sub>M holds x is right-mult-cancelable\<^sub>M))"

lemmas algstr_0_def_37a = algstr_0_def_37[THEN iffD1,THEN conjunct2,rule_format]

definition almost_cancelable_M ("almost-cancelable") where algstr_0_def_38 [THEN defattr_property]:
   "attr almost-cancelable means (\<lambda> M. M be multLoopStr_0 & M is almost-right-cancelable \<bar> almost-left-cancelable)"
lemmas algstr_0_def_38a = algstr_0_def_37[THEN iffD1,THEN conjunct2,rule_format]

theorem algstr_0_cl_60:
  "cluster almost-right-cancelable \<bar> almost-left-cancelable \<rightarrow> almost-cancelable  for multLoopStr_0" using  algstr_0_def_38 by auto

theorem algstr_0_cl_61:
  "cluster almost-cancelable \<rightarrow> almost-right-cancelable \<bar> almost-left-cancelable for multLoopStr_0" using  algstr_0_def_38 by auto

theorem algstr_0_cl_62:
  "cluster Trivial-multLoopStr_0 \<rightarrow> almost-cancelable"
proof(unfold algstr_0_def_38,rule conjI)
  let ?T ="Trivial-multLoopStr_0"
  show T: "?T be multLoopStr_0" using  algstr_0_def_34 by auto
  show "?T is almost-right-cancelable  \<bar>  almost-left-cancelable"
    proof (rule attr_attr[THEN iffD2],rule conjI)
       have T0: "?T be Function" "?T be one-sorted" "?T be ZeroStr" using T multLoopStr_0 one_sorted ZeroStr by auto
       have Z: "0\<^sub>?T be Element-of-struct ?T" using struct_0_def_6[of ?T] T0 by auto
       show "?T is almost-right-cancelable"
        proof(unfold algstr_0_def_37,rule conjI,rule T,intro ballI)
          fix x assume T2: "x be Element-of-struct ?T"
          show "x <>0\<^sub>?T implies x is right-mult-cancelable\<^sub>?T" using struct_0_def_10[OF T0(2),THEN iffD1,OF algstr_0_def_34_t,rule_format,OF Z T2] by simp
        qed
       show "?T is almost-left-cancelable"
        proof(unfold algstr_0_def_36,rule conjI,rule T,intro ballI)
          fix x assume T2: "x be Element-of-struct ?T"
          show "x <>0\<^sub>?T implies x is left-mult-cancelable\<^sub>?T" using struct_0_def_10[OF T0(2),THEN iffD1,OF algstr_0_def_34_t,rule_format,OF Z T2] by simp
        qed
   qed
qed

theorem algstr_0_cl_63:
  "cluster almost-cancelable\<bar>strict multLoopStr_0\<bar>1-element-struct for multLoopStr_0"
proof
  show "Trivial-multLoopStr_0 is almost-cancelable\<bar>strict multLoopStr_0\<bar>1-element-struct" using algstr_0_cl_58 algstr_0_cl_62 by auto
  show "Trivial-multLoopStr_0 be multLoopStr_0" using algstr_0_def_34 by auto
qed

definition almost_left_invertible_M ("almost-left-invertible") where algstr_0_def_39 [THEN defattr_property]:
   "attr almost-left-invertible means (\<lambda> M. M be multLoopStr_0 &
                                       (for x be Element-of-struct M st x <> 0\<^sub>M holds x is left-invertible\<^sub>M))"
lemmas algstr_0_def_39a = algstr_0_def_39[THEN iffD1,THEN conjunct2,rule_format]

definition almost_right_invertible_M ("almost-right-invertible") where algstr_0_def_40 [THEN defattr_property]:
   "attr almost-right-invertible means (\<lambda> M. M be multLoopStr_0 &
                                       (for x be Element-of-struct M st x <> 0\<^sub>M holds x is right-invertible\<^sub>M))"

lemmas algstr_0_def_40a = algstr_0_def_39[THEN iffD1,THEN conjunct2,rule_format]

definition almost_invertible_M ("almost-invertible") where algstr_0_def_41 [THEN defattr_property]:
   "attr almost-invertible means (\<lambda> M. M be multLoopStr_0 & M is almost-right-invertible \<bar> almost-left-invertible)"
lemmas algstr_0_def_41a = algstr_0_def_40[THEN iffD1,THEN conjunct2,rule_format]

theorem algstr_0_cl_64:
  "cluster almost-right-invertible \<bar> almost-left-invertible \<rightarrow> almost-invertible  for multLoopStr_0" using  algstr_0_def_41 by auto

theorem algstr_0_cl_65:
  "cluster almost-invertible \<rightarrow> almost-right-invertible \<bar> almost-left-invertible for multLoopStr_0" using  algstr_0_def_41 by auto

theorem algstr_0_cl_66:
  "cluster Trivial-multLoopStr_0 \<rightarrow> almost-invertible"
proof(unfold algstr_0_def_41,rule conjI)
  let ?T ="Trivial-multLoopStr_0"
  show T: "?T be multLoopStr_0" using  algstr_0_def_34 by auto
  show "?T is almost-right-invertible  \<bar>  almost-left-invertible"
    proof (rule attr_attr[THEN iffD2],rule conjI)
       have T0: "?T be Function" "?T be one-sorted" "?T be ZeroStr" using T multLoopStr_0 one_sorted ZeroStr by auto
       have Z: "0\<^sub>?T be Element-of-struct ?T" using struct_0_def_6[of ?T] T0 by auto
       show "?T is almost-right-invertible"
        proof(unfold algstr_0_def_40,rule conjI,rule T,intro ballI)
          fix x assume T2: "x be Element-of-struct ?T"
          show "x <>0\<^sub>?T implies x is right-invertible\<^sub>?T" using struct_0_def_10[OF T0(2),THEN iffD1,OF algstr_0_def_34_t,rule_format,OF Z T2] by simp
        qed
       show "?T is almost-left-invertible"
        proof(unfold algstr_0_def_39,rule conjI,rule T,intro ballI)
          fix x assume T2: "x be Element-of-struct ?T"
          show "x <>0\<^sub>?T implies x is left-invertible\<^sub>?T" using struct_0_def_10[OF T0(2),THEN iffD1,OF algstr_0_def_34_t,rule_format,OF Z T2] by simp
        qed
   qed
qed

theorem algstr_0_cl_67:
  "cluster almost-invertible\<bar>almost-cancelable\<bar>strict multLoopStr_0\<bar>1-element-struct for multLoopStr_0"
proof
  show "Trivial-multLoopStr_0 is almost-invertible\<bar>almost-cancelable\<bar>strict multLoopStr_0\<bar>1-element-struct"
    using algstr_0_cl_58 algstr_0_cl_62 algstr_0_cl_66 by auto
  show "Trivial-multLoopStr_0 be multLoopStr_0" using algstr_0_def_34 by auto
qed

(*begin :: Double*)
abbreviation "doubleLoopStr_fields \<equiv>
 (# carrier \<rightarrow> \<lambda>S. set;
   addF \<rightarrow> \<lambda>S. BinOp-of the carrier of S;
   ZeroF \<rightarrow> \<lambda>S. Element-of the carrier of S;
   multF \<rightarrow> \<lambda>S. BinOp-of the carrier of S;
   OneF \<rightarrow> \<lambda>S. Element-of the carrier of S#)"

text_raw \<open>\DefineSnippet{doubleLoopStr_ex}{\<close>
term "{\<langle>carrier, the set\<rangle>} \<union>
  {\<langle>addF, the BinOp-of the set\<rangle>} \<union> {\<langle>ZeroF, the Element-of the set\<rangle>} \<union>
  {\<langle>multF, the BinOp-of the set\<rangle>} \<union> {\<langle>OneF,the Element-of the set\<rangle>}"
text_raw \<open>}%EndSnippet\<close>

lemma doubleLoopStr_well_pre:"
 multLoopStr_0_fields\<bar>(#addF \<rightarrow>BinOp-of' the' carrier #)
                    well defined on {carrier} \<union>{multF}\<union>{ZeroF}\<union>{OneF}\<union> {addF}"
proof(rule Fields_add_argM1[OF multLoopStr_0_well],simp add:string,simp add:string)
  show "for X1 be multLoopStr_0_fields\<parallel>Function holds ex it be BinOp-of-struct X1 st True"
  proof(rule ballI)
    fix X1 assume "X1 be multLoopStr_0_fields\<parallel>Function"
    hence "the carrier of X1 be set" using field by auto
    thus "ex it be BinOp-of the carrier of X1 st True" using BinOp_ex by auto
  qed
qed

lemma doubleLoopStr_well:"doubleLoopStr_fields well defined on {carrier} \<union>{addF}\<union>{ZeroF}\<union>{multF}\<union>{OneF} "
proof-
  have A0: "{carrier} \<union>{multF}\<union>{ZeroF}\<union>{OneF}\<union> {addF} = {carrier} \<union>{addF}\<union>{ZeroF}\<union>{multF}\<union>{OneF}" by auto
  have A1: "\<And>X. X is  multLoopStr_0_fields\<bar>(#addF \<rightarrow>BinOp-of' the' carrier #) iff X is doubleLoopStr_fields"
     by auto
  show ?thesis using  well_defined_order[OF A1 doubleLoopStr_well_pre] A0 by auto
qed

text_raw \<open>\DefineSnippet{doubleLoopStr}{\<close>
definition
"struct doubleLoopStr (#
   carrier \<rightarrow> \<lambda>S. set;
   addF \<rightarrow> \<lambda>S. BinOp-of the carrier of S;
   ZeroF \<rightarrow> \<lambda>S. Element-of the carrier of S;
   multF \<rightarrow> \<lambda>S. BinOp-of the carrier of S;
   OneF \<rightarrow> \<lambda>S. Element-of the carrier of S
#)"
text_raw \<open>}%EndSnippet\<close>

schematic_goal doubleLoopStr:
  shows ?X by (rule struct_well_defined[OF doubleLoopStr_def doubleLoopStr_well])


text_raw \<open>\DefineSnippet{doubleLoopStr_inheritance}{\<close>
theorem doubleLoopStr_inheritance:
  assumes "X be doubleLoopStr"
  shows "X be multLoopStr_0" "X be addLoopStr"
text_raw \<open>}%EndSnippet\<close>
using assms doubleLoopStr addLoopStr multLoopStr_0 by simp_all



lemma doubleLoopStr_ag[rule_format]: "X be set \<Longrightarrow> A be BinOp-of X \<Longrightarrow> M be BinOp-of X\<Longrightarrow> E be Element-of X \<Longrightarrow> Z be Element-of X \<Longrightarrow>
   ({[carrier,X]}\<union>{[addF,A]}\<union>{[multF,M]}\<union>{[OneF,E]}\<union>{[ZeroF,Z]}) be doubleLoopStr &
   ({[carrier,X]}\<union>{[addF,A]}\<union>{[multF,M]}\<union>{[OneF,E]}\<union>{[ZeroF,Z]}) be Function"
proof-
  assume A1: "X be set" "A be BinOp-of X" "M be BinOp-of X" "E be Element-of X" "Z be Element-of X"
  let ?A= "({[carrier,X]}\<union>{[addF,A]}\<union>{[multF,M]}\<union>{[OneF,E]}\<union>{[ZeroF,Z]})"
  have T1: "?A be Function" using Function_5[of carrier addF multF OneF ZeroF] by (simp add:string)
  have "the carrier of ?A=X" using the_selector_of_1[OF T1, of carrier X] tarski_def_1 by auto
  thus ?thesis using T1 doubleLoopStr Field_1[OF T1,of multF M]  Field_1[OF T1,of addF A]
      Field_1[of ?A carrier X ] Field_1[of ?A OneF E ] Field_1[of ?A ZeroF Z] A1 string by auto
qed

theorem algstr_0_cl_68:
  "let D be non empty\<parallel>set & o be BinOp-of D & o1 be BinOp-of D & d be Element-of D & e be Element-of D
   cluster {[carrier,D]}\<union>{[addF,o]}\<union>{[multF,o1]}\<union>{[OneF,d]}\<union>{[ZeroF,e]} \<rightarrow> non empty-struct"
proof-
  assume T0:"D be non empty\<parallel>set & o be BinOp-of D & o1 be BinOp-of D & d be Element-of D & e be Element-of D"
  let ?X = "{[carrier,D]}\<union>{[addF,o]}\<union>{[multF,o1]}\<union>{[OneF,d]}\<union>{[ZeroF,e]}"
  have T1: "?X be doubleLoopStr" "?X be Function" using doubleLoopStr_ag[of D o o1 d e] T0 by auto
  have "the carrier of ?X = D" using the_selector_of_1[of ?X carrier D] T1(2) string by auto
  thus "?X is non empty-struct" using  struct_0_def_1_b doubleLoopStr one_sorted T1 T0 by auto
qed

theorem algstr_0_cl_69:
  "let T be trivial\<parallel>set & f be BinOp-of T & f1 be BinOp-of T & s be Element-of T & t be Element-of T
   cluster {[carrier,T]}\<union>{[addF,f]}\<union>{[multF,f1]}\<union>{[OneF,s]}\<union>{[ZeroF,t]} \<rightarrow> trivial-struct"
proof-
  assume T0:"T be trivial\<parallel>set & f be BinOp-of T & f1 be BinOp-of T & s be Element-of T & t be Element-of T"
  let ?X = "{[carrier,T]}\<union>{[addF,f]}\<union>{[multF,f1]}\<union>{[OneF,s]}\<union>{[ZeroF,t]}"
  have T1: "?X be doubleLoopStr" "?X be Function" using doubleLoopStr_ag T0 by auto
  hence T2: "the carrier of ?X = T" "?X be one-sorted" using the_selector_of_1[of ?X carrier T]
    doubleLoopStr one_sorted string by auto
  show "?X is  trivial-struct" using  struct_0_def_9_a[of ?X,THEN iffD2,rule_format, OF T2(2)] T0 T2(1) by auto
qed

theorem algstr_0_cl_70:
  "let N be non trivial\<parallel>set & b be BinOp-of N & b1 be BinOp-of N & n be Element-of N & m be Element-of N
   cluster {[carrier,N]}\<union>{[addF,b]}\<union>{[multF,b1]}\<union>{[OneF,n]}\<union>{[ZeroF,m]} \<rightarrow> non trivial-struct"
proof-
  assume T0:"N be non trivial\<parallel>set & b be BinOp-of N & b1 be BinOp-of N & n be Element-of N & m be Element-of N"
  let ?X = "{[carrier,N]}\<union>{[addF,b]}\<union>{[multF,b1]}\<union>{[OneF,n]}\<union>{[ZeroF,m]}"
  have T1: "?X be doubleLoopStr" "?X be Function" using doubleLoopStr_ag T0 by auto
  hence T2: "the carrier of ?X = N" "?X be one-sorted" using the_selector_of_1[of ?X carrier N]  doubleLoopStr one_sorted string by auto
  show "?X is  non trivial-struct" using  struct_0_def_9_b[of ?X,THEN iffD2,rule_format, OF T2(2)] T0 T2(1) by auto
qed

definition algstr_0_def_42 ("Trivial-doubleLoopStr") where
  "func Trivial-doubleLoopStr \<rightarrow> doubleLoopStr equals
     {[carrier,{{}}]}\<union>{[addF,op2]}\<union>{[multF,op2]}\<union>{[OneF,op0]}\<union>{[ZeroF,op0]}"

schematic_goal algstr_0_def_42:
  shows "?X"
proof (rule equals_property [OF algstr_0_def_42_def])
  show "({[carrier,{{}}]}\<union>{[addF,op2]}\<union>{[multF,op2]}\<union>{[OneF,op0]}\<union>{[ZeroF,op0]}) be doubleLoopStr"
     using doubleLoopStr_ag funct_5_def_9 funct_5_def_7 all_set by auto
qed
lemmas [simp] = algstr_0_def_42[THEN conjunct2]

lemma algstr_0_def_42_t:"Trivial-doubleLoopStr is trivial-struct"
proof-
  have A1: "{{}} is trivial" using zfmisc_1_def_10a all_set tarski_def_1b by auto
  have "op2 be  BinOp-of {{}}" "op0 be Element-of {{}}" using funct_5_def_9 funct_5_def_7 funct_5_def_4 by simp+
  thus ?thesis using  algstr_0_cl_69[of "{{}}" op2 op2 op0] all_set A1 by auto
qed

theorem algstr_0_cl_71:
  "cluster Trivial-doubleLoopStr \<rightarrow> 1-element-struct\<bar> strict doubleLoopStr"
proof(rule attr_attr[THEN iffD2],rule conjI)
  let ?T ="Trivial-doubleLoopStr"
  have T0: "?T be doubleLoopStr" "?T be one-sorted" "?T be Function" using algstr_0_def_42 doubleLoopStr one_sorted by auto
  hence T1: "the carrier of ?T={{}}"
    using the_selector_of_1[OF T0(3),of carrier "{{}}"] string by auto
  thus T2: "Trivial-doubleLoopStr is 1-element-struct" using T0 struct_0_def_19_a by auto
  have  "domain_of doubleLoopStr = dom ?T"  using doubleLoopStr Dom_5 by auto
  thus "Trivial-doubleLoopStr is strict doubleLoopStr" using T2 strict T0 by auto
qed

theorem algstr_0_cl_72:
  "cluster strict doubleLoopStr\<bar>1-element-struct for doubleLoopStr"
proof
  show "Trivial-doubleLoopStr is strict doubleLoopStr\<bar>1-element-struct" using algstr_0_cl_71 by auto
  show "Trivial-doubleLoopStr be doubleLoopStr" using algstr_0_def_42 by auto
qed

definition algstr_0_def_43 ("_ '/\<^sub>_ _" [66,1000, 67] 66) where
  "func x /\<^sub>M y \<rightarrow> Element-of-struct M equals
     x  \<otimes>\<^sub>M /\<^sub>M y"

schematic_goal algstr_0_def_43:
   assumes " M be multLoopStr & x be Element-of-struct M & y be Element-of-struct M" shows "?X"
proof (rule equals_property [OF algstr_0_def_43_def,of x M y])
    have T0:"M be multMagma" using assms multMagma multLoopStr by auto
    have "/\<^sub>M y  be Element-of-struct M"  using assms algstr_0_def_30 by simp
    thus "(x  \<otimes>\<^sub>M /\<^sub>M y) be Element-of-struct M" using  algstr_0_def_18[of M x "/\<^sub>M y"] T0 assms by auto
qed

end