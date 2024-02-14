\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory struct_0
  imports "../mizar/mizar_struct" 
          "../mizar/mizar_string"
          "../mizar/mizar_fraenkel_2"
  binop_1
begin

abbreviation "one_sorted_fields \<equiv> (# carrier \<rightarrow> set' #)"

mdefinition one_sorted :: "Ty"  ("1-sorted") where
  "struct 1-sorted (# carrier \<rightarrow>  set' #)"
  :well_defined_property[of _ _ "{carrier}"]
  by (auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

lemmas one_sortedA = one_sorted(1)
lemmas [ex] = one_sorted(2,3)
lemmas one_sortedD = one_sorted(4)

lemmas [ty_func] = one_sorted(5)[rule_format]
lemma [ty_func]:"S be 1-sorted \<Longrightarrow> the carrier of S be set" using field one_sortedA by auto
lemma [ty_parent]:"S be 1-sorted \<Longrightarrow> S be Struct" using one_sortedA by auto

attr struct_0_def_1 ("empty-struct")
   "attr empty-struct for 1-sorted means (\<lambda> IT. (the carrier of IT) is empty)"

theorem struct_0_cl_1[ex]:
  "cluster empty-struct\<bar> strict (1-sorted) for 1-sorted"
  unfolding inhabited_def
proof(rule exI,simp,intro conjI)
    let ?X = "[#carrier \<mapsto>{} #]"
    have F1: "?X be Struct" using Struct_1 by simp
    thus F2: "?X be 1-sorted" using Field_1[of _ carrier "{}"] one_sortedA Aggr by mauto
    have "the carrier of ?X ={}" using the_selector_of_1[OF F1,of carrier op0] Aggr by auto
    hence "?X is empty-struct" using struct_0_def_1 F2 by mty simp
    thus "?X is empty-struct" " ?X is strict (1-sorted)"
       using Dom_1 strict[THEN conjunct2] one_sortedD F2 by auto
qed

theorem struct_0_cl_2[ex]:
  "cluster non empty-struct \<bar> strict(1-sorted) for 1-sorted"
  unfolding inhabited_def
proof(rule exI,simp,intro conjI)
   let ?X = "[# carrier \<mapsto> {{}}#]"
    have F1: "?X be Struct" using Struct_1 by simp
    thus F2: "?X be 1-sorted" using Field_1[of _ carrier "{{}}"] one_sortedA Aggr by mauto
    have "the carrier of ?X ={{}}" using the_selector_of_1[OF F1,of carrier "{op0}"] Aggr by auto
    hence "?X is non empty-struct" using F2 tarski_def_1 struct_0_def_1 xboole_0_def_1 by mauto
    thus "\<not>?X is empty-struct" "?X is strict(1-sorted)" using Dom_1 strict[THEN conjunct2] one_sortedD F2 by auto
qed

theorem struct_0_cl_3[ty_func_cluster]:
  "let S be (empty-struct \<bar> 1-sorted)
   cluster (the carrier of S) \<rightarrow> empty" using struct_0_def_1[of S] by simp

theorem struct_0_cl_4[ty_func_cluster]:
  "let S be (non empty-struct \<bar> 1-sorted)
   cluster (the carrier of S) \<rightarrow> non empty" using struct_0_def_1[of S] by auto


abbreviation struct_of_mode_1_prefix ("Element-of-struct _" [150] 150)
  where "Element-of-struct X \<equiv> Element-of (the carrier of X)"
abbreviation struct_of_mode_2_prefix ("Subset-of-struct _" [150] 150)
  where "Subset-of-struct X \<equiv> Subset-of (the carrier of X)"
abbreviation struct_of_mode_3_prefix ("Subset-Family-of-struct _" [150] 150)
  where "Subset-Family-of-struct X \<equiv> Subset-Family-of (the carrier of X)"


abbreviation struct_of_mode_4_prefix ("Function-of-1struct _ , _ " [150] 150)
  where "Function-of-1struct X,Y \<equiv> Function-of (the carrier of X), Y"
abbreviation struct_of_mode_5_prefix ("Function-of-2struct _ , _ " [150] 150)
  where "Function-of-2struct X,Y \<equiv> Function-of X, (the carrier of Y)"

abbreviation struct_of_mode_6_prefix ("Function-of-struct _ , _ " [150] 150)
  where "Function-of-struct X,Y \<equiv> Function-of (the carrier of X), (the carrier of Y)"

text_raw {*\DefineSnippet{struct0def2prefix}{*}
func struct_0_def_2 ( "{}s _ " 90) where
  mlet "T be 1-sorted"
  "func ({}s T) \<rightarrow> Subset-of-struct T equals {}"
text_raw {*}%EndSnippet*}
proof-
  show "op0 be (Subset-of-struct T)" using Subset_of_rule xb tarski_def_3
     one_sortedA field by auto
qed

text_raw {*\DefineSnippet{struct0def3}{*}
func struct_0_def_3 ( "[#] _ " 90) where
  mlet "T be 1-sorted"
  "func ([#] T) \<rightarrow> Subset-of-struct T equals
    the carrier of T"
text_raw {*}%EndSnippet*}
proof-
  show "(the carrier of T) be (Subset-of-struct T)" using Subset_of_rule xb tarski_def_3
     one_sortedA[of T] field by auto
qed


theorem struct_0_cl_5[ty_func_cluster]:
  "let T be 1-sorted
   cluster {}s T \<rightarrow> empty" using struct_0_def_2 xboole_0_def_2d by auto

theorem struct_0_cl_6[ty_func_cluster]:
  "let T be empty-struct \<bar>1-sorted
   cluster [#]T \<rightarrow> empty" using struct_0_def_3 struct_0_def_1 by auto

theorem struct_0_cl_7[ty_func_cluster]:
  "let T be non empty-struct \<bar>1-sorted
   cluster [#]T \<rightarrow> non empty" using struct_0_def_3 struct_0_def_1 by auto

theorem struct_0_cl_8[ex]:
  "let S be non empty-struct \<bar>1-sorted
   cluster non empty for (Subset-of-struct S)"
  unfolding inhabited_def
proof
  fix S assume[ty]: "S be (non empty-struct) \<bar>1-sorted"
  show "([#]S) be (non empty) \<bar> (Subset-of-struct S)" using struct_0_cl_7 by mauto
qed


func struct_0_def_4( "id-struct _" [90] 90) where
  mlet "S be 1-sorted"
  "func id-struct S \<rightarrow> Function-of-struct S,S equals
     id the carrier of S"
proof-
  show "id (the carrier of S) be Function-of-struct S,S" by mauto
qed

abbreviation struct_of_mode_8_prefix ("PartFunc-of-1struct _ , _ " 150)
  where "PartFunc-of-1struct X,Y \<equiv> PartFunc-of (the carrier of X), Y"
abbreviation struct_of_mode_9_prefix ("PartFunc-of-2struct _ , _ " 150)
  where "PartFunc-of-2struct X,Y \<equiv> PartFunc-of X,(the carrier of Y)"
abbreviation struct_of_mode_10_prefix ("PartFunc-of-struct _ , _ " 150)
  where "PartFunc-of-struct X,Y \<equiv> PartFunc-of (the carrier of X), (the carrier of Y)"

abbreviation(input) in_struct_prefix ("_ in'_struct _" 10) where
  "x in_struct y \<equiv> x in (the carrier of y)"

abbreviation "ZeroStr_fields \<equiv> (# carrier \<rightarrow> set' ; ZeroF \<rightarrow> Element-of' the' carrier#)"

mdefinition ZeroStr_d ("ZeroStr") where
  "struct ZeroStr (#
      carrier \<rightarrow> set' ;
      ZeroF \<rightarrow> Element-of' the' carrier#)"
  :well_defined_property[of _ _ "{carrier}\<union>{ZeroF}"]
  by (auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

lemmas ZeroStrA = ZeroStr_d(1)
lemmas [ex] = ZeroStr_d(2,3)
lemmas ZeroStrD = ZeroStr_d(4)
lemmas [ty_func] = ZeroStr_d(5)

theorem ZeroStr_inheritance[ty_parent]:
  "X be ZeroStr \<Longrightarrow> X be 1-sorted" using ZeroStrA one_sortedA by simp

theorem [ty_func]:
  "X be ZeroStr \<Longrightarrow> (the ZeroF of X) be Element-of-struct X" using field ZeroStrA by auto




theorem struct_0_cl_9[ex]:
  "cluster strict (ZeroStr) \<bar> non empty-struct for ZeroStr"
  unfolding inhabited_def
proof(intro exI,simp,intro conjI)
    let ?x = "the set"
     let ?X ="[#carrier \<mapsto> {?x} ; ZeroF\<mapsto> ?x#]"
        have R: "carrier \<noteq> ZeroF" by (simp add:string)
        hence S1[ty]: "?X be Struct" using Struct_2[of carrier ZeroF] by auto
        have S2: "?X is (carrier \<rightarrow>set')" using Field_1[of ?X carrier "{?x}" set'] Aggr by mauto
        have C1: "the carrier of ?X = {?x}" using the_selector_of_1[of _ "carrier" "{the set}"] Aggr by mauto
        have S3:"?x be Element-of {?x}" using Element_of_rule3 tarski_def_1 tarski_def_1_ty by auto
        have BB1: "the ZeroF of ?X = ?x" using the_selector_of_1[of _ "ZeroF" "the set"] Aggr by mauto
        hence "?X is (ZeroF \<rightarrow> Element-of' the' carrier)" using Field_1[of ?X,OF S1,of ZeroF ?x] C1 Aggr S3 by auto
        thus S3:"?X be ZeroStr" using ZeroStrA S2 by simp
        have "dom ?X = {carrier}\<union>{ZeroF}" using R Dom_2 by auto
        thus "?X is strict (ZeroStr)" using ZeroStrD strict[THEN conjunct2] S3 by auto
        have "the carrier of ?X is non empty" using C1 tarski_def_1 xboole_0_def_1 by mauto
        thus "\<not> ?X is empty-struct" using C1 struct_0_def_1 ZeroStr_inheritance S3 by auto
      qed


abbreviation "OneStr_fields \<equiv> (# carrier \<rightarrow> set' ; OneF \<rightarrow> Element-of' the' carrier#)"

mdefinition OneStr_d ("OneStr") where
  "struct OneStr (#
      carrier \<rightarrow> set' ;
      OneF \<rightarrow> Element-of' the' carrier#)"
  :well_defined_property[of _ _ "{carrier}\<union>{OneF}"]
  by (auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)


(*struct_well_defined
proof(rule Fields_add_argM1[OF one_sorted(5)])
    fix X1 assume "X1 be one_sorted_fields\<bar>Struct"
    hence [ty]: "X1 be 1-sorted" using one_sortedA by auto
    thus "inhabited(Element-of-struct X1)" by auto
  qed (simp_all add:string)
*)


lemmas OneStrA = OneStr_d(1)
lemmas [ex] = OneStr_d(2,3)
lemmas OneStrD = OneStr_d(4)
lemmas [ty_func] = OneStr_d(5)

theorem OneStr_inheritance[ty_parent]:
  "X be OneStr \<Longrightarrow> X be 1-sorted" using OneStrA one_sortedA by auto

theorem [ty_func]:
  "X be OneStr \<Longrightarrow> (the OneF of X) be Element-of-struct X" using field OneStrA by auto

abbreviation "ZeroOneStr_fields \<equiv>(# carrier \<rightarrow> set' ; ZeroF \<rightarrow> Element-of' the' carrier; OneF \<rightarrow> Element-of' the' carrier#)"

mdefinition ZeroOneStr_d ("ZeroOneStr") where
  "struct ZeroOneStr (# carrier \<rightarrow> set' ; ZeroF \<rightarrow> Element-of' the' carrier; OneF \<rightarrow> Element-of' the' carrier#)"
  :well_defined_property[of _ _ "{carrier}\<union>{ZeroF}\<union>{OneF}"]
  by (auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)



(*:struct_well_defined
proof(rule Fields_add_argM1[OF ZeroStr_d(5)])
  fix X1 assume "X1 be ZeroStr_fields\<bar>Struct"
    hence [ty]:"X1 be ZeroStr" using ZeroStrA by auto
    thus "inhabited(Element-of the carrier of X1)" by auto
qed (simp_all add:string) *)

lemmas ZeroOneStrA = ZeroOneStr_d(1)
lemmas [ex] = ZeroOneStr_d(2,3)
lemmas ZeroOneStrD = ZeroOneStr_d(4)
lemmas [ty_func] = ZeroOneStr_d(5)

theorem ZeroOneStr_inheritance[ty_parent]:
  "X be ZeroOneStr \<Longrightarrow> X be ZeroStr \<and> X be OneStr" using ZeroOneStrA ZeroStrA OneStrA by simp

text_raw {*\DefineSnippet{struct0def6}{*}
func struct_0_def_6 ( "0\<^sub>_" [1000] 99) where
mlet "S be ZeroStr"
  "func 0\<^sub>S \<rightarrow> Element-of-struct S equals
     the ZeroF of S"
text_raw {*}%EndSnippet*}
proof-
  show "(the ZeroF of S) be Element-of (the carrier of S)"
       by simp
qed


text_raw {*\DefineSnippet{struct0def7}{*}
func struct_0_def_7 ("1\<^sub>_" [1000] 99) where
  mlet "S be OneStr"
  "func 1\<^sub>S \<rightarrow> Element-of-struct S equals
     the OneF of S"
text_raw {*}%EndSnippet*}
proof-
  show "(the OneF of S) be Element-of (the carrier of S)" by auto
qed



attr struct_0_def_8 ("degenerated")
   "attr degenerated for ZeroOneStr means (\<lambda> S. 0\<^sub>S = 1\<^sub>S)"

lemma struct_0_def_8c: "X is ZeroOneStr \<Longrightarrow> 0\<^sub>X \<noteq> 1\<^sub>X \<Longrightarrow> \<not> X is degenerated" using struct_0_def_8 by auto

attr struct_0_def_9 ("trivial-struct")
   "attr trivial-struct for 1-sorted means (\<lambda> S. the carrier of S is trivial)"

theorem struct_0_def_10:
  "let S be 1-sorted
   redefine attr S is trivial-struct means
        for x, y be Element-of-struct S holds x=y"
proof(rule iffI3)
  assume A1[ty]:"S be 1-sorted"
  show "S is trivial-struct \<longrightarrow> (for x, y be Element-of-struct S holds x=y)"
  proof(intro impI ballI)
    fix x y assume A2[ty]: "S is trivial-struct" "x be Element-of-struct S" "y be Element-of-struct S"
    have A3: "the carrier of S is trivial" using struct_0_def_9E A2 by auto
    show "x=y"
    proof (cases "the carrier of S={}")
      case True
        hence "x={}" "y={}" using A2(2,3) Element(5)  by auto
        thus ?thesis by simp
    next
      case False
        hence "x in_struct S" "y in_struct S" using Element_of_rule2 by auto
        thus ?thesis using zfmisc_1_def_10 A3 by auto
      qed
  qed simp_all
  assume A4: "for x, y be Element-of-struct S holds x=y"
  show "S is trivial-struct"
  proof(intro struct_0_def_9I)
    show "(the carrier of S) is trivial"
      proof
        fix x y assume "x in_struct S" "y in_struct S"
        hence "x be Element-of-struct S" "y be Element-of-struct S" using Element_of_rule3 by mauto
        thus "x=y" using A4 by auto
     qed mauto
  qed mauto
qed

lemmas struct_0_def_10a = struct_0_def_10[THEN iffD1,THEN bspec,THEN bspec]

attr struct_0_def_12 ("zero \<^sub>_" [190] 190)
   "S be ZeroStr \<Longrightarrow> attr zero \<^sub>S for Element-of-struct S means (\<lambda> IT.  IT = 0\<^sub>S )"

theorem struct_0_cl_10[ty_func_cluster]:
  "let S be ZeroStr
   cluster 0\<^sub>S \<rightarrow> zero \<^sub>S"
proof-
  assume [ty]:"S be ZeroStr"
  show "0\<^sub>S be zero \<^sub>S" using struct_0_def_12I[of S "0\<^sub>S"] by mauto
qed

theorem struct_0_cl_11[ex]:
  "cluster strict (ZeroOneStr) \<bar> non degenerated for ZeroOneStr"
  unfolding inhabited_def
proof(intro exI)
  let ?c = "carrier \<rightarrow> set'"
  let ?z = "ZeroF \<rightarrow> Element-of' the' carrier"
  let ?o = "OneF \<rightarrow> Element-of' the' carrier"
  let ?x = "the set"
  let ?X ="[#carrier \<mapsto> ({?x}\<union>{{?x}}) ; ZeroF \<mapsto> ?x ;OneF\<mapsto> {?x} #]"
        have "carrier \<noteq> ZeroF" "carrier \<noteq>OneF" "ZeroF\<noteq>OneF" by (simp add:string)+
        hence A1[ty]: "?X be Struct" using Struct_3[of carrier ZeroF OneF "{?x}\<union>{{?x}}" ?x] by auto
        have T1:"({?x}\<union>{{?x}}) be set" using all_set by auto
        have F1: "?X is (#?c#)" using Field_1[OF A1,of _ "{?x}\<union>{{?x}}"] T1 Aggr by auto
        have t: "the carrier of ?X ={?x}\<union>{{?x}} " using A1 the_selector_of_1[of _ carrier "{?x}\<union>{{?x}}"] Aggr
            by auto
        hence T2: "?x be Element-of the carrier of ?X"
          using Element(6) T1 choice_ax string by auto
        have T3: "{?x} be Element-of the carrier of ?X"
          using Element(6) T1 choice_ax t string by auto
        have F2: "?X is (#?z#)"
          using Field_1[OF A1,of ZeroF ?x] T2 Aggr by auto
        have F3: "?X is (#?o#)"
          using Field_1[OF A1,of _ "{?x}"] T3 Aggr by auto
        then have "?X is (#?c;?z;?o #)" using F1 F2 by simp
        hence S3:"?X be ZeroOneStr" using ZeroOneStrA A1 by simp
        have "dom (?X)={carrier}\<union>{ZeroF}\<union>{OneF}" using Dom_3 by simp
        hence W1: "?X is strict(ZeroOneStr)" using S3 ZeroOneStrD strict[THEN conjunct2] by auto
        have "the ZeroF of ?X = ?x " "the OneF of ?X = {?x} "
          using the_selector_of_1[OF A1,of ZeroF ?x] the_selector_of_1[OF A1,of OneF "{?x}"] Aggr by auto
        hence "0\<^sub>?X = ?x" "1\<^sub>?X={?x}" using struct_0_def_7 struct_0_def_6 ZeroOneStr_inheritance S3 by auto
        hence "0\<^sub>?X in 1\<^sub>?X" using tarski_def_1 by auto
        hence "0\<^sub>?X \<noteq> 1\<^sub>?X" using prefix_in_irreflexive all_set by auto
        hence "?X is non degenerated" using struct_0_def_8 S3 by auto
        thus "?X is strict (ZeroOneStr)\<bar> non degenerated\<bar>ZeroOneStr" using W1 S3 by auto
      qed


text_raw {*\DefineSnippet{struct_0_cl_12}{*}
theorem struct_0_cl_12[ty_func_cluster]:
  "let S be non degenerated \<bar> ZeroOneStr
   cluster 1\<^sub>S \<rightarrow> non zero \<^sub>S"
text_raw {*}%EndSnippet*}
proof-
  assume A1[ty]: "S be non degenerated \<bar> ZeroOneStr"
  hence "1\<^sub>S \<noteq> 0\<^sub>S" "S be ZeroStr" using struct_0_def_8[of S] by auto
  thus "1\<^sub>S is non zero \<^sub>S" using struct_0_def_12 by mauto
qed

abbreviation struct_of_mode_11_prefix ("BinOp-of-struct _ " 60)
  where "BinOp-of-struct X \<equiv> BinOp-of (the carrier of X)"


abbreviation struct_of_mode_12_prefix ("UnOp-of-struct _ " 60)
  where "UnOp-of-struct X \<equiv> BinOp-of (the carrier of X)"

(* :: "(Set\<Rightarrow>Set)\<Rightarrow>Set\<Rightarrow>Mode"*)
text_raw {*\DefineSnippet{BinOfP}{*}
abbreviation(input) BinOp_of ("BinOp-of'' _") where
  "BinOp-of' X \<equiv> \<lambda>it. BinOp-of X(it)"
text_raw {*}%EndSnippet*}

abbreviation(input) Subset_Falmily_of :: "(Set \<Rightarrow> Set) \<Rightarrow> (Set \<Rightarrow> Ty)" ("Subset-Family-of'' _") where
  "Subset-Family-of' X \<equiv> \<lambda>it. Subset-Family-of X(it)"

abbreviation(input) Function_of :: "(Set \<Rightarrow> Set) \<Rightarrow> (Set \<Rightarrow> Set) \<Rightarrow> (Set \<Rightarrow> Ty)" ("Function-of'' _ , _") where
  "Function-of' X, Y\<equiv> \<lambda>it. Function-of X(it), Y(it)"

abbreviation(input) cartesian_product1 :: "Set \<Rightarrow> (Set \<Rightarrow> Set) \<Rightarrow> (Set \<Rightarrow> Set)" ("[: _ , _ '':]") where
  "[: X, Y ':] \<equiv> \<lambda>it. [: X, Y(it):]"

abbreviation(input) cartesian_product2 :: "(Set \<Rightarrow> Set) \<Rightarrow> Set \<Rightarrow> (Set \<Rightarrow> Set)" ("[:'' _ , _ :]") where
  "[:' X, Y :] \<equiv> \<lambda>it. [: X(it), Y:]"

attr struct_0_def_19_a ("1-element-struct")
  "attr 1-element-struct for 1-sorted means (\<lambda> IT. ex x be object st {x} = the carrier of IT)"

theorem struct_0_redef_1[ty_func]:
  "let S be non empty-struct\<bar>1-sorted \<and>
       x be Element-of-struct S
   redefine func {x} \<rightarrow> Subset-of-struct S"
proof (intro impI)
  assume [ty]:"S is non empty-struct \<bar> 1-sorted \<and> x is Element-of-struct S"
  have [ty]:"S is 1-sorted" by auto
  have "the carrier of S is non empty" using struct_0_def_1 by auto
  hence "x in the carrier of S" using Element(7) by auto
  hence "{x} c= the carrier of S" using tarski_def_3 tarski_def_1 by mauto
  thus "{x} be Subset-of-struct S" using Subset_of_rule by auto
qed


text_raw {*\DefineSnippet{struct_0_redef_2}{*}
theorem struct_0_redef_2[ty_func]:
  "let S be non empty-struct\<bar>1-sorted \<and>
       x be Element-of-struct S \<and> y be Element-of-struct S
   redefine func {x,y} \<rightarrow> Subset-of-struct S"
text_raw {*}%EndSnippet*}
proof (intro impI)
  assume [ty]:"S is non empty-struct \<bar> 1-sorted \<and> x is Element-of-struct S \<and> y is Element-of-struct S"
  have "the carrier of S is non empty" using struct_0_def_1 by auto
  hence "x in the carrier of S" " y in the carrier of S" using Element(7)[of "the carrier of S"]  by auto
  hence "{x,y} c= the carrier of S" using tarski_def_2 by (intro tarski_def_3b) mauto
  thus "{x,y} be Subset-of-struct S" using Subset_of_rule by auto
qed

lemma struct_0_def_1c:"X be 1-sorted \<Longrightarrow>  (the carrier of X) is non empty \<Longrightarrow> X be non empty-struct" using struct_0_def_1 by auto

theorem struct_0_cl_triv[ty_cond_cluster]:
  "cluster non trivial-struct \<rightarrow> non empty-struct for 1-sorted"
proof(intro struct_0_def_1c,simp)
  fix X assume [ty]:"X is 1-sorted" "X is non trivial-struct"
  have "the carrier of X is non trivial" using struct_0_def_9 by mauto
  then obtain x y where
       "x be object" "y be object"
       "x in the carrier of X \<and> x in the carrier of X \<and> x\<noteq>y" using zfmisc_1_def_10 by mauto
  thus "the carrier of X is non empty" using xboole_0_def_1E by mauto
qed

func struct_0_def_17 ("NonZero \<^sub>_" [1000] 99) where
  assumes "S be ZeroStr"
  "func NonZero \<^sub>S \<rightarrow> Subset-of-struct S equals ([#]S) \\ {0\<^sub>S}"
proof-
  have A1:"([#]S) be Subset-of-struct S" using struct_0_def_3[of S] Subset_of_rule xboole_0_def_10 by mauto
  have "(([#]S) \\ {0\<^sub>S}) be Subset-of ([#]S)" using Subset_of_rule xboole_0_def_5[of "[#]S" "{0\<^sub>S}"]
         tarski_def_3[of "([#]S) \\ {0\<^sub>S}" "[#]S"] by mauto
  thus "(([#]S) \\ {0\<^sub>S}) be Subset-of-struct S" using A1 Subset_trans[OF _ A1] by auto
qed


mdefinition two_sorted_d ("2-sorted") where
  "struct 2-sorted (#
      carrier \<rightarrow> set' ;
      carrier` \<rightarrow> set'#)"
  :well_defined_property[of _ _ "{carrier}\<union>{carrier`}"]
  by (auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

lemmas two_sortedA = two_sorted_d(1)
lemmas [ex] = two_sorted_d(2,3)
lemmas two_sortedD = two_sorted_d(4)
lemmas [ty_func] = two_sorted_d(5)

theorem two_sorted_inheritance[ty_parent]:
  "X be 2-sorted \<Longrightarrow> X be 1-sorted" using two_sortedA one_sortedA by simp

theorem [ty_func]:
  "X be 2-sorted \<Longrightarrow> (the carrier` of X) be set" using field two_sortedA by auto

attr struct_0_def_13 ("void-struct")
   "attr void-struct for 2-sorted means (\<lambda> IT. (the carrier` of IT) is empty)"

theorem struct_0_cl_x[ty_func_cluster]:
  "let S be (non void-struct \<bar> 2-sorted)
   cluster (the carrier` of S) \<rightarrow> non empty" using struct_0_def_13[of S] by auto

text_raw {*\DefineSnippet{struct_contrE}{*}
mdefinition I_one_sorted :: "Ty"  ("Inhabited'_1-sorted") where
  "struct Inhabited_1-sorted (# carrier \<rightarrow>  (\<lambda>S. non empty\<bar>set) #)"
  :well_defined_property[of _ _ "{carrier}"]
text_raw {*}%EndSnippet*}
  by (auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

lemmas Ione_sortedA = I_one_sorted(1)
lemmas [ex] = one_sorted(2,3)
lemmas Ione_sortedD = I_one_sorted(4)

lemmas [ty_func] = I_one_sorted(5)[rule_format]
lemma [ty_func]:"S be Inhabited_1-sorted \<Longrightarrow> the carrier of S be non empty\<bar> set" using field Ione_sortedA by auto
lemma [ty_parent]:"S be Inhabited_1-sorted \<Longrightarrow> S be Struct" using Ione_sortedA by auto

text_raw {*\DefineSnippet{struct_contr1a}{*}
theorem
  "X be Inhabited_1-sorted \<Longrightarrow> X be 1-sorted"
  "X be non empty-struct\<bar>1-sorted \<Longrightarrow> X be Inhabited_1-sorted"
text_raw {*}%EndSnippet*}
proof-
  assume [ty]: "X be Inhabited_1-sorted"
  hence "X is (carrier \<rightarrow>  (\<lambda>S. non empty\<bar>set))" using Ione_sortedA[of X] by auto+
  hence "(the carrier of X) is non empty\<bar>set" "carrier in dom X" using field by simp+
  thus "X is 1-sorted" using one_sortedA field by auto
next
  assume [ty]:"X be non empty-struct\<bar>1-sorted"
  hence [ty]: "the carrier of X is non empty" by mauto
  have "X is (carrier \<rightarrow>  (\<lambda>S. set))" using one_sortedA[of X] by auto+
  hence "(the carrier of X) is set" "carrier in dom X" using field by simp+
  hence "X is (carrier \<rightarrow>  (\<lambda>S. non empty\<bar>set))" using field by auto
  thus "X is Inhabited_1-sorted" using Ione_sortedA field by auto
qed


text_raw {*\DefineSnippet{struct_contr1b}{*}
definition
  "struct Test (# testA \<rightarrow> (\<lambda>T. Element-of the testB of T);
                     testB \<rightarrow> (\<lambda>T. Element-of the testA of T) #)"
text_raw {*}%EndSnippet*}

schematic_goal Test:
   shows ?X
proof (induct rule: struct_scheme[OF Test_def,of "{testA}\<union>{testB}",case_names existence monotone restriction])
  let ?A = "testA \<rightarrow> (\<lambda>T . Element-of the testB of T)"
  let ?B = "testB \<rightarrow> (\<lambda>T . Element-of the testA of T)"
  let ?AB = "{testA}\<union>{testB}"
  case existence
  show "\<exists>\<^sub>L X . X be (#?A;?B #)\<bar>Struct \<and> dom X = ?AB"
  proof (intro exI)
    let ?ab = "[# testA\<mapsto>{};testB \<mapsto>{} #]"
     have [ty]:"?ab is Struct" using Struct_2[of testA testB "{}" "{}"] string by auto
     have A1: "[testA,{}] in ?ab" "[testB,{}] in ?ab" using Aggr by auto
     hence A2: "the testA of ?ab = {}" "the testB of ?ab = {}" using the_selector_of_1 by mauto
     have A4: "{} is Element-of {}" using Element_of_rule1 by simp
     have A3:"dom ?ab = ?AB" using Dom_2 by auto
     hence "testA in dom ?ab" "testB in dom ?ab" using string by auto
     hence "?ab be ?A" "?ab be ?B" using A4 field A2 by auto
     thus "?ab be (#?A;?B #)\<bar>Struct\<and>dom ?ab = ?AB" using A3 by auto
    qed
  case monotone
    show "\<forall>\<^sub>L X1. X1 be (#?A;?B#)\<bar>Struct \<longrightarrow> ?AB \<subseteq> dom X1"
      proof(standard,standard)
         fix X1
         assume [ty]:"X1 be (#?A;?B#)\<bar>Struct"
         hence A1: "testA in dom X1" "testB in dom X1" using field by auto
         have [ty]: "X1 be Function" using Struct_def by mauto
         show "?AB \<subseteq> dom X1"
         proof(intro tarski_def_3b)
           fix x assume "x in {testA} \<union> {testB}"
           hence "x=testA \<or> x=testB" using tarski_def_1 xboole_0_def_3 by mauto
           thus "x in dom X1" using A1 by mauto
         qed mauto
      qed
  case restriction
  show "\<forall>\<^sub>L X1. X1 be (#?A;?B#)\<bar>Struct \<longrightarrow> X1|?AB is (#?A;?B#)"
      proof(standard,standard)
        fix X1
        assume A1[ty]: "X1 be (#?A;?B#)\<bar>Struct"
        have G1: "testA in ?AB" "testB in ?AB" using tarski_def_1 xboole_0_def_3 all_set by auto
        have "testA in dom X1" "testB in dom X1" using A1 field[of X1 testA "\<lambda>T . Element-of the testB of T"]
                                        field[of X1 testB "\<lambda>T . Element-of the testA of T"] by auto
        hence "the' testA(X1) = the' testA(X1|?AB)"
              "the' testB(X1) = the' testB(X1|?AB)" using the_selector_of_restriction[of X1 _ ?AB] G1 by mauto
        thus "(X1 | ?AB) is (#?A;?B#)" using A1 G1 fields_restriction by simp
     qed
qed

lemmas [ex] = Test[THEN conjunct2,THEN conjunct1]


text_raw {*\DefineSnippet{struct_contr3}{*}
theorem "\<forall>T:Test. the testA of T = {} \<and> the testB of T = {}"
text_raw {*}%EndSnippet*}
proof(standard,standard)
  fix T
  assume A1:"T be Test"
  hence A2: "the testA of T is Element-of the testB of T"
            "the testB of T is Element-of the testA of T" using field Test by auto
  show "the testA of T ={}"
    proof (rule ccontr)
      assume A3: "the testA of T \<noteq> {}"
      hence A4: "the testB of T in the testA of T" using Element_of_rule2 A2 all_set by auto
      have "the testB of T \<noteq> {}" using Element_of_rule[of "the testA of T"] A2(1) A3 by auto
      hence "the testA of T in the testB of T" using Element_of_rule2 A2 all_set by auto
      thus "False" using prefix_in_asymmetry all_set A4 by mauto
    qed
  show "the testB of T ={}"
    proof (rule ccontr)
      assume A3: "the testB of T \<noteq> {}"
      hence A4: "the testA of T in the testB of T" using Element_of_rule2 A2 all_set by auto
      have "the testA of T \<noteq> {}" using Element_of_rule[of "the testB of T"] A2(2) A3 by auto
      hence "the testB of T in the testA of T" using Element_of_rule2 A2 all_set by auto
      thus "False" using prefix_in_asymmetry all_set A4 by auto
    qed
  qed mauto

attr struct_0_def_21 ("trivial`-struct")
   "attr trivial`-struct for 2-sorted means (\<lambda> S. the carrier` of S is trivial)"


theorem struct_0_def_21R:
  "let S be 2-sorted
   redefine attr S is trivial`-struct means
        for x, y be Element-of the carrier` of S holds x=y"
proof(rule iffI3)
  assume A1[ty]:"S be 2-sorted"
  show "S is trivial`-struct \<longrightarrow> (for x, y be Element-of the carrier` of S holds x=y)"
  proof(intro impI ballI)
    fix x y assume A2[ty]: "S is trivial`-struct" "x be Element-of the carrier` of S" "y be Element-of the carrier` of S"
    have A3: "the carrier` of S is trivial" using struct_0_def_21E A2 by auto
    show "x=y"
    proof (cases "the carrier` of S={}")
      case True
        hence "x={}" "y={}" using A2(2,3) Element(5)  by auto
        thus ?thesis by simp
    next
      case False
        hence "x in the carrier` of S" "y in the carrier` of S" using Element_of_rule2 by auto
        thus ?thesis using zfmisc_1_def_10 A3 by auto
      qed
  qed simp_all
  assume A4: "for x, y be Element-of the carrier` of S holds x=y"
  show "S is trivial`-struct"
  proof(intro struct_0_def_21I)
    show "(the carrier` of S) is trivial"
      proof
        fix x y assume "x in the carrier` of S" "y in the carrier` of S"
        hence "x be Element-of the carrier` of S" "y be Element-of the carrier` of S" using Element_of_rule3 by mauto
        thus "x=y" using A4 by auto
     qed mauto
  qed mauto
qed

end