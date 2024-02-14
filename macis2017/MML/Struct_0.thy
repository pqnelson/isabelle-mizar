\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Struct_0
  imports "../Mizar/Mizar_struct" "../Mizar/Mizar_string" "../Mizar/Mizar_Fraenkel_2" Binop_1
begin

text_raw \<open>\DefineSnippet{onesorted}{\<close>
definition one_sorted :: "Mode"  ("one-sorted") where
  "struct one-sorted (# carrier \<rightarrow> \<lambda>_. set #)"
text_raw \<open>}%EndSnippet\<close>

abbreviation "one_sorted_fields \<equiv> (# carrier \<rightarrow> set' #)"
  
lemma one_sorted_well:"one_sorted_fields well defined on {carrier}"
proof(rule First_0_arg_Mode)
  show "ex x being set st True" proof (rule bexI[of _ "the object"])
    show "(the object) be set" using all_set by simp
    show "True" by simp
  qed
qed  
  
schematic_goal one_sorted:
   shows ?X by (rule struct_well_defined[OF one_sorted_def one_sorted_well])

definition empty_struct ("empty-struct") where struct_0_def_1_a [THEN defattr_property,simp]:
   "attr empty-struct means (\<lambda> IT. (IT be one_sorted) & (the carrier of IT) is empty)"
definition non_empty_struct :: "Attr" ("non empty-struct") where struct_0_def_1_b [THEN defattr_property,simp]:
   "attr non empty-struct means (\<lambda> IT. (IT be one_sorted) & (the carrier of IT) is nonempty)"

theorem struct_0_cl_1:
  "cluster empty-struct\<bar> strict one_sorted for one_sorted"
proof
    let ?X = "{[carrier,{}]}"
    have F1: "?X be Function" using Function_1 by simp
    thus F2: "?X be one_sorted" using F1 Field_1 one_sorted tarski_def_1 by simp
    have "the carrier of ?X ={}" using the_selector_of_1 F1 tarski_def_1 by auto
    hence "?X is empty-struct" using struct_0_def_1_a F2 by simp
    thus "?X is  empty-struct\<bar> strict one_sorted" using Dom_1 strict one_sorted[THEN conjunct1,THEN conjunct2] F2 by auto     
qed

theorem struct_0_cl_2:
  "cluster non empty-struct \<bar> strict one_sorted for one_sorted"
proof
   let ?X = "{[carrier,{{}}]}"
    have F1: "?X be Function" using Function_1 by simp
    thus F2: "?X be one_sorted" using F1 Field_1 one_sorted tarski_def_1 by simp
    have "the carrier of ?X ={{}}" using the_selector_of_1 F1 tarski_def_1 by auto
    hence "?X is non empty-struct" using F2 tarski_def_1 by simp
    thus "?X is  non empty-struct\<bar> strict one_sorted" using Dom_1 strict one_sorted[THEN conjunct1,THEN conjunct2] F2 by auto      
qed

theorem struct_0_cl_3:
  "let S be (empty_struct \<parallel> one_sorted)
   cluster (the carrier of S) \<rightarrow> empty" using struct_0_def_1_a by simp

theorem struct_0_cl_4:
  "let S be (non_empty_struct \<parallel> one_sorted)
   cluster (the carrier of S) \<rightarrow> non empty" using struct_0_def_1_b by auto
  
   
abbreviation struct_of_mode_1_prefix  ("Element-of-struct _" 150)
  where "Element-of-struct X \<equiv> Element-of (the carrier of X)"
abbreviation  struct_of_mode_2_prefix  ("Subset-of-struct _" 150)
  where "Subset-of-struct X \<equiv> Subset-of (the carrier of X)"
abbreviation  struct_of_mode_3_prefix  ("Subset-Family-of-struct _" 150)
  where "Subset-Family-of-struct X \<equiv> Subset-Family-of (the carrier of X)"
    
    
abbreviation  struct_of_mode_4_prefix  ("Function-of-1struct _ , _ " 150)
  where "Function-of-1struct X,Y \<equiv> Function-of (the carrier of X), Y"
abbreviation  struct_of_mode_5_prefix  ("Function-of-2struct _ , _ " 150)
  where "Function-of-2struct X,Y \<equiv> Function-of X, (the carrier of Y)"

abbreviation  struct_of_mode_6_prefix  ("Function-of-struct _ , _ " 150)
  where "Function-of-struct X,Y \<equiv> Function-of (the carrier of X), (the carrier of Y)"

text_raw \<open>\DefineSnippet{struct0def2prefix}{\<close>
definition struct_0_def_2_prefix ( "{}s _ " 90) where
  "func ({}s T) \<rightarrow> Subset-of-struct T equals
    {}"
schematic_goal subset_0_def_2:
  assumes "T be one_sorted" shows "?X"
text_raw \<open>}%EndSnippet\<close>
    
proof (rule equals_property[OF struct_0_def_2_prefix_def,of T])
  show "{} be (Subset-of-struct T)" using assms zfmisc_1_def_1 subset_1_cl_1 subset_1_def_2 
     one_sorted[THEN conjunct1,THEN conjunct1,THEN conjunct1,of T] field by auto
qed

text_raw \<open>\DefineSnippet{struct0def3}{\<close>
definition struct_0_def_3_prefix ( "[#] _ " 90) where
  "func ([#] T) \<rightarrow> Subset-of-struct T equals
    the carrier of T"
schematic_goal struct_0_def_3:
  assumes "T be one_sorted" shows "?X"
text_raw \<open>}%EndSnippet\<close>
proof (rule equals_property[OF struct_0_def_3_prefix_def,of T])
  show "(the carrier of T) be (Subset-of-struct T)" using assms zfmisc_1_def_1 subset_1_cl_1 subset_1_def_2 
     one_sorted[THEN conjunct1,THEN conjunct1,THEN conjunct1,of T] field by auto
qed
  
theorem struct_0_cl_5:
  "let T be one_sorted
   cluster {}s T \<rightarrow> empty" using subset_0_def_2 xboole_0_def_2c by auto
  
theorem struct_0_cl_6:
  "let T be empty-struct \<parallel>one_sorted
   cluster [#]T \<rightarrow> empty" using struct_0_def_3 struct_0_def_1_a by auto
  
theorem struct_0_cl_7:
  "let T be non empty-struct \<parallel>one_sorted
   cluster [#]T \<rightarrow> non empty" using struct_0_def_3 struct_0_def_1_a by auto

theorem struct_0_cl_8:
  "let S be non empty-struct \<parallel>one_sorted
   cluster non empty for (Subset-of-struct S)" using  struct_0_cl_7[of S] struct_0_def_3[of S] by auto
  
abbreviation  struct_of_mode_7_prefix  ("ManySortedSet-of-struct _ " 150)
  where "ManySortedSet-of-struct X \<equiv> ManySortedSet-of (the carrier of X)"
  
definition struct_0_def_4( "id-struct _" [90] 90) where
  "func id-struct S \<rightarrow> Function-of-struct S,S equals
     id the carrier of S"

schematic_goal struct_0_def_4:
   assumes "S be one_sorted" shows "?X"
proof (rule equals_property[OF struct_0_def_4_def,of S])
  show "id (the carrier of S) be Function-of-struct S,S" using funct_2_cl_10 all_set by simp
qed

abbreviation  struct_of_mode_8_prefix  ("PartFunc-of-1struct _ , _ " 150)
  where "PartFunc-of-1struct X,Y \<equiv> PartFunc-of (the carrier of X), Y"
abbreviation  struct_of_mode_9_prefix  ("PartFunc-of-2struct _ , _ " 150)
  where "PartFunc-of-2struct X,Y \<equiv> PartFunc-of X,(the carrier of Y)"
abbreviation  struct_of_mode_10_prefix  ("PartFunc-of-struct _ , _ " 150)
  where "PartFunc-of-struct X,Y \<equiv> PartFunc-of (the carrier of X), (the carrier of Y)"

abbreviation in_struct_prefix ("_ in'_struct _" 10) where
  "x in_struct y \<equiv> x in (the carrier of y)"

abbreviation "ZeroStr_fields \<equiv> (# carrier \<rightarrow> set' ; ZeroF \<rightarrow> Element-of' the' carrier#)" 


text_raw \<open>\DefineSnippet{ZeroStr}{\<close>
definition ZeroStr ("ZeroStr") where
  "struct ZeroStr (# 
      carrier \<rightarrow> set' ; 
      ZeroF \<rightarrow> Element-of' the' carrier#)"
text_raw \<open>}%EndSnippet\<close>
  
  

lemma ZeroStr_well:"ZeroStr_fields well defined on {carrier} \<union>{ZeroF}" 
proof(rule Fields_add_argM1[OF one_sorted_well],simp add:string,simp add:string)
  show "for X1 be  one_sorted_fields \<parallel>Function holds ex it be Element-of-struct X1 st True" 
  proof(rule ballI)
    fix X1 assume "X1 be one_sorted_fields\<parallel>Function"
    hence "the carrier of X1 be set" using field by auto 
    thus "ex it be Element-of the carrier of X1 st True"  using subset_1_def_1[THEN conjunct2] by auto
  qed    
qed  
  
schematic_goal ZeroStr:
   shows ?X by (rule struct_well_defined[OF ZeroStr_def ZeroStr_well])
  
theorem ZeroStr_inheritance:
  "X be ZeroStr \<Longrightarrow> X be one_sorted" using ZeroStr one_sorted attr_mode attr_attr by blast

theorem struct_0_cl_9:
  "cluster strict ZeroStr \<bar> non empty-struct for ZeroStr"
proof - 
    obtain x where "x = the set" by simp
    obtain X where X_def:"X= {[carrier,{x}]}\<union>{[ZeroF,x]}" by simp
    show "ex S be ZeroStr st S is strict ZeroStr \<bar> non empty-struct"
      proof(rule bexI[of _ X])
        have R: "carrier <> ZeroF" by (simp add:string)
        hence S1: "X be Function" using Function_2[of carrier ZeroF] X_def by auto  
        have S2: "X is carrier \<rightarrow>set'" using Field_1[of X carrier "{x}" ] all_set S1 X_def tarski_def_1 by auto
        have C1: "the carrier of X = {x}" using the_selector_of_1[of X carrier "{x}",OF S1] X_def tarski_def_1 by auto
        have S3:"x be Element-of {x}" using Element_of_rule tarski_def_1 by auto     
        have BB1: "the ZeroF of X = x" using the_selector_of_1[of X ZeroF x,OF S1] X_def tarski_def_1 by auto
        hence "X is ZeroF \<rightarrow> Element-of' the' carrier" using Field_1[of X,OF S1,of ZeroF x] C1 S3 X_def tarski_def_1 by auto
        thus S3:"X be ZeroStr" using ZeroStr S1 S2 by simp 
        
        have "dom X = {carrier}\<union>{ZeroF}" using R Dom_2 X_def by auto
        hence "X is strict ZeroStr" using S3 ZeroStr strict by auto
        thus "X is strict ZeroStr \<bar> non empty-struct" using C1 struct_0_def_1_b S3 ZeroStr_inheritance tarski_def_1 by auto  
      qed
qed
      
abbreviation "OneStr_fields \<equiv> (# carrier \<rightarrow> set' ; OneF \<rightarrow> Element-of' the' carrier#)"
  
definition OneStr ("OneStr") where
  "struct OneStr OneStr_fields"

lemma OneStr_well:"OneStr_fields
                    well defined on {carrier} \<union>{OneF}" 
proof(rule Fields_add_argM1[OF one_sorted_well],simp add:string,simp add:string)
  show "for X1 be one_sorted_fields\<parallel>Function holds ex it be Element-of-struct X1 st True" 
  proof(rule ballI)
    fix X1 assume "X1 be one_sorted_fields\<parallel>Function"
    hence "the carrier of X1 be set" using field tarski_def_1 by auto 
    thus "ex it be Element-of the carrier of X1 st True"  using subset_1_def_1[THEN conjunct2] by auto
  qed    
qed  
  
schematic_goal OneStr:
   shows ?X by (rule struct_well_defined[OF OneStr_def OneStr_well])
        
theorem OneStr_inheritance:
  "X be OneStr \<Longrightarrow> X be one-sorted" using OneStr one_sorted by simp

abbreviation  "ZeroOneStr_fields \<equiv>(# carrier \<rightarrow> set' ; ZeroF \<rightarrow> Element-of' the' carrier; OneF \<rightarrow> Element-of' the' carrier#)"    
    
definition ZeroOneStr ("ZeroOneStr") where
  "struct ZeroOneStr ZeroOneStr_fields"

lemma ZeroOneStr_well:"ZeroOneStr_fields
                    well defined on {carrier} \<union>{ZeroF}\<union>{OneF}" 
proof(rule Fields_add_argM1[OF ZeroStr_well])
  show "carrier in {carrier}\<union>{ZeroF}" using tarski_def_1 by auto
  show "not OneF in {carrier}\<union>{ZeroF}" by (simp add:string)     
  show "for X1 be ZeroStr_fields\<parallel>Function holds ex it be Element-of-struct X1 st True" 
  proof(rule ballI)
    fix X1 assume "X1 be ZeroStr_fields\<parallel>Function"
    hence "the carrier of X1 be set" using field by auto 
    thus "ex it be Element-of the carrier of X1 st True"  using subset_1_def_1[THEN conjunct2] by auto
  qed    
qed  
  
schematic_goal ZeroOneStr:
   shows ?X by (rule struct_well_defined[OF ZeroOneStr_def ZeroOneStr_well])
      
theorem ZeroOneStr_inheritance:
  "X be ZeroOneStr \<Longrightarrow> X be ZeroStr & X be OneStr" using ZeroOneStr[THEN conjunct1] ZeroStr[THEN conjunct1] OneStr[THEN conjunct1] by simp

text_raw \<open>\DefineSnippet{struct0def6}{\<close>
definition struct_0_def_6_prefix ( "0\<^sub>_" [1000] 99) where
  "func 0\<^sub>S \<rightarrow> Element-of-struct S  equals
     the ZeroF of S"
schematic_goal struct_0_def_6:
  assumes "S be ZeroStr" shows "?X"
text_raw \<open>}%EndSnippet\<close>
proof (rule equals_property [OF struct_0_def_6_prefix_def,of S]) 
  show "(the ZeroF of S) be Element-of (the carrier of S)" using assms ZeroStr[THEN conjunct1,THEN conjunct1,THEN conjunct1] field by simp
qed
  
text_raw \<open>\DefineSnippet{struct0def7}{\<close>
definition struct_0_def_7_prefix ("1\<^sub>_" [1000] 99) where
  "func 1\<^sub>S \<rightarrow> Element-of-struct S  equals
     the OneF of S"
schematic_goal struct_0_def_7:
  assumes "S be OneStr" shows "?X"
text_raw \<open>}%EndSnippet\<close>
proof (rule equals_property [OF struct_0_def_7_prefix_def,of S])
  show "(the OneF of S) be Element-of (the carrier of S)" using assms OneStr[THEN conjunct1,THEN conjunct1,THEN conjunct1] field by auto
qed

definition degenerated_struct  ("degenerated") where struct_0_def_8_a [THEN defattr_property]:
   "attr degenerated means (\<lambda> S. S be ZeroOneStr & 0\<^sub>S = 1\<^sub>S)"
definition non_degenerated ("non degenerated") where struct_0_def_8_b [THEN defattr_property]:
   "attr non degenerated means (\<lambda> S. S be ZeroOneStr & 0\<^sub>S <> 1\<^sub>S)"   
   
   
definition trivial_struct :: "Attr" ("trivial-struct") where struct_0_def_9_a [THEN defattr_property,simp]:
   "attr trivial-struct means (\<lambda> S. S be one_sorted & the carrier of S is trivial)"
definition non_trivial_struct :: "Attr" ("non trivial-struct") where struct_0_def_9_b [THEN defattr_property,simp]:
   "attr non trivial-struct means (\<lambda> S. S be one_sorted & the carrier of S is non trivial)"   
 
      
   
theorem struct_0_def_10:
  "let S be one-sorted
   redefine attr S is trivial-struct means
        for x, y be Element-of-struct S holds x=y" 
proof(rule iffI3)
  assume A1: "S be one-sorted"
  show "S is trivial-struct implies (for x, y be Element-of-struct S holds x=y)"
  proof(intro impI ballI)
    fix x y assume A2: "S is trivial-struct" "x be Element-of-struct S" "y be Element-of-struct S" 
    have  A3: "the carrier of S is trivial" using struct_0_def_9_a[THEN iffD1,OF A2(1)] by blast
    show "x=y"
    proof (cases "the carrier of S={}")
      case True
        hence "x={}" "y={}" using A2 by auto
        thus ?thesis by simp
    next
      case False
        hence "x in_struct S" "y in_struct S" using  Element_of_rule1[of "the carrier of S",OF _ A2(2)] 
                                            Element_of_rule1[of "the carrier of S",OF _ A2(3)] by auto
        thus  ?thesis using zfmisc_1_def_10a[THEN iffD1,OF A3,THEN conjunct2,rule_format ] by simp        
    qed  
  qed
  assume A4: "for x, y be Element-of-struct S holds x=y"
  show  "S is trivial-struct"
  proof(unfold  struct_0_def_9_a,rule conjI,rule A1,unfold zfmisc_1_def_10a,rule conjI,rule all_set,intro ballI impI)
    fix x y assume "(x in_struct S) & (y in_struct S)"
    hence "x be Element-of-struct S" "y be Element-of-struct S" using Element_of_rule by simp+
    thus "x=y" using A4[rule_format, of x y] by simp  
  qed
qed
  
definition zero_struct :: "Set \<Rightarrow> Attr" ("zero \<^sub>_") where struct_0_def_12_a [THEN defattr_property,simp]:
   "attr zero \<^sub>S means (\<lambda> IT. (S be ZeroStr) & IT = 0\<^sub>S )"
definition non_zero_struct :: "Set \<Rightarrow> Attr" ("non zero \<^sub>_") where struct_0_def_12_b [THEN defattr_property,simp]:
   "attr non zero \<^sub>S means (\<lambda> IT. (S be ZeroStr) & IT <> 0\<^sub>S)"
  
theorem struct_0_cl_10:
  "let S be ZeroStr
   cluster 0\<^sub>S \<rightarrow> zero \<^sub>S" 
  using struct_0_def_12_a by auto

theorem struct_0_cl_11:   
  "cluster strict ZeroOneStr \<bar> non degenerated for ZeroOneStr"
proof-
  let ?c = "carrier \<rightarrow> set'"
  let ?z = "ZeroF \<rightarrow> Element-of' the' carrier"
  let ?o = "OneF \<rightarrow> Element-of' the' carrier"
    obtain x where "x = the set" by simp
    obtain X where X_def:"X= {[carrier,{x}\<union>{{x}}]}\<union>{[ZeroF,x]}\<union>{[OneF,{x}]}" by simp
    show "ex S be ZeroOneStr st S is strict ZeroOneStr \<bar> non degenerated"
    proof(rule bexI[of _ X])
        have "carrier <> ZeroF" "carrier <>OneF" "ZeroF<>OneF" by (simp add:string)+ 
        hence A1: "X be Function" using Function_3[of carrier ZeroF OneF "{x}\<union>{{x}}" x] X_def by auto
        have T1:"({x}\<union>{{x}}) be set" using all_set by auto
        have F1: "X is (#?c#)" using Field_1[OF A1,of _ "{x}\<union>{{x}}"] T1 X_def tarski_def_1 by auto        
        have t: "the carrier of X ={x}\<union>{{x}} " using A1 the_selector_of_1[of _ carrier "{x}\<union>{{x}}"] X_def tarski_def_1 by auto
        hence T2: "x be Element-of the carrier of X" 
          using Element_of_rule T1 the_property tarski_def_1b by auto
        have T3: "{x} be Element-of the carrier of X" 
          using Element_of_rule T1 the_property t tarski_def_1b by auto
        have F2: "X is  (#?z#)" 
          using Field_1[OF A1,of ZeroF "x"] T2 X_def tarski_def_1b by auto
        have F3: "X is  (#?o#)" 
          using Field_1[OF A1,of _ "{x}"] T3 X_def tarski_def_1b by auto
        then have "X is  (#?c;?z;?o #)" using F1 F2 by simp
        thus S3:"X be ZeroOneStr" using ZeroOneStr A1 by simp 
        have "dom (X)={carrier}\<union>{ZeroF}\<union>{OneF}" using Dom_3 X_def by simp
        hence W1: "X is strict ZeroOneStr" using S3 ZeroOneStr strict by auto
        have "the ZeroF of X = x " "the OneF of X = {x} " 
          using the_selector_of_1[OF A1,of ZeroF x] the_selector_of_1[OF A1,of OneF "{x}"] X_def tarski_def_1 by simp+
        hence "0\<^sub>X = x" "1\<^sub>X={x}" using struct_0_def_7 struct_0_def_6 ZeroOneStr_inheritance S3 by auto   
        hence "0\<^sub>X in 1\<^sub>X" using tarski_def_1b by auto    
        hence "0\<^sub>X <> 1\<^sub>X" using prefix_in_irreflexive all_set by auto    
        hence "X is non degenerated" using struct_0_def_8_b S3 by auto     
        thus "X is strict ZeroOneStr \<bar> non degenerated" using W1 by auto  
      qed  
qed

theorem struct_0_cl_12:  
  "let S be non degenerated \<parallel> ZeroOneStr
   cluster 1\<^sub>S \<rightarrow> non zero \<^sub>S"
proof-
  assume A1: "S be non degenerated \<parallel> ZeroOneStr"
  hence "1\<^sub>S <> 0\<^sub>S" "S be ZeroStr" using not_eq struct_0_def_8_b[of S]  ZeroOneStr_inheritance by auto
  thus "1\<^sub>S is non zero \<^sub>S" using struct_0_def_12_b by auto
qed

abbreviation  struct_of_mode_11_prefix  ("BinOp-of-struct _ " 60)
  where "BinOp-of-struct X \<equiv> BinOp-of (the carrier of X)"


abbreviation  struct_of_mode_12_prefix  ("UnOp-of-struct _ " 60)
  where "UnOp-of-struct X \<equiv> BinOp-of (the carrier of X)"

(* :: "(Set\<Rightarrow>Set)\<Rightarrow>Set\<Rightarrow>Mode"*)
text_raw \<open>\DefineSnippet{BinOfP}{\<close>  
abbreviation BinOp_of ("BinOp-of'' _") where
  "BinOp-of' X \<equiv> \<lambda>it. BinOp-of X(it)"
text_raw \<open>}%EndSnippet\<close>
  
abbreviation Subset_Falmily_of :: "(Set \<Rightarrow> Set) \<Rightarrow> (Set \<Rightarrow> Mode)" ("Subset-Family-of'' _") where
  "Subset-Family-of' X \<equiv> \<lambda>it. Subset-Family-of X(it)"

abbreviation Function_of :: "(Set \<Rightarrow> Set) \<Rightarrow> (Set \<Rightarrow> Set) \<Rightarrow> (Set \<Rightarrow> Mode)" ("Function-of'' _ , _") where
  "Function-of' X, Y\<equiv> \<lambda>it. Function-of X(it), Y(it)"

abbreviation cartesian_product1 :: "Set \<Rightarrow> (Set \<Rightarrow> Set) \<Rightarrow> (Set \<Rightarrow> Set)" ("[: _ , _ '':]") where
  "[: X, Y ':] \<equiv> \<lambda>it. [: X, Y(it):]"
  
abbreviation cartesian_product2 :: "(Set \<Rightarrow> Set) \<Rightarrow> Set \<Rightarrow> (Set \<Rightarrow> Set)" ("[:'' _ , _ :]") where
  "[:' X, Y :] \<equiv> \<lambda>it. [: X(it), Y:]"  
  
definition one_element ("1-element-struct") where struct_0_def_19_a[THEN defattr_property,simp]:
  "attr 1-element-struct means (\<lambda> IT. (IT be one_sorted) & (ex x be object st {x} = the carrier of IT))"

theorem struct_0_redef_1:
  "let S be non empty-struct\<parallel>one-sorted & 
       x be Element-of-struct S 
   redefine func {x} \<rightarrow> Subset-of-struct S"
  by (rule Subset_of_rule,erule conjE) (simp add:tarski_def_1b)
 
text_raw \<open>\DefineSnippet{struct_0_redef_2}{\<close>
theorem struct_0_redef_2:
  "let S be non empty-struct\<parallel>one-sorted & 
       x be Element-of-struct S & y be Element-of-struct S
   redefine func {x,y} \<rightarrow> Subset-of-struct S"
text_raw \<open>}%EndSnippet\<close>
by  (elim conjE,rule Subset_of_rule, unfold tarski_def_3,rule ballI,rule impI) auto
  
definition struct_0_def_17_prefix ( "NonZero \<^sub>_" [1000] 99) where
  "func NonZero \<^sub>S \<rightarrow> Subset-of-struct S  equals
     ([#]S) \\ {0\<^sub>S}"

schematic_goal struct_0_def_17:
  assumes "S be ZeroStr" shows "?X"
text_raw \<open>}%EndSnippet\<close>
proof (rule equals_property [OF struct_0_def_17_prefix_def,of S])   
  have A1:"([#]S) be Subset-of-struct S" using struct_0_def_3[of S] assms ZeroStr one_sorted by auto 
  have "(([#]S) \\ {0\<^sub>S}) be Subset-of ([#]S)" using Subset_of_rule by auto
  thus "(([#]S) \\ {0\<^sub>S}) be Subset-of-struct S" using A1  Subset_trans[OF _ A1]  by auto
qed  

end