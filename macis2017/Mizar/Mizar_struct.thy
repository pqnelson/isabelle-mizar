\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Mizar_struct
  imports "../MML/Funct_1"
begin

nonterminal "Attrs"
syntax
  ""       :: "Attr \<Rightarrow> Attrs"  ("_")
  "_Attrs" :: "[Attr, Attrs] \<Rightarrow> Attrs"  ("_ ; _")
  "_Attr1" :: "Attr \<Rightarrow> Attr"         ("(# _ #)")
  "_Tuple" :: "[Attr, Attrs] \<Rightarrow> Attr" ("(#(_;/ _)#)")

translations
  "(# x ; y; z #)"   \<rightharpoonup>  "(# (# x; y #); z #)"
  "(# x; y #)"    \<rightharpoonup>    " x \<bar> y"
  "(# x #)"  \<rightharpoonup> "x"

  (* :: "Set \<Rightarrow> Set \<Rightarrow> Set" *)
text_raw \<open>\DefineSnippet{theselectorof}{\<close>
definition TheSelectorOf ("the _ of _ " [90,90] 190) where
   "func the selector of Term \<rightarrow> object means \<lambda>it.
      for T be object st \<langle>selector,T\<rangle> in Term holds it = T"
text_raw \<open>}%EndSnippet\<close>
  
schematic_goal the_selector_of:
  assumes "Term be Function" "selector in dom Term" shows "?X"
proof (induct rule: means_property[OF TheSelectorOf_def,of selector Term, case_names existence uniqueness])
  obtain D where
      A1: "D be object" "[selector,D] in Term" using xtuple_0_def_12 assms by auto
  case existence
    obtain D where
      A1: "D be object" "[selector,D] in Term" using xtuple_0_def_12 assms by auto
    show "ex x be object st for T be object st [selector,T] in Term holds x = T"
       proof(rule bexI[of _ D],intro ballI)
          show "D be object" by simp
          fix T
          show "[selector,T] in Term implies D=T" using funct_1_def_1 A1 assms(1) all_set by auto
       qed
  case uniqueness
    fix x1 x2 
    assume "for T be object st [selector,T] in Term holds x1 = T"
           "for T be object st [selector,T] in Term holds x2 = T"
    thus "x1=x2"  using A1 by simp+
qed

lemma the_selector_of_1:
  assumes "Term be Function"
         "[selector,D] in Term"
  shows "the selector of Term = D"
proof-
  have "selector in dom Term" using assms xtuple_0_def_12 by auto
  thus ?thesis using the_selector_of assms by auto
qed

lemma the_selector_of_2:
  assumes "Term be Function"
          "Term1 be Function"
          "Term \<subseteq> Term1"
          "selector in dom Term"
  shows "the selector of Term = the selector of Term1"
proof-
   obtain D where
    A1:"[selector,D] in Term" using assms(1,4) xtuple_0_def_12 by auto
   hence "[selector,D] in Term1" using assms(3) by simp
   thus ?thesis using the_selector_of_1 assms(1,2) A1 by auto     
qed
  
  
  (* :: "Set \<Rightarrow> (Set \<Rightarrow> Mode) \<Rightarrow> Attr" *)
text_raw \<open>\DefineSnippet{structfield}{\<close>
definition Field ("_ \<rightarrow> _" 91) where
   "selector \<rightarrow> spec \<equiv> define_attr (\<lambda>it. 
      the selector of it be spec(it) & selector in dom it)"
text_raw \<open>}%EndSnippet\<close>

lemmas field = Field_def[THEN defattr_property]

(*  (input)    :: "Set \<Rightarrow> Set \<Rightarrow> Set" *)
text_raw \<open>\DefineSnippet{TheS}{\<close>
abbreviation TheS ("the'' _") where
   "TheS \<equiv> \<lambda>selector Term. the selector of Term"
text_raw \<open>}%EndSnippet\<close>


(* :: "Mode \<Rightarrow> Set" *)
text_raw \<open>\DefineSnippet{domainof}{\<close>
definition domain_of::"Mode \<Rightarrow> Set" ("domain'_of _" 200) where
  "func domain_of M \<rightarrow> set means (\<lambda>it.
      (ex X be M st it = dom X) & (for X be M holds it \<subseteq> dom X))"
text_raw \<open>}%EndSnippet\<close>


text_raw \<open>\DefineSnippet{truct_strict}{\<close>
definition strict :: "Mode \<Rightarrow> Attr" ("strict _" 200) where
   "attr strict M means (\<lambda>X. X be M & dom X =  domain_of M)"
text_raw \<open>}%EndSnippet\<close>
lemmas strict = strict_def[THEN defattr_property]

text_raw \<open>\DefineSnippet{struct_restriction}{\<close>
definition the_restriction_of :: "Set \<Rightarrow> Mode \<Rightarrow> Set"
                      ("the'_restriction'_of _ to _" 90) where
   "func the_restriction_of X to Struct \<rightarrow>
      strict Struct \<parallel> Struct equals X | domain_of Struct"
text_raw \<open>}%EndSnippet\<close>

lemma Field_1:
assumes "Term be Function"
        "[selector,D] in Term"
        "D be specification(Term)"
shows "Term is (# selector \<rightarrow> specification #)"
proof-
  have "selector in dom (Term)" using assms(1,2) xtuple_0_def_12 by auto
  thus "Term is (#selector \<rightarrow> specification#)" using the_selector_of_1[OF assms(1) assms(2)] assms field by auto
qed

lemma Field_2:
  assumes "Term be Function"
          "[selector,D] in Term"
          "Term is (# selector \<rightarrow> specification #)"
  shows "D be specification(Term)"
proof-
   have "the selector of Term = D" using the_selector_of_1 assms(1,2) by simp
  thus ?thesis  using  assms(3) field by auto
qed

  theorem Function_and_pair:
  assumes "not (selector in dom X)"  
          "X be Function" 
  shows "(X \<union>{[selector,S]}) be Function" "dom (X \<union>{[selector,S]}) = (dom X) \<union> {selector}"
proof-
  let ?F = "{[selector,S]}"  
  have "for x,y1,y2 being object st [x,y1] in X\<union>?F & [x,y2] in X\<union>?F holds y1 = y2"
     proof(intro ballI impI)
       fix x y1 y2
       assume "x be object" "y1 be object" "y2 be object"
       assume "[x , y1] in X\<union>?F & [x , y2] in X\<union>?F"
       hence "[x,y1] in X or [x , y1] in ?F" "[x , y2] in X or [x , y2] in ?F" using xboole_0_def_3 by auto
       hence A5: "[x,y1] in X or [x,y1] =[selector,S]"  "[x,y2] in X or [x,y2] =[selector,S]" using tarski_def_1 by simp+
       show "y1 = y2" 
       proof(rule disjE[OF A5(1)])
         assume C1:"[x,y1] in X"
           hence "x in dom X" using assms xtuple_0_def_12 by auto
           hence "x <> selector" using assms by auto
           hence "[x,y2] in X" using  xtuple_0_th_1[of x y2 selector S] A5(2) by auto
           thus "y1=y2" using  funct_1_def_1[OF all_set,of X,THEN iffD1,rule_format, of x y1 y2] C1 assms by simp  
       next
         assume C1:"[x,y1] = [selector,S]"
           hence C2: "x=selector" "y1=S" using  xtuple_0_th_1[of x y1 selector S] by auto
           hence "[x,y2] = [selector,S]" using A5(2) assms xtuple_0_def_12 by auto    
           thus "y1=y2" using  C2 xtuple_0_th_1[of x y2 selector S] by auto
       qed
     qed
  hence A: "(X \<union> ?F) is Function_like" using funct_1_def_1 by simp
  have "(X \<union> ?F) is Relation_like" using relat_1_cl_7 assms relat_1_cl_5[of X ?F] by simp
  thus W1: "(X \<union> ?F) be Function" using A by simp       
   have F: "?F be Relation" using relat_1_cl_7 by simp
  hence "dom (?F) = {selector}" using relat_1_th_3[of S selector ?F] by auto    
  thus "dom (X\<union> ?F) = (dom X) \<union> {selector}" using W1 F assms xtuple_th_23[of ?F X] by auto
qed  

theorem fields_restriction:
  "X be Function \<Longrightarrow> X is (s\<rightarrow>Typ) \<Longrightarrow> s in D \<Longrightarrow> IFOL.eq(Typ(X),Typ(X|D)) \<Longrightarrow> (X|D) is (s\<rightarrow>Typ)"
proof-
  assume A:"X be Function" "X is (s\<rightarrow>Typ)" "s in D" "IFOL.eq(Typ(X),Typ(X|D))"
  hence "s in dom X" using field by simp
  then obtain T where
    A1:"T be object" "[s,T] in X" using A xtuple_0_def_12 by auto
  have "T be Typ(X)" using A(1,2,3) A1 Field_2 by auto
  hence A2:"T be Typ(X|D)" using A(4) by simp
  have A3: "D be set" "X be Relation" using A(1) all_set by auto
  have A4: "(X|D) be Relation" "[s,T] in (X|D)" using relat_1_def_11[of X D,OF A3(2,1),THEN conjunct1] A1 A(3) by auto
  hence "(X|D) be Function" using funct_1_cl[of D X] A(1) A3(1) by auto
  thus "(X|D) is (s\<rightarrow>Typ)" using Field_1[of "(X|D)"] A4(2) A2 by auto
qed

  
theorem the_selector_of_restriction:
 assumes "X be Function"
         "selector in dom X" "selector in D"
 shows  "the' selector(X) = the' selector(X|D)"
proof-
  obtain T where
    A1:"T be object" "[selector,T] in X" using assms(1,2) xtuple_0_def_12 by auto
  have A3: "D be set" "X be Relation" using assms(1) all_set by auto
  have A4: "(X|D) be Relation" "[selector,T] in (X|D)" using relat_1_def_11[of X D,OF A3(2,1),THEN conjunct1] A1 assms(3) by auto
  hence "(X|D) be Function" using funct_1_cl[of D X] assms(1) A3(1) by auto
  hence "the' selector(X|D) =T" using the_selector_of_1 A4(2) by simp
  thus ?thesis using the_selector_of_1 assms(1) A1(2) by simp
qed

text_raw \<open>\DefineSnippet{welldefined}{\<close>
definition struct_well_defined :: "Attr \<Rightarrow> Set \<Rightarrow> o"
            (" _ well defined on _"[10,10] 200)
where
  "Fields well defined on D \<equiv> 
     (ex X be Function st X is Fields & dom X=D)
  & (for X1 be Fields\<parallel>Function holds D \<subseteq> dom X1)
  & (for X1 be Fields\<parallel>Function holds X1|D is Fields)
  & (for X1 be Fields\<parallel>Function, X2 be Function st
        D \<subseteq> dom X1 & X1 \<subseteq> X2 holds X2 is Fields)"
text_raw \<open>}%EndSnippet\<close>

theorem First_0_arg_Mode:
  assumes "ex S be M st True"
  shows "(#selector \<rightarrow> \<lambda>S . M#) well defined on {selector}"
proof(unfold struct_well_defined_def, intro conjI)
  let ?Spec="\<lambda>S . M"
  obtain S where
    A2: "S be M" "True" using assms by auto   
  let ?F = "{[selector,S]}"
  show "ex X be Function st X is (#selector\<rightarrow>?Spec#) & dom X={selector}"
  proof(rule bexI[of _ "?F"],intro conjI)
      have A3: "?F be Function" using funct_1_cl_3 relat_1_cl_7 by simp
      hence "dom ?F = {selector}" using relat_1_th_3[of S selector "{[selector,S]}"] by auto
      thus "?F is (#selector\<rightarrow>?Spec#)" 
           "dom ?F = {selector}" "?F be Function" using Field_1[of ?F selector S] A2 A3 tarski_def_1b by auto
    qed  
  show "for X1 be (selector \<rightarrow> ?Spec)  \<parallel>  Function , X2 be Function st
       {selector} \<subseteq> (dom X1) & (X1 \<subseteq> X2) holds X2 is  (selector \<rightarrow> ?Spec)"
  proof(intro ballI,rule impI)
    fix X1 X2
    assume B1: "X1 be (selector \<rightarrow> ?Spec)  \<parallel>  Function"
      and  B2: "X2 be Function"
      and  B3: "{selector} \<subseteq> dom X1 & X1 \<subseteq> X2"  
     have B5: "the selector of X1 be ?Spec(X2)" using B1 field by auto    
     have B6: "dom X1 \<subseteq> dom X2" using xtuple_0_th_8[of X2 X1] B3 B2 B1 by auto     
     have "selector in dom X1" using B3 tarski_def_1b by auto 
     hence "the selector of X1 = the selector of X2" "selector in dom X2" using B6 the_selector_of_2[of X1 X2 selector] B1 B2 B3 by auto        
     thus  "X2 is (#selector \<rightarrow>?Spec#)" using B5 field by auto
   qed 
  show "for X1 be (#selector \<rightarrow>?Spec#)\<parallel>Function holds {selector} \<subseteq> dom X1"
  proof(rule ballI)
    fix X1 assume C1: "X1 be (#selector \<rightarrow>?Spec#)\<parallel>Function"  
    have "selector in dom X1" using field C1 by auto
    thus  "{selector} \<subseteq> dom X1" using tarski_def_1b by auto        
  qed 
  show "for X1 be (#selector \<rightarrow>?Spec#)\<parallel>Function holds X1| {selector} is (#selector \<rightarrow>?Spec#)"
  proof(rule ballI)
    fix X1 assume C1: "X1 be (#selector \<rightarrow>?Spec#)\<parallel>Function"  
    have "X1| {selector} is (#selector \<rightarrow>?Spec#)" using fields_restriction[of X1 "selector" "?Spec" "{selector}"]
       C1 tarski_def_1b by auto
    thus "X1| ({selector}) is (#selector \<rightarrow>?Spec#)"  by simp     
  qed          
qed 

text_raw \<open>\DefineSnippet{WellAddM0}{\<close>  
theorem Fields_add_0_arg_Mode:
  assumes "Fields well defined on D"
          "not (selector in D)"  
          "ex S be M st True"
  shows "Fields\<bar> (selector \<rightarrow> \<lambda>S . M) well defined on D\<union>{selector}"
text_raw \<open>}%EndSnippet\<close>
proof(unfold  struct_well_defined_def,intro conjI)
  have A0: "ex X be Function st X is Fields & dom X=D"
            "for X1 be Fields\<parallel>Function, X2 be Function st D \<subseteq> dom X1 & X1 \<subseteq> X2 holds X2 is Fields"
            "for X1 be Fields\<parallel>Function holds D \<subseteq> dom X1 & X1|D is Fields" using struct_well_defined_def assms by auto
  let ?Spec="\<lambda>S . M"
  obtain X where 
    A1: "X be Function" "X is Fields" "dom X=D" using A0(1) by blast
  have B1:"X is Function_like" using A1 by simp
  obtain S where
    A2: "S be M" "True" using assms(3) by auto   
  let ?F = "{[selector,S]}"
  show "ex X be Function st X is Fields\<bar>(selector\<rightarrow>?Spec) & (dom X)=D\<union>{selector}"
    proof(rule bexI[of _ "X \<union>?F"],intro conjI)
      have A3: "(X \<union>?F) be Function" "dom (X \<union>?F) = (dom X) \<union> {selector}" using A1(1,3) assms(2)  Function_and_pair[of selector X] by auto
      have "X \<subseteq> X \<union> ?F" by auto
      hence A4: "(X \<union>?F) is Fields" using A1(1,2,3) A3(1) A0(2)[rule_format,of X "X\<union>?F"] by auto   
      have A5: "S be ?Spec(X\<union>?F)" "[selector,S] in (X\<union>?F)" using A2(1) tarski_def_1b by auto
      have  "(X\<union>?F) is (#selector \<rightarrow>?Spec#)" using Field_1[OF A3(1) A5(2),of ?Spec,OF A5(1)] by auto
      thus "(X \<union>?F) is Fields\<bar>(selector\<rightarrow>?Spec)" 
           "dom (X \<union> ?F) = (D \<union> {selector})" "(X \<union>?F) be Function" using A4 A1 A3 by auto
    qed  
  show "for X1 be Fields  \<bar>  (selector \<rightarrow> ?Spec)  \<parallel>  Function , X2 be Function st
       (D\<union>{selector}) \<subseteq> (dom X1) & (X1 \<subseteq> X2) holds X2 is Fields  \<bar>  (selector \<rightarrow> ?Spec)"
  proof(intro ballI,rule impI)
    fix X1 X2
    assume B1: "X1 be Fields  \<bar>  (selector \<rightarrow> ?Spec)  \<parallel>  Function"
      and  B2: "X2 be Function"
      and  B3: " D \<union> {selector} \<subseteq> dom X1 & X1 \<subseteq> X2"  
    hence B7: "X2 is Fields" using A0(2)[rule_format,of X1 X2] by auto  
    have B5: "the selector of X1 be ?Spec(X2)" using B1 field by auto    
    have B6: "dom X1 \<subseteq> dom X2" using xtuple_0_th_8[of X2 X1] B3 B2 B1 by auto     
    have "selector in dom X1" using B3 tarski_def_1b by auto 
    hence "the selector of X1 = the selector of X2" "selector in dom X2" using B6 the_selector_of_2[of X1 X2 selector] B1 B2 B3 by auto        
    thus  "X2 is Fields\<bar>(#selector \<rightarrow>?Spec#)" using B5 field B7 by auto
  qed  
  show "for X1 be Fields\<bar>(#selector \<rightarrow>?Spec#)\<parallel>Function holds D\<union>{selector} \<subseteq> dom X1"
  proof(rule ballI)
    fix X1 assume C1: "X1 be Fields\<bar>(#selector \<rightarrow>?Spec#)\<parallel>Function"  
    have C5: "D \<subseteq> dom X1" using A0(3) C1 by auto
    have "selector in dom X1" using field C1 by auto
    thus  "D\<union>{selector} \<subseteq> dom X1" using C5 tarski_def_1b by auto        
  qed   
  show "for X1 be Fields\<bar>(#selector \<rightarrow>?Spec#)\<parallel>Function holds X1| (D\<union>{selector}) is Fields\<bar>(#selector \<rightarrow>?Spec#)"
  proof(rule ballI)
    fix X1 assume C1: "X1 be Fields\<bar>(#selector \<rightarrow>?Spec#)\<parallel>Function"  
    hence T0:"X1 be Relation" by simp
    hence T1: "X1|(D\<union>{selector}) be Relation" "X1|D be Relation" 
      using relat_1_def_11[of X1,THEN conjunct1,THEN conjunct1] all_set by auto
    hence T2: "X1| (D\<union>{selector}) is Function_like"  
      using funct_1_cl[of "D\<union>{selector}" X1,rule_format,OF all_set] C1   by auto
    hence "X1| D is Function_like"
       using funct_1_cl[of D X1,rule_format,OF all_set] C1  by auto   
    hence C2: "X1| (D\<union>{selector}) be Function" "X1|D be Function" 
       using T2 T1 by auto
    have C5: "D \<subseteq> dom X1" using A0(3) C1 by auto
    hence C3:"X1|D be Fields\<parallel>Function" using A0(3) C1 C2 by auto
    have "dom (X1|D) = (dom X1)\<inter> D" using relat_1_th_55 T0 all_set by auto  
    hence C4: "D \<subseteq> dom (X1|D)" using C5 by auto    
    have "X1|D \<subseteq> X1| (D\<union>{selector})" using relat_1_th75[of X1 "D\<union>{selector}" D,OF _ all_set all_set] C1 by auto
    hence C6: "X1| (D\<union>{selector}) is Fields"  using  C2 C3 A0(2)[rule_format, OF C3 C2(1) C4]  by auto  
    have "X1| (D\<union>{selector}) is (#selector \<rightarrow>?Spec#)" using fields_restriction[of X1 "selector" "?Spec" "D\<union>{selector}"]
       C1 tarski_def_1b by auto
    thus "X1| (D\<union>{selector}) is Fields\<bar>(#selector \<rightarrow>?Spec#)" using C6 by simp
   qed   
qed 

text_raw \<open>\DefineSnippet{WellAddM1}{\<close>  
theorem Fields_add_argM1:
assumes "Fields well defined on D"
 and "selector_1 in D"     
 and "not (selector in D)"
 and "for X1 be Fields\<parallel>Function holds
           ex S be M1 (the selector_1 of X1) st True"
shows
 "Fields \<bar> (selector \<rightarrow> \<lambda>S. M1 (the selector_1 of S))
         well defined on D \<union> {selector}"
text_raw \<open>}%EndSnippet\<close>
proof(unfold  struct_well_defined_def,intro conjI)  
  have A0: "ex X be Function st X is Fields & dom X=D"
            "for X1 be Fields\<parallel>Function, X2 be Function st D \<subseteq> dom X1 & X1 \<subseteq> X2 holds X2 is Fields"
            "for X1 be Fields\<parallel>Function holds D \<subseteq> dom X1 & X1|D is Fields" using struct_well_defined_def assms(1) by auto 
  let ?Spec="\<lambda>S . M1 (the selector_1 of S)"
  obtain X where 
    A1: "X be Function" "X is Fields" "dom X=D" using A0(1) by blast
  have B1:"X is Function_like" using A1 by simp
  obtain S where
    A2: "S be M1 (the selector_1 of X)" "True" using assms(4)[rule_format] A1 by auto   
  let ?F = "{[selector,S]}"
  show "ex X be Function st X is Fields\<bar>(selector\<rightarrow>?Spec) & (dom X)=D\<union>{selector}"
    proof(rule bexI[of _ "X \<union>?F"],intro conjI)
      have A3: "(X \<union>?F) be Function" "dom (X \<union>?F) = (dom X) \<union> {selector}" using A1(1,3) assms(3)  Function_and_pair[of selector X] by auto
      have "X \<subseteq> X \<union> ?F" by auto
      hence A4: "(X \<union>?F) is Fields" using A1(1,2,3) A3(1) A0(2)[rule_format,of X "X\<union>?F"]  by auto   
      have "(the selector_1 of X)= (the selector_1 of (X\<union>?F))" using A1(3) the_selector_of_2[OF A1(1) A3(1)] assms(2) by auto  
      hence A5: "S be ?Spec(X\<union>?F)" "[selector,S] in (X\<union>?F)" using A2(1) tarski_def_1b by auto
      have  "(X\<union>?F) is (#selector \<rightarrow>?Spec#)" using Field_1[OF A3(1) A5(2),of ?Spec,OF A5(1)] by auto
      thus "(X \<union>?F) is Fields\<bar>(selector\<rightarrow>?Spec)" 
           "dom (X \<union> ?F) = (D \<union> {selector})" "(X \<union>?F) be Function" using A4 A1 A3 by auto
    qed  
  show "for X1 be Fields  \<bar>  (selector \<rightarrow> ?Spec)  \<parallel>  Function , X2 be Function st
       (D\<union>{selector}) \<subseteq> (dom X1) & (X1 \<subseteq> X2) holds X2 is Fields  \<bar>  (selector \<rightarrow> ?Spec)"
  proof(intro ballI,rule impI)
    fix X1 X2
    assume B1: "X1 be Fields  \<bar>  (selector \<rightarrow> ?Spec)  \<parallel>  Function"
      and  B2: "X2 be Function"
      and  B3: " D \<union> {selector} \<subseteq> dom X1 & X1 \<subseteq> X2"  
    hence B7: "X2 is Fields" using A0(2)[rule_format,of X1 X2] by auto  
    have B4: "selector_1 in dom X1" using assms(2) B3 by auto    
    hence "the selector_1 of X1= the selector_1 of (X2)" using  the_selector_of_2[OF _ B2] B1 B3 by auto  
    hence B5: "the selector of X1 be ?Spec(X2)" using B1 field by auto    
    have B6: "dom X1 \<subseteq> dom X2" using xtuple_0_th_8[of X2 X1] B3 B2 B1 by auto     
    have "selector in dom X1" using B3 tarski_def_1b by auto 
    hence "the selector of X1 = the selector of X2" "selector in dom X2" using B6 the_selector_of_2[of X1 X2 selector] B1 B2 B3 by auto        
    thus  "X2 is Fields\<bar>(#selector \<rightarrow>?Spec#)" using B5 field B7 by auto
  qed  
   show "for X1 be Fields\<bar>(#selector \<rightarrow>?Spec#)\<parallel>Function holds D\<union>{selector} \<subseteq> dom X1"
  proof(rule ballI)
    fix X1 assume C1: "X1 be Fields\<bar>(#selector \<rightarrow>?Spec#)\<parallel>Function"  
    have C5: "D \<subseteq> dom X1" using A0(3) C1 by auto
    have "selector in dom X1" using field C1 by auto
    thus  "D\<union>{selector} \<subseteq> dom X1" using C5 tarski_def_1b by auto        
  qed      
  show "for X1 be Fields\<bar>(#selector \<rightarrow>?Spec#)\<parallel>Function holds X1| (D\<union>{selector}) is Fields\<bar>(#selector \<rightarrow>?Spec#)"
  proof(rule ballI)
    fix X1 assume C1: "X1 be Fields\<bar>(#selector \<rightarrow>?Spec#)\<parallel>Function"  
    hence T0:"X1 be Relation" by simp
    hence T1: "X1|(D\<union>{selector}) be Relation" "X1|D be Relation" 
      using relat_1_def_11[of X1,THEN conjunct1,THEN conjunct1] all_set by auto
    hence T2: "X1| (D\<union>{selector}) is Function_like"  
      using funct_1_cl[of "D\<union>{selector}" X1,rule_format,OF all_set] C1   by auto
    hence "X1| D is Function_like"
       using funct_1_cl[of D X1,rule_format,OF all_set] C1  by auto   
    hence C2: "X1| (D\<union>{selector}) be Function" "X1|D be Function" 
       using T2 T1 by auto
    have C5: "D \<subseteq> dom X1" using A0(3) C1 by auto
    hence C3:"X1|D be Fields\<parallel>Function" using A0(3) C1 C2 by auto
    have "dom (X1|D) = (dom X1)\<inter> D" using relat_1_th_55 T0 all_set by auto  
    hence C4: "D \<subseteq> dom (X1|D)" using C5 by auto    
    have "X1|D \<subseteq> X1| (D\<union>{selector})" using relat_1_th75[of X1 "D\<union>{selector}" D,OF _ all_set all_set] C1 by auto
    hence C6: "X1| (D\<union>{selector}) is Fields"  using  C2 C3 A0(2)[rule_format, OF C3 C2(1) C4]  by auto  
    have "selector_1 in dom X1" "selector_1 in (D\<union>{selector})"  using assms(2) C5 by auto
    hence "the selector_1 of X1 = the selector_1 of (X1|(D \<union> {selector}))" 
      using C1 the_selector_of_restriction[of X1 selector_1 "D\<union>{selector}"] by auto 
    hence "X1| (D\<union>{selector}) is (#selector \<rightarrow>?Spec#)" using fields_restriction[of X1 "selector" "?Spec" "D\<union>{selector}"]
       C1 tarski_def_1b by auto
    thus "X1| (D\<union>{selector}) is Fields\<bar>(#selector \<rightarrow>?Spec#)" using C6 by simp
  qed          
qed 

text_raw \<open>\DefineSnippet{WellAddM2}{\<close>    
theorem Fields_add_2_arg_Mode:
  assumes "Fields well defined on D"
          "selector_1 in D"
          "selector_2 in D"
          "not (selector in D)"  
          "for X1 be Fields\<parallel>Function holds ex S be M1 (the selector_1 of X1,the selector_2 of X1) st True"
  shows "Fields\<bar> (selector \<rightarrow> \<lambda>S . M1 (the selector_1 of S,the selector_2 of S)) well defined on D\<union>{selector}"
text_raw \<open>}%EndSnippet\<close>
proof(unfold  struct_well_defined_def,intro conjI)  
  have A0: "ex X be Function st X is Fields & dom X=D"
            "for X1 be Fields\<parallel>Function, X2 be Function st D \<subseteq> dom X1 & X1 \<subseteq> X2 holds X2 is Fields"
            "for X1 be Fields\<parallel>Function holds D \<subseteq> dom X1 & X1|D is Fields" using struct_well_defined_def assms(1) by auto 
  let ?Spec="\<lambda>S . M1 (the selector_1 of S,the selector_2 of S)"
  obtain X where 
    A1: "X be Function" "X is Fields" "dom X=D" using A0(1) by blast
  have B1:"X is Function_like" using A1 by simp
  obtain S where
    A2: "S be M1 (the selector_1 of X,the selector_2 of X)" "True" using assms(5)[rule_format] A1 by auto   
  let ?F = "{[selector,S]}"
  show "ex X be Function st X is Fields\<bar>(selector\<rightarrow>?Spec) & (dom X)=D\<union>{selector}"
    proof(rule bexI[of _ "X \<union>?F"],intro conjI)
      have A3: "(X \<union>?F) be Function" "dom (X \<union>?F) = (dom X) \<union> {selector}" using A1(1,3) assms(4)  Function_and_pair[of selector X] by auto
      have "X \<subseteq> X \<union> ?F" by auto
      hence A4: "(X \<union>?F) is Fields" using A1(1,2,3) A3(1) A0(2)[rule_format,of X "X\<union>?F"]  by auto   
      have "(the selector_1 of X)= (the selector_1 of (X\<union>?F))" 
           "(the selector_2 of X)= (the selector_2 of (X\<union>?F))" using A1(3) the_selector_of_2[OF A1(1) A3(1)] assms(2,3) by auto  
      hence A5: "S be ?Spec(X\<union>?F)" "[selector,S] in (X\<union>?F)" using A2(1) tarski_def_1b by auto
      have  "(X\<union>?F) is (#selector \<rightarrow>?Spec#)" using Field_1[OF A3(1) A5(2),of ?Spec,OF A5(1)] by auto
      thus "(X \<union>?F) is Fields\<bar>(selector\<rightarrow>?Spec)" 
           "dom (X \<union> ?F) = (D \<union> {selector})" "(X \<union>?F) be Function" using A4 A1 A3 by auto
    qed  
  show "for X1 be Fields  \<bar>  (selector \<rightarrow> ?Spec)  \<parallel>  Function , X2 be Function st
       (D\<union>{selector}) \<subseteq> (dom X1) & (X1 \<subseteq> X2) holds X2 is Fields  \<bar>  (selector \<rightarrow> ?Spec)"
  proof(intro ballI,rule impI)
    fix X1 X2
    assume B1: "X1 be Fields  \<bar>  (selector \<rightarrow> ?Spec)  \<parallel>  Function"
      and  B2: "X2 be Function"
      and  B3: " D \<union> {selector} \<subseteq> dom X1 & X1 \<subseteq> X2"  
    hence B7: "X2 is Fields" using A0(2)[rule_format,of X1 X2] by auto  
    have B4: "selector_1 in dom X1" "selector_2 in dom X1"using assms(2,3) B3 by auto    
    hence "the selector_1 of X1= the selector_1 of (X2)" 
          "the selector_2 of X1= the selector_2 of (X2)" using  the_selector_of_2[OF _ B2] B1 B3 by auto  
    hence B5: "the selector of X1 be ?Spec(X2)" using B1 field by auto    
    have B6: "dom X1 \<subseteq> dom X2" using xtuple_0_th_8[of X2 X1] B3 B2 B1 by auto     
    have "selector in dom X1" using B3 tarski_def_1b by auto 
    hence "the selector of X1 = the selector of X2" "selector in dom X2" using B6 the_selector_of_2[of X1 X2 selector] B1 B2 B3 by auto        
    thus  "X2 is Fields\<bar>(#selector \<rightarrow>?Spec#)" using B5 field B7 by auto
  qed
  show "for X1 be Fields\<bar>(#selector \<rightarrow>?Spec#)\<parallel>Function holds D\<union>{selector} \<subseteq> dom X1"
  proof(rule ballI)
    fix X1 assume C1: "X1 be Fields\<bar>(#selector \<rightarrow>?Spec#)\<parallel>Function"  
    have C5: "D \<subseteq> dom X1" using A0(3) C1 by auto
    have "selector in dom X1" using field C1 by auto
    thus  "D\<union>{selector} \<subseteq> dom X1" using C5 tarski_def_1b by auto        
  qed   
  show "for X1 be Fields\<bar> (#selector \<rightarrow>?Spec#)\<parallel>Function holds  X1| (D\<union>{selector}) is Fields\<bar>(#selector \<rightarrow>?Spec#)"
  proof(rule ballI)
    fix X1 assume C1: "X1 be Fields\<bar>(#selector \<rightarrow>?Spec#)\<parallel>Function"  
    hence T0:"X1 be Relation" by simp
    hence T1: "X1|(D\<union>{selector}) be Relation" "X1|D be Relation" 
      using relat_1_def_11[of X1,THEN conjunct1,THEN conjunct1] all_set by auto
    hence T2: "X1| (D\<union>{selector}) is Function_like"  
      using funct_1_cl[of "D\<union>{selector}" X1,rule_format,OF all_set] C1   by auto
    hence "X1| D is Function_like"
       using funct_1_cl[of D X1,rule_format,OF all_set] C1  by auto   
    hence C2: "X1| (D\<union>{selector}) be Function" "X1|D be Function" 
       using T2 T1 by auto
    have C5: "D \<subseteq> dom X1" using A0(3) C1 by auto
    hence C3:"X1|D be Fields\<parallel>Function" using A0(3) C1 C2 by auto
    have "dom (X1|D) = (dom X1)\<inter> D" using relat_1_th_55 T0 all_set by auto  
    hence C4: "D \<subseteq> dom (X1|D)" using C5 by auto    
    have "X1|D \<subseteq> X1| (D\<union>{selector})" using relat_1_th75[of X1 "D\<union>{selector}" D,OF _ all_set all_set] C1 by auto
    hence C6: "X1| (D\<union>{selector}) is Fields"  using  C2 C3 A0(2)[rule_format, OF C3 C2(1) C4]  by auto  
    have "selector_1 in dom X1" "selector_1 in (D\<union>{selector})" 
         "selector_2 in dom X1" "selector_2 in (D\<union>{selector})" using assms(2,3) C5 by auto
    hence "the selector_1 of X1 = the selector_1 of (X1|(D \<union> {selector}))" 
          "the selector_2 of X1 = the selector_2 of (X1|(D \<union> {selector}))" 
      using C1 the_selector_of_restriction[of X1 selector_1 "D\<union>{selector}"]
               the_selector_of_restriction[of X1 selector_2 "D\<union>{selector}"] by auto 
    hence "X1| (D\<union>{selector}) is (#selector \<rightarrow>?Spec#)" using fields_restriction[of X1 "selector" "?Spec" "D\<union>{selector}"]
       C1 tarski_def_1b by auto
    thus "X1| (D\<union>{selector}) is Fields\<bar>(#selector \<rightarrow>?Spec#)" using C6 by simp
  qed          
qed  

theorem Fields_add_3_arg_Mode:
  assumes "Fields well defined on D"
          "selector_1 in D"
          "selector_2 in D"
          "selector_3 in D"
          "not (selector in D)"  
          "for X1 be Fields\<parallel>Function holds ex S be M1 (the selector_1 of X1,the selector_2 of X1,the selector_3 of X1) st True"
  shows "Fields\<bar> (selector \<rightarrow> \<lambda>S . M1 (the selector_1 of S,the selector_2 of S,the selector_3 of S)) well defined on D\<union>{selector}"
text_raw \<open>}%EndSnippet\<close>
proof(unfold  struct_well_defined_def,intro conjI)  
  have A0: "ex X be Function st X is Fields & dom X=D"
            "for X1 be Fields\<parallel>Function, X2 be Function st D \<subseteq> dom X1 & X1 \<subseteq> X2 holds X2 is Fields"
            "for X1 be Fields\<parallel>Function holds D \<subseteq> dom X1 & X1|D is Fields" using struct_well_defined_def assms(1) by auto 
  let ?Spec="\<lambda>S . M1 (the selector_1 of S,the selector_2 of S,the selector_3 of S)"
  obtain X where 
    A1: "X be Function" "X is Fields" "dom X=D" using A0(1) by blast
  have B1:"X is Function_like" using A1 by simp
  obtain S where
    A2: "S be M1 (the selector_1 of X,the selector_2 of X,the selector_3 of X)" "True" using assms(6)[rule_format] A1 by auto   
  let ?F = "{[selector,S]}"
  show "ex X be Function st X is Fields\<bar>(selector\<rightarrow>?Spec) & (dom X)=D\<union>{selector}"
    proof(rule bexI[of _ "X \<union>?F"],intro conjI)
      have A3: "(X \<union>?F) be Function" "dom (X \<union>?F) = (dom X) \<union> {selector}" using A1(1,3) assms(5)  Function_and_pair[of selector X] by auto
      have "X \<subseteq> X \<union> ?F" by auto
      hence A4: "(X \<union>?F) is Fields" using A1(1,2,3) A3(1) A0(2)[rule_format,of X "X\<union>?F"]  by auto   
      have "(the selector_1 of X)= (the selector_1 of (X\<union>?F))" 
           "(the selector_2 of X)= (the selector_2 of (X\<union>?F))" 
           "(the selector_3 of X)= (the selector_3 of (X\<union>?F))"using A1(3) the_selector_of_2[OF A1(1) A3(1)] assms(2,3,4) by auto  
      hence A5: "S be ?Spec(X\<union>?F)" "[selector,S] in (X\<union>?F)" using A2(1) tarski_def_1b by auto
      have  "(X\<union>?F) is (#selector \<rightarrow>?Spec#)" using Field_1[OF A3(1) A5(2),of ?Spec,OF A5(1)] by auto
      thus "(X \<union>?F) is Fields\<bar>(selector\<rightarrow>?Spec)" 
           "dom (X \<union> ?F) = (D \<union> {selector})" "(X \<union>?F) be Function" using A4 A1 A3 by auto
    qed  
  show "for X1 be Fields  \<bar>  (selector \<rightarrow> ?Spec)  \<parallel>  Function , X2 be Function st
       (D\<union>{selector}) \<subseteq> (dom X1) & (X1 \<subseteq> X2) holds X2 is Fields  \<bar>  (selector \<rightarrow> ?Spec)"
  proof(intro ballI,rule impI)
    fix X1 X2
    assume B1: "X1 be Fields  \<bar>  (selector \<rightarrow> ?Spec)  \<parallel>  Function"
      and  B2: "X2 be Function"
      and  B3: " D \<union> {selector} \<subseteq> dom X1 & X1 \<subseteq> X2"  
    hence B7: "X2 is Fields" using A0(2)[rule_format,of X1 X2] by auto  
    have B4: "selector_1 in dom X1" "selector_2 in dom X1" "selector_3 in dom X1"using assms(2,3,4) B3 by auto    
    hence "the selector_1 of X1= the selector_1 of (X2)" 
          "the selector_2 of X1= the selector_2 of (X2)"
          "the selector_3 of X1= the selector_3 of (X2)" using the_selector_of_2[OF _ B2] B1 B3 by auto  
    hence B5: "the selector of X1 be ?Spec(X2)" using B1 field by auto    
    have B6: "dom X1 \<subseteq> dom X2" using xtuple_0_th_8[of X2 X1] B3 B2 B1 by auto     
    have "selector in dom X1" using B3 tarski_def_1b by auto 
    hence "the selector of X1 = the selector of X2" "selector in dom X2" using B6 the_selector_of_2[of X1 X2 selector] B1 B2 B3 by auto        
    thus  "X2 is Fields\<bar>(#selector \<rightarrow>?Spec#)" using B5 field B7 by auto
  qed
  show "for X1 be Fields\<bar>(#selector \<rightarrow>?Spec#)\<parallel>Function holds D\<union>{selector} \<subseteq> dom X1"
  proof(rule ballI)
    fix X1 assume C1: "X1 be Fields\<bar>(#selector \<rightarrow>?Spec#)\<parallel>Function"  
    have C5: "D \<subseteq> dom X1" using A0(3) C1 by auto
    have "selector in dom X1" using field C1 by auto
    thus  "D\<union>{selector} \<subseteq> dom X1" using C5 tarski_def_1b by auto        
  qed   
  show "for X1 be Fields\<bar> (#selector \<rightarrow>?Spec#)\<parallel>Function holds  X1| (D\<union>{selector}) is Fields\<bar>(#selector \<rightarrow>?Spec#)"
  proof(rule ballI)
    fix X1 assume C1: "X1 be Fields\<bar>(#selector \<rightarrow>?Spec#)\<parallel>Function"  
    hence T0:"X1 be Relation" by simp
    hence T1: "X1|(D\<union>{selector}) be Relation" "X1|D be Relation" 
      using relat_1_def_11[of X1,THEN conjunct1,THEN conjunct1] all_set by auto
    hence T2: "X1| (D\<union>{selector}) is Function_like"  
      using funct_1_cl[of "D\<union>{selector}" X1,rule_format,OF all_set] C1   by auto
    hence "X1| D is Function_like"
       using funct_1_cl[of D X1,rule_format,OF all_set] C1  by auto   
    hence C2: "X1| (D\<union>{selector}) be Function" "X1|D be Function" 
       using T2 T1 by auto
    have C5: "D \<subseteq> dom X1" using A0(3) C1 by auto
    hence C3:"X1|D be Fields\<parallel>Function" using A0(3) C1 C2 by auto
    have "dom (X1|D) = (dom X1)\<inter> D" using relat_1_th_55 T0 all_set by auto  
    hence C4: "D \<subseteq> dom (X1|D)" using C5 by auto    
    have "X1|D \<subseteq> X1| (D\<union>{selector})" using relat_1_th75[of X1 "D\<union>{selector}" D,OF _ all_set all_set] C1 by auto
    hence C6: "X1| (D\<union>{selector}) is Fields"  using  C2 C3 A0(2)[rule_format, OF C3 C2(1) C4]  by auto  
    have "selector_1 in dom X1" "selector_1 in (D\<union>{selector})" 
         "selector_2 in dom X1" "selector_2 in (D\<union>{selector})" 
         "selector_3 in dom X1" "selector_3 in (D\<union>{selector})" using assms(2,3,4) C5 by auto
    hence "the selector_1 of X1 = the selector_1 of (X1|(D \<union> {selector}))" 
          "the selector_2 of X1 = the selector_2 of (X1|(D \<union> {selector}))" 
          "the selector_3 of X1 = the selector_3 of (X1|(D \<union> {selector}))" 
      using C1 the_selector_of_restriction[of X1 selector_1 "D\<union>{selector}"]
               the_selector_of_restriction[of X1 selector_2 "D\<union>{selector}"] 
               the_selector_of_restriction[of X1 selector_3 "D\<union>{selector}"] by auto 
    hence "X1| (D\<union>{selector}) is (#selector \<rightarrow>?Spec#)" using fields_restriction[of X1 "selector" "?Spec" "D\<union>{selector}"]
       C1 tarski_def_1b by auto
    thus "X1| (D\<union>{selector}) is Fields\<bar>(#selector \<rightarrow>?Spec#)" using C6 by simp
  qed          
qed  

theorem well_defined_order_1:
  assumes "\<And>X. X is Fields1 iff X is Fields2"
          "D1=D2"  
          "Fields1 well defined on D1"
 shows  "Fields2 well defined on D2"
proof(unfold  struct_well_defined_def,intro conjI)
    show "ex X be Function st X is Fields2 & dom X=D2" using assms struct_well_defined_def by auto
    show "for X1 be Fields2\<parallel>Function, X2 be Function st D2 \<subseteq> dom X1 & X1 \<subseteq> X2 holds X2 is Fields2"
      using assms  struct_well_defined_def by auto 
    show "for X1 be Fields2\<parallel>Function holds D2 \<subseteq> dom X1 " using assms  struct_well_defined_def by auto 
    show "for X1 be Fields2\<parallel>Function holds X1|D2 is Fields2" using assms  struct_well_defined_def by auto 
  qed  
    
text_raw \<open>\DefineSnippet{WellOrder}{\<close>     
theorem well_defined_order:
  assumes "\<And>X. X is Fields1 iff X is Fields2"           
     and "Fields1 well defined on D1"
  shows "Fields2 well defined on D1"
text_raw \<open>}%EndSnippet\<close>

proof(unfold  struct_well_defined_def,intro conjI)
    show "ex X be Function st X is Fields2 & dom X=D1" using assms  struct_well_defined_def by auto
    show "for X1 be Fields2\<parallel>Function, X2 be Function st D1 \<subseteq> dom X1 & X1 \<subseteq> X2 holds X2 is Fields2"
      using assms  struct_well_defined_def by auto 
    show "for X1 be Fields2\<parallel>Function holds D1 \<subseteq> dom X1" using assms  struct_well_defined_def by auto 
    show "for X1 be Fields2\<parallel>Function holds X1|D1 is Fields2" using assms  struct_well_defined_def by auto 
qed     
   
  
text_raw \<open>\DefineSnippet{struct}{\<close>
abbreviation(input) struct ("struct _ _ " [10,10] 10)
  where "struct Name Fields \<equiv> 
     (Name \<equiv> define_mode(\<lambda>it.
       it be Function & it is Fields))"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{structScheme}{\<close>
lemma struct_scheme:
assumes df:
   "S \<equiv> define_mode(\<lambda>it. it be Function & it is Fields)"
 and ex:
   "ex X be Function st X is Fields & dom X = D"
 and monotone: "for X1 be Function st X1 is Fields
              holds D \<subseteq> dom X1"
 and restriction: "for X1 be Function st X1 is Fields
              holds (X1|D) is Fields"
shows "(x be S iff (x be Function & x is Fields)) & 
       Ex (\<lambda>x. x be S) & (domain_of S) = D &
       (for X be S holds
          (the_restriction_of X to S) be (strict S) \<parallel> S)"
text_raw \<open>}%EndSnippet\<close>
proof(intro conjI)
   have S1:"\<And> x. x be S iff (x be Function & x is Fields)"
       "Ex (\<lambda>x. x be S)"
   using defmode_property[of S "\<lambda>it.(it be Function & it is Fields)",OF df ] ex by auto
   obtain X where
     func: "X be Function" and
     fields: "X is Fields" and
     dom:   "dom X=D" using ex by blast
   show "x be S iff (x be Function & x is Fields)"
       "Ex (\<lambda>x. x be S)" using S1 by auto
   have A1:"X be S" using S1 func fields by auto 
   let ?P="\<lambda>it. (ex X be S st it = dom X) & 
            (for X be S holds it \<subseteq> dom X)"
   let ?D = "domain_of S"
   have "?D be set & ?P(?D) & (x be set & ?P(x) implies x = ?D)"
    proof(induct rule: means_property[OF domain_of_def, case_names existence uniqueness])
       case existence  
         show "ex x be set st ?P(x)"
             proof(rule bexI[of _ D],intro conjI)
               show "ex X be S st D=dom X" using A1 dom by auto
               show "for X be S holds D \<subseteq> dom X" using monotone S1 by auto
               show "D be set" using all_set by simp
             qed
        case uniqueness 
      show "\<And>x y. x be set \<Longrightarrow>
          y be set \<Longrightarrow> ?P(x) \<Longrightarrow> ?P(y) \<Longrightarrow>x=y" 
        proof-
          fix x y
          assume A2:"x be set" "y be set" "?P(x)" "?P(y)"
          then obtain X1 where
            A3: "X1 be S" "x = dom X1" by auto
          obtain X2 where
            A4: "X2 be S" "y = dom X2" using A2 by auto
          have "x \<subseteq> y" "y \<subseteq> x" using A2(3)[THEN conjunct2,rule_format,of X2,OF A4(1)] A2(4)[THEN conjunct2,rule_format,of X1,OF A3(1)] A3 A4
             by auto
          thus "x=y" using A2(1,2) xboole_0_def_10 by simp           
        qed
    qed
   hence A2:"?P(?D)" by iprover
   then obtain X1 where
     A3:"X1 be S" "?D=dom X1" by auto
   hence "X1 be Function" "X1 is Fields" using S1 by auto
   hence  "D c= dom X1" "dom X1 c= D" using monotone A2[THEN conjunct2,rule_format,of X,OF A1] dom A3 by auto
   thus A4: "?D = D" using A3(2) xboole_0_def_10[of D "dom X1",simplified all_set] by auto
   show "for X be S holds (the_restriction_of X to S) be (strict S) \<parallel> S"
    proof(rule ballI)
      fix X1
      assume B0: "X1 be S"
      hence B1: "X1 be Function" "X1 is Fields" "?D be set" using S1 all_set by simp+
      hence B: "X1 be Relation" by simp
      have B2: "X1|?D be Relation" "X1|?D is Function_like" using relat_1_def_11[of X1 "?D", OF B B1(3),THEN conjunct1] 
         funct_1_cl[OF conjI[OF B1(3,1)]] by auto 
      have "X1|?D is Fields" using restriction B1(1,2) A4 by simp
      hence B3: "X1|?D be S" using S1 B2 by simp
      have "?D \<subseteq> dom X1" using A2[THEN conjunct2] B0 by auto      
      hence "dom (X1|?D) = ?D" using relat_1_th_56[of X1 ?D] all_set B1 by auto
      hence "X1|?D be (strict S) \<parallel> S" using B3 strict by simp    
      thus "(the_restriction_of X1 to S) be (strict S) \<parallel> S"
         using equals_property[OF  the_restriction_of_def] by auto 
    qed
qed
  
theorem Equal_strict:
  assumes "A1 be Function" "A2 be Function"
          "A1 is strict M" "A2 is strict M"
          "\<And>selector. selector in domain_of M \<Longrightarrow>
             the selector of A1 = the selector of A2"   
  shows "A1=A2"
proof
  show "A1 be set" "A2 be set" using all_set by auto
  have D: "dom A1 = domain_of M" "dom A2 = domain_of M"
     using assms strict by auto
  fix x
  show "x in A1 iff x in A2"  
    proof(rule iffI3)
      show "x in A1 implies x in A2"
      proof
        assume A0: "x in A1"
        then obtain a b where
          A1: "a be object" "b be object" "x=[a,b]" 
          using relat_1_def_1a assms(1) by auto
        hence A2: "the a of A1 = b" using the_selector_of_1 A0 assms(1) by auto
        have A3: "a in dom A1" using A0 A1 xtuple_0_def_12 assms(1) by auto
        hence "a in dom A2" using D by auto
        hence A4: "[a,A2. a] in A2" 
          using assms(2) funct_1_th_1[of A2 "A2. a"] by auto
        hence "the a of A2 = A2. a" using the_selector_of_1 A0 assms(2) 
           by auto
        thus "x in A2" using A1 A2 A3 assms(5) D A4 by auto
      qed
        assume A0: "x in A2"
        then obtain a b where
          A1: "a be object" "b be object" "x=[a,b]" 
          using relat_1_def_1a assms(2) by auto
        hence A2: "the a of A2 = b" using the_selector_of_1 A0 assms(2) by auto
        have A3: "a in dom A2" using A0 A1 xtuple_0_def_12 assms(2) by auto
        hence "a in dom A1" using D by auto
        hence A4: "[a,A1. a] in A1" 
          using assms(1) funct_1_th_1[of A1 "A1. a"] by auto
        hence "the a of A1 = A1. a" using the_selector_of_1 A0 assms(1) 
           by auto
        thus "x in A1" using A1 A2 A3 assms(5) D A4 by auto
      qed  
qed          
  
  
text_raw \<open>\DefineSnippet{structSchemeWell}{\<close>  
lemma struct_well_defined:
assumes df: 
  "S \<equiv> define_mode(\<lambda>it. it be Function & it is Fields)"
 and well: "Fields well defined on D"  
shows "(x be S iff (x be Function & x is Fields)) & 
    Ex (\<lambda>x. x be S) & domain_of S = D &
    (for X be S holds
       (the_restriction_of X to S) be (strict S) \<parallel> S)"
text_raw \<open>}%EndSnippet\<close>
proof-
  have A0: "ex X be Function st X is Fields & dom X=D"
            (*"for X1 be Fields\<parallel>Function, X2 be Function st D \<subseteq> dom X1 & X1 \<subseteq> X2 holds X2 is Fields"*)
            "for X1 be Fields\<parallel>Function holds D \<subseteq> dom X1 & X1|D is Fields" using struct_well_defined_def well by auto 
  have monotone: "\<And> X1. X1 be Function & X1 is Fields implies D \<subseteq> dom X1" using A0(2) by auto 
  have restriction: "\<And> X1. X1 be Function & X1 is Fields implies X1|D is Fields" using A0(2) by auto
  thus ?thesis using  monotone struct_scheme[OF df A0(1),of x] by auto    
qed
  
theorem Function_1:
  "{[s,D]} be Function" using funct_1_cl_3 relat_1_cl_7 by simp

theorem Function_2:
  "s1 <> s2 \<Longrightarrow> ({[s1,D1]} \<union> {[s2,D2]}) be Function"
proof-
  assume A1:"s1<>s2"
  let ?F1 = "{[s1,D1]}"
  let ?F2 = "{[s2,D2]}"
  have "for x,y1,y2 being object st [x,y1] in ?F1\<union>?F2 & [x,y2] in ?F1\<union>?F2 holds y1 = y2"
     proof(intro ballI impI)
       fix x y1 y2
       assume "[x , y1] in ?F1\<union>?F2 & [x , y2] in ?F1\<union>?F2"
       hence "[x,y1] in ?F1 or [x , y1] in ?F2" "[x , y2] in ?F1 or [x , y2] in ?F2" using xboole_0_def_3 by auto
       hence  "[x,y1] = [s1,D1] or [x,y1] =[s2,D2]"  "[x,y2] = [s1,D1] or [x,y2] =[s2,D2]" using tarski_def_1 by simp+
       hence "(x=s1 & y1=D1) or (x=s2 & y1=D2)" "(x=s1 & y2=D1) or (x=s2 & y2=D2)" 
          using  xtuple_0_th_1[of x y1 s1 D1] xtuple_0_th_1[of x y1 s2 D2] 
                 xtuple_0_th_1[of x y2 s1 D1] xtuple_0_th_1[of x y2 s2 D2] by auto
       thus  "y1=y2" using A1 by auto
     qed
  hence A: "(?F1 \<union> ?F2) is Function_like" using funct_1_def_1 by simp
  have "(?F1 \<union> ?F2) is Relation_like" using relat_1_cl_7 relat_1_cl_5[of ?F1 ?F2] by simp
  thus "(?F1 \<union> ?F2) be Function" using A by simp
qed

theorem Function_3:
  "s1 <> s2 & s1<>s3 & s2<>s3 \<Longrightarrow> ({[s1,D1]} \<union> {[s2,D2]} \<union> {[s3,D3]}) be Function"
proof-
  assume A1:"s1<>s2 & s1<>s3 & s2<>s3"
  let ?F1 = "{[s1,D1]}"
  let ?F2 = "{[s2,D2]}"
  let ?F3 = "{[s3,D3]}"
  have "for x,y1,y2 being object st [x,y1] in ?F1\<union>?F2\<union>?F3 & [x,y2] in ?F1\<union>?F2\<union>?F3 holds y1 = y2"
     proof(intro ballI impI)
       fix x y1 y2
       assume "[x , y1] in ?F1\<union>?F2\<union>?F3 & [x , y2] in ?F1\<union>?F2\<union>?F3"
       hence "[x,y1] in ?F1 or [x , y1] in ?F2 or [x , y1] in ?F3" "[x , y2] in ?F1 or [x , y2] in ?F2 or [x , y2] in ?F3" using xboole_0_def_3 by auto
       hence  "[x,y1] = [s1,D1] or [x,y1] =[s2,D2] or [x,y1] =[s3,D3]"  "[x,y2] = [s1,D1] or [x,y2] =[s2,D2]or [x,y2] =[s3,D3]" 
           using tarski_def_1 by simp+
       hence "(x=s1 & y1=D1) or (x=s2 & y1=D2)or (x=s3 & y1=D3)" "(x=s1 & y2=D1) or (x=s2 & y2=D2) or (x=s3 & y2=D3)"
          using  xtuple_0_th_1[of x y1 s1 D1] xtuple_0_th_1[of x y1 s2 D2] xtuple_0_th_1[of x y1 s3 D3] 
                 xtuple_0_th_1[of x y2 s1 D1] xtuple_0_th_1[of x y2 s2 D2] xtuple_0_th_1[of x y2 s3 D3]  by auto
       thus  "y1=y2" using A1 by auto
     qed
  hence A: "(?F1 \<union> ?F2 \<union> ?F3) is Function_like" using funct_1_def_1 by simp
  have "(?F1 \<union> ?F2 \<union> ?F3) is Relation_like" using relat_1_cl_7 relat_1_cl_5[of ?F1 ?F2] relat_1_cl_5[of "?F1\<union>?F2" ?F3] by simp
  thus "(?F1 \<union> ?F2 \<union> ?F3) be Function" using A by auto
qed

theorem Function_4:
  "s1 <> s2 & s1<>s3 & s1<> s4 & s2<>s3 & s2<>s4 & s3<>s4 \<Longrightarrow> ({[s1,D1]} \<union> {[s2,D2]} \<union> {[s3,D3]}\<union>{[s4,D4]}) be Function"
proof-
  assume A1:"s1 <> s2 & s1<>s3 & s1<> s4 & s2<>s3 & s2<>s4 & s3<>s4"
  let ?F1 = "{[s1,D1]}"
  let ?F2 = "{[s2,D2]}"
  let ?F3 = "{[s3,D3]}"
  let ?F4 = "{[s4,D4]}"
  have "for x,y1,y2 being object st [x,y1] in ?F1\<union>?F2\<union>?F3\<union>?F4 & [x,y2] in ?F1\<union>?F2\<union>?F3\<union>?F4 holds y1 = y2"
     proof(intro ballI impI)
       fix x y1 y2
       assume "[x , y1] in ?F1\<union>?F2\<union>?F3\<union>?F4 & [x , y2] in ?F1\<union>?F2\<union>?F3\<union>?F4"
       hence "[x,y1] in ?F1 or [x , y1] in ?F2 or [x , y1] in ?F3 or [x , y1] in ?F4" 
             "[x , y2] in ?F1 or [x , y2] in ?F2 or [x , y2] in ?F3 or [x , y2] in ?F4" using xboole_0_def_3 by auto
       hence  "[x,y1] = [s1,D1] or [x,y1] =[s2,D2] or [x,y1] =[s3,D3] or [x,y1] =[s4,D4]"  "[x,y2] = [s1,D1] or [x,y2] =[s2,D2]or [x,y2] =[s3,D3]or [x,y2] =[s4,D4]" 
           using tarski_def_1 by simp+
       hence "(x=s1 & y1=D1) or (x=s2 & y1=D2)or (x=s3 & y1=D3) or (x=s4 & y1=D4)" "(x=s1 & y2=D1) or (x=s2 & y2=D2) or (x=s3 & y2=D3)  or (x=s4 & y2=D4)"
          using  xtuple_0_th_1[of x y1 s1 D1] xtuple_0_th_1[of x y1 s2 D2] xtuple_0_th_1[of x y1 s3 D3] xtuple_0_th_1[of x y1 s4 D4] 
                 xtuple_0_th_1[of x y2 s1 D1] xtuple_0_th_1[of x y2 s2 D2] xtuple_0_th_1[of x y2 s3 D3] xtuple_0_th_1[of x y2 s4 D4] by auto
       thus  "y1=y2" using A1 by auto
     qed
  hence A: "(?F1 \<union> ?F2 \<union> ?F3\<union>?F4) is Function_like" using funct_1_def_1 by simp
  have "(?F1 \<union> ?F2 \<union> ?F3\<union>?F4) is Relation_like" using relat_1_cl_7 relat_1_cl_5[of ?F1 ?F2] relat_1_cl_5[of "?F1\<union>?F2" ?F3] 
     relat_1_cl_5[of "?F1\<union>?F2\<union>?F3" ?F4] by simp
  thus "(?F1 \<union> ?F2 \<union> ?F3\<union>?F4) be Function" using A by auto
qed  
  
theorem Function_5:
  "s1 <> s2 & s1<>s3 & s1<> s4 & s1<> s5 & s2<>s3 & s2<>s4 & s2<> s5 & s3<>s4 & s3<> s5 & s4<> s5 
       \<Longrightarrow> ({[s1,D1]} \<union> {[s2,D2]} \<union> {[s3,D3]}\<union>{[s4,D4]}\<union>{[s5,D5]}) be Function"
proof-
  assume A1:"s1 <> s2 & s1<>s3 & s1<> s4 & s1<> s5 & s2<>s3 & s2<>s4 & s2<> s5 & s3<>s4 & s3<> s5 & s4<> s5"
  let ?F1 = "{[s1,D1]}"
  let ?F2 = "{[s2,D2]}"
  let ?F3 = "{[s3,D3]}"
  let ?F4 = "{[s4,D4]}"
  let ?F5 = "{[s5,D5]}"
  have "for x,y1,y2 being object st [x,y1] in ?F1\<union>?F2\<union>?F3\<union>?F4\<union>?F5 & [x,y2] in ?F1\<union>?F2\<union>?F3\<union>?F4\<union>?F5 holds y1 = y2"
     proof(intro ballI impI)
       fix x y1 y2
       assume "[x , y1] in ?F1\<union>?F2\<union>?F3\<union>?F4\<union>?F5 & [x , y2] in ?F1\<union>?F2\<union>?F3\<union>?F4\<union>?F5"
       hence "[x,y1] in ?F1 or [x , y1] in ?F2 or [x , y1] in ?F3 or [x , y1] in ?F4 or [x , y1] in ?F5" 
             "[x , y2] in ?F1 or [x , y2] in ?F2 or [x , y2] in ?F3 or [x , y2] in ?F4  or [x , y2] in ?F5" using xboole_0_def_3 by auto
       hence  "[x,y1] = [s1,D1] or [x,y1] =[s2,D2] or [x,y1] =[s3,D3] or [x,y1] =[s4,D4] or [x,y1] =[s5,D5]"  
               "[x,y2] = [s1,D1] or [x,y2] =[s2,D2]or [x,y2] =[s3,D3]or [x,y2] =[s4,D4] or [x,y2] =[s5,D5]" 
           using tarski_def_1 by simp+
         hence "(x=s1 & y1=D1) or (x=s2 & y1=D2)or (x=s3 & y1=D3) or (x=s4 & y1=D4) or (x=s5 & y1=D5)" 
                "(x=s1 & y2=D1) or (x=s2 & y2=D2) or (x=s3 & y2=D3)  or (x=s4 & y2=D4) or (x=s5 & y2=D5)"
          using  xtuple_0_th_1[of x y1 s1 D1] xtuple_0_th_1[of x y1 s2 D2] xtuple_0_th_1[of x y1 s3 D3] xtuple_0_th_1[of x y1 s4 D4] xtuple_0_th_1[of x y1 s5 D5] 
                 xtuple_0_th_1[of x y2 s1 D1] xtuple_0_th_1[of x y2 s2 D2] xtuple_0_th_1[of x y2 s3 D3] xtuple_0_th_1[of x y2 s4 D4] xtuple_0_th_1[of x y2 s5 D5] 
             by auto
       thus  "y1=y2" using A1 by auto
     qed
  hence A: "(?F1 \<union> ?F2 \<union> ?F3\<union>?F4\<union>?F5) is Function_like" using funct_1_def_1 by simp
  have "(?F1 \<union> ?F2 \<union> ?F3\<union>?F4\<union>?F5) is Relation_like" using relat_1_cl_7 relat_1_cl_5[of ?F1 ?F2] relat_1_cl_5[of "?F1\<union>?F2" ?F3] 
     relat_1_cl_5[of "?F1\<union>?F2\<union>?F3" ?F4] relat_1_cl_5[of "?F1\<union>?F2\<union>?F3\<union>?F4" ?F5] by simp
  thus "(?F1 \<union> ?F2 \<union> ?F3\<union>?F4\<union>?F5) be Function" using A by auto
qed   
  
theorem Function_6:
  "s1 <> s2 & s1<>s3 & s1<> s4 & s1<> s5 & s1<>s6 & 
              s2<>s3 & s2<>s4 & s2<> s5 & s2<>s6 & 
             s3<>s4 & s3<> s5 & s3<>s6 & s4<> s5 & s4<>s6 & s5<>s6 
       \<Longrightarrow> ({[s1,D1]} \<union> {[s2,D2]} \<union> {[s3,D3]}\<union>{[s4,D4]}\<union>{[s5,D5]}\<union>{[s6,D6]}) be Function"
proof-
  assume A1:"s1 <> s2 & s1<>s3 & s1<> s4 & s1<> s5 & s1<>s6 & 
              s2<>s3 & s2<>s4 & s2<> s5 & s2<>s6 & 
             s3<>s4 & s3<> s5 & s3<>s6 & s4<> s5 & s4<>s6 & s5<>s6"
  let ?F1 = "{[s1,D1]}"
  let ?F2 = "{[s2,D2]}"
  let ?F3 = "{[s3,D3]}"
  let ?F4 = "{[s4,D4]}"
  let ?F5 = "{[s5,D5]}"
   let ?F6 = "{[s6,D6]}"
  have "for x,y1,y2 being object st [x,y1] in ?F1\<union>?F2\<union>?F3\<union>?F4\<union>?F5\<union>?F6 & [x,y2] in ?F1\<union>?F2\<union>?F3\<union>?F4\<union>?F5\<union>?F6 holds y1 = y2"
     proof(intro ballI impI)
       fix x y1 y2
       assume "[x , y1] in ?F1\<union>?F2\<union>?F3\<union>?F4\<union>?F5\<union>?F6 & [x , y2] in ?F1\<union>?F2\<union>?F3\<union>?F4\<union>?F5\<union>?F6"
       hence "[x,y1] in ?F1 or [x , y1] in ?F2 or [x , y1] in ?F3 or [x , y1] in ?F4 or [x , y1] in ?F5 or [x , y1] in ?F6" 
             "[x , y2] in ?F1 or [x , y2] in ?F2 or [x , y2] in ?F3 or [x , y2] in ?F4  or [x , y2] in ?F5  or [x , y2] in ?F6" 
            using xboole_0_def_3 by auto
       hence  "[x,y1] = [s1,D1] or [x,y1] =[s2,D2] or [x,y1] =[s3,D3] or [x,y1] =[s4,D4] or [x,y1] =[s5,D5] or [x,y1] =[s6,D6]"  
               "[x,y2] = [s1,D1] or [x,y2] =[s2,D2]or [x,y2] =[s3,D3]or [x,y2] =[s4,D4] or [x,y2] =[s5,D5] or [x,y2] =[s6,D6]" 
           using tarski_def_1 by simp+
         hence "(x=s1 & y1=D1) or (x=s2 & y1=D2)or (x=s3 & y1=D3) or (x=s4 & y1=D4) or (x=s5 & y1=D5) or (x=s6 & y1=D6)" 
                "(x=s1 & y2=D1) or (x=s2 & y2=D2) or (x=s3 & y2=D3)  or (x=s4 & y2=D4) or (x=s5 & y2=D5)  or (x=s6 & y2=D6)"
           using  xtuple_0_th_1[of x y1 s1 D1] xtuple_0_th_1[of x y1 s2 D2] xtuple_0_th_1[of x y1 s3 D3] xtuple_0_th_1[of x y1 s4 D4] xtuple_0_th_1[of x y1 s5 D5] 
             xtuple_0_th_1[of x y1 s6 D6]
                 xtuple_0_th_1[of x y2 s1 D1] xtuple_0_th_1[of x y2 s2 D2] xtuple_0_th_1[of x y2 s3 D3] xtuple_0_th_1[of x y2 s4 D4] xtuple_0_th_1[of x y2 s5 D5]
             xtuple_0_th_1[of x y2 s6 D6]    
             by auto
       thus  "y1=y2" using A1 by auto
     qed
  hence A: "(?F1 \<union> ?F2 \<union> ?F3\<union>?F4\<union>?F5\<union>?F6) is Function_like" using funct_1_def_1 by simp
  have "(?F1 \<union> ?F2 \<union> ?F3\<union>?F4\<union>?F5\<union>?F6) is Relation_like" using relat_1_cl_7 relat_1_cl_5[of ?F1 ?F2] relat_1_cl_5[of "?F1\<union>?F2" ?F3] 
     relat_1_cl_5[of "?F1\<union>?F2\<union>?F3" ?F4] relat_1_cl_5[of "?F1\<union>?F2\<union>?F3\<union>?F4" ?F5] relat_1_cl_5[of "?F1\<union>?F2\<union>?F3\<union>?F4\<union>?F5" ?F6] by simp
  thus "(?F1 \<union> ?F2 \<union> ?F3\<union>?F4\<union>?F5\<union>?F6) be Function" using A by auto
qed     
  


theorem Dom_1:
  "dom {[s,D]}={s}"
proof-
  have "{[s,D]} be Relation" using relat_1_cl_7 by simp
  thus ?thesis using relat_1_th_3[of D s "{[s,D]}"] by auto
qed

theorem Dom_2:
  "dom ({[s1,D1]} \<union> {[s2,D2]}) = {s1}\<union>{s2}"
proof-
  have A1:"{[s1,D1]} be Relation & {[s2,D2]} be Relation" using relat_1_cl_7 by simp
  have "({[s1,D1]} \<union> {[s2,D2]}) be Relation" using relat_1_cl_5[OF A1] by auto
  hence "dom ({[s1,D1]} \<union> {[s2,D2]}) = (dom {[s1,D1]}) \<union> (dom {[s2,D2]})" using xtuple_th_23 relat_1_def_1a by simp
  thus ?thesis using Dom_1 by auto
qed
  
theorem Dom_3:
  "dom ({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) = {s1}\<union>{s2}\<union>{s3}"
proof-
  have A2:"{[s1,D1]} be Relation & {[s2,D2]} be Relation" using relat_1_cl_7 by simp
    have A3: "({[s1,D1]} \<union> {[s2,D2]}) be Relation &  {[s3,D3]} be Relation" using relat_1_cl_7 relat_1_cl_5[OF A2] by simp
  have A4: "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) be Relation" using  relat_1_cl_7 relat_1_cl_5[OF A3] by simp
  hence "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) be Relation" using relat_1_cl_5[of "{[s1,D1]} \<union> {[s2,D2]}" "{[s3,D3]}"] by simp
  hence "dom ({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) = (dom ({[s1,D1]}\<union>{[s2,D2]})) \<union> (dom {[s3,D3]})" using xtuple_th_23 relat_1_def_1a by simp
  thus ?thesis using Dom_1 Dom_2 by auto
qed 
  
theorem Dom_4:
  "dom ({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}) = {s1}\<union>{s2}\<union>{s3}\<union>{s4}"
proof-
  have A2:"{[s1,D1]} be Relation & {[s2,D2]} be Relation" using relat_1_cl_7 by simp
  have A3: "({[s1,D1]} \<union> {[s2,D2]}) be Relation &  {[s3,D3]} be Relation" using relat_1_cl_7 relat_1_cl_5[OF A2] by simp
   have A4: "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) be Relation &  {[s4,D4]} be Relation " using  relat_1_cl_7 relat_1_cl_5[OF A3] by simp
  have A5: "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}) be Relation " using  relat_1_cl_7 relat_1_cl_5[OF A4] by simp     
  hence "dom ({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}) = (dom ({[s1,D1]}\<union>{[s2,D2]}\<union>{[s3,D3]})) \<union> (dom {[s4,D4]})" using xtuple_th_23 relat_1_def_1a by simp
  thus ?thesis using Dom_1 Dom_3 by auto
qed

  
theorem Dom_5:
  "dom ({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}\<union>{[s5,D5]}) = {s1}\<union>{s2}\<union>{s3}\<union>{s4}\<union>{s5}"
proof-
  have A2:"{[s1,D1]} be Relation & {[s2,D2]} be Relation" using relat_1_cl_7 by simp
    have A3: "({[s1,D1]} \<union> {[s2,D2]}) be Relation &  {[s3,D3]} be Relation" using relat_1_cl_7 relat_1_cl_5[OF A2] by simp
  have A4: "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) be Relation &  {[s4,D4]} be Relation " using  relat_1_cl_7 relat_1_cl_5[OF A3] by simp
  have A5: "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}) be Relation &  {[s5,D5]} be Relation " using  relat_1_cl_7 relat_1_cl_5[OF A4] by simp
  have A5: "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}\<union>{[s5,D5]}) be Relation " using  relat_1_cl_7 relat_1_cl_5[OF A5] by simp
  hence "dom ({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}\<union>{[s5,D5]}) = (dom ({[s1,D1]}\<union>{[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]})) \<union> (dom {[s5,D5]})" 
    using xtuple_th_23 relat_1_def_1a by simp
  thus ?thesis using Dom_1 Dom_4 by auto
qed
  
theorem Dom_6:
  "dom ({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}\<union>{[s5,D5]}\<union>{[s6,D6]}) = {s1}\<union>{s2}\<union>{s3}\<union>{s4}\<union>{s5}\<union>{s6}"
proof-
  have A2:"{[s1,D1]} be Relation & {[s2,D2]} be Relation" using relat_1_cl_7 by simp
    have A3: "({[s1,D1]} \<union> {[s2,D2]}) be Relation &  {[s3,D3]} be Relation" using relat_1_cl_7 relat_1_cl_5[OF A2] by simp
  have A4: "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) be Relation &  {[s4,D4]} be Relation " using  relat_1_cl_7 relat_1_cl_5[OF A3] by simp
  have A5: "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}) be Relation &  {[s5,D5]} be Relation " using  relat_1_cl_7 relat_1_cl_5[OF A4] by simp
  have A6: "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}\<union>{[s5,D5]}) be Relation &  {[s6,D6]} be Relation " using  relat_1_cl_7 relat_1_cl_5[OF A5] by simp
  have A6: "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}\<union>{[s5,D5]}\<union>{[s6,D6]}) be Relation" using  relat_1_cl_7 relat_1_cl_5[OF A6] by simp
  hence "dom ({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}\<union>{[s5,D5]}\<union>{[s6,D6]}) = (dom ({[s1,D1]}\<union>{[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}\<union>{[s5,D5]})) \<union> (dom {[s6,D6]})" 
    using xtuple_th_23 relat_1_def_1a by simp
  thus ?thesis using Dom_1 Dom_5 by auto
qed

(*
theorem monotone_1:
  "X is (#s1\<rightarrow>Typ1#) \<Longrightarrow> {s1} \<subseteq> dom X" using field by auto

theorem monotone_2:
  "X is (#s1\<rightarrow>Typ1;s2\<rightarrow>Typ2 #) \<Longrightarrow> {s1}\<union>{s2} \<subseteq> dom X" using field by auto

theorem monotone_3:
  "X is (#s1\<rightarrow>Typ1;s2\<rightarrow>Typ2;s3\<rightarrow>Typ3 #) \<Longrightarrow> {s1}\<union>{s2}\<union>{s3} \<subseteq> dom X" using field by auto

theorem monotone_4:
  "X is (#s1\<rightarrow>Typ1;s2\<rightarrow>Typ2;s3\<rightarrow>Typ3;s4\<rightarrow>Typ4 #) \<Longrightarrow> {s1}\<union>{s2}\<union>{s3}\<union>{s4} \<subseteq> dom X" using field by auto    
 
theorem monotone_5:
  "X is (#s1\<rightarrow>Typ1;s2\<rightarrow>Typ2;s3\<rightarrow>Typ3;s4\<rightarrow>Typ4;s5\<rightarrow>Typ5 #) \<Longrightarrow> {s1}\<union>{s2}\<union>{s3}\<union>{s4}\<union>{s5} \<subseteq> dom X" using field by auto    
*)    

(**strings**)

end