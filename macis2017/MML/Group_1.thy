\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Group_1
  imports Algstr_0
begin

text_raw \<open>\DefineSnippet{group1def1}{\<close>
definition unital_prefix :: "Attr" ("unital") 
  where group_1_def_1 [THEN defattr_property]:
   "attr unital means 
      (\<lambda>S. (S be multMagma) & 
        (ex e being Element-of-struct S st
            for h being (Element-of-struct S) holds 
              ( h \<otimes>\<^sub>S e = h  &  e  \<otimes>\<^sub>S h = h ) ))"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{group1def2}{\<close>
definition Group_like_prefix :: "Attr" ("Group-like") 
  where group_1_def_2 [THEN defattr_property]:
   "attr Group-like means 
      (\<lambda>S. S be multMagma & 
          (ex e being Element-of-struct S st 
            for h being Element-of-struct S holds 
              h  \<otimes>\<^sub>S e = h & e \<otimes>\<^sub>S h = h & 
              (ex g being Element-of-struct S st 
                 h  \<otimes>\<^sub>S g = e & g \<otimes>\<^sub>S h = e ) ))"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{group1def3}{\<close>
definition associative_prefix :: "Attr" ("associative") 
  where group_1_def_3 [THEN defattr_property,rule_format]:
   "attr associative means 
      (\<lambda> S. S be multMagma & 
            (for x,y,z being (Element-of-struct S) holds 
                  x \<otimes>\<^sub>S y \<otimes>\<^sub>S z =  x \<otimes>\<^sub>S ( y \<otimes>\<^sub>S  z)))"
text_raw \<open>}%EndSnippet\<close> 

lemmas group_1_def_3a = group_1_def_3[THEN iffD1,THEN conjunct2,rule_format]

theorem group_1_cl_2:
  "cluster ( strict multMagma \<bar> (Group-like \<bar> (associative \<bar>  (non empty-struct))))
           for multMagma"
proof-
    obtain x where "x=the set" by simp
    obtain B where B_def:"B={[ [x,x], x]}" by simp
    have "B is Function_like" "B is Relation_like" using B_def funct_1_cl_3 relat_1_cl_7 by simp+
    hence B1: "B be Function" using all_set by simp
    hence "dom B=[:{x},{x}:]" "rng B = {x}" using relat_1_th_3[of x "[x,x]" B] zfmisc_1_th_28 B_def by simp+
    hence B2: "B be BinOp-of {x}" using funct_2_th_2[of B,OF B1] binop_1_mode_2_def by auto
    obtain X where X_def:"X= {[carrier,{x}]}\<union>{[multF,B]}" by simp
    have "carrier <> multF" by (simp add:string) 
    hence S1: "X be Function" using Function_2[of carrier multF "{x}"] X_def by auto  
    have S2: "X is carrier \<rightarrow>set'" using Field_1[of X carrier "{x}" ] all_set S1 X_def tarski_def_1b by auto
    have C1: "the carrier of X = {x}" using the_selector_of_1[of X carrier "{x}",OF S1] X_def tarski_def_1b by auto
    have BB1: "the multF of X = B" using the_selector_of_1[of X multF B,OF S1] X_def tarski_def_1b by auto
    hence "X is multF \<rightarrow> BinOp-of' the' carrier" using Field_1[of X,OF S1,of multF B] B2 C1 X_def tarski_def_1b by auto
    hence S3:"X be multMagma" using multMagma S1 S2 by simp 
    have "dom X = {carrier}\<union>{multF}" using Dom_2 X_def by simp
    hence W1: "X is  strict multMagma" using S3 strict multMagma[THEN conjunct1,THEN conjunct2] by auto

    have F1: "for a,b being Element-of-struct X holds a  \<otimes>\<^sub>X  b = x"
    proof(intro ballI)
       fix a b
       assume T1: "a be (Element-of-struct X )" "b be (Element-of-struct X)"
       hence T2: "{x} be set & B be (BinOp-of {x}) & a be (Element-of {x}) & b be (Element-of {x})" using B2 C1 by auto+
       have S: "[[a,b],x] in B" using tarski_def_1b T2 B_def by auto
       have "a   \<otimes>\<^sub>X b =  B.  \<lparr> a , b \<rparr>"  using algstr_0_def_18[of _ a b] S3 T1 C1 BB1 by auto
       also have "... = B.[a,b]" using binop_0_def_1 B1 by simp
       also have "... = x" using funct_1_th_1[of B x "[a,b]",OF B1 ] S by simp
       finally show  "a  \<otimes>\<^sub>X b = x" by simp
    qed
    have W2: "X is Group-like" 
        proof (unfold group_1_def_2,intro conjI)
           show "X be multMagma" using S3 by simp
           show "ex e being Element-of-struct X st 
                                   for h being Element-of-struct X holds 
                                       h   \<otimes>\<^sub>X e = h & e   \<otimes>\<^sub>X h = h & 
                                        (ex g being Element-of-struct X st 
                                          h  \<otimes>\<^sub>X g = e & g    \<otimes>\<^sub>X h = e )"
           proof (rule bexI[of _ x], intro ballI)
              show X: "x be (Element-of-struct X)" using tarski_def_1b C1 by auto
              fix h
              assume T2: "h be (Element-of-struct X)"
              show " h \<otimes>\<^sub>X x = h & x \<otimes>\<^sub>X h = h & 
                                        (ex g being Element-of-struct X st 
                                          h  \<otimes>\<^sub>X g = x & g  \<otimes>\<^sub>X h = x )"
                 proof(intro conjI)
                     have XH: "x = h" using T2 subset_1_def_1 C1 tarski_def_1b by simp 
                     show " h  \<otimes>\<^sub>X x = h"  " x  \<otimes>\<^sub>X h = h" using F1 X T2 subset_1_def_1 C1 tarski_def_1b by simp+                    
                     thus "ex g being Element-of-struct X st 
                                          h  \<otimes>\<^sub>X g = x & g  \<otimes>\<^sub>X h = x" using XH X C1 tarski_def_1b by simp
                 qed
           qed
        qed
    have W3: "X is associative"
        proof(unfold group_1_def_3,intro conjI ballI)
          show "X be multMagma" using S3 by simp
          fix x1 y z
          assume T1: "x1 be (Element-of-struct X )" "y be (Element-of-struct X)"  "z be (Element-of-struct X)"
          have "( x1  \<otimes>\<^sub>X y ) \<otimes>\<^sub>X  z = x \<otimes>\<^sub>X  z" using T1 F1 by simp
          also have "... = x" using T1(3) F1 C1 tarski_def_1b by simp
          also have "... = x1 \<otimes>\<^sub>X x" using T1 F1 C1 tarski_def_1b by simp
          also have "... = x1 \<otimes>\<^sub>X ( y  \<otimes>\<^sub>X z)" using T1 F1 by simp
          finally
          show "( x1  \<otimes>\<^sub>X y )  \<otimes>\<^sub>X  z =  x1  \<otimes>\<^sub>X ( y \<otimes>\<^sub>X z)" by simp
        qed 
    have "X is non empty-struct" using C1 S3 multMagma_inheritance struct_0_def_1_b tarski_def_1b by simp
    hence "X is (strict multMagma)  \<bar>  (Group-like  \<bar>  (associative  \<bar>  non empty-struct))" using W1 W2 W3 S3 by auto
    thus ?thesis using S3 by auto
qed

text_raw \<open>\DefineSnippet{group1cl1}{\<close>
theorem group_1_cl_1[rule_format]:
  "cluster Group-like \<rightarrow> unital for multMagma"
text_raw \<open>}%EndSnippet\<close>
proof(rule ballI, rule impI)
  fix G 
  assume A1: "G be multMagma"
  assume A2: "G is Group-like"
  then obtain e where
    T1:"e be (Element-of-struct G)" and 
    A3: "for h being Element-of-struct G holds 
        h  \<otimes>\<^sub>G e = h & e \<otimes>\<^sub>G h = h & 
            (ex g being Element-of-struct G st 
            h \<otimes>\<^sub>G g = e & g  \<otimes>\<^sub>G h = e )" using group_1_def_2 A2 by auto
  have "for h being Element-of-struct G holds h \<otimes>\<^sub>G e = h & e \<otimes>\<^sub>G h = h" using A3 by simp
  thus "G is unital" using group_1_def_1 T1 A1 by auto
qed

text_raw \<open>\DefineSnippet{groupmode}{\<close>
abbreviation Group where 
   "Group \<equiv> Group-like \<bar> associative \<bar> non empty-struct \<parallel> multMagma"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{group1def4}{\<close>
definition group_1_def_4 ("1'.\<^sub>_" [1000] 99) where
  "assume G is unital
   func 1.\<^sub>G \<rightarrow> Element-of-struct G means \<lambda>it.
      for h being Element-of-struct G holds
         h \<otimes>\<^sub>G it = h & it \<otimes>\<^sub>G h = h"
text_raw \<open>}%EndSnippet\<close>

schematic_goal group_1_def_4:
  assumes "G be multMagma" shows "?X"
proof (induct rule: assume_means_property[OF group_1_def_4_def assms, of G,  case_names existence uniqueness coherence])
  case existence
   assume "G is unital"
   thus "ex it being Element-of-struct G st
         for h being  Element-of-struct G  holds  h \<otimes>\<^sub>G it  = h &  it \<otimes>\<^sub>G h  = h" using group_1_def_1 by auto
next
   case uniqueness
     assume "G is unital"
     fix  e1 e2 
     assume T0: "e1 be Element-of-struct G"
                "e2 be Element-of-struct G" and
    A2: "for h being Element-of-struct G holds h \<otimes>\<^sub>G e1 = h & e1 \<otimes>\<^sub>G h = h" and 
    A3: "for h being Element-of-struct G holds h \<otimes>\<^sub>G e2 = h & e2 \<otimes>\<^sub>G h = h"
    have "e1 = e1  \<otimes>\<^sub>G e2" using T0 A3 by simp
    also have "\<dots> = e2" using T0 A2 by simp
     finally show "e1=e2" .
 next
   case coherence
     have "(the carrier of G) be set" using assms multMagma_inheritance one_sorted field by simp
     hence "(the (Element-of-struct G)) be (Element-of-struct G)" 
           using subset_1_def_1[of "the carrier of G"] the_property by auto
     thus "ex x being (Element-of-struct G) st True" by auto
qed

text_raw \<open>\DefineSnippet{group1def5}{\<close>
definition group_1_def_5 (infix "\<^sup>-\<^sup>1\<^sub>" 105) where
  "func h\<^sup>-\<^sup>1\<^sub>G \<rightarrow> Element-of-struct G means \<lambda>it.
      h \<otimes>\<^sub>G it = 1.\<^sub>G & it \<otimes>\<^sub>G h = 1.\<^sub>G"
text_raw \<open>}%EndSnippet\<close>

schematic_goal group_1_def_5[rule_format]:
  assumes "G be Group & h be (Element-of-struct G)" shows "?X"

text_raw \<open>\DefineSnippet{proof}{\<close>    
proof (induct rule: means_property[OF group_1_def_5_def, 
   of G h, case_names existence uniqueness])
case existence
   have "G is Group-like" using assms by simp
   then obtain e where 
     T0:"e be Element-of-struct G" and
     A1:"for h being Element-of-struct G 
           holds h \<otimes>\<^sub>G e = h & e  \<otimes>\<^sub>G h = h &
         (ex g being Element-of-struct G st 
           h \<otimes>\<^sub>G g = e & g \<otimes>\<^sub>G h = e)" 
       using group_1_def_2 assms by auto 
   have "ex g being Element-of-struct G st 
     h \<otimes>\<^sub>G g = e & g \<otimes>\<^sub>G h = e" using A1 assms by blast
   then obtain g where 
T1: "g be Element-of-struct G" and
A2: "h  \<otimes>\<^sub>G g = e & g  \<otimes>\<^sub>G h = e" 
     using A1 T0 assms by auto
   have "G is unital" 
     using assms group_1_cl_1 A1 T0 by auto
   hence "e = 1.\<^sub>G" using group_1_def_4[of G e] 
     assms[THEN conjunct1] T0 A1 by auto
   thus "ex g being Element-of-struct G st 
     h \<otimes>\<^sub>G g = 1.\<^sub>G & g \<otimes>\<^sub>G h = 1.\<^sub>G" using T1 A2 by auto
 next
  case uniqueness
   fix x1 x2 
   assume T1: "x1 be Element-of-struct G"
          "x2 be Element-of-struct G" and
        A3:"h \<otimes>\<^sub>G x1 = 1.\<^sub>G & x1 \<otimes>\<^sub>G h = 1.\<^sub>G" and
        A4:"h \<otimes>\<^sub>G x2 = 1.\<^sub>G & x2 \<otimes>\<^sub>G h = 1.\<^sub>G"
   have "x1 = 1.\<^sub>G  \<otimes>\<^sub>G x1" using T1 group_1_def_4 
     assms group_1_cl_1 by simp
   also have "... = x2 \<otimes>\<^sub>G h \<otimes>\<^sub>G x1" using A4 assms by simp
   also have "... = x2 \<otimes>\<^sub>G (h \<otimes>\<^sub>G x1)" 
     using assms T1 group_1_def_3 by auto
   also have "... = x2" 
     using T1 group_1_def_4 assms A3 group_1_cl_1 by simp
   finally show "x1 = x2" by simp  
 qed
text_raw \<open>}%EndSnippet\<close>

reserve G for Group
text_raw \<open>\DefineSnippet{group1def5involutiveness}{\<close>
mtheorem group_1_def_5_involutiveness:
  "for h being Element-of-struct G holds (h\<^sup>-\<^sup>1\<^sub>G)\<^sup>-\<^sup>1\<^sub>G = h"
text_raw \<open>}%EndSnippet\<close>
proof(rule ballI)
  fix h
  assume T1:"h be Element-of-struct G"
  hence T2: "h\<^sup>-\<^sup>1\<^sub>G be Element-of-struct G" using assms group_1_def_5 by simp
  hence "(h\<^sup>-\<^sup>1\<^sub>G)   \<otimes>\<^sub>G  h = 1.\<^sub>G &  h  \<otimes>\<^sub>G  (h\<^sup>-\<^sup>1\<^sub>G) = 1.\<^sub>G" using assms T1 group_1_def_5 by auto
  thus " (h\<^sup>-\<^sup>1\<^sub>G)\<^sup>-\<^sup>1\<^sub>G = h" using T1 group_1_def_5[of G "h\<^sup>-\<^sup>1\<^sub>G" h,OF assms T2]  by auto
qed

text_raw \<open>\DefineSnippet{group1th5}{\<close>
theorem group_1_th_5:
  assumes "G be Group"
     "h be Element-of-struct G"
     "g be Element-of-struct G"
  shows "h \<otimes>\<^sub>G g = 1.\<^sub>G & g \<otimes>\<^sub>G h = 1.\<^sub>G implies g = h\<^sup>-\<^sup>1\<^sub>G" 
text_raw \<open>}%EndSnippet\<close>
proof-          
    show ?thesis using  group_1_def_5[of G h g] assms by auto
  qed

mtheorem group_1_th_6[rule_format]:
 "for h, g, f being Element-of-struct G st
    h  \<otimes>\<^sub>G g = h  \<otimes>\<^sub>G f or g  \<otimes>\<^sub>G h = f  \<otimes>\<^sub>G h holds g = f"
proof (rule ballI,rule ballI,rule ballI, rule impI)
  fix h g f
  assume T1:"h be (Element-of-struct G)"
            "g be (Element-of-struct G)"
            "f be (Element-of-struct G)"
  assume  A1:" h  \<otimes>\<^sub>G g = h  \<otimes>\<^sub>G f or g  \<otimes>\<^sub>G h = f  \<otimes>\<^sub>G h "
  have T2: "(h\<^sup>-\<^sup>1\<^sub>G) be (Element-of-struct G)" using assms T1 group_1_def_5 by simp
  show "g = f"
    proof (rule disjE[OF A1])
       assume "h  \<otimes>\<^sub>G g = h  \<otimes>\<^sub>G f"
         hence "(h\<^sup>-\<^sup>1\<^sub>G)  \<otimes>\<^sub>G (h \<otimes>\<^sub>G g)  =  ((h\<^sup>-\<^sup>1\<^sub>G)  \<otimes>\<^sub>G h)  \<otimes>\<^sub>G f" using assms T1 T2 group_1_def_3 by simp
         hence "(h\<^sup>-\<^sup>1\<^sub>G)  \<otimes>\<^sub>G (h  \<otimes>\<^sub>G g) = 1.\<^sub>G  \<otimes>\<^sub>G f" using assms T1 T2 group_1_def_5 by simp
         hence "(h\<^sup>-\<^sup>1\<^sub>G)  \<otimes>\<^sub>G (h  \<otimes>\<^sub>G g) = f" using assms T1 group_1_def_4 group_1_cl_1 by simp
         hence "((h\<^sup>-\<^sup>1\<^sub>G)  \<otimes>\<^sub>G h)  \<otimes>\<^sub>G g = f" using assms T1 T2 group_1_def_3 by simp
         hence "1.\<^sub>G  \<otimes>\<^sub>G g = f" using assms T1 group_1_def_5 by simp
       thus "g= f" using assms T1 group_1_def_4 group_1_cl_1 by simp
    next   
       assume "g  \<otimes>\<^sub>G h = f  \<otimes>\<^sub>G h"
         hence "(g  \<otimes>\<^sub>G h)  \<otimes>\<^sub>G h\<^sup>-\<^sup>1\<^sub>G = f  \<otimes>\<^sub>G (h  \<otimes>\<^sub>G h\<^sup>-\<^sup>1\<^sub>G)"  using assms T1 T2 group_1_def_3 by simp
         hence "(g  \<otimes>\<^sub>G h)  \<otimes>\<^sub>G h\<^sup>-\<^sup>1\<^sub>G = f  \<otimes>\<^sub>G 1.\<^sub>G " using assms T1 T2 group_1_def_5 by simp
         hence "(g  \<otimes>\<^sub>G h)  \<otimes>\<^sub>G h\<^sup>-\<^sup>1\<^sub>G = f "  using assms T1 group_1_def_4 group_1_cl_1 by simp
         hence  "g  \<otimes>\<^sub>G (h  \<otimes>\<^sub>G h\<^sup>-\<^sup>1\<^sub>G) = f "  using assms T1 T2 group_1_def_3 by simp
         hence "g  \<otimes>\<^sub>G 1.\<^sub>G = f" using assms T1 group_1_def_5 by simp
       thus "g= f" using assms T1 group_1_def_4 group_1_cl_1 by simp
   qed
qed

text_raw \<open>\DefineSnippet{group1th7}{\<close>
theorem group_1_th_7:
  assumes "G be Group"
     "h be Element-of-struct G"
     "g be Element-of-struct G"
  shows "h \<otimes>\<^sub>G g = h or g \<otimes>\<^sub>G h = h implies g = 1.\<^sub>G"
text_raw \<open>}%EndSnippet\<close>
proof - 
  have T2:"G is unital" using assms group_1_cl_1 by simp
  hence "h \<otimes>\<^sub>G 1.\<^sub>G = h & 1.\<^sub>G \<otimes>\<^sub>G h = h & 1.\<^sub>G be Element-of-struct G" 
    using assms group_1_def_4[of G] by auto
  thus "h \<otimes>\<^sub>G g = h or g \<otimes>\<^sub>G h = h implies g = 1.\<^sub>G" 
    using assms group_1_th_6[of G h g "1.\<^sub>G"] by simp
qed

text_raw \<open>\DefineSnippet{group1th8}{\<close>
mtheorem group_1_th_8:
  "(1.\<^sub>G) \<^sup>-\<^sup>1\<^sub>G = 1.\<^sub>G"
proof - 
  have A0: "G is unital" using assms group_1_cl_1 by simp 
  have T0:"1.\<^sub>G be Element-of-struct G" 
    using assms group_1_def_4[of G] group_1_th_7 by simp
  have  "1.\<^sub>G \<otimes>\<^sub>G 1.\<^sub>G = 1.\<^sub>G" using assms group_1_def_4 T0 A0 by simp
  thus "(1.\<^sub>G) \<^sup>-\<^sup>1\<^sub>G = 1.\<^sub>G" using assms T0 A0 
    group_1_def_5[of G "1.\<^sub>G" "1.\<^sub>G"] by auto
qed 
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{group1th9}{\<close>
mtheorem group_1_th_9[rule_format]:
  "for h, g being Element-of-struct G st h \<^sup>-\<^sup>1\<^sub>G = g \<^sup>-\<^sup>1\<^sub>G holds h = g"
proof(rule ballI, rule ballI, rule impI)
  fix h g
  assume T1:"h be Element-of-struct G"
            "g be Element-of-struct G"
  hence T2: "h\<^sup>-\<^sup>1\<^sub>G be Element-of-struct G"
            "g\<^sup>-\<^sup>1\<^sub>G be Element-of-struct G" 
    using assms group_1_def_5 by auto
  assume "h\<^sup>-\<^sup>1\<^sub>G = g\<^sup>-\<^sup>1\<^sub>G"
  hence
A1: "h \<otimes>\<^sub>G g \<^sup>-\<^sup>1\<^sub>G = 1.\<^sub>G" using T1 T2 assms 
    group_1_def_5[of G h] by simp
  have "g \<otimes>\<^sub>G g \<^sup>-\<^sup>1\<^sub>G = 1.\<^sub>G" using T1 T2 assms 
    group_1_def_5[of G g] by simp
  thus "h = g" using assms T1 T2 A1 
    group_1_th_6[of G "g \<^sup>-\<^sup>1\<^sub>G" h g]  by simp
qed
text_raw \<open>}%EndSnippet\<close>
 
text_raw \<open>\DefineSnippet{group1th10}{\<close>
mtheorem group_1_th_10[rule_format]:
  "for h being Element-of-struct G st  
     h\<^sup>-\<^sup>1\<^sub>G = 1.\<^sub>G holds h = 1.\<^sub>G"
proof(rule ballI,rule impI)
  fix h
  assume T1:"h be Element-of-struct G"           
  have T2: "1.\<^sub>G be Element-of-struct G" 
    using assms group_1_def_4[of G] by simp
  assume "h \<^sup>-\<^sup>1\<^sub>G = 1.\<^sub>G"
  hence "(1.\<^sub>G) \<^sup>-\<^sup>1\<^sub>G = h \<^sup>-\<^sup>1\<^sub>G" using assms T1 
    group_1_th_8 by simp
  thus " h = 1.\<^sub>G" using group_1_th_9[OF assms T2] 
    assms T1 T2 by auto
qed
text_raw \<open>}%EndSnippet\<close>
  
text_raw \<open>\DefineSnippet{group1th11}{\<close>
mtheorem group_1_th_11[rule_format]:
  "for h, g being Element-of-struct G st 
      h  \<otimes>\<^sub>G g = 1.\<^sub>G holds h = g \<^sup>-\<^sup>1\<^sub>G & g = h \<^sup>-\<^sup>1\<^sub>G"
proof(intro ballI impI)
  fix h g
  assume T1:"h be Element-of-struct G"  
            "g be Element-of-struct G" 
  hence T2:"h\<^sup>-\<^sup>1\<^sub>G be Element-of-struct G"  
           "g\<^sup>-\<^sup>1\<^sub>G be Element-of-struct G" 
    using assms group_1_def_5 by auto
  assume
A1:" h \<otimes>\<^sub>G g = 1.\<^sub>G"
  have "h \<otimes>\<^sub>G h \<^sup>-\<^sup>1\<^sub>G = 1.\<^sub>G" "g \<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G g = 1.\<^sub>G" 
    using assms T1 group_1_def_5 by simp+
  thus "h = g \<^sup>-\<^sup>1\<^sub>G & g = h \<^sup>-\<^sup>1\<^sub>G" using 
    group_1_th_6[OF assms,of h "h\<^sup>-\<^sup>1\<^sub>G" g] 
    group_1_th_6[OF assms,of g h "g\<^sup>-\<^sup>1\<^sub>G"] T1 T2 A1 by auto
qed
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{group1th12}{\<close>  
mtheorem group_1_th_12[rule_format]:
  "for h, g, f being Element-of-struct G holds h \<otimes>\<^sub>G f = g iff f = (h\<^sup>-\<^sup>1\<^sub>G)   \<otimes>\<^sub>G g"
proof(intro ballI, rule iffI3)
  fix h g f
  assume T1:"h be Element-of-struct G"  
            "g be Element-of-struct G"
            "f be Element-of-struct G" 
  hence T2:"h\<^sup>-\<^sup>1\<^sub>G be Element-of-struct G"  
           "g\<^sup>-\<^sup>1\<^sub>G be Element-of-struct G" 
    using assms group_1_def_5 by auto
  have T3:"G is unital" using assms group_1_cl_1 by simp
  have T4:"h \<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G g be Element-of-struct G" 
    using assms algstr_0_def_18[of G "h \<^sup>-\<^sup>1\<^sub>G" g] T1 T2 by auto
   show "h \<otimes>\<^sub>G f = g implies  f = h\<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G g" 
    proof
    assume A1: "h   \<otimes>\<^sub>G f = g"
    have "h   \<otimes>\<^sub>G ((h \<^sup>-\<^sup>1\<^sub>G) \<otimes>\<^sub>G g) = (h   \<otimes>\<^sub>G h \<^sup>-\<^sup>1\<^sub>G)  \<otimes>\<^sub>G g" using T1 T2 assms group_1_def_3 by simp
    also have  "...= 1.\<^sub>G   \<otimes>\<^sub>G g" using assms group_1_def_5 T1 by simp
    also have "... =  g" using  assms group_1_def_4 T1 T3 by auto
    finally show "f = (h \<^sup>-\<^sup>1\<^sub>G)   \<otimes>\<^sub>G g" using A1 group_1_th_6[OF assms T1(1) T4 T1(3)] by simp
  qed
  assume "f = h\<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G g"
  hence "h \<otimes>\<^sub>G f = h  \<otimes>\<^sub>G h\<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G g" using assms group_1_def_3 T1 T2 by simp
  also have "... = 1.\<^sub>G \<otimes>\<^sub>G g" using assms group_1_def_5 T1 by simp
  also have "... = g" using T3 T1 group_1_def_4 assms by auto
  finally show "h \<otimes>\<^sub>G f = g" by simp 
qed
text_raw \<open>}%EndSnippet\<close>
  
text_raw \<open>\DefineSnippet{group1th16}{\<close>
theorem group_1_th_16:
  assumes "G be Group"
          "h be Element-of-struct G" "g be Element-of-struct G"
  shows "(h \<otimes>\<^sub>G g)\<^sup>-\<^sup>1\<^sub>G = g\<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G h\<^sup>-\<^sup>1\<^sub>G"
text_raw \<open>}%EndSnippet\<close>
proof-           
  have T2:"h\<^sup>-\<^sup>1\<^sub>G be Element-of-struct G"  
          "g\<^sup>-\<^sup>1\<^sub>G be Element-of-struct G" 
    using assms group_1_def_5 by auto
  have T3:"G is unital" 
    using assms group_1_cl_1 by simp
  have T4:"g\<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G h \<^sup>-\<^sup>1\<^sub>G be Element-of-struct G" 
    using assms algstr_0_def_18[of G "g \<^sup>-\<^sup>1\<^sub>G" "h \<^sup>-\<^sup>1\<^sub>G"] T2 by auto
  have T5:"h \<otimes>\<^sub>G g be Element-of-struct G" 
    using assms algstr_0_def_18[of G h g] by auto
  have  "g\<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G h \<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G  (h \<otimes>\<^sub>G g) =g\<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G h\<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G h  \<otimes>\<^sub>G g" 
    using assms group_1_def_3[of G] assms T4 by auto
  also have "... = g\<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G (h\<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G h) \<otimes>\<^sub>G g"  
    using assms group_1_def_3[of G] assms T2 by auto
  also have "... = g \<^sup>-\<^sup>1\<^sub>G  \<otimes>\<^sub>G 1.\<^sub>G \<otimes>\<^sub>G g"  
    using assms group_1_def_5[of G] assms T2 by auto
  also have "... = (g \<^sup>-\<^sup>1\<^sub>G)  \<otimes>\<^sub>G g" 
    using assms group_1_def_4 T2 T3 by auto
  also have "... = 1.\<^sub>G" 
    using assms group_1_def_5 assms by auto
  finally show  "(h  \<otimes>\<^sub>G g) \<^sup>-\<^sup>1\<^sub>G = g \<^sup>-\<^sup>1\<^sub>G  \<otimes>\<^sub>G h \<^sup>-\<^sup>1\<^sub>G" 
    using assms(1) group_1_th_11 T4 T5 by simp
qed

definition commutative_prefix :: "Attr" ("commutative") where group_1_def_12 [THEN defattr_property,rule_format]:
   "attr commutative means (\<lambda> S. S be multMagma & (for x,y being Element-of-struct S holds 
                                         x \<otimes>\<^sub>S y  = y \<otimes>\<^sub>S  x))"
lemmas group_1_def_12a = group_1_def_12[THEN iffD1,THEN conjunct2,rule_format]

end