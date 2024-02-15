\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Funct_1
  imports Relset_1
begin

reserve x,y,z,x1,x2,y1,y2 for object
reserve X,Y,Z for set

definition Function_like :: Attr where funct_1_def_1_prefix[THEN defattr_property] :
  "attr Function_like means (\<lambda>IT. IT be set & (for x,y1,y2 being object st [x,y1] in IT & [x,y2] in IT holds y1 = y2))"

mtheorem funct_1_def_1:
  "X is Function_like iff
              (for x,y1,y2 being object st [x,y1] in X & [x,y2] in X holds y1 = y2)" using funct_1_def_1_prefix assms by (simp add:defattr_property)

theorem funct_1_cl_1:
  "cluster empty \<rightarrow> Function_like for set" by (simp add: funct_1_def_1) 

theorem funct_1_cl_2:
"cluster Function_like for Relation"
proof
  show "{} is Function_like" by (simp add: funct_1_def_1)
  show "{} be Relation" by simp
qed


theorem funct_1_cl_3:
  "let (a be object & b be object)
   cluster {[a,b]} \<rightarrow> Function_like"
proof-
  let ?F = "{[a,b]}"
  have "for x,y1,y2 being object st [x,y1] in ?F & [x,y2] in ?F holds y1 = y2"
     proof(intro ballI impI)
       fix x y1 y2
       assume "[x , y1] in ?F & [x , y2] in ?F"
       hence "[x,y1] = [a,b]" "[x,y2] =[a,b]" using tarski_def_1 by auto
       thus  "y1=y2" using  xtuple_0_th_1[of x y1]  xtuple_0_th_1[of x y2] by auto
     qed
  thus "?F is Function_like" using relat_1_cl_7 funct_1_def_1 by simp
qed


theorem funct_1_cl_4:
  "let X be set
   cluster id X \<rightarrow> Function_like"
proof-
  assume "X be set"
  have A:"(id X) be set" using all_set by auto
  show "(id X) is Function_like"
    proof (unfold funct_1_def_1[OF A],intro conjI ballI impI)
       fix x y1 y2
       assume "x be object" "y1 be object" "y2 be object"
       assume "[x,y1] in (id X) & [x,y2] in (id X)"
       thus "y1=y2" by auto       
    qed
qed


abbreviation "Function \<equiv> Function_like \<parallel> Relation"

theorem funct_1_cl:
  "let X be set & F be Function
   cluster F | X \<rightarrow> Function_like"
proof-
  assume A0:"X be set & F be Function"
  hence A1: "F|X be Relation" using relat_1_def_11[of F X,THEN conjunct1] by auto
  have "for x,y1,y2 being object st [x,y1] in F|X & [x,y2] in F|X holds y1 = y2"
  proof(intro ballI impI)
       fix x y1 y2
       assume T0: "x be object" "y1 be object " "y2 be object"
       assume "[x,y1] in F|X & [x,y2] in F|X"
       hence  A2: "[x,y1] in F & [x,y2] in F" using A0 relat_1_def_11[of F X,THEN conjunct1] by simp
       have A4: "for x,y1,y2 be object holds ([x,y1] in F & [x,y2] in F implies y1=y2)" using funct_1_def_1[of F] A0 by auto
       thus "y1=y2" using A4[rule_format,of x y1 y2,OF T0] A2 by simp
  qed
  thus "F | X is Function_like" using funct_1_def_1 A1 by auto
qed

reserve f for Function
text_raw \<open>\DefineSnippet{funct_1_def_2}{\<close>
definition funct_apply ( "_ . _" [90,90] 90) where
"func f . x \<rightarrow> set means 
  \<lambda>it. ([x,it] in f if x in dom f otherwise it = {})"
text_raw \<open>}%EndSnippet\<close> 
schematic_goal funct_1_def_2:
  assumes "f be Function & x be object" shows "?X"
proof (induct rule: means_property[OF funct_apply_def, of x f,case_names existence uniqueness])
  case existence
     have A0: "{} be set" using xboole_0_def_2 by auto
     {assume "x in dom(f)"
      then obtain y where
A1:       "y be object & [x,y] in f" using assms  by auto
      hence "ex y being set st [x,y] in f" using A1 tarski_0_1 by auto
     }
     thus "ex it being set st ([x,it] in f if x in dom(f) otherwise it = {})" using A0 all_set by auto
  case uniqueness
    fix y1 y2
    assume A1: "y1 be set" "([x,y1] in f if x in dom(f) otherwise y1 = {})" and
           A2: "y2 be set" "([x,y2] in f if x in dom(f) otherwise y2 = {})"
     {
       assume "x in dom(f)"
       then have "[x,y1] in f & [x,y2] in f" using A1 A2 by auto
       hence "y1=y2" using assms funct_1_def_1 A1 by auto 
     }
    thus "y1 = y2" using A1 A2 by auto
qed

lemmas funct_1_def_2a = funct_1_def_2[THEN conjunct1,THEN conjunct1,rule_format,OF _ object_root]
lemmas funct_1_def_2b = funct_1_def_2[THEN conjunct1,THEN conjunct2,rule_format,OF _ object_root]

mtheorem funct_1_th_1: " [x,y] in f iff x in dom f & y = f . x"
 proof(intro  conjI iffI)
  assume A1: "[x,y] in f"
  thus A2: "x in dom f" using assms by auto
  hence "[x , f . x] in f" using A2 funct_1_def_2b assms by auto
  thus "y = f . x" using A1 funct_1_def_1 all_set assms by auto
 next
  assume "x in dom f & y = f . x"
  then show "[x , y] in f" using assms funct_1_def_2b by auto
qed

text_raw \<open>\DefineSnippet{redefine_func}{\<close>
theorem funct_1_def_3:
  "let f be Function
   redefine func rng f \<rightarrow> set means
     (\<lambda> it. for y being object holds y in it iff
        (ex x being object st x in dom f & y = f . x))"
text_raw \<open>}%EndSnippet\<close>
proof-
  assume T0: "f be Function"
  show "(rng f) be set & (for y being object holds (y in rng f) iff
        (ex x being object st x in dom f & y = f . x))"
  proof(induct rule : redefine_func_means_property[ OF T0, case_names coherence compatibility ])
    case coherence 
        show "(rng f) be set" using all_set by simp
    case compatibility 
        fix Y
        assume T2: "Y be set"
        show "Y = rng f  iff (for y being object holds y in Y iff
          (ex x being object st x in dom f & y = f . x))"
        proof(rule iffI3)
          show "Y = rng f  implies (for y being object holds y in Y iff
            (ex x being object st x in dom f & y = f . x))" 
          proof
            assume A1: "Y = rng f"
            show "for y being object holds y in Y iff
              (ex x being object st x in dom f & y = f . x)"
            proof (intro ballI impI)
              fix y
              assume T3: "y be object"
              show "y in Y iff
                (ex x being object st x in dom f & y = f . x)"
              proof (intro iffI3)
                show "y in Y implies
                     (ex x being object st x in dom f & y = f . x)"
                 proof
                   assume "y in Y"
                   then obtain x where
                     T4: "x be object" and A2:"[x,y] in f" using A1 T0 xtuple_0_def_13  by auto
                   have "x in dom f & y = f . x " using A2 T0 T4 T3 funct_1_th_1[of "f" "y" "x"] by auto
                   thus "ex x being object st x in dom f & y = f . x" using T4 bexI[of "\<lambda>x. x in dom f & y = f . x"] by auto
                 qed
                assume "ex x being object st x in dom f & y = f . x"
                then obtain x where
                  T5: "x be object" and A3:"x in dom f & y = f . x" by blast
                have "[x,y] in f" using T0 T5 A3 funct_1_def_2 by auto
                thus "y in Y" using A1 T0 xtuple_0_def_13 by auto
             qed       
         qed
      qed
             assume A4: "for y being object holds y in Y iff
               (ex x being object st x in dom f & y = f . x)"            
             show "Y = rng f"
               proof (unfold xboole_0_def_10[rule_format, OF all_set all_set, of Y "rng f"],intro conjI)
                 show "Y \<subseteq> rng f"
                   proof (unfold tarski_def_3, intro ballI impI)
                      fix y 
                      assume T7: "y be object"
                      assume "y in Y"
                      then obtain x where 
                      T6: "x be object" and A5:"x in dom f & y = f . x" using A4 T7 by blast
                      have "[x,y] in f" using T0 A5 funct_1_def_2 by auto
                      thus "y in rng f" using T0 xtuple_0_def_13 by auto
                   qed
                 show "rng f \<subseteq> Y"
              proof (unfold tarski_def_3, intro ballI impI)                
                fix y 
                assume T8: "y be object"               
                assume "y in rng f"
                then obtain x where 
                   T9: "x be object" and A6: "[x,y] in f" using T0 xtuple_0_def_13 by auto
                hence "x in dom f & y = f . x" using T0 A6 funct_1_th_1[of "f" "y" "x"] T9 T8 by auto
                thus "y in Y" using A4 by auto
              qed
           qed
          qed
  qed
qed   

  
  
definition function_1_notation_1_prefix ("_ *` _" [90,90] 190) where
 Product: "let f be Function & g be Function synonym f *` g  for g * f"
  
theorem funct_1_cl_f:
  "let f be Function & g be Function 
  cluster g*`f \<rightarrow> Function_like"
  proof-
    assume T0: "f be Function & g be Function"
    hence T1: "f be Relation & g be Relation" by auto
    have "for x,y1,y2 being object st [x,y1] in (g*`f) & [x,y2] in (g*`f) holds y1 = y2"
     proof(intro ballI impI)
       fix x y1 y2
       assume A0: "[x , y1] in (g*`f) & [x , y2] in (g*`f)"
       then obtain z1 where
         A1: "z1 be object" "[x,z1] in f" "[z1,y1] in g" using relat_1_def_9[of f g,OF T1,THEN conjunct1,THEN conjunct2] T0 Product by auto
       obtain z2 where
         A2: "z2 be object" "[x,z2] in f" "[z2,y2] in g" using relat_1_def_9[of f g,OF T1,THEN conjunct1,THEN conjunct2] T0 A0 Product by auto
       have "z1=z2" using funct_1_def_1[of f] T0 A1(2) A2(2) all_set by auto   
       thus "y1 = y2" using funct_1_def_1[of g,OF all_set,THEN iffD1,rule_format,of z1 y1 y2] T0 A1(3) A2(3) by auto 
     qed
  thus "(g*`f) is Function_like" using funct_1_def_1 all_set by simp     
qed
  
  
reserve f,g for Function   

mtheorem funct_1_cl_F: "(f *` g) be Function"
proof-
  have A1: "f*`g is Function_like" using funct_1_cl_f[of g f] assms by auto
  have "f be Relation & g be Relation" using assms by simp
  thus ?thesis using relat_1_def_9[of g f,THEN conjunct1,THEN conjunct1] A1 assms Product by auto    
qed  
  
mtheorem funct_1_th_11:
  "x in dom(g*`f) iff x in dom f & f. x in dom g"
proof(rule iffI3)
  let ?h = "g*` f"
  have T0: "?h be Function" using assms funct_1_cl_F[of f g] by simp
  have T1: "f be Relation & g be Relation" using assms by simp    
  show "x in dom ?h implies x in dom f & f. x in dom g"
    proof
      assume "x in dom ?h"
      hence "x in proj1 ?h" using assms T0 by auto  
    then obtain y where
  A1: "y be object" "[x,y] in ?h" using  xtuple_0_def_12 by auto
    have B1: "[x,y] in f*g" using A1 assms Product by auto    
    then obtain z where
      T2:"z be object" and
      A2: "[x,z] in f" and
      A3: "[z,y] in g" using relat_1_def_9[of f g,OF T1,THEN conjunct1,THEN conjunct2] by auto
    
    have "x in dom f" "f. x = z " using A2 funct_1_th_1[of f z x] assms  by auto
    thus  "x in dom f & f. x in dom g"  using A3 funct_1_th_1[of g y "f. x"] assms by auto
    qed
  assume
A4: "x in dom f & f. x in dom g"
  then obtain z where 
   "z be object" and
A5: "[x,z] in f" using  xtuple_0_def_12 assms by auto
   obtain y where "y be object" and
A6: "[f. x,y] in g" using A4 xtuple_0_def_12 assms by auto
   hence "[z,y] in g" using A4 A5 funct_1_def_2[of f x] all_set assms by auto
   hence "[x,y] in g*`f" using assms relat_1_def_9[of f g,OF T1,THEN conjunct1] A5 Product by auto
   thus "x in dom (g*`f)" using funct_1_th_1[of ?h y x,OF T0] by auto
qed

mtheorem funct_1_th_12:
  "x in dom(g*`f) implies (g*`f).x = g.(f. x)"
proof
  let ?h = "g*`f"
  have T0: "?h be Function" using assms funct_1_cl_F[of f g] by simp
  have T1: "f be Relation & g be Relation" using assms by simp    

  assume "x in dom ?h"
  hence "x in proj1 ?h" using assms T0 by auto  
   then obtain y where
  A1: "y be object" "[x,y] in ?h" using  xtuple_0_def_12 by auto
    have B1: "[x,y] in f*g" using A1 assms Product by auto    
    then obtain z where
      T2:"z be object" and
      A2: "[x,z] in f" and
      A3: "[z,y] in g" using relat_1_def_9[of f g,OF T1,THEN conjunct1,THEN conjunct2] by auto
    
    have "x in dom f" "f. x = z " using A2 funct_1_th_1[of f z x] assms  by auto
    hence  "g.( f. x) = y" "?h . x = y "  using A3 funct_1_th_1[of g y "f. x"] assms 
                                  A1(2) funct_1_th_1[of ?h y x,OF T0] by auto+
    thus "(g*`f). x = g.(f. x)" by auto
qed

definition OneToOne :: Attr ("one-to-one") where funct_1_def_4[THEN defattr_property] :
  "attr one-to-one means (\<lambda>IT. IT be Function & (for x1,x2 being object st x1 in dom IT & x2 in dom IT holds x1 = x2))"

end