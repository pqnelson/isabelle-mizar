\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Funct_1 
  imports Relset_1 "../Mizar/Mizar_Fraenkel"
begin

reserve x,y,z,x1,x2,y1,y2 for object
reserve X,Y,Z for set

text_raw \<open>\DefineSnippet{funct_1def1}{\<close>
definition Function_like :: Attr 
  where funct_1_def_1_prefix[THEN defattr_property] :
  "attr Function_like means 
     (\<lambda>IT. IT be set & 
       (for x,y1,y2 being object st 
          [x,y1] in IT & [x,y2] in IT holds y1 = y2))"
text_raw \<open>}%EndSnippet\<close>
          
mtheorem funct_1_def_1:
  "X is Function_like iff
              (for x,y1,y2 being object st [x,y1] in X & [x,y2] in X holds y1 = y2)" using funct_1_def_1_prefix assms by (simp add:defattr_property)

theorem funct_1_cl_1:
  "cluster empty \<rightarrow> Function_like for set" by (simp add: funct_1_def_1) 

theorem funct_1_cl_2:
"cluster Function_like for Relation"
proof
  show "{} is Function_like" by (simp add: funct_1_def_1)
  show "{} be Relation" using relat_1_def_1a by simp
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

text_raw \<open>\DefineSnippet{Function}{\<close>
abbreviation 
  "Function \<equiv> Function_like \<parallel> Relation"
text_raw \<open>}%EndSnippet\<close>

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
text_raw \<open>\DefineSnippet{funct1def2}{\<close>
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

lemmas funct_1_def_2a[type_infer] = funct_1_def_2[THEN conjunct1,THEN conjunct1,rule_format,OF _ object_root]
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

theorem funct_1_th_18:
  "x in X implies (id X).x = x"
proof
  have I: "id X be Function" using funct_1_cl_4 all_set by auto
  assume "x in X"
  hence "[x,x] in id X" by auto
  thus "(id X).x = x" using funct_1_th_1[OF I, of x x] by auto          
qed  
  
text_raw \<open>\DefineSnippet{redefine_func_rng}{\<close>
theorem funct_1_def_3:
  "let f be Function
   redefine func rng f \<rightarrow> set means
     (\<lambda> it. for y being object holds y in it iff
        (ex x being object st x in dom f & y = f . x))"
text_raw \<open>}%EndSnippet\<close>
proof(rule redefine_func_means_property,simp)
  assume T0: "f be Function"
  show "(rng f) be set" using all_set by simp
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
  
theorem funct_1_sch_Lambda:
  assumes "A be set"
  shows "ex f be Function st dom f = A & (for x st x in A holds f .x = P(x))" 
 proof-     
   
   let ?Z = "\<lambda> x y.(y = P(x))"
     
   have A1:"for x,y,z st ?Z(x,y) & ?Z(x,z) holds y=z" by auto
   obtain Y where
     T0: "Y be set" "for y be object holds y in Y iff (ex z be object st z in A & ?Z(z,y))" using tarski_0_sch_1[OF assms A1] by blast  
     
      obtain Q where
        T2: "Q be Relation" and
        A2: "for x,y holds [x,y] in Q iff x in A & y in Y & ?Z (x,y)" 
         using assms relat_1_sch_1[of A Y "?Z"] T0(1) by auto
     have "Q be Relation" using T2 by simp
     have "for x,y1,y2 being object st [x,y1] in Q & [x,y2] in Q holds y1 = y2"
     proof(intro ballI impI)
       fix x y1 y2
       assume "[x , y1] in Q & [x , y2] in Q"
       hence "y1 = P(x)" "y2 = P(x)" using A2 by auto
       thus  "y1=y2" using  xtuple_0_th_1[of x y1]  xtuple_0_th_1[of x y2] by auto
     qed
     hence P: "Q is Function_like" using  funct_1_def_1 all_set by simp   
     show "ex f be Function st dom f = A & (for x st x in A holds f .x = P(x))"
       proof (rule bexI[of _ Q],rule conjI)
         show "dom Q = A"
           proof (unfold xboole_0_def_10[OF all_set all_set],intro conjI) 
       show "dom Q \<subseteq> A"
          proof (unfold tarski_def_3,intro ballI impI)      
            fix x 
            assume "x be object"
            assume "x in dom Q"
            then obtain  y where 
              "y be object" " [x,y] in Q" using T2 by auto
            thus "x in A" using A2 by auto
          qed
          show "A \<subseteq> dom Q"
           proof (unfold tarski_def_3,intro ballI impI)      
            fix x 
            assume "x be object"
            assume B: "x in A"
            hence "P(x) in Y" using T0 by auto  
            hence "[x,P(x)] in Q" using A2 B by auto
            thus "x in dom Q" using T2 by auto
          qed
        qed
        show Q: "Q be Function" using T2 P by simp 
        show "for x st x in A holds Q .x = P(x)"
         proof (intro ballI impI)      
            fix y 
            assume "y be object"
            assume B: "y in A"
            hence "P(y) in Y" using T0 by auto  
            hence "[y,P(y)] in Q" using A2 B by auto
            thus "Q .y = P(y)" using funct_1_th_1[of Q "P(y)" y,OF Q] by auto
          qed
       qed
    qed

      
 mtheorem funct_1_th_5:
  "ex f be Function st dom f = X & rng f c= {z}"
proof-  
    let ?Z = "\<lambda> x y.(y=z)"
      obtain P where
        T2: "P be Relation" and
        A2: "for x,y holds [x,y] in P iff x in X & y in {z} & ?Z (x,y)" 
         using assms relat_1_sch_1[of X "{z}" "?Z"] by auto
     have "P be Relation" using T2 by simp
     have "for x,y1,y2 being object st [x,y1] in P & [x,y2] in P holds y1 = y2"
     proof(intro ballI impI)
       fix x y1 y2
       assume "[x , y1] in P & [x , y2] in P"
       hence "y1=z" "y2=z" using A2 by auto
       thus  "y1=y2" using  xtuple_0_th_1[of x y1]  xtuple_0_th_1[of x y2] by auto
     qed
     hence P: "P is Function_like" using  funct_1_def_1 all_set by simp   
     show "ex f be Function st dom f = X & rng f c= {z}"
       proof (rule bexI[of _ P],rule conjI)
         show "dom P = X"
           proof (unfold xboole_0_def_10[OF all_set all_set],intro conjI) 
       show "dom P \<subseteq> X"
          proof (unfold tarski_def_3,intro ballI impI)      
            fix x 
            assume "x be object"
            assume "x in dom P"
            then obtain  y where 
              "y be object" " [x,y] in P" using T2 by auto
            thus "x in X" using A2 by auto
          qed
          show "X \<subseteq> dom P"
           proof (unfold tarski_def_3,intro ballI impI)      
            fix x 
            assume "x be object"
            assume "x in X"
            hence "[x,z] in P" using A2 tarski_def_1b[of z z] by auto
            thus "x in dom P" using T2 by auto
          qed
        qed
        show "rng P c= {z}"
         proof (unfold tarski_def_3,intro ballI impI)      
            fix y 
            assume "y be object"
            assume "y in rng P"
            then obtain x where 
              "x be object" " [x,y] in P" using T2 by auto
            thus "y in {z}" using A2 by auto
          qed
        show "P be Function" using T2 P by simp    
       
       qed
    qed
  
text_raw \<open>\DefineSnippet{product}{\<close>  
definition funct_1_notation_1 ("_ *` _" [90,90] 190) where
 Product: "let f be Function & g be Function synonym f *` g  for g * f"
text_raw \<open>}%EndSnippet\<close>
  
abbreviation funct_1_prod (" _ \<circ> _ " [20,21] 20) where
  "f \<circ> g \<equiv> f *` g"  
  
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
  
mtheorem funct_1_th_47:
  "x in dom(f|X) implies (f|X).x = f. x"
proof
  have T0: "f|X be Function" using assms funct_1_cl relat_1_def_11[of f X,THEN conjunct1,THEN conjunct1] by simp
  assume
A1: "x in dom (f|X)"
  hence A2: "x in dom f" using relat_1_th_51 assms by simp
  hence "[x,(f|X).x] in (f|X)" using T0 funct_1_def_2 A1 by simp
  hence "[x,(f|X).x] in f" "[x,f. x] in f" using relat_1_def_11[of f X,THEN conjunct1,THEN conjunct2] funct_1_def_2[of f x,THEN conjunct1,THEN conjunct2] 
        assms A2 by simp+    
  thus "(f|X).x = f. x"  using funct_1_def_1[of f,THEN iffD1,rule_format, of x _ "f. x"] assms by auto
qed  
  
mtheorem funct_1_th_48:
  "x in dom f \<inter> X implies (f|X). x = f. x"
proof
  assume "x in dom f \<inter> X"
  hence "x in dom(f|X)" using assms relat_1_th_55 by simp
  thus "(f|X). x = f. x" using assms  funct_1_th_47 by simp
qed

text_raw \<open>\DefineSnippet{fraenkel_test}{\<close>
term "{f. x where x be Element-of dom f: x in X}"
text_raw \<open>}%EndSnippet\<close>

theorem funct_1_th_test:
  assumes "f be non empty\<parallel>Function" 
  shows "rng (f|X) = { f. x where x be Element-of dom f: x in X}" 
proof( unfold xboole_0_def_10[OF all_set all_set],rule conjI)
  have T0: "f|X be Function" using assms funct_1_cl relat_1_def_11[of f X,THEN conjunct1,THEN conjunct1] all_set by simp
  show "rng (f|X) \<subseteq> { f. x where x be Element-of dom f: x in X}"
  proof(unfold tarski_def_3,rule ballI,rule impI)
    fix y assume A1: "y in rng (f|X)"
    then obtain x where
      A2: "x be object" "x in dom (f|X) & (f|X).x =y" using T0 funct_1_def_3 by auto
    have A3: "x in dom f" "x in X" using A2 relat_1_th_51 assms all_set by auto
    hence A4:"x be Element-of dom f" using Element_of_rule by simp
    have "(f|X).x = f. x" using assms A2 funct_1_th_47 all_set by auto
    thus "y in { f. x where x be Element-of dom f: x in X}" using A2 Fraenkel_A1_in A3 A4 by auto
  qed  
  show "{ f. x where x be Element-of dom f: x in X} \<subseteq> rng (f|X)"
  proof(unfold tarski_def_3,rule ballI,rule impI)
    fix y assume A1: "y in { f. x where x be Element-of dom f: x in X}"
    obtain x where
      A2: "x be Element-of dom f" "y = f. x & x in X" using Fraenkel_A1_ex[OF _ A1] by auto
    have A3:"x in dom (f|X)" using A2 relat_1_th_51 assms all_set A2 Element_of(1) assms relat_1_cl_10 by auto
    have "y = (f|X).x" using assms funct_1_th_48 A2 all_set Element_of(1) assms relat_1_cl_10 by auto
    thus "y in rng (f|X)" using A3 T0 funct_1_def_3 by auto        
  qed
qed
  
  
mtheorem funct_1_th_49:
  "x in X implies (f|X).x = f. x"
proof
  have T0: "f|X be Function" using assms funct_1_cl relat_1_def_11[of f X,THEN conjunct1,THEN conjunct1] by simp
  assume
A1: "x in X"
  show "(f|X).x = f. x"
  proof(cases "x in dom f")
    assume "x in dom f"
      hence "x in dom(f|X)" using  A1 relat_1_th_55 assms by simp
      thus ?thesis using funct_1_th_47 assms by simp
    next
      assume A2: "not x in dom f"
      hence "not x in dom (f|X)" using relat_1_th_55 assms by simp  
      hence "(f|X).x = {}" using funct_1_def_2 T0 by simp
      also have "... = f. x" using funct_1_def_2 A2 assms  by simp
      finally show ?thesis by simp
  qed  
qed  
  
  
definition OneToOne :: Attr ("one-to-one") where funct_1_def_4[THEN defattr_property] :
  "attr one-to-one means (\<lambda>IT. IT be Function & (for x1,x2 being object st x1 in dom IT & x2 in dom IT holds x1 = x2))"

definition functional:: Attr where funct_1_def_13[THEN defattr_property]:
  "attr functional means (\<lambda>IT. IT be set & (for x be object st x in IT holds x be Function))"

  
  definition funct_1_def_141  (" _ -compatible") where
  funct_1_def_14[THEN defattr_property]: " attr g -compatible means (\<lambda>f. f be Function & g be Function & (for x be object st x in dom f holds f .x in g .x) )"
 
definition funct_1_def_9  ("non-empty") where
  funct_1_def_9[THEN defattr_property]: " attr non-empty means (\<lambda>f. f be Function & not {} in rng f )"
  
text_raw \<open>\DefineSnippet{funct1th110}{\<close>
theorem funct_1_th_110:
  assumes "B be non empty \<bar> functional \<parallel> set"
          "f be Function" "f = union B"
  shows
     "dom f = union the set-of-all dom g where g be Element-of B"
     "rng f = union the set-of-all rng g where g be Element-of B"
  text_raw \<open>}%EndSnippet\<close>
proof -
  let ?D = "the set-of-all dom g where g be Element-of B"
  let ?R = "the set-of-all rng g where g be Element-of B"
  show "dom f = union ?D"
  proof(unfold xboole_0_def_10[OF all_set all_set],rule conjI)
    show "dom f \<subseteq> union ?D"
       proof(unfold tarski_def_3,rule ballI,rule impI)
         fix x assume "x be object"
         assume "x in dom f" 
         hence "[x,f. x] in f" using funct_1_th_1[of f "f. x" x] assms(2) by auto
         then obtain g where
           A2: "g be set" "[x, f. x] in g" "g in B" using assms(3) tarski_def_4 by auto
         have T2: "g be Element-of B" using A2(3) Element_of_rule by simp
         have "g be Function" using A2(3) funct_1_def_13 assms(1) by auto
         hence C1: "x in dom g" using A2 funct_1_th_1[of g "f. x" x] by auto+    
         have "dom g in ?D" using Set_of_All_in[OF _ T2] by auto  
         thus "x in union ?D" using C1 tarski_def_4b all_set by auto
       qed
    show "union ?D \<subseteq> dom f"
       proof(unfold tarski_def_3,rule ballI,rule impI)
         fix x assume "x be object"
         assume "x in union ?D"
         then obtain d where
           A4: "d be set" "x in d" "d in ?D" using tarski_def_4 by auto
         obtain g where
           A6: "g be Element-of B" "d = dom g" using Set_of_All_ex[OF _ A4(3)] by auto
         have T3: "g in B" "g be Function" using funct_1_def_13 assms(1) A6(1)  by auto
         hence "[x,g. x] in g" using A4(2) A6(2) funct_1_th_1[of g "g. x" x] by auto 
         hence "[x,g. x] in f" using assms(3) tarski_def_4b T3(1) all_set by auto   
         thus "x in dom f" using assms(2) funct_1_th_1[of g "g. x" x] by auto
       qed
  qed
  show "rng f = union ?R" 
  proof(unfold xboole_0_def_10[OF all_set all_set],rule conjI)
    show "rng f \<subseteq> union ?R"
       proof(unfold tarski_def_3,rule ballI,rule impI)
         fix y assume "y be object"
         assume "y in rng f" 
         then obtain x where
            "x be object" "x in dom f" "y = f. x" using  funct_1_def_3 assms(2) by auto 
         hence "[x,y] in f" using funct_1_th_1[of f y x] assms(2) by auto
         then obtain g where
           A2: "g be set" "[x, y] in g" "g in B" using assms(3) tarski_def_4 by auto
         have T2: "g be Element-of B" using A2(3) Element_of_rule by simp
         have T3: "g be Function" using A2(3) funct_1_def_13 assms(1) by auto
         hence C1: "x in dom g" "y=g. x" using A2 funct_1_th_1[of g y x] by auto+    
         have C2: "y in rng g" using funct_1_def_3[of g] C1 T3 by auto  
         have "rng g in ?R" using Set_of_All_in[OF _ T2] by auto  
         thus "y in union ?R" using C2 tarski_def_4b all_set by auto
       qed
    show "union ?R \<subseteq> rng f"
       proof(unfold tarski_def_3,rule ballI,rule impI)
         fix y assume "y be object"
         assume "y in union ?R"
         then obtain r where
           A4: "r be set" "y in r" "r in ?R" using tarski_def_4 by auto
         obtain g where
           A6: "g be Element-of B" "r = rng g" using Set_of_All_ex[OF _ A4(3)] by auto
         have T3: "g in B" "g be Function" using funct_1_def_13 assms(1) A6(1)  by auto
         then obtain x where
           A7: "x be object" "x in dom g" "y = g. x" using  funct_1_def_3 A4(2) A6(2) by auto 
         have "[x,y] in g" using A7 funct_1_th_1[of g y x] T3(2) by  auto
         hence "[x,y] in f" using assms tarski_def_4b all_set T3 by auto    
         thus "y in rng f" using xtuple_0_def_13[THEN conjunct1,THEN conjunct2] all_set assms(2) by auto
       qed
     qed
   qed     
     
end