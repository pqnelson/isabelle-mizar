\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory funct_1
  imports relset_1 "../mizar/mizar_fraenkel"
begin

reserve x,y,z,x1,x2,y1,y2 for object
reserve X,Y,Z for set

text_raw \<open>\DefineSnippet{funct_1def1}{\<close>
attr funct_1_def_1 ("Function'_like")
  "attr Function_like for set means
     (\<lambda>IT. for x,y1,y2 being object st
          [x,y1] in IT \<and> [x,y2] in IT holds y1 = y2)"
text_raw \<open>}%EndSnippet\<close>

theorem funct_1_cl_1[ty_cond_cluster]:
  "cluster empty \<rightarrow> Function_like for set" using xboole_0_def_1 funct_1_def_1 by auto

theorem funct_1_cl_2[ex]:
"cluster Function_like for Relation"
unfolding inhabited_def
proof
  show "{} be Function_like\<bar>Relation" by mty auto
qed


theorem funct_1_cl_3[ty_func_cluster]:
  "let (a be object \<and> b be object)
   cluster {[a,b]} \<rightarrow> Function_like"
proof-
  let ?F = "{[a,b]}"
  have "for x,y1,y2 being object st [x,y1] in ?F \<and> [x,y2] in ?F holds y1 = y2"
     proof(intro ballI impI)
       fix x y1 y2
       assume "[x , y1] in ?F \<and> [x , y2] in ?F"
       hence "[x,y1] = [a,b]" "[x,y2] =[a,b]" using tarski_def_1 by auto
       thus "y1=y2" using xtuple_0_th_1[of x y1]  xtuple_0_th_1[of x y2] by auto
     qed simp_all
  thus "?F is Function_like" using funct_1_def_1I by mauto
qed


(*lemmas aa[simp]=tarski_def_5

theorem
  "x=x"
proof
  have " {[x,x]} is Function_like" apply mty thm ty apply simp apply mauto
qed *)



theorem funct_1_cl_4[ty_func_cluster]:
  "let X be set
   cluster id X \<rightarrow> Function_like"
proof-
  assume [ty]:"X be set"
  show "(id X) is Function_like"
  proof (intro funct_1_def_1I conjI ballI impI)
       fix x y1 y2
       assume "[x,y1] in (id X)" "[x,y2] in (id X)"
       thus "y1=y2" using relat_1_def_8 by auto
    qed mauto
qed

text_raw \<open>\DefineSnippet{Function}{\<close>
abbreviation
  "Function \<equiv> Function_like \<bar>Relation"
text_raw \<open>}%EndSnippet\<close>

theorem funct_1_cl[ty_func_cluster]:
  "let X be set \<and> F be Function
   cluster F | X \<rightarrow> Function_like"
proof-
  assume A0[ty]:"X be set \<and> F be Function"
  have "for x,y1,y2 being object st [x,y1] in F|X \<and> [x,y2] in F|X holds y1 = y2"
  proof(intro ballI impI)
       fix x y1 y2
       assume T0: "x be object" "y1 be object " "y2 be object"
       assume "[x,y1] in F|X \<and> [x,y2] in F|X"
       hence A2: "[x,y1] in F \<and> [x,y2] in F" using A0 relat_1_def_11[of F X] by simp
       have A4: "for x,y1,y2 be object holds ([x,y1] in F \<and> [x,y2] in F \<longrightarrow> y1=y2)" using funct_1_def_1[of F] A0 by auto
       thus "y1=y2" using A2 by auto
  qed simp_all
  thus "F | X is Function_like" using funct_1_def_1 by mauto
qed

reserve f for Function
text_raw \<open>\DefineSnippet{funct1def2}{\<close>
func funct_1_def_2 (infix "." 110) where
  mlet "f be Function", "x be object"
  "func f . x \<rightarrow> object means
     \<lambda>it. ([x,it] in f if x in dom f otherwise it = {})"
text_raw \<open>}%EndSnippet\<close>
proof-
     {assume "x in dom(f)"
      then obtain y where
A1:       "y be object \<and> [x,y] in f" using xtuple_0_def_12 by auto
      hence "ex y being object st [x,y] in f" using A1 tarski_0_1 by auto
     }
     thus "ex it being object st ([x,it] in f if x in dom(f) otherwise it = {})" by auto
  next
    fix y1 y2
    assume A1: "y1 be object" "([x,y1] in f if x in dom(f) otherwise y1 = {})" and
           A2: "y2 be object" "([x,y2] in f if x in dom(f) otherwise y2 = {})"
    {
       assume "x in dom(f)"
       then have "[x,y1] in f \<and> [x,y2] in f" using A1 A2 by auto
       hence "y1=y2" using funct_1_def_1E[of f] by auto
     }
    thus "y1 = y2" using A1 A2 by auto
qed simp



lemma funct_1_def_2A[ty_func](*,ty_cond_cluster]*): "x be object \<Longrightarrow> f be Function \<Longrightarrow> (f. x) be set" using all_set by auto

mtheorem funct_1_th_1: "[x,y] in f \<longleftrightarrow> x in dom f \<and> y = f . x"
proof(intro conjI iffI)
  assume A1: "[x,y] in f"
  thus A2: "x in dom f" using xtuple_0_def_12 by auto
  hence "[x , f . x] in f" using A2 funct_1_def_2 by auto
  thus "y = f . x" using A1 funct_1_def_1E by mby auto
 next
  assume "x in dom f \<and> y = f . x"
  then show "[x , y] in f" using funct_1_def_2 by auto
qed print_theorems


mtheorem funct_1_th_18:
  "x in X \<longrightarrow> (id X).x = x"
proof
  assume "x in X"
  hence "[x,x] in id X" using relat_1_def_8 by auto
  thus "(id X).x = x" using funct_1_th_1 by auto
qed

text_raw \<open>\DefineSnippet{redefine_func_rng}{\<close>
theorem funct_1_def_3:
  "let f be Function
   redefine func rng f \<rightarrow> set means
     (\<lambda> it. for y being object holds y in it iff
        (ex x being object st x in dom f \<and> y = f . x))"
text_raw \<open>}%EndSnippet\<close>
proof(rule redefine_func_means_property,simp)
  assume [ty]: "f be Function"
  show "(rng f) be set" by mauto
  fix Y
  assume [ty]: "Y be set"
  show "Y = rng f \<longleftrightarrow> (for y being object holds y in Y iff
        (ex x being object st x in dom f \<and> y = f . x))"
        proof(rule iffI3)
          show "Y = rng f \<longrightarrow> (for y being object holds y in Y iff
            (ex x being object st x in dom f \<and> y = f . x))"
          proof
            assume A1: "Y = rng f"
            show "for y being object holds y in Y iff
              (ex x being object st x in dom f \<and> y = f . x)"
            proof (intro ballI impI)
              fix y
              assume [ty]: "y be object"
              show "y in Y iff
                (ex x being object st x in dom f \<and> y = f . x)"
              proof (intro iffI3)
                show "y in Y \<longrightarrow>
                     (ex x being object st x in dom f \<and> y = f . x)"
                 proof
                   assume "y in Y"
                   then obtain x where
                     [ty]: "x be object" and A2:"[x,y] in f" using A1 xtuple_0_def_13 by auto
                   have "x in dom f \<and> y = f . x " using A2 funct_1_th_1[of "f" "y" "x"] by auto
                   thus "ex x being object st x in dom f \<and> y = f . x" by auto
                 qed
                assume "ex x being object st x in dom f \<and> y = f . x"
                then obtain x where
                   "x be object" and A3:"x in dom f \<and> y = f . x" by auto
                have "[x,y] in f" using A3 funct_1_def_2 by auto
                thus "y in Y" using A1 xtuple_0_def_13 by auto
             qed
         qed simp
      qed
             assume A4: "for y being object holds y in Y iff
               (ex x being object st x in dom f \<and> y = f . x)"
             show "Y = rng f"
               proof (intro xboole_0_def_10a conjI)
                 show "Y \<subseteq> rng f"
                   proof (intro tarski_def_3b ballI impI)
                      fix y
                      assume "y in Y"
                      then obtain x where
                      T6: "x be object" and A5:"x in dom f \<and> y = f . x" using A4 by auto
                      have "[x,y] in f" using A5 funct_1_def_2 by auto
                      thus "y in rng f" using xtuple_0_def_13 by auto
                   qed mauto
                 show "rng f \<subseteq> Y"
              proof (intro tarski_def_3b ballI impI)
                fix y
                assume "y in rng f"
                then obtain x where
                   T9: "x be object" and A6: "[x,y] in f" using xtuple_0_def_13 by auto
                hence "x in dom f \<and> y = f . x" using A6 funct_1_th_1[of f y x] by auto
                thus "y in Y" using A4 by auto
              qed mauto
           qed mauto
          qed
  qed

lemmas funct_1_def_3b = funct_1_def_3[rule_format,THEN conjunct2,THEN conjunct1]

theorem funct_1_sch_Lambda:
  assumes [ty]:"A be set"
  shows "ex f be Function st dom f = A \<and> (for x st x in A holds f .x = P(x))"
 proof-
   let ?Z = "\<lambda> x y.(y = P(x))"
   have A1:"for x,y,z st ?Z(x,y) \<and> ?Z(x,z) holds y=z" by auto
   obtain Y where
     T0[ty]: "Y be set" and A0: "\<forall>y : object.  y in Y \<longleftrightarrow> (ex z be object st z in A \<and> ?Z(z,y))" using tarski_0_sch_1[of A,OF _ A1]
       by auto
      obtain Q where
        T2[ty]: "Q be Relation" and
        A2: "for x,y holds [x,y] in Q \<longleftrightarrow> x in A \<and> y in Y \<and> ?Z (x,y)"
         using assms relat_1_sch_1[of A Y "?Z", OF _ T0] by mauto
     have "for x,y1,y2 being object st [x,y1] in Q \<and> [x,y2] in Q holds y1 = y2"
     proof(intro ballI impI)
       fix x y1 y2
       assume "[x , y1] in Q \<and> [x , y2] in Q"
       hence "y1 = P(x)" "y2 = P(x)" using A2 by auto
       thus "y1=y2" using xtuple_0_th_1[of x y1]  xtuple_0_th_1[of x y2] by auto
     qed simp_all
     hence P: "Q is Function_like" using funct_1_def_1 all_set by simp
     show "ex f be Function st dom f = A \<and> (for x st x in A holds f .x = P(x))"
       proof (intro bexI[of _ _ Q] conjI)
         show "dom Q = A"
           proof (intro xboole_0_def_10a conjI)
       show "dom Q \<subseteq> A"
          proof (intro tarski_def_3b ballI impI)
            fix x
            assume "x in dom Q"
            then obtain y where
              "y be object" " [x,y] in Q" using xtuple_0_def_12 by auto
            thus "x in A" using A2 by auto
          qed mauto
          show "A \<subseteq> dom Q"
           proof (intro tarski_def_3b)
            fix x
            assume B: "x in A"
            hence "P(x) in Y" using A0 by auto
            hence "[x,P(x)] in Q" using A2 B by auto
            thus "x in dom Q" using xtuple_0_def_12 by auto
          qed mauto
        qed mauto
        show Q: "Q be Function" using T2 P by simp
        show "for x st x in A holds Q .x = P(x)"
         proof (intro ballI impI)
            fix y
            assume "y be object"
            assume B: "y in A"
            hence "P(y) in Y" using A0 by auto
            hence "[y,P(y)] in Q" using A2 B by auto
            thus "Q .y = P(y)" using funct_1_th_1[of Q "P(y)" y,OF Q] by auto
          qed simp_all
       qed simp_all
    qed


mtheorem funct_1_th_5:
  "ex f be Function st dom f = X \<and> rng f c= {z}"
proof-
    let ?Z = "\<lambda> x y.(y=z)"
      obtain P where
        T2[ty]: "P be Relation" and
        A2: "for x,y holds [x,y] in P \<longleftrightarrow> x in X \<and> y in {z} \<and> ?Z (x,y)"
         using relat_1_sch_1[of X "{z}" "?Z"] by mauto
     have "P be Relation" using T2 by simp
     have "for x,y1,y2 being object st [x,y1] in P \<and> [x,y2] in P holds y1 = y2"
     proof(intro ballI impI)
       fix x y1 y2
       assume "[x , y1] in P \<and> [x , y2] in P"
       hence "y1=z" "y2=z" using A2 by auto
       thus "y1=y2" using xtuple_0_th_1[of x y1]  xtuple_0_th_1[of x y2] by auto
     qed simp_all
     hence P: "P is Function_like" using funct_1_def_1 all_set by simp
     show "ex f be Function st dom f = X \<and> rng f c= {z}"
       proof (intro bexI[of _ _ P] conjI)
         show "dom P = X"
           proof (intro xboole_0_def_10a conjI)
       show "dom P \<subseteq> X"
          proof (intro tarski_def_3b)
            fix x
            assume "x in dom P"
            then obtain y where
              "y be object" " [x,y] in P" using xtuple_0_def_12 by auto
            thus "x in X" using A2 by auto
          qed mauto
          show "X \<subseteq> dom P"
           proof (intro tarski_def_3b)
            fix x
            assume "x in X"
            hence "[x,z] in P" using A2 tarski_def_1 by auto
            thus "x in dom P" using xtuple_0_def_12 by auto
          qed mauto
        qed mauto
        show "rng P c= {z}"
         proof (intro tarski_def_3b)
            fix y

            assume "y in rng P"
            then obtain x where
              "x be object" " [x,y] in P" using xtuple_0_def_13 by auto
            thus "y in {z}" using A2 by auto
          qed mauto
        show "P be Function" using P by simp
       qed simp
    qed

text_raw \<open>\DefineSnippet{product}{\<close>
abbreviation(input) funct_1_notation_1 ("_ *` _" [110,110] 110) where
  "f *` g \<equiv> g * f"
text_raw \<open>}%EndSnippet\<close>

abbreviation(input) funct_1_prod (infixl "\<circ>" 20) where
  "f \<circ> g \<equiv> f *` g"


text_raw \<open>\DefineSnippet{product_is_func}{\<close>
theorem [ty_func_cluster]:
  "f be Function \<and> g be Function \<Longrightarrow> (g \<circ> f) be Function_like"
text_raw \<open>}%EndSnippet\<close>
  proof-
    assume T0[ty]: "f be Function \<and> g be Function"
    hence T1: "f be Relation \<and> g be Relation" by auto
    have "for x,y1,y2 being object st [x,y1] in (g*`f) \<and> [x,y2] in (g*`f) holds y1 = y2"
     proof(intro ballI impI)
       fix x y1 y2
       assume A0: "[x , y1] in (g*`f) \<and> [x , y2] in (g*`f)"
       then obtain z1 where
          "z1 be object" and A1: "[x,z1] in f" "[z1,y1] in g" using relat_1_def_9[of f g]  by auto
       obtain z2 where
          "z2 be object" and A2: "[x,z2] in f" "[z2,y2] in g" using relat_1_def_9[of f g] A0 by auto
       have "z1=z2" using funct_1_def_1E[of f] A2 A1 by mby auto
       thus "y1 = y2" using funct_1_def_1E[of g] A2 A1 by mby auto
     qed simp_all
  thus "(g*`f) is Function_like" using funct_1_def_1 all_set by simp
qed

reserve f,g for Function

mtheorem funct_1_th_11:
  "x in dom(g \<circ> f) \<longleftrightarrow> x in dom f \<and> f. x in dom g"
proof(rule iffI3)
  let ?h = "g \<circ> f"
  show "x in dom ?h \<longrightarrow> x in dom f \<and> f. x in dom g"
    proof
      assume "x in dom ?h"
      then obtain y where [ty]: "y be object" and
       A1:"[x,y] in ?h" using xtuple_0_def_12 by auto
      then obtain z where [ty]:"z be object" and
       A2: "[x,z] in f" and
       A3: "[z,y] in g" using relat_1_def_9[of f g] by auto
      have "x in dom f" "f. x = z " using A2 xtuple_0_def_12 funct_1_def_2_uniq[of f x z]  by auto
      thus "x in dom f \<and> f. x in dom g" using A3 xtuple_0_def_12 by auto
    qed
  assume
A4: "x in dom f \<and> f. x in dom g"
  then obtain z where "z be object" and
A5: "[x,z] in f" using xtuple_0_def_12 by auto
   obtain y where "y be object" and
A6: "[f. x,y] in g" using A4 xtuple_0_def_12 by auto
   hence "[z,y] in g" using A4 A5 funct_1_def_2_uniq[of f] by auto
   hence "[x,y] in g*`f" using relat_1_def_9[of f g] A5 by auto
   thus "x in dom g*`f" using funct_1_th_1[of "g*`f",simplified] by mauto
qed

mtheorem funct_1_th_12:
  "x in dom(g*`f) \<longrightarrow> (g*`f).x = g.(f. x)"
proof
  let ?h = "g*`f"
  assume "x in dom ?h"
   then obtain y where
    "y be object" and A1: "[x,y] in ?h" using xtuple_0_def_12 by auto
    then obtain z where
      T2:"z be object" and
      A2: "[x,z] in f" and
      A3: "[z,y] in g" using relat_1_def_9[of f g] by auto
    have "x in dom f" "f. x = z " using A2 funct_1_th_1[of f z x] by auto
    hence "g.( f. x) = y" "?h . x = y " using A3 A1 funct_1_th_1[of g] funct_1_th_1[of ?h] by auto
    thus "(g*`f). x = g.(f. x)" by auto
qed

mtheorem funct_1_th_47:
  "x in dom(f|X) \<longrightarrow> (f|X).x = f. x"
proof
  assume
A1: "x in dom (f|X)"
  hence A2: "x in dom f" using relat_1_th_51 by auto
  hence "[x,(f|X).x] in (f|X)" using funct_1_def_2 A1 by mauto
  hence "[x,(f|X).x] in f" "[x,f. x] in f" using relat_1_def_11[of f X] funct_1_def_2[of f x]
        A2 by auto
  thus "(f|X).x = f. x"
    by (intro funct_1_def_1[THEN iffD1,THEN bspec,THEN bspec,THEN bspec,THEN mp]) mauto
qed

mtheorem funct_1_th_48:
  "x in dom f \<inter> X \<longrightarrow> (f|X). x = f. x"
proof
  assume "x in dom f \<inter> X"
  hence "x in dom(f|X)" using relat_1_th_55 by simp
  thus "(f|X). x = f. x" using funct_1_th_47 by simp
qed

text_raw \<open>\DefineSnippet{fraenkel_test}{\<close>
term "{f. x where x be Element-of dom f: x in X}"
text_raw \<open>}%EndSnippet\<close>

theorem [ex]:
  "cluster non empty for Function"
  unfolding inhabited_def
proof
  have "{[{},{}]} is non empty" using tarski_def_1 xboole_0_def_1 by mauto
  thus "{[{},{}]} be non empty\<bar>Function" by mauto
qed

mtheorem funct_1_th_test:
  "for f be non empty\<bar>Function holds
     rng (f|X) = { f. x where x be Element-of dom f: x in X}"
proof(intro ballI xboole_0_def_10a conjI)
  fix f assume A[ty]:"f be non empty\<bar>Function"
  show "{ f. x where x be Element-of dom f: x in X} be set" by mauto
  show "(rng (f|X)) be set" by mauto
  show "rng (f|X) \<subseteq> { f. x where x be Element-of dom f: x in X}"
  proof(intro tarski_def_3b)
    fix y assume A1: "y in rng (f|X)"
    then obtain x where
      A2: "x be object" "x in dom (f|X) \<and> (f|X).x =y" using funct_1_def_3 by mauto
    have A3: "x in dom f" "x in X" using A2 relat_1_th_51 by auto
    hence A4:"x be Element-of dom f" using Element(6) by mauto
    have "(f|X).x = f. x" using A2 funct_1_th_47 by auto
    thus "y in { f. x where x be Element-of dom f: x in X}" using A2 Fraenkel_A1_in A3 A4 by auto
  qed mauto
  show "{ f. x where x be Element-of dom f: x in X} \<subseteq> rng (f|X)"
  proof(intro tarski_def_3b)
    fix y assume A1: "y in { f. x where x be Element-of dom f: x in X}"
    obtain x where
      A2[ty]: "x be Element-of dom f" and A22: "y = f. x \<and> x in X" using A1 Fraenkel_A1_ex[OF _ _ A1] by mauto
    have "(dom f) is non empty" by mty auto
    have A3:"x in dom (f|X)" using Element(1)[of "proj1 f"] A2 A22 by (intro relat_1_th_51[THEN iffD2]) mauto
    have "x in (dom f) \<inter> X" using Element(1)[of "proj1 f"] A2 A22 xboole_0_def_4 by mty auto
    hence "y = (f|X).x" using A22 funct_1_th_48 by auto
    thus "y in rng (f|X)" using A3 funct_1_def_3 by mauto
  qed mauto
qed mauto

mtheorem funct_1_th_49:
  "x in X \<longrightarrow> (f|X).x = f. x"
proof
  have T0: "f|X be Function" using funct_1_cl relat_1_def_11[of f X] by simp
  assume
A1: "x in X"
  show "(f|X).x = f. x"
  proof(cases "x in dom f")
    assume "x in dom f"
      hence "x in dom(f|X)" using A1 relat_1_th_55 xboole_0_def_4 by mauto
      thus ?thesis using funct_1_th_47 by simp
    next
      assume A2: "not x in dom f"
      hence "not x in dom (f|X)" using relat_1_th_55 xboole_0_def_4 by mauto
      hence "(f|X).x = {}" using funct_1_def_2 by simp
      also have "... = f. x" using funct_1_def_2 A2 by simp
      finally show ?thesis by simp
  qed
qed

text_raw \<open>\DefineSnippet{funct_1_def_4}{\<close>
attr funct_1_def_4 ("one-to-one")
  "attr one-to-one for Function means (\<lambda>IT. for x1,x2 being object st x1 in dom IT \<and> x2 in dom IT holds x1 = x2)"
text_raw \<open>}%EndSnippet\<close>


text_raw \<open>\DefineSnippet{funct_1_contr_ex1}{\<close>
theorem [ex]:
  "cluster one-to-one for set"
text_raw \<open>}%EndSnippet\<close>
  unfolding inhabited_def
proof
  let ?L = "{[{},{}]}"
  have [ty]:"?L be non empty\<bar>Function" by mauto
  hence A1: "dom ?L = {{}}" using relat_1_th_3 by mauto
  have "?L is one-to-one"
  proof
    fix x1 x2 assume "x1 in dom ?L" "x2 in dom ?L"
    hence "x1={}" "x2={}" using A1 tarski_def_1 by mby auto
    thus "x1=x2" by simp
  qed mauto
  thus "{[{},{}]} be one-to-one\<bar>set" by mauto
qed


text_raw \<open>\DefineSnippet{funct_1_contr_ex2a}{\<close>
theorem [ex]: "inhabited(set\<bar>one-to-one)"
text_raw \<open>}%EndSnippet\<close>
  unfolding inhabited_def
proof
  let ?L = "{[{},{}]}"
  have [ty]:"?L be non empty\<bar>Function" by mauto
  hence A1: "dom ?L = {{}}" using relat_1_th_3 by mauto
  have "?L is one-to-one"
  proof
    fix x1 x2 assume "x1 in dom ?L" "x2 in dom ?L"
    hence "x1={}" "x2={}" using A1 tarski_def_1 by mby auto
    thus "x1=x2" by simp
  qed mauto
  thus "{[{},{}]} be set\<bar>one-to-one" by mauto
qed


text_raw \<open>\DefineSnippet{funct_1_contr_ex2b}{\<close>
theorem "\<forall>X : set\<bar>one-to-one. X be one-to-one\<bar>set"
text_raw \<open>}%EndSnippet\<close>
  by simp

attr funct_1_def_13 ("functional")
  "attr functional for set means (\<lambda>IT. for x be object st x in IT holds x be Function)"

attr funct_1_def_14 ("_-compatible" [110] 110)
  "g be Function \<Longrightarrow> attr g -compatible for Function
    means (\<lambda>f. for x be object st x in dom f holds f .x in g .x) "

attr funct_1_def_9 ("non-empty")
  "attr non-empty for Function means (\<lambda>f.  \<not> {} in rng f )"

text_raw \<open>\DefineSnippet{funct1th110}{\<close>
theorem funct_1_th_110:
  assumes [ty]:"B be non empty\<bar>functional\<bar>set"    "f be Function"
     and "f = union B"
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
       proof(intro tarski_def_3b)
         fix x
         assume "x in dom f"
         hence "[x,f. x] in f" using funct_1_th_1[of f "f. x" x] assms(2) by auto
         then obtain g where
           [ty]: "g be set" and A2: "[x, f. x] in g" "g in B" using assms(3) tarski_def_4 by auto
         have T2: "g be Element-of B" using A2(2) Element(6) by simp
         have [ty]:"g be Function" using A2(2) funct_1_def_13 assms(1) by mauto
         hence C1: "x in dom g" using A2 funct_1_th_1[of g "f. x" x] by auto
         have "dom g in ?D" using Set_of_All_in[OF _ T2] by auto
         thus "x in union ?D" using tarski_def_4[of ?D x] C1 exI[of _ "proj1 g"] by mauto
       qed mauto
    show "union ?D \<subseteq> dom f"
       proof(intro tarski_def_3b ballI impI)
         fix x
         assume "x in union ?D"
         then obtain d where
           A4: "d be set" "x in d" "d in ?D" using tarski_def_4 by mauto
         obtain g where
           [ty]: "g be Element-of B" and A6: "d = dom g" using Set_of_All_ex[OF _ _ A4(3)] by auto
         have T3: "g in B" using assms(1) Element(1)[THEN iffD1] by auto
         hence [ty]: "g be Function" using funct_1_def_13 assms(1) A6(1)  by mauto
         hence "[x,g. x] in g" using A4(2) A6 funct_1_th_1[of g "g. x" x] by auto
         hence "[x,g. x] in union B" unfolding tarski_def_4[of B "[x, g . x]",simplified] using assms exI[of _ g] T3 by auto
         thus "x in dom f" using assms funct_1_th_1 by auto
       qed mauto
  qed
  show "rng f = union ?R"
  proof(unfold xboole_0_def_10[OF all_set all_set],rule conjI)
    show "rng f \<subseteq> union ?R"
       proof(intro tarski_def_3b)
         fix y
         assume "y in rng f"
         then obtain x where
            "x be object" "x in dom f" "y = f. x" using funct_1_def_3 assms(2) by auto
         hence "[x,y] in f" using funct_1_th_1[of f y x] assms(2) by auto
         then obtain g where
          [ty]: "g be set" and A2:"[x, y] in g" "g in B" using assms(3) tarski_def_4 by auto
         have T2: "g be Element-of B" using A2 Element(6) by simp
         have T3[ty]: "g be Function" using A2 funct_1_def_13[THEN iffD1] assms(1) by mauto
         hence C1: "x in dom g" "y=g. x" using A2 funct_1_th_1[of g y x] by auto+
         have C2: "y in rng g" using funct_1_def_3[of g] C1 T3 by auto
         have "rng g in ?R" using Set_of_All_in[OF _ T2] by auto
         thus "y in union ?R" using C2 tarski_def_4 all_set by auto
       qed mauto
    show "union ?R \<subseteq> rng f"
       proof(intro tarski_def_3b)
         fix y
         assume "y in union ?R"
         then obtain r where
           A4: "r be set" "y in r" "r in ?R" using tarski_def_4 by mauto
         obtain g where
           A[ty]: "g be Element-of B" and A6:"r = rng g" using Set_of_All_ex[OF _ _ A4(3)] by auto

          have T3: "g in B" using assms(1) A6 A Element(7) by auto
         hence [ty]: "g be Function" using funct_1_def_13 assms(1) A6(1)  by mauto
          then obtain x where
           A7: "x be object" "x in dom g" "y = g. x" using funct_1_def_3 A4(2) A6 by auto
         have "[x,y] in g" using A7 funct_1_th_1[of g y x] T3 by auto
         hence "[x,y] in union B" unfolding tarski_def_4[of B "[x, y]",simplified] using assms exI[of _ g] T3 by auto
         thus "y in rng f" using xtuple_0_def_13 assms by auto
       qed mauto
     qed
   qed

text_raw \<open>\DefineSnippet{relat_1_contr}{\<close>
theorem
   "for X be set st X be non (rng X)-valued holds
      \<not> X be Function"
text_raw \<open>}%EndSnippet\<close>
proof(standard,standard,standard)
  fix X assume [ty]:"X is set" and A1:"X is non (rng X)-valued" and [ty]:"X is Function"
  have "X is (rng X)-valued" using relat_1_def_19 xboole_0_def_10 by mauto
  thus "False" using A1 by simp
qed mauto

theorem [ex]:
  "let X be set
  cluster X-valued for Function"
proof
  assume [ty]:"X be set"
  have "rng {} is empty" by mty auto
  hence "rng {} = {}" using xboole_0_lm_1 by mauto
  hence "rng {} \<subseteq> X" using xb tarski_def_3 by mauto
  thus "{} is X-valued \<bar> Function" using relat_1_def_19I by mauto
qed

end