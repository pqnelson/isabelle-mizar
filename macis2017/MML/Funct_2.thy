\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Funct_2
  imports Partfun_1 funcop_1
begin

reserve x,y,z,x1,x2,y1,y2 for object
reserve X,Y,Z for set
reserve f,g for Function

(*funct_2*)

definition quasi_total :: "Set \<Rightarrow> Set \<Rightarrow> Attr" ("_ , _ : quasi-total" 190) where funct_2_def_1a [THEN defattr_property,simp]:
   "attr X , Y :quasi-total means (\<lambda> IT. IT be (Relation-of X,Y) & 
                                          ((X = dom IT) if (Y <> {}) otherwise (IT={})))"

text_raw \<open>\DefineSnippet{expandable_modes}{\<close>
abbreviation funct_2_def_1 ("Function-of _ , _" 190)
where "Function-of X,Y \<equiv> (X,Y: quasi-total) \<parallel> (PartFunc-of X,Y)"
text_raw \<open>}%EndSnippet\<close>

mtheorem funct_2_th_2:
  "f be Function-of dom f, rng f" 
proof-
  have "dom f  c= dom f" "rng f c= rng f" using all_set by auto
  hence "f be Relation-of dom f,rng f" using assms relset_1_th_4 by simp
  hence A1: "f be PartFunc-of dom f,rng f" using assms by auto
  show "f be Function-of dom f, rng f"
  proof (cases "rng f={}")
     assume "rng f <>{}"
     thus  "f be Function-of dom f, rng f" using A1 funct_2_def_1a by simp
    next
     assume A2: "rng f = {}"
      hence "f={}" using relat_1_th_41[of f] assms by simp
     thus  "f be Function-of dom f, rng f" using A1 A2 funct_2_def_1a by simp
  qed 
qed
   
theorem funct_2_cl_ex:
  "let X be set & Y be set
   cluster (X,Y: quasi-total) for (PartFunc-of X,Y)"
proof-
  fix X Y
  assume "X be set & Y be set"
  show "(Ex (\<lambda> IT. IT be (X,Y: quasi-total) \<parallel> (PartFunc-of X,Y)))"
  proof(cases "Y={}")
    case True
      then have "{} be Function-of X,Y" using funct_1_cl_1 funct_2_def_1a funct_1_cl_1 relset_1_th_4 all_set relat_1_def_1a by auto
      thus ?thesis by auto
   next
    case K: False
      then obtain y where
        A1: "y be object" "y in Y" using  xboole_0_def_1a all_set by auto
      have "ex f be Function st dom f = X & rng f c= {y}"  using funct_1_th_5[of y X] all_set by auto
      then obtain f where
        A2: "f be Function" "dom f = X & rng f c= {y}"  by blast
      have "{y} c= Y" using A1(2) tarski_def_3 tarski_def_1b by simp
      have "rng f c= Y" using A1(2) tarski_def_3 A2 tarski_def_1b by auto 
      hence "f be PartFunc-of X,Y" using A2 relset_1_th_4 by auto
      thus ?thesis using  funct_2_def_1a A2 K by auto
    qed
qed  

theorem funct_2_th_4:
  "for X,Y,x holds for f being (Function-of X,Y) st (Y <> {} & x in X) holds f . x in rng f"
proof (intro ballI, rule impI )
  fix X Y x f
  assume T1: "f be (Function-of X,Y)"
  assume A1: "Y <> {} & x in X"
  have T2: "f be Function" "(rng f) be set" using T1 all_set relset_1_cl_1 relset_1_def_1 by auto
  hence "dom f = X" using  funct_2_def_1a T1 A1 by auto
  thus "f . x in rng f" using funct_1_def_3 A1 T2 by auto
qed

mtheorem funct_2_th_5:
  "for X,Y,x holds for f being Function-of X,Y st Y <> {} & x in X holds f . x in Y"
proof (intro ballI, rule impI)
  fix X Y x f 
  assume T1: "f be Function-of X,Y"
  hence T2: "f be Relation-of X , Y" by auto
  hence "f is (X -defined) \<bar> (Y -valued)" using relset_1_cl_2[rule_format,of X Y f] all_set by auto
  hence T3: "f is (Y-valued)" by simp
  assume "Y <> {} & x in X"
  hence "f . x in rng f" using funct_2_th_4 T1 assms all_set by auto
  thus "f . x in Y" using relat_1_def_19a T3 by auto
qed

definition onto :: "Set \<Rightarrow> Attr" ("_ -onto" [90]100) where funct_2_def_3[THEN defattr_property] :
  "attr Y -onto means (\<lambda>IT. Y be set & IT be (Y-valued \<parallel>Function) & rng IT = Y)"

definition bijective :: "Set \<Rightarrow> Attr" ("_ -bijective" [90]100) where funct_2_def_4[THEN defattr_property] :
  "attr Y -bijective means (\<lambda>IT. Y be set & IT be (Y-valued \<parallel> Function) & IT is ((Y-onto) \<bar> one-to-one))"

text_raw \<open>\DefineSnippet{funct_2_def_5}{\<close>
theorem funct_2_def_5:
  "let C be non empty\<parallel>set & D be set &
       f be (Function-of C,D) & c be Element-of C
   redefine func f . c \<rightarrow> (Element-of D)"
text_raw \<open>}%EndSnippet\<close>
proof-
  assume A0: "C be non empty\<parallel>set & (D be set) & f be (Function-of C,D) & c be Element-of C"
  show "(f . c)  be  (Element-of D)"
  proof ( cases "D is empty")
    assume  A1: "D is empty"    
    hence "dom f = {}" using A0[THEN conjunct1,THEN conjunct2] relat_1_def_1a  by auto
    hence "f . c = {}" using funct_1_def_2[THEN conjunct1,THEN conjunct2, of f c] A0[THEN conjunct1,THEN conjunct2] 
        A0[THEN conjunct1,THEN conjunct1,THEN conjunct1] relat_1_def_1a by auto
    thus "(f . c) be (Element-of D)"  using A1 subset_1_def_1 by auto
  next
    assume "not D is empty"
    hence A2:"D <> {}" by auto
    have "c in C" using A0 subset_1_def_1 by auto
    hence "(f . c) in D" using A2 funct_2_th_5 A0 by auto
    thus  "(f . c) be Element-of D" using A2 subset_1_def_1 A0 all_set by auto
  qed 
qed

text_raw \<open>\DefineSnippet{funct_2_def_7}{\<close>
theorem funct_2_def_7:
  "let A be set & B be set &
      f1 be Function-of A,B & f2 be Function-of A,B
   redefine pred f1 = f2 means
      for a be Element-of A holds f1 . a = f2 . a"
text_raw \<open>}%EndSnippet\<close>
proof(rule redefine_pred_means_property[of "A be set & B be set & f1 be (Function-of A,B) & f2 be (Function-of A,B)"])
  assume A0: "A be set & B be set & f1 be (Function-of A,B) & f2 be (Function-of A,B)"
  show " f1 = f2 iff (for a be  Element-of A holds f1 . a = f2 . a)"
  proof(rule iffI3)
    show " f1 = f2 implies (for a be  Element-of A holds f1 . a = f2 . a)" by auto
    assume A: "for a be  Element-of A holds f1 . a = f2 . a"
    show "f1=f2" 
    proof(rule tarski_th_2[rule_format,OF all_set all_set],rule iffI3)
      fix a assume "a be object"
      have A1: "f1 is Relation_like" "f2 is Relation_like" using A0 relset_1_cl_1[of A B] relset_1_def_1 by auto
      have T1: "f1 be Function" "f2 be Function" using A0 relset_1_cl_ad all_set by auto 
      have T2: "f1 be Relation-of A,B" "f2 be Relation-of A,B" using A0 by simp+
      have T3: "f1 is (B-valued)" "f2 is (B-valued)" using relset_1_cl_2[rule_format, of A B] T2 all_set by auto
      show "a in f1 implies a in f2"
      proof
        assume A2: "a in f1"
        then obtain x y where
           A3: "x be object" "y be object" "a=[x,y]" using  relat_1_def_1a A1 by auto   
        hence A4:"x in dom f1 & y = f1 .x" using funct_1_th_1[of f1 y x] T1 A2 by auto
        have "y in proj2 f1" using A2 A3 by auto
        hence "y in B" using T1 T3 relat_1_def_19a by simp
        hence A5: "dom f1 = A" "dom f2 = A" using funct_2_def_1a A0 by simp+
        hence "f1 . x = f2 . x" using A A4 Element_of_rule by auto  
        hence "[x,y] in f2" using funct_1_th_1[of f2 y x,OF T1(2) A3(2,1)] A4 A5 by auto 
        thus "a in f2" using A3 by simp
      qed        
      assume A2: "a in f2"
      then obtain x y where
        A3: "x be object" "y be object" "a=[x,y]" using  relat_1_def_1a A1 by auto   
      hence A4:"x in dom f2 & y = f2 .x" using funct_1_th_1[of f2 y x] T1 A2 by auto
        have "y in proj2 f2" using A2 A3 by auto
        hence "y in B" using T1 T3 relat_1_def_19a by simp
        hence A5: "dom f2 = A" "dom f1 = A" using funct_2_def_1a A0 by simp+
        hence "f1 . x = f2 . x" using A A4 Element_of_rule by auto  
        hence "[x,y] in f1" using funct_1_th_1[of f1 y x, OF T1(1) A3(2,1)] A4 A5 by auto 
        thus "a in f1" using A3 by simp
      qed
  qed
qed  

text_raw \<open>\DefineSnippet{funct_2_th_50}{\<close>
theorem funct_2_th_50:
  "for y be object, X be non empty \<parallel>set holds
     for f1,f2 be Function-of X,{y} holds f1=f2"
proof(intro ballI)
  fix y X f1 f2
  assume T0: "y be object" "X be non empty\<parallel>set" 
             "f1 be  Function-of X,{y}" "f2 be  Function-of X,{y}"
  show "f1 = f2" 
  proof (rule  iffD2[OF funct_2_def_7[of X "{y}" f1 f2]])
text_raw \<open>}%EndSnippet\<close>
    show "X be set & {y} be set & f1 be  Function-of X,{y} & f2 be  Function-of X,{y}" using T0 by auto
    show "for a be Element-of X holds f1 . a = f2 . a"
       proof     
         fix a assume A1: "a be Element-of X" 
         hence A2: "a in X" using T0(2) by simp  
         have "f1 .a in {y}" "f2 .a in {y}"  
           using funct_2_th_5[rule_format,of X "{y}" a f1,OF _ _ _ T0(3) _ A2]
                 funct_2_th_5[rule_format,of X "{y}" a f2,OF _ _ _ T0(4) _ A2]  all_set tarski_def_1b by auto
           thus "f1 .a = f2 .a" using tarski_def_1b by auto      
        qed
      qed
qed

theorem funct_2_lm_1:
  assumes "f be Function & g be Function"
          "rng f c= dom g" 
  shows "dom f = dom (g*`f)"
proof (unfold xboole_0_def_10[OF all_set all_set],intro conjI) 
       show "dom f \<subseteq> dom (g*`f)"
          proof (unfold tarski_def_3,intro ballI impI)      
            fix x 
            assume "x be object"
            assume K: "x in dom f"
            hence "f. x in dom g" using assms funct_1_def_3  by auto  
            thus "x in dom (g*`f)" using funct_1_th_11[of f g x] assms K by auto
          qed
          show "dom (g*`f) \<subseteq> dom f" 
           proof (unfold tarski_def_3,intro ballI impI)      
            fix x 
            assume "x in dom (g*`f)"
            thus "x in dom f" using funct_1_th_11[of f g x] assms by auto                
          qed
        qed

theorem funct_2_lm_2:
  assumes "f be Function & g be Function"
          "rng f c= dom g" 
  shows  "rng (g*`f) c= rng g"
proof(unfold tarski_def_3,intro ballI impI)
  have T1: "g*`f be Function" using assms  funct_1_cl_F[of f g] by auto
  fix y             
  assume "y in rng (g*`f)"
  then obtain x where
    C1: "x be object" "x in dom (g*`f)" "(g*`f). x = y" using funct_1_def_3 T1 assms by auto             
  have "x in dom f & f. x in dom g" using funct_1_th_11[of f g x] assms C1 by auto              
  hence "g.(f. x) = (g*`f). x" "g.(f. x) in rng g" using funct_1_th_12[of f g x] 
    funct_1_def_3[of g] assms C1 by auto             
  thus "y in rng g" using C1 by simp
qed

text_raw \<open>\DefineSnippet{funct_2_def_11}{\<close>
definition funct_2_def_11
  (" _ '/*`[_, _] _" [10,0,0,10] 90)
where
  "assume rng f c= dom p 
   func p /*`[X, Z] f \<rightarrow>
             Function-of X,Z equals
      p*`f"
text_raw \<open>}%EndSnippet\<close>

schematic_goal funct_2_def_11:
  assumes "X be set & Z be set & Y be (non empty)\<parallel>set & f be Function-of X,Y & p be (Z-valued) \<parallel>Function"
  shows "?X"
proof (induct rule: assume_equals_property[OF funct_2_def_11_def assms, of f p X Z,case_names coherence existence])
  case coherence
  assume A1: "rng f c= dom p"
    have T0: "f be Function" using assms all_set relset_1_cl_1 relset_1_def_1  by auto
    hence T1: "p*`f be Function" using assms  funct_1_cl_F[of f p] by auto
    hence T2: "p*`f is Function_like" by auto
    hence T3: "p*`f be Relation" using T1 by auto
    have A22: "rng p c= Z" using relat_1_def_19a assms by simp 
    let ?y = "the (Element-of Y)"     
    have "Y <> {}" using assms subset_1_def_1[of Y] by auto    
    hence B3: "dom f = X" using assms funct_2_def_1a by simp
    have A2: "dom f = dom (p*`f)" using funct_2_lm_1[of f p] assms A1 T0 by auto
        have A3: "rng (p*`f) c= Z"
        proof(unfold tarski_def_3,intro ballI impI)
             fix y 
             assume "y in rng (p*`f)"
             then obtain x where 
               C1: "x be object" "x in dom (p*`f)" "(p*`f). x = y" using funct_1_def_3[OF T1] by auto
             have "x in dom f & f. x in dom p" using funct_1_th_11[of f p x,OF T0] assms C1 B3 by auto 
             hence "p.(f. x) = (p*`f). x" "p.(f. x) in rng p" using funct_1_th_12[of f p x,OF T0] assms C1 
               funct_1_def_3[of p] by auto+
             thus "y in Z" using A22 C1 by simp
          qed
       hence T3: "p*`f be Relation-of X,Z" using A2 B3 relset_1_th_4[rule_format, of "p*`f" X Z] T1 by auto
  show "p*`f be (Function-of X,Z)" 
  proof(cases "Z={}")
    case T: True
    hence A: "{} be Function-of X,Z" using funct_1_cl_1 funct_2_def_1a funct_1_cl_1 relset_1_th_4 all_set relat_1_def_1a by auto
    have "(p*`f) ={}" using relat_1_th_41[of "p*`f"] T1 A3 T xboole_0_def_10[of "rng (p*`f)" "{}"] all_set by auto              
    thus  "p*`f be (X,Z: quasi-total) \<parallel> (PartFunc-of X,Z)" using A funct_2_def_1a[of "p*`f" X Z] T3 T by auto
  next
     case K: False
    hence A4: "p*`f be  Function_like \<parallel> (Relation-of X,Z)" using T2 T3 by auto
    hence  "p*`f is (X,Z: quasi-total) or (p*`f = {} & Z={})" using funct_2_def_1a[of "p*`f" X Z,THEN iffD2] A2 A3 T3 K B3 by simp
    thus  "p*`f be (X,Z: quasi-total) \<parallel> (PartFunc-of X,Z)" using A4 by auto
      
   qed
next
  case existence
  show "ex F be Function-of X,Z st True" using funct_2_cl_ex all_set by simp  
qed

theorem funct_2_cl_10:
  "let X be set 
   redefine func id X \<rightarrow> Function-of X,X"
proof-
  assume T0: "X be set"
  hence A1: "dom (id X) = X" "rng (id X) = X" using relat_1_id_dom relat_1_id_rng by auto 
  hence T1:"id X be Relation-of X,X" using relset_1_th_4 by auto      
  have T2: "id X is Function_like" using funct_1_cl_4 all_set by simp     
  show "id X be Function-of X,X"
  proof (cases "X={}")
    case True
      hence "id X={}" using relat_1_th_41[of "id X"] A1 T1 relset_1_cl_1 by auto 
      thus ?thesis using T1 T2 A1 funct_2_def_1a[of "id X" X X] by auto
  next
    case False    
       thus ?thesis using T1 T2 A1 funct_2_def_1a[of "id X" X X] by auto
  qed  
qed
  
definition funct_2_def_2 ("Funcs'( _ , _ ')") where
  "func Funcs(X,Y) \<rightarrow> set means
     \<lambda>it. for x be object holds
         x in it iff (ex f being Function st x = f & dom f = X & rng f c= Y)"

schematic_goal funct_2_def_2:
  assumes "X be set" "Y be set" shows "?X"
proof (induct rule: means_property[OF funct_2_def_2_def, of X Y,case_names existence uniqueness])
  case existence
    let ?P = "\<lambda>x. ex f being Function st x = f & dom f = X & rng f c= Y"
    have A0: "bool [:X,Y:] be set" using all_set by auto
     obtain IT where
   A1:"IT be set"  "for x being object holds x in IT iff x in bool [:X,Y:] & ?P(x)" using xboole_0_sch_1[OF A0, of ?P] by blast
     show "ex IT be set st for x be object holds x in IT iff (ex f being Function st x = f & dom f = X & rng f c= Y)"
     proof(rule bexI[of _ IT],rule ballI, rule iffI3)
       show "IT be set" using A1(1) by simp 
       fix x assume "x be object"
       show "x in IT implies (ex f being Function st x = f & dom f = X & rng f c= Y)" using A1 by auto
       assume A2: "ex f being Function st x = f & dom f = X & rng f c= Y" 
       then obtain f where 
         A3:"f be Function" "x=f & dom f = X & rng f c= Y" using all_set by blast
       have A4: "rng x c= Y" using A2 all_set by auto 
       have "dom x c= X" using  A3 by auto
       hence A5: "[:dom x,rng x:] c= [:X,Y:]" using A4 A3(1) zfmisc_1_th_96[of Y "rng x" X "dom x"] all_set by auto    
       have "x c= [:dom x,rng x:]" using relat_1_th_7[of x] A2 all_set by auto    
       hence "x c= [:X,Y:]" using A5 by auto
       hence "x in bool [:X,Y:]" using all_set zfmisc_1_def_1 by auto    
       thus "x in IT" using A1(2) A2 by auto 
     qed
   case uniqueness     
  fix A1 A2
  assume A1:"A1 be set" "(for x be object holds
         x in A1 iff (ex f being Function st x = f & dom f = X & rng f c= Y))" and
        A2: "A2 be set" "for x be object holds
         x in A2 iff (ex f being Function st x = f & dom f = X & rng f c= Y)"
    {
      fix x
      assume Z1: "x be object"
      have "x in A1 iff (ex f being Function st x = f & dom f = X & rng f c= Y)" using Z1 A1 by auto
      then have "x in A1 \<longleftrightarrow> x in A2" using Z1 A2 by auto
    }
  thus "A1 = A2" using tarski_th_2[OF A1(1) A2(1)] by auto
qed  

theorem  funct_2_cl_Funcs:
  "let X be set
   cluster Funcs(X,X) \<rightarrow> non empty"
proof-
  have "id X be Function" "dom id X=X" "rng id X=X"
    using relat_1_id_dom relat_1_id_rng funct_1_cl_4 relat_1_def_8 
       all_set by auto
  hence "id X in Funcs(X,X)" using all_set funct_2_def_2 by auto
  thus "Funcs(X,X) is non empty" using xboole_0_def_1b all_set by auto    
qed  

text_raw \<open>\DefineSnippet{Action}{\<close>  
abbreviation funct_2_action ("Action-of _ , _") where
  "Action-of O,E \<equiv> Function-of O,Funcs(E,E)"  
text_raw \<open>}%EndSnippet\<close>
theorem funct_2_cl_action:
  "ex A be Action-of O,E st True" using funct_2_cl_ex all_set by auto
 abbreviation pboole_def_1 ("ManySortedSet-of _" 190) where
  "ManySortedSet-of I \<equiv> I:total \<bar> I-defined \<parallel> Function"
  
theorem pboole_def_1_th_1:
  assumes "F be Function" "dom F=X"
  shows  "F be ManySortedSet-of X" using assms partfun_1_def_2a relat_1_def_18a funct_2_def_1a by auto 
     
theorem pboole_cl_ex:
  "let I be set
   cluster I:total \<bar> I-defined for Function"
proof-
  assume T0: "I be set"
  obtain F where
    A1: "F be Function-of I,{I}" using funct_2_cl_ex all_set by blast  
  have A2: "F be Function" using A1 all_set relset_1_cl_1 relset_1_def_1 by auto
 have "I in {I}" using tarski_def_1b by simp
  hence "{I} <>{}" by auto
  hence "dom F = I" using A1 funct_2_def_1a by simp
      thus ?thesis using A2 pboole_def_1_th_1  by auto
    qed  
      
theorem funct_2_cl_comp:
  "let I be set & f be non-empty\<bar>I:total \<parallel>Function
   cluster I:total \<bar> f-compatible for Function"
proof-
  assume A1: "I be set & f be non-empty\<bar>I:total\<parallel>Function"
  let ?P = "\<lambda>x. the Element-of f .x"
  obtain F where 
    A2: "F be Function" "dom F=I" "for x be object st x in I holds F .x = ?P(x)" using funct_1_sch_Lambda[of I ?P] A1 by blast
  have "F is I:total" using pboole_def_1_th_1 A2 by simp
  have A3: "dom f=I" using partfun_1_def_2a A1 by simp     
  have "F is f-compatible"
  proof(unfold funct_1_def_14,intro conjI)
    show S1: "f be Function" "F be Function" using A1 A2(1) by auto
    show "for x be object st x in dom F holds F .x in f .x"  
    proof(rule ballI,rule impI)
      fix x assume A4: "x be object" "x in dom F"
      hence "f. x in rng f" using A3 A2 funct_1_def_3[OF S1(1)] by auto
      hence A5: "f. x <> {}" using  funct_1_def_9 A1 by auto
      have "F .x = the Element-of f .x" using A2 A4 by auto   
      hence "(F. x) be (Element-of f .x)" using subset_1_def_1[OF all_set,THEN conjunct2] the_property by auto
      thus "F .x in f .x" using Element_of_rule1[of "f .x" "F .x"] A5 by auto
    qed      
  qed
  thus ?thesis using A2 A3 by auto      
qed         
 
theorem funcop_cl:
  "y in B implies (A --> y) be (Function-of A,B)"
proof
  assume A0: "y in B"
  hence "{y} c= B" using tarski_def_1b by auto  
  hence "[:A, {y}:] c= [:A,B:]" using zfmisc_1_th_96 all_set by auto       
  hence W0:"[:A,{y}:] be Subset-of [:A,B:]" using Subset_of_rule by auto
  hence W1: "[:A,{y}:] be Relation-of A,B" using relset_1_def_1 all_set by auto
  hence "(A --> y) be Relation-of A,B" using all_set funcop_1_def_2 by auto
  hence W2: "(A --> y) be PartFunc-of A,B" using  funcop_1_cl_1 all_set by auto
  have "dom (A --> y) = A" using funcop_1_th_13 all_set by auto
  hence "(A --> y) is (A,B: quasi-total)" using funct_2_def_1a W2 A0 by auto  
  thus "(A --> y) be (Function-of A,B)" using W2 by auto
qed

definition card_3_def_5 ("product _") where
  "func product f \<rightarrow> set means
     \<lambda>it. for x be object holds
         x in it iff (ex g st x = g & dom g = dom f & 
       (for y being object st y in dom f holds g. y in f. y))"

schematic_goal card_3_def_5:
  assumes "f be Function" shows "?X"
proof (induct rule: means_property[OF card_3_def_5_def, of f,case_names existence uniqueness])
  case existence
    let ?P = "\<lambda>x.  ex g be Function st x = g & dom g = dom f &
      (for x being object st x in dom f holds g. x in f. x)"
    have A0: "Funcs(dom f, union rng f) be set" using all_set by auto
     obtain IT where
   A1:"IT be set"  "for x being object holds x in IT iff x in Funcs(dom f, union rng f) & ?P(x)" using xboole_0_sch_1[OF A0, of ?P] by blast
     show "ex IT be set st for x be object holds x in IT iff ?P(x)"
     proof(rule bexI[of _ IT],rule ballI, rule iffI3)
       show "IT be set" using A1(1) by simp 
       fix x assume "x be object"
       show "x in IT implies ?P(x)" using A1 by auto
       assume A2: "?P(x)" 
       then obtain g where 
         A3:"g be Function" "x=g" "dom g = dom f" "for x being object st x in dom f holds g. x in f. x"
         using all_set by blast
       have "rng g c= union rng f"
       proof(unfold tarski_def_3,intro ballI impI)
         fix y assume "y in rng g"
         then obtain x where
           A4: "x be object" "x in dom g & g .x =y" using funct_1_def_3 A3(1) by auto
         have "y in f. x" "f. x in rng f" using A3 A4 funct_1_def_3[OF assms]  by auto   
         thus "y in union rng f" using tarski_def_4 all_set by auto  
         qed
       thus "x in IT" using A1(2) A2  funct_2_def_2 A3(1,2,3) all_set by auto 
     qed
   case uniqueness     
  fix A1 A2
  assume A1:"A1 be set" "(for x be object holds
         x in A1 iff (ex g be Function st x = g & dom g = dom f &
      (for x being object st x in dom f holds g. x in f. x)))" and
        A2: "A2 be set" "for x be object holds
         x in A2 iff (ex g be Function st x = g & dom g = dom f &
      (for x being object st x in dom f holds g. x in f. x))"
    {
      fix x
      assume Z1: "x be object"
      have "x in A1 iff (ex g be Function st x = g & dom g = dom f &
      (for x being object st x in dom f holds g. x in f. x))" using Z1 A1 by auto
      then have "x in A1 \<longleftrightarrow> x in A2" using Z1 A2 by auto
    }
  thus "A1 = A2" using tarski_th_2[OF A1(1) A2(1)] by auto
qed  
 
theorem card_3_cl:
  "let f be non-empty\<parallel>Function
   cluster product f \<rightarrow> non empty"
proof-
  assume A1: "f be non-empty\<parallel>Function"
  hence A2: "(dom f) be set & f be non-empty  \<bar>   dom f : total   \<parallel>  Function" using pboole_def_1_th_1 by auto
  obtain g where
     A3: "g be (dom f):total \<bar> f-compatible\<parallel>Function" using funct_2_cl_comp[OF A2] by auto
  have "for y being object st y in dom f holds g. y in f. y"  using funct_1_def_14 A3 by auto 
  hence "g in product f" using A1 A3 partfun_1_def_2a card_3_def_5[of f] by auto
  thus "product f is non empty" using xboole_0_def_1b all_set by auto
qed  

end