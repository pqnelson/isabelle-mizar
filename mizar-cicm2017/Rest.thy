\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Rest
  imports Partfun_1
begin

reserve x,y,z,x1,x2,y1,y2 for object
reserve X,Y,Z for set

(*funct_2*)

definition quasi_total :: "Set \<Rightarrow> Set \<Rightarrow> Attr" ("_ , _ : quasi-total" 190) where funct_2_def_1a [THEN defattr_property,simp]:
   "attr X , Y :quasi-total means (\<lambda> IT. IT be (Relation-of X,Y) & 
                                          ((X = dom IT) if (Y <> {}) otherwise (IT={})))"

text_raw \<open>\DefineSnippet{expandable_modes}{\<close>
abbreviation funct_2_def_1 ("Function-of _ , _" 190)
where "Function-of X,Y \<equiv> (X,Y: quasi-total) \<parallel> (PartFunc-of X,Y)"
text_raw \<open>}%EndSnippet\<close>

theorem "Function-of X,Y \<equiv>  (X,Y: quasi-total) \<parallel> (PartFunc-of X,Y)" by simp
theorem "Function-of X,Y \<equiv>  (X,Y: quasi-total) \<parallel> ( Function_like \<parallel> (Relation-of X,Y))" by simp
theorem "Function-of X,Y \<equiv>  (X,Y: quasi-total) \<parallel> ( Function_like \<parallel> (Subset-of [:X,Y:]))" using relset_1_def_1 by simp

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
        

          
mtheorem funct_2_cl_ex:
  "let X be set & Y be set
   cluster (X,Y: quasi-total) for (PartFunc-of X,Y)"
proof-
  fix X Y
  assume "X be set & Y be set"
  show "(Ex (\<lambda> IT. IT be (X,Y: quasi-total) \<parallel> (PartFunc-of X,Y)))"
  proof(cases "Y={}")
    case True
      then have "{} be Function-of X,Y" using funct_1_cl_1 funct_2_def_1a funct_1_cl_1 relset_1_th_4 all_set by auto
      thus ?thesis by auto
   next
    case K: False
      then obtain y where
        A1: "y be object" "y in Y" using  xboole_0_def_1a all_set by auto
      have "ex f be Function st dom f = X & rng f c= {y}"  using funct_1_th_5[of y X] all_set by auto
      then obtain f where
        A2: "f be Function" "dom f = X & rng f c= {y}"  by blast
      have "{y} c= Y" using A1(2) tarski_def_3 by simp
      have "rng f c= Y" using A1(2) tarski_def_3 A2 by auto 
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
 
  



  
text_raw \<open>\DefineSnippet{funct_2_def_5_2}{\<close> 
definition funct_2_def_5_2 (" _ , _ : _ . _" 190) where
  "func C, D : f . c \<rightarrow> (Element-of D) equals f . c"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{funct_2_def_5_1}{\<close> 
definition funct_2_def_5_1 (" _ : _ . _" 190) where
   "func D : f . c \<rightarrow> (Element-of D) equals f . c"
text_raw \<open>}%EndSnippet\<close>
  
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
    hence "dom f = {}" using A0[THEN conjunct1,THEN conjunct2]  by auto
    hence "f . c = {}" using funct_1_def_2[THEN conjunct1,THEN conjunct2, of f c] A0[THEN conjunct1,THEN conjunct2] 
        A0[THEN conjunct1,THEN conjunct1,THEN conjunct1] by auto
    thus "(f . c) be (Element-of D)"  using A1 subset_1_def_1 by auto
  next
    assume "not D is empty"
    hence A2:"D <> {}" by auto
    have "c in C" using A0 subset_1_def_1 by auto
    hence "(f . c) in D" using A2 funct_2_th_5 A0 by auto
    thus  "(f . c) be Element-of D" using A2 subset_1_def_1 A0 all_set by auto
  qed 
qed

  
schematic_goal funct_2_def_5_1:
  fixes C
  assumes "C be non empty\<parallel>set & (D be set) & f be (Function-of C,D) & c be Element-of C" shows "?X"
proof (rule equals_property[OF funct_2_def_5_1_def], cases "D is empty")
  assume  A1: "D is empty"    
  hence "dom f = {}" using assms[THEN conjunct1,THEN conjunct2]  by auto
  hence "f . c = {}" using funct_1_def_2[THEN conjunct1,THEN conjunct2, of f c] assms[THEN conjunct1,THEN conjunct2] 
    assms[THEN conjunct1,THEN conjunct1,THEN conjunct1] by auto
    thus "(f . c) be (Element-of D)"  using A1 subset_1_def_1 by auto
next
  assume "not D is empty"
  hence A2:"D <> {}" by auto
  have "c in C" using assms subset_1_def_1 by auto
  hence "(f . c) in D" using A2 funct_2_th_5 assms by auto
  thus  "(f . c) be Element-of D" using A2 subset_1_def_1 assms all_set by auto
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
  
(*abbreviation (input)  funct_2_redefine (" _ =funct'_2'_def'_7[! _ ,_ !] _" [90,90,90,90]90)
where "f =funct_2_def_7[! A,B !] g \<equiv> f = g"   
*)  


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
                 funct_2_th_5[rule_format,of X "{y}" a f2,OF _ _ _ T0(4) _ A2]  all_set by auto
           thus "f1 .a = f2 .a" by auto      
        qed
      qed
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
    have A2: "dom f = dom (p*`f)"
       proof (unfold xboole_0_def_10[OF all_set all_set],intro conjI) 
       show "dom f \<subseteq> dom (p*`f)"
          proof (unfold tarski_def_3,intro ballI impI)      
            fix x 
            assume "x be object"
            assume K: "x in dom f"
            hence "f. x in dom p" using A1 B3 funct_1_def_3[OF T0]  by auto  
            thus "x in dom (p*`f)" using funct_1_th_11[of f p x,OF T0] assms K B3 by auto
          qed
          show "dom (p*`f) \<subseteq> dom f" 
           proof (unfold tarski_def_3,intro ballI impI)      
            fix x 
            assume "x in dom (p*`f)"
            thus "x in dom f" using funct_1_th_11[of f p x,OF T0] assms B3 by auto                
          qed
        qed
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
    hence A: "{} be Function-of X,Z" using funct_1_cl_1 funct_2_def_1a funct_1_cl_1 relset_1_th_4 all_set by auto
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

(*binop_1*)

text_raw \<open>\DefineSnippet{binop_0_def_1_prefix}{\<close>
definition binop_0_def_1_prefix (" _ . \<lparr> _ , _ \<rparr>"[90,90,90]) where
  (*let f be Function & a be object & b be object*) 
  "func f . \<lparr> a , b \<rparr> \<rightarrow> set equals 
        f.[a,b]"
  
schematic_goal binop_0_def_1:
  assumes "f be Function & a be object & b be object" shows "?X"
text_raw \<open>}%EndSnippet\<close>

proof (rule equals_property[OF binop_0_def_1_prefix_def])    
  show "(f.[a,b]) be set" using assms funct_1_def_2 by simp
qed

theorem   binop_0_def_2_1:
 "let A be non empty \<parallel> set & B be non empty \<parallel> set & C be set &
        f be (Function-of [:A,B:],C) & a be (Element-of A) & b be (Element-of B)
  redefine func f.\<lparr>a,b\<rparr>  \<rightarrow> Element-of C"
proof-
  assume A0: "A be non empty \<parallel> set & B be non empty \<parallel> set & C be set &
        f be (Function-of [:A,B:],C) & a be (Element-of A) & b be (Element-of B)"
 have "a in A & b in B " using A0 subset_1_def_1 by auto
  hence "[a,b] in [:A,B:]" by auto
  hence "[:A,B:] be non empty\<parallel>set" "[a,b] be Element-of [:A,B:]" using subset_1_def_1[of "[:A,B:]" "[a,b]"] all_set by auto
  hence A1: "(f.[a,b]) be Element-of C" using A0 funct_2_def_5[of "[:A,B:]" "C" "f" "[a,b]"]  by auto
  have "f be Function" using A0 relset_1_cl_ad all_set by auto
  thus "f.\<lparr> a, b \<rparr> be Element-of C" using A0 binop_0_def_1 all_set A1 by auto
qed
  
definition binop_0_def_2_prefix (" _ :  _ . \<lparr> _ , _ \<rparr> ") where
  "func (C : f.\<lparr>a,b\<rparr> ) \<rightarrow> Element-of C equals 
        f.\<lparr>a,b\<rparr>"

schematic_goal binop_0_def_2_schem:
  assumes "A be non empty \<parallel> set & B be non empty \<parallel> set & C be set &
        f be (Function-of [:A,B:],C) & a be (Element-of A) & b be (Element-of B)" shows "?X"
proof (rule equals_property[OF binop_0_def_2_prefix_def])    
  have "a in A & b in B " using assms subset_1_def_1 by auto
  hence "[a,b] in [:A,B:]" by auto
  hence "[:A,B:] be non empty\<parallel>set" "[a,b] be Element-of [:A,B:]" using subset_1_def_1[of "[:A,B:]" "[a,b]"] all_set by auto
  hence A1: "(f.[a,b]) be Element-of C" using assms funct_2_def_5[of "[:A,B:]" "C" "f" "[a,b]"]  by auto
  have "f be Function" using assms relset_1_cl_ad all_set by auto
  thus "f.\<lparr> a, b \<rparr> be Element-of C" using assms binop_0_def_1 all_set A1 by auto
qed

abbreviation  (input) binop_1_mode_1 ("UnOp-of _" 190) where 
  "UnOp-of X \<equiv> Function-of X , X"

definition binop_1_mode_2 ("BinOp-of _" 190) where 
  "BinOp-of X \<equiv> Function-of [:X,X:] , X"

theorem relat_1_cl_20:
   "let X be empty \<parallel> set 
    cluster dom X \<rightarrow> empty" by auto

schematic_goal binop_0_def_20:
  assumes "A be set & (f be BinOp-of A) & (a be Element-of A) & (b be Element-of A)" shows "?X"
proof (rule equals_property[OF binop_0_def_2_prefix_def])  
  have W: "f be Function" using assms relset_1_cl_ad all_set binop_1_mode_2_def by auto
   hence Z: "f.\<lparr> a,b \<rparr> = f.[a,b]" using binop_0_def_1 by simp 
   show "f.\<lparr>a,b\<rparr> be (Element-of A)"
    proof(cases "A={}")
      assume A1: "A={}"
       hence "f = {}" using funct_2_def_1a assms all_set binop_1_mode_2_def by simp 
       hence "not [a,b] in dom f" using relat_1_cl_20 by simp
       hence "f.[a,b] = {}" using funct_1_def_2 W by simp
      thus  "f.\<lparr>a,b\<rparr> be (Element-of A)" using A1 Z by simp
    next
      assume A2: "A<>{} "
       hence "A is non empty" using xboole_0_lm_1 assms by auto   
       hence "dom f = [:A,A:]" "a in A" "b in A" using A2 subset_1_def_1 funct_2_def_1a assms binop_1_mode_2_def by auto
       hence "[a,b] in [:A,A:]" using all_set  by auto
       hence "[:A,A:] be non empty\<parallel>set" "[a,b] be Element-of [:A,A:]" using subset_1_def_1[of "[:A,A:]" "[a,b]"] all_set by auto
       hence "(f.[a,b]) be Element-of A" using assms funct_2_def_5[of "[:A,A:]" "A" "f" "[a,b]"] binop_1_mode_2_def by auto   
      thus  "f.\<lparr>a,b\<rparr> be (Element-of A)" using Z by auto
    qed 
qed

end