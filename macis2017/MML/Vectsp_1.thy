\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Vectsp_1 
  imports Z2 Rlvect_1 Group_1
begin

lemma Z2_cl_7:
  "cluster Z \<rightarrow> add-associative \<bar> right-zeroed \<bar> right-complementable \<bar> Abelian \<bar> non empty-struct" 
proof(intro attr_attr[THEN iffD2] conjI)
  have T0:"Z be addMagma" "Z be addLoopStr" using Z doubleLoopStr addMagma addLoopStr by simp+
  show "Z is add-associative" 
  proof(unfold rlvect_1_def_3,rule conjI,rule T0(1),intro ballI)
    fix u v w assume T1: "u be Element-of-struct Z" "v be Element-of-struct Z"  "w be Element-of-struct Z"
    hence A1: "u=One or u = Zero" "v=One or v = Zero" "w=One or w = Zero" using Z2d(3) by simp+
    show "u \<oplus>\<^sub>Z v \<oplus>\<^sub>Z w = u \<oplus>\<^sub>Z (v \<oplus>\<^sub>Z w)"
    proof (cases "u=One")
      case C1: True
        show ?thesis
        proof(cases "v=One")
          case C2:True 
            show ?thesis
            proof(cases "w=One")
              case True thus ?thesis using C1 C2 Z2d(6,7,8,9) by auto next
              case False thus ?thesis using C1 C2 Z2d(6,7,8,9) A1 by auto    
            qed next
          case C2:False 
            show ?thesis
            proof(cases "w=One")
              case True thus ?thesis using C1 C2 Z2d(6,7,8,9) A1 by auto next
              case False thus ?thesis using C1 C2 Z2d(6,7,8,9) A1 by auto    
            qed
          qed next
      case C1: False
        show ?thesis
        proof(cases "v=One")
          case C2:True 
            show ?thesis
            proof(cases "w=One")
              case True thus ?thesis using C1 C2 Z2d(6,7,8,9) A1 by auto next
              case False thus ?thesis using C1 C2 Z2d(6,7,8,9) A1 by auto    
            qed next
          case C2:False 
            show ?thesis
            proof(cases "w=One")
              case True thus ?thesis using C1 C2 Z2d(6,7,8,9) A1 by auto next
              case False thus ?thesis using C1 C2 Z2d(6,7,8,9) A1 by auto    
            qed
        qed      
    qed       
  qed   
  show "Z is right-zeroed"
  proof(unfold rlvect_1_def_4,rule conjI,rule T0(2),intro ballI)
     fix v assume "v be Element-of-struct Z" 
     hence  "v=One or v = Zero"  using Z2d(3) by simp
     thus "v \<oplus>\<^sub>Z 0\<^sub>Z = v" using Z2d(3,4,6,8) by auto
   qed 
  show "Z is right-complementable"
  proof(unfold algstr_0_def_16,rule conjI,rule T0(2),intro ballI,unfold algstr_0_def_11)
    fix x assume A1:"x be Element-of-struct Z"
    show "Z be addLoopStr & x be Element-of-struct Z & (\<exists>y be Element-of-struct Z. x \<oplus>\<^sub>Z y = 0\<^sub>Z)"
      proof(intro conjI,rule T0(2),rule A1,rule bexI[of _ x])
        have  "x=One or x = Zero"  using A1 Z2d(3) by simp
        thus "x \<oplus>\<^sub>Z x = 0\<^sub>Z" using A1 Z2d(4,6,9)  by auto
        show "x be Element-of-struct Z" using A1 by simp
      qed  
  qed
  show "Z is Abelian"
  proof(unfold rlvect_1_def_2,rule conjI,rule T0(1),intro ballI)
    fix u v assume T1: "u be Element-of-struct Z" "v be Element-of-struct Z"  
    hence A1: "u=One or u = Zero" "v=One or v = Zero" using Z2d(3) by simp+
    show "u \<oplus>\<^sub>Z v = v \<oplus>\<^sub>Z u"
    proof (cases "u=One")
      case C1: True
        show ?thesis 
        proof(cases "v=One")
          case C2:True 
            show ?thesis using C1 C2 Z2d(6,7,8,9) by simp next 
          case C2:False 
           show ?thesis using C1 C2 Z2d(6,7,8,9) A1 by simp
        qed next
      case C1: False
        show ?thesis 
        proof(cases "v=One")
          case C2:True 
            show ?thesis using C1 C2 Z2d(6,7,8,9) A1 by simp next 
          case C2:False 
           show ?thesis using C1 C2 Z2d(6,7,8,9) A1 by simp
        qed     
     qed  
   qed
  have "the carrier of Z is non empty" using Z2d(14) by auto
  thus "Z is non empty-struct" using T0 struct_0_def_1_b addMagma one_sorted by auto
qed    

theorem vectsp_1_cl_7:
  "cluster add-associative\<bar>right-zeroed\<bar>right-complementable\<bar> Abelian  for
    non empty-struct\<parallel>addLoopStr"
proof
  show "Z is add-associative\<bar>right-zeroed\<bar>right-complementable\<bar>Abelian" using Z2_cl_7 by auto
  show "Z be non empty-struct  \<parallel>  addLoopStr" using Z2_cl_7 Z doubleLoopStr addLoopStr by auto
qed    

abbreviation(input) 
  "AddGroup \<equiv> add-associative\<bar>right-zeroed\<bar>right-complementable\<bar>non empty-struct\<parallel>addLoopStr"

abbreviation 
  "AbGroup \<equiv> Abelian\<parallel>AddGroup"

definition right_distributive_M ("right-distributive") where vectsp_1_def_2 [THEN defattr_property]:
   "attr right-distributive means (\<lambda> M. M be non empty-struct\<parallel>doubleLoopStr & 
     (for a,b,c be Element-of-struct M holds a \<otimes>\<^sub>M (b \<oplus>\<^sub>M c) = a \<otimes>\<^sub>M b \<oplus>\<^sub>M  a \<otimes>\<^sub>M c))"
lemmas vectsp_1_def_2a = vectsp_1_def_2[THEN iffD1,THEN conjunct2,rule_format]

   
   
definition left_distributive_M ("left-distributive") where vectsp_1_def_3 [THEN defattr_property]:
   "attr left-distributive means (\<lambda> M. M be non empty-struct\<parallel>doubleLoopStr & 
     (for a,b,c be Element-of-struct M holds (b \<oplus>\<^sub>M c) \<otimes>\<^sub>M a = b \<otimes>\<^sub>M a \<oplus>\<^sub>M  c \<otimes>\<^sub>M a))"
lemmas vectsp_1_def_3a = vectsp_1_def_3[THEN iffD1,THEN conjunct2,rule_format]

definition right_unital_M ("right-unital") where vectsp_1_def_4 [THEN defattr_property]:
   "attr right-unital means (\<lambda> M. M be non empty-struct\<parallel>doubleLoopStr & 
     (for a be Element-of-struct M holds a \<otimes>\<^sub>M 1\<^sub>M = a))"

definition well_unital_M ("well-unital") where vectsp_1_def_6 [THEN defattr_property]:
   "attr well-unital means (\<lambda> M. M be non empty-struct\<parallel>doubleLoopStr & 
     (for a be Element-of-struct M holds a \<otimes>\<^sub>M 1\<^sub>M = a & 1\<^sub>M \<otimes>\<^sub>M a = a))"
lemmas vectsp_1_def_6a = vectsp_1_def_6[THEN iffD1,THEN conjunct2,rule_format]
 
lemma Z2_cl_15:
  "cluster Z \<rightarrow> well-unital" 
proof(unfold vectsp_1_def_6,rule conjI)
  show "Z  be non empty-struct\<parallel>doubleLoopStr" using Z Z2_cl_7 by auto
  show "for a be Element-of-struct Z holds a \<otimes>\<^sub>Z 1\<^sub>Z = a & 1\<^sub>Z \<otimes>\<^sub>Z a = a"
  proof(rule ballI)
    fix a assume A1: "a be Element-of-struct Z"
    show "a \<otimes>\<^sub>Z 1\<^sub>Z = a & (1\<^sub>Z) \<otimes>\<^sub>Z a = a"
    proof (cases "a=One")
      case  True
       thus ?thesis using Z2d(5,13) by auto next
      case False
        hence "a=Zero" using Z2d(3)[of a] A1 by auto
        thus ?thesis using Z2d(5,11,12) by auto next
    qed       
  qed   
qed   
  
theorem vectsp_1_cl_15:
  "cluster well-unital for non empty-struct\<parallel>multLoopStr_0"
proof
  show "Z is well-unital" using  Z2_cl_15 by simp
  show " Z be non empty-struct  \<parallel>  multLoopStr_0" using Z2_cl_7 Z doubleLoopStr_inheritance by auto    
qed  
  
theorem vectsp_1_reduce_1:
  "let L be well-unital\<bar>non empty-struct\<parallel>multLoopStr_0 & x be Element-of-struct L
   reduce x\<otimes>\<^sub>L 1\<^sub>L to x" using vectsp_1_def_6 by auto

theorem vectsp_1_reduce_2:
  "let L be well-unital\<bar>non empty-struct\<parallel>multLoopStr_0 & x be Element-of-struct L
   reduce (1\<^sub>L) \<otimes>\<^sub>L x to x" using vectsp_1_def_6 by auto
  
definition distributive_M ("distributive") where vectsp_1_def_7 [THEN defattr_property]:
   "attr distributive means (\<lambda> M. M be non empty-struct\<parallel>doubleLoopStr & 
     (for a,b,c be Element-of-struct M holds a \<otimes>\<^sub>M (b \<oplus>\<^sub>M c) = a \<otimes>\<^sub>M b \<oplus>\<^sub>M  a \<otimes>\<^sub>M c & (b \<oplus>\<^sub>M c) \<otimes>\<^sub>M a = b \<otimes>\<^sub>M a \<oplus>\<^sub>M c \<otimes>\<^sub>M a))"  

   
definition left_unital_M ("left-unital") where vectsp_1_def_8 [THEN defattr_property]:
   "attr left-unital means (\<lambda> M. M be non empty-struct\<parallel>doubleLoopStr & 
     (for a be Element-of-struct M holds 1\<^sub>M \<otimes>\<^sub>M a = a))"
 
   
theorem vectsp_1_def_9:
  "let  M be non empty-struct\<parallel>multLoopStr_0
   redefine attr M is almost-left-invertible means
      for x be Element-of-struct M st x <> 0\<^sub>M holds ex y be Element-of-struct M st y \<otimes>\<^sub>M x = 1\<^sub>M"
proof(rule iffI3 )
  assume T0: "M be non empty-struct\<parallel>multLoopStr_0"
  show "M is almost-left-invertible implies (for x be Element-of-struct M st x <>0\<^sub>M holds ex y be Element-of-struct M st y \<otimes>\<^sub>M x = 1\<^sub>M)"
    by (unfold algstr_0_def_39 algstr_0_def_27,auto)
  assume A1: "for x be Element-of-struct M st x <>0\<^sub>M holds ex y be Element-of-struct M st y \<otimes>\<^sub>M x = 1\<^sub>M"    
  show "M is almost-left-invertible"
  proof(unfold algstr_0_def_39 algstr_0_def_27,intro conjI ballI impI)
    show "M be multLoopStr_0" using T0 by auto
    fix x assume T1:"x be Element-of-struct M" "x <>0\<^sub>M"
    show "M be multLoopStr" "x be Element-of-struct M" using T0 T1 multLoopStr_0_inheritance by auto 
    show "ex y be Element-of-struct M st y \<otimes>\<^sub>M x = 1\<^sub>M" using A1 T1 by auto    
  qed
qed

theorem vectsp_1_cl_20:
  "cluster distributive \<rightarrow> left-distributive \<bar>right-distributive for 
    non empty-struct \<parallel>doubleLoopStr"
   by (intro ballI impI,rule attr_attr[THEN iffD2],rule conjI, unfold vectsp_1_def_2 vectsp_1_def_3 vectsp_1_def_7,auto)

theorem vectsp_1_cl_21:
  "cluster left-distributive \<bar>right-distributive \<rightarrow> distributive  for 
    non empty-struct \<parallel>doubleLoopStr"
   by (unfold attr_attr, intro ballI uncurry impI, unfold vectsp_1_def_2 vectsp_1_def_3 vectsp_1_def_7,auto) 

theorem vectsp_1_cl_22:
  "cluster well-unital \<rightarrow> left-unital \<bar>right-unital for 
    non empty-struct \<parallel>doubleLoopStr"
   by (intro ballI impI,rule attr_attr[THEN iffD2],rule conjI, unfold vectsp_1_def_4 vectsp_1_def_6 vectsp_1_def_8,auto)

theorem vectsp_1_cl_23:
  "cluster left-unital \<bar>right-unital \<rightarrow> well-unital  for 
    non empty-struct \<parallel>doubleLoopStr"
   by (unfold attr_attr, intro ballI uncurry impI,unfold vectsp_1_def_4 vectsp_1_def_6 vectsp_1_def_8,auto) 

theorem Z2_cl_24:
  "cluster Z \<rightarrow> commutative\<bar>associative\<bar>unital"
proof(intro attr_attr[THEN iffD2] conjI)
  have A1: "Z be multMagma" using Z multMagma doubleLoopStr by simp 
  show "Z is commutative"
  proof(unfold group_1_def_12,rule conjI,rule A1,intro ballI)
    fix u v assume T1: "u be Element-of-struct Z" "v be Element-of-struct Z"  
    hence A1: "u=One or u = Zero" "v=One or v = Zero" using Z2d(3) by simp+
    show "u \<otimes>\<^sub>Z v = v \<otimes>\<^sub>Z u"
    proof (cases "u=One")
      case C1: True
        show ?thesis 
        proof(cases "v=One",simp add:C1)
          case False thus ?thesis using C1 Z2d(11,12) A1 by simp
        qed next
      case C1: False
        hence C1:"u=Zero" using A1 by auto   
        show ?thesis 
        proof(cases "v=One",simp add:C1 Z2d(11,12))
          case False 
           thus ?thesis using C1 A1 by simp
        qed     
    qed  
  qed 
  show "Z is associative"
      proof(unfold group_1_def_3,rule conjI,rule A1,intro ballI)
        fix u v w assume T1: "u be Element-of-struct Z" "v be Element-of-struct Z"  "w be Element-of-struct Z"
         hence A1: "u=One or u = Zero" "v=One or v = Zero" "w=One or w = Zero" using Z2d(3) by simp+
    show "u \<otimes>\<^sub>Z v \<otimes>\<^sub>Z w = u \<otimes>\<^sub>Z (v \<otimes>\<^sub>Z w)" 
    proof (cases "u=One")
      case C1: True
        show ?thesis
        proof(cases "v=One")
          case C2:True 
            show ?thesis
            proof(cases "w=One",simp add:C1 C2 Z2d(13))
              case False thus ?thesis using C1 C2 Z2d(11,12,13) A1 by auto    
            qed next
          case False hence C2:"v=Zero" using A1 by simp
            show ?thesis
            proof(cases "w=One",simp add:C1 C2 Z2d(11,12,13))
               case False thus ?thesis using C1 C2 Z2d(10,11,12,13) A1 by auto    
            qed
          qed next
      case False hence C1:"u=Zero" using A1 by simp
        show ?thesis
        proof(cases "v=One")
          case C2:True 
            show ?thesis
            proof(cases "w=One",simp add:C1 C2 Z2d(11,13) A1)
              case False thus ?thesis using C1 C2 Z2d(10,11,12,13) A1 by auto    
            qed next
          case False hence C2:"v=Zero" using A1 by simp
            show ?thesis
            proof(cases "w=One",simp add:C1 C2 Z2d(10,11,12,13) A1)
              case False thus ?thesis using C1 C2 Z2d(10,11,12,13) A1 by auto    
            qed
        qed      
    qed       
  qed 
  show "Z is unital"
  proof(unfold group_1_def_1,rule conjI,rule A1,rule bexI[of _ "1\<^sub>Z"],rule ballI,rule conjI)
    show "1\<^sub>Z be Element-of-struct Z" by (simp add:Z2d(2,5))
    fix h assume A1:"h be Element-of-struct Z"
    hence "h=One or h=Zero" "1\<^sub>Z = One" using Z2d(5,3) by simp+
    thus "h \<otimes>\<^sub>Z 1\<^sub>Z = h" " 1\<^sub>Z \<otimes>\<^sub>Z h = h" using Z2d(11,12,13) by auto +   
  qed   
qed  

theorem vectsp_1_cl_24:
  "cluster commutative\<bar>associative for non empty-struct \<parallel>multMagma"
proof
   show "Z is commutative\<bar>associative" using Z2_cl_24 by auto
   show "Z be non empty-struct \<parallel>multMagma" using Z Z2_cl_7 multMagma doubleLoopStr by auto  
 qed

   
theorem vectsp_1_cl_25:
  "cluster commutative\<bar>associative\<bar>unital for non empty-struct \<parallel>multLoopStr"
proof
   show "Z is commutative\<bar>associative\<bar>unital" using Z2_cl_24 by auto
   show "Z be non empty-struct \<parallel>multLoopStr" using Z Z2_cl_7 multLoopStr doubleLoopStr by auto  
 qed  

theorem Z2_cl_26:
  "cluster Z \<rightarrow> almost-left-invertible\<bar>distributive\<bar>non degenerated\<bar>strict doubleLoopStr"
proof(intro attr_attr[THEN iffD2] conjI)
  have A1: "Z be multLoopStr_0" "Z be multLoopStr" "Z be non empty-struct  \<parallel>  doubleLoopStr" "Z be ZeroOneStr"
     using  doubleLoopStr multLoopStr_0 multLoopStr Z Z2_cl_7 ZeroOneStr by auto 
  show "Z is  almost-left-invertible"
  proof(unfold algstr_0_def_39 algstr_0_def_27,intro ballI conjI impI,rule A1(1),rule A1(2),simp,rule bexI[of _ "1\<^sub>Z"])
    fix x assume "x be Element-of-struct Z" "x<> 0\<^sub>Z"
    thus "1\<^sub>Z \<otimes>\<^sub>Z x = 1\<^sub>Z" "1\<^sub>Z be Element-of-struct Z" using Z2d(3)[of x] Z2d(2,4,5,13) by auto  
  qed  
  show "Z is distributive"
  proof(unfold vectsp_1_def_7,rule conjI,rule A1(3),intro ballI)
        fix u v w assume T1: "u be Element-of-struct Z" "v be Element-of-struct Z"  "w be Element-of-struct Z"
         hence A1: "u=One or u = Zero" "v=One or v = Zero" "w=One or w = Zero" using Z2d(3) by simp+
    show "u \<otimes>\<^sub>Z (v \<oplus>\<^sub>Z w) = (u \<otimes>\<^sub>Z v) \<oplus>\<^sub>Z (u \<otimes>\<^sub>Z w) & (v \<oplus>\<^sub>Z w) \<otimes>\<^sub>Z u = (v \<otimes>\<^sub>Z u) \<oplus>\<^sub>Z (w \<otimes>\<^sub>Z u)" 
    proof (cases "u=One")
      case C1: True
        show ?thesis
        proof(cases "v=One")
          case C2:True 
            show ?thesis
            proof(cases "w=One",simp add:C1 C2 Z2d)
              case False  thus ?thesis using C1 C2 Z2d(6,7,8,9,10,11,12,13) A1 by auto    
            qed next
          case False hence C2:"v=Zero" using A1 by simp
            show ?thesis
            proof(cases "w=One",simp add:C1 C2 Z2d(7,11,12,13))
               case False thus ?thesis using C1 C2 Z2d(6,7,8,9,10,11,12,13) A1 by auto    
            qed
          qed next
      case False hence C1:"u=Zero" using A1 by simp
        show ?thesis
        proof(cases "v=One")
          case C2:True 
            show ?thesis
            proof(cases "w=One",simp add:C1 C2 Z2d(6,9,10,11,12,13) A1)
              case False thus ?thesis using C1 C2 Z2d(6,7,8,9,10,11,12,13) A1 by auto    
            qed next
          case False hence C2:"v=Zero" using A1 by simp
            show ?thesis
            proof(cases "w=One",simp add:C1 C2 Z2d(6,7,10,11,12,13) A1)
              case False thus ?thesis using C1 C2 Z2d(6,7,8,9,10,11,12,13) A1 A1 by auto    
            qed
        qed      
    qed       
  qed 
  show "Z is non degenerated" unfolding struct_0_def_8_b using A1(4) Z2d(4,5) by auto
  have "domain_of doubleLoopStr = 
      dom ({[carrier , { Zero , One }]} \<union> {[addF , addZ2]} \<union> {[multF , multZ2]} \<union> {[OneF , One]} \<union> {[ZeroF , Zero]})"  
       using doubleLoopStr Dom_5 by auto  
  thus  "Z is strict doubleLoopStr" using Z strict by auto
qed   

text_raw \<open>\DefineSnippet{vectsp1cl26}{\<close>
theorem vectsp_1_cl_26:
 "cluster add-associative \<bar> right-zeroed \<bar> right-complementable \<bar> 
          Abelian \<bar> commutative \<bar> associative \<bar> left-unital\<bar>
          right-unital \<bar> distributive \<bar> almost-left-invertible\<bar>
          non degenerated \<bar> well-unital \<bar> strict doubleLoopStr 
     for non empty-struct \<parallel> doubleLoopStr" 
text_raw \<open>}%EndSnippet\<close>
proof(rule bexI[of _ "Z"],intro attr_attr[THEN iffD2] conjI) 
  show "Z is add-associative" "Z is right-zeroed" "Z is right-complementable" "Z is Abelian"  
       "Z is commutative" "Z is associative" "Z is left-unital " "Z is right-unital" 
       "Z is distributive" "Z is almost-left-invertible" "Z is non degenerated" 
       "Z is well-unital" "Z is strict doubleLoopStr" 
       "Z be non empty-struct\<parallel>doubleLoopStr" using Z2_cl_26 Z2_cl_24  Z2_cl_15 vectsp_1_cl_22[rule_format] Z Z2_cl_7 by auto
qed

text_raw \<open>\DefineSnippet{Ring}{\<close>
abbreviation
 "Ring \<equiv> Abelian \<bar> add-associative \<bar> right-zeroed \<bar>
          right-complementable \<bar> associative \<bar>
          well-unital \<bar> distributive \<bar>
          non empty-struct \<parallel> doubleLoopStr"
text_raw \<open>}%EndSnippet\<close>
text_raw \<open>\DefineSnippet{SkewField}{\<close>
abbreviation
 "SkewField \<equiv> non degenerated \<bar>
                     almost-left-invertible \<parallel> Ring"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{FIELD}{\<close> 
abbreviation
  "FIELD \<equiv> commutative \<parallel> SkewField"
text_raw \<open>}%EndSnippet\<close>

theorem vectsp_1_Field_Test:
  "ex R be FIELD st True" using vectsp_1_cl_26 by auto

    
theorem vectsp_1_th_5:
  "for F be associative\<bar>commutative\<bar>well-unital\<bar>distributive\<bar> 
            almost-left-invertible \<bar>non empty-struct\<parallel>doubleLoopStr, 
       x,y,z be Element-of-struct F
   st x <> 0\<^sub>F & x \<otimes>\<^sub>F y = x \<otimes>\<^sub>F z holds y = z"
proof(intro ballI uncurry impI) 
  fix F x y z assume T0: " F be associative  \<bar> commutative  \<bar> well-unital  \<bar> distributive \<bar> 
                         almost-left-invertible  \<bar> non empty-struct \<parallel>doubleLoopStr"
                 and T1: "x be Element-of-struct F"  "y be Element-of-struct F" "z be Element-of-struct F"
  have W1: " F be non empty-struct \<parallel>multLoopStr_0" "F is left-unital" using T0 doubleLoopStr multLoopStr_0 vectsp_1_cl_22 by simp+
  assume "x<>0\<^sub>F"
  then obtain x1 where T2:"x1 be Element-of-struct F" and
    A1:" x1 \<otimes>\<^sub>F x = 1\<^sub>F" using vectsp_1_def_9[OF W1(1),THEN iffD1,rule_format,of x] T0 T1 by auto
  have A2: "(x1 \<otimes>\<^sub>F x) \<otimes>\<^sub>F y = x1 \<otimes>\<^sub>F (x \<otimes>\<^sub>F y) & x1 \<otimes>\<^sub>F (x \<otimes>\<^sub>F z) = (x1 \<otimes>\<^sub>F x) \<otimes>\<^sub>F z" using group_1_def_3[of F] T0 T1 T2 by auto
  assume "x \<otimes>\<^sub>F y = x \<otimes>\<^sub>F z"
  hence  "(x1 \<otimes>\<^sub>F x) \<otimes>\<^sub>F y = z" using A1 A2 vectsp_1_def_8 W1 T1(3) by auto 
  thus "y=z" using A1 A2 vectsp_1_def_8 W1 T1(2) by auto
qed

  
abbreviation inv (infix "\<hungarumlaut>\<^sup>" 105) where
  "x\<hungarumlaut>\<^sup>S \<equiv> /\<^sub>S x"  
  
text_raw \<open>\DefineSnippet{vectsp1def10}{\<close>
theorem vectsp_1_def_10: 
  "let F be associative \<bar> commutative \<bar> well-unital \<bar> 
       almost-left-invertible \<bar> non empty-struct \<parallel> doubleLoopStr & 
       x be Element-of-struct F & x <> 0\<^sub>F
   redefine func x\<hungarumlaut>\<^sup>F \<rightarrow> Element-of-struct F means
     (\<lambda>it. it \<otimes>\<^sub>F x = 1\<^sub>F)" 
text_raw \<open>}%EndSnippet\<close>
text_raw \<open>\DefineSnippet{vectsp1def10proof}{\<close>
proof(rule redefine_func_means_property,simp)
  assume T0: "F be associative \<bar> commutative \<bar> well-unital \<bar> 
                   almost-left-invertible \<bar> non empty-struct\<parallel> doubleLoopStr & 
              x be Element-of-struct F & 
              x <> 0\<^sub>F" 
  have T1:"F be multLoopStr" "F be multMagma" 
     using T0(1) doubleLoopStr multLoopStr multMagma by simp+
  thus T2:  "x\<hungarumlaut>\<^sup>F be Element-of-struct F" 
    using algstr_0_def_30[of F x] T0 by auto
  have A2: "x is left-invertible\<^sub>F" using algstr_0_def_39a T0 by auto
  then obtain x1 where T3: "x1 be Element-of-struct F" and
    A3: "x1 \<otimes>\<^sub>F x = 1\<^sub>F" using algstr_0_def_27a by auto 
  have A3': "x \<otimes>\<^sub>F x1 = 1\<^sub>F" 
    using group_1_def_12a[of F x1 x] A3 T3 T0 by auto
  have A: "x is right-mult-cancelable\<^sub>F"
   proof(unfold algstr_0_def_21,intro conjI ballI impI)
     show "F be multMagma" "x be Element-of-struct F" 
       using T0 T1 by auto
     fix y z assume T4: "y be Element-of-struct F" 
                        "z be Element-of-struct F"   
     assume A4: "y \<otimes>\<^sub>F x = z \<otimes>\<^sub>F x" 
     have "y = y \<otimes>\<^sub>F 1\<^sub>F" using vectsp_1_def_6a T0 T4 by auto
     also have "\<dots> = z \<otimes>\<^sub>F x \<otimes>\<^sub>F x1" 
       using A3' A4 group_1_def_3a[of F y x x1] T0 T4 T3 by auto 
     also have "\<dots> = z \<otimes>\<^sub>F 1\<^sub>F" 
       using A3' A4 group_1_def_3a[of F z x x1] T0 T4 T3 by auto
     also have "\<dots> = z " using vectsp_1_def_6a T0 T4 by auto   
     finally show "y = z" by auto
   qed
   fix IT assume B:"IT be Element-of-struct F" 
   thus "IT = x\<hungarumlaut>\<^sup>F iff IT \<otimes>\<^sub>F x = 1\<^sub>F" 
     using A A2 algstr_0_def_30[OF T1(1),of x IT] T0 T1 by auto
qed  
text_raw \<open>}%EndSnippet\<close>  
  
theorem vectsp_1_th_6[rule_format]:
  "for F be add-associative\<bar>right-zeroed\<bar>right-complementable\<bar>
  right-distributive\<bar>non empty-struct \<parallel>doubleLoopStr, x be Element-of-struct F holds
   x \<otimes>\<^sub>F 0\<^sub>F = 0\<^sub>F"
proof (intro ballI)
  fix F x assume T0:"F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
    right-distributive\<bar>non empty-struct \<parallel>doubleLoopStr" "x be Element-of-struct F"
  have C1:"0\<^sub>F be Element-of-struct F" using struct_0_def_6[of F] ZeroStr doubleLoopStr T0 by auto  
  have C2: "F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>non empty-struct \<parallel>doubleLoopStr" using T0 by simp  
  have C3: "(x\<otimes>\<^sub>F ( 0\<^sub>F \<oplus>\<^sub>F 0\<^sub>F)) be Element-of-struct F" using algstr_0_def_1[THEN conjunct1,of F "0\<^sub>F" "0\<^sub>F"]
         algstr_0_def_18[THEN conjunct1,of F x "0\<^sub>F \<oplus>\<^sub>F 0\<^sub>F"] C1 T0 multMagma addMagma doubleLoopStr by auto
  have C4: "(x \<otimes>\<^sub>F 0\<^sub>F) be Element-of-struct F" using algstr_0_def_18[THEN conjunct1,of F x "0\<^sub>F"] C1 T0 multMagma doubleLoopStr by auto
  
  have "x \<otimes>\<^sub>F 0\<^sub>F \<oplus>\<^sub>F 0\<^sub>F = x\<otimes>\<^sub>F(0\<^sub>F \<oplus>\<^sub>F 0\<^sub>F) \<oplus>\<^sub>F 0\<^sub>F" using rlvect_1_th_4 C1 T0 addLoopStr doubleLoopStr by auto 
  also have "\<dots>= x\<otimes>\<^sub>F ( 0\<^sub>F \<oplus>\<^sub>F 0\<^sub>F)" using rlvect_1_th_4 C3 T0 addLoopStr doubleLoopStr by auto 
  also have "\<dots>= x\<otimes>\<^sub>F 0\<^sub>F \<oplus>\<^sub>F x \<otimes>\<^sub>F 0\<^sub>F" using vectsp_1_def_2a C1 T0 by auto 
  finally show " x \<otimes>\<^sub>F 0\<^sub>F = 0\<^sub>F" using rlvect_1_th_8[OF _ C4 C1 C4] T0(1) C1 C4 addLoopStr doubleLoopStr by auto
qed

theorem vectsp_1_reduce_3[rule_format]:
  "let F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
            right-distributive\<bar>non empty-struct \<parallel>doubleLoopStr & 
       (x be Element-of-struct F &
       y be zero \<^sub>F \<parallel> Element-of-struct F)
   reduce x \<otimes>\<^sub>F y to y"
proof
  assume T0: " F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
            right-distributive\<bar>non empty-struct \<parallel>doubleLoopStr & 
       (x be Element-of-struct F &
       y be zero \<^sub>F \<parallel> Element-of-struct F)"
  hence "y=0\<^sub>F" using struct_0_def_12_a by auto
  thus "x \<otimes>\<^sub>F y = y" using vectsp_1_th_6[of F x] T0 by auto  
qed
  
theorem vectsp_1_th_7[rule_format]:
  "for F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
     left-distributive\<bar>non empty-struct \<parallel>doubleLoopStr, x be Element-of-struct F holds
     0\<^sub>F \<otimes>\<^sub>F x = 0\<^sub>F"
proof (intro ballI)
  fix F x assume T0:"F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
    left-distributive\<bar>non empty-struct \<parallel>doubleLoopStr" "x be Element-of-struct F"
  have C1:"0\<^sub>F be Element-of-struct F" using struct_0_def_6[of F] ZeroStr doubleLoopStr T0 by auto  
  have C2: "F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>non empty-struct \<parallel>doubleLoopStr" using T0 by simp  
  have C3: "(( 0\<^sub>F \<oplus>\<^sub>F 0\<^sub>F)\<otimes>\<^sub>F x) be Element-of-struct F" using algstr_0_def_1[THEN conjunct1,of F "0\<^sub>F" "0\<^sub>F"]
         algstr_0_def_18[THEN conjunct1,of F "0\<^sub>F \<oplus>\<^sub>F 0\<^sub>F" x] C1 T0 multMagma addMagma doubleLoopStr by auto
  have C4: "0\<^sub>F \<otimes>\<^sub>F x be Element-of-struct F" using algstr_0_def_18[THEN conjunct1,of F "0\<^sub>F" x] C1 T0 multMagma doubleLoopStr by auto
  
  have "0\<^sub>F  \<otimes>\<^sub>F x \<oplus>\<^sub>F 0\<^sub>F = ( 0\<^sub>F \<oplus>\<^sub>F 0\<^sub>F)\<otimes>\<^sub>F x \<oplus>\<^sub>F 0\<^sub>F" using rlvect_1_th_4 C1 T0 addLoopStr doubleLoopStr by auto 
  also have "\<dots>= ( 0\<^sub>F \<oplus>\<^sub>F 0\<^sub>F)\<otimes>\<^sub>F x" using rlvect_1_th_4 C3 T0 addLoopStr doubleLoopStr by auto 
  also have "\<dots>=  0\<^sub>F \<otimes>\<^sub>F x \<oplus>\<^sub>F 0\<^sub>F \<otimes>\<^sub>F x" using vectsp_1_def_3a C1 T0 by auto 
  finally show " 0\<^sub>F \<otimes>\<^sub>F x= 0\<^sub>F" using rlvect_1_th_8[OF _ C4 C1 C4] T0(1) addLoopStr doubleLoopStr by auto
qed

theorem vectsp_1_reduce_4[rule_format]:
  "let F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
            left-distributive\<bar>non empty-struct \<parallel>doubleLoopStr & 
       (x be Element-of-struct F &
       y be zero \<^sub>F \<parallel> Element-of-struct F)
   reduce y \<otimes>\<^sub>F x to y"
proof
  assume T0: " F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
            left-distributive\<bar>non empty-struct \<parallel>doubleLoopStr & 
       (x be Element-of-struct F &
       y be zero \<^sub>F \<parallel> Element-of-struct F)"
  hence "y=0\<^sub>F" using struct_0_def_12_a by auto
  thus "y \<otimes>\<^sub>F x = y" using vectsp_1_th_7[of F x] T0 by auto  
qed

theorem vectsp_1_th_8[rule_format]:
  "for F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
  right-distributive\<bar>non empty-struct \<parallel>doubleLoopStr, x,y be Element-of-struct F holds
   x \<otimes>\<^sub>F (\<ominus>\<^sub>F y) = \<ominus>\<^sub>F x \<otimes>\<^sub>F y"
proof (intro ballI)
  fix F x y assume T0:"F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
    right-distributive\<bar>non empty-struct \<parallel>doubleLoopStr" "x be Element-of-struct F" "y be Element-of-struct F"
  have C1:"(\<ominus>\<^sub>F y) be Element-of-struct F" using T0(1,3) algstr_0_def_13[of F y] addLoopStr doubleLoopStr by auto
  have C2:"(x \<otimes>\<^sub>F y) be Element-of-struct F" using algstr_0_def_18[THEN conjunct1,of F x y] T0 multMagma doubleLoopStr by auto
  have C3:"(x \<otimes>\<^sub>F (\<ominus>\<^sub>F y)) be Element-of-struct F" using algstr_0_def_18[THEN conjunct1,of F x "\<ominus>\<^sub>F y"] T0 C1 multMagma doubleLoopStr by auto  
  have "(x \<otimes>\<^sub>F y) \<oplus>\<^sub>F (x \<otimes>\<^sub>F (\<ominus>\<^sub>F y)) = x \<otimes>\<^sub>F (y \<oplus>\<^sub>F \<ominus>\<^sub>F y)" using vectsp_1_def_2a T0 C1 by auto    
  also have "\<dots>=x \<otimes>\<^sub>F 0\<^sub>F " using rlvect_1_def_10 addLoopStr doubleLoopStr T0 by auto 
  also have "\<dots>= 0\<^sub>F " using vectsp_1_th_6 T0 by auto 
  finally show "x \<otimes>\<^sub>F (\<ominus>\<^sub>F y) = \<ominus>\<^sub>F x \<otimes>\<^sub>F y" using rlvect_1_def_10[THEN conjunct2,THEN conjunct2,rule_format,of F "x \<otimes>\<^sub>F y" "x \<otimes>\<^sub>F (\<ominus>\<^sub>F y)"] T0 C2 C3 
      addLoopStr doubleLoopStr by auto     
qed

theorem vectsp_1_th_9[rule_format]:
  "for F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
  left-distributive\<bar>non empty-struct \<parallel>doubleLoopStr, x,y be Element-of-struct F holds
  (\<ominus>\<^sub>F x) \<otimes>\<^sub>F  y = \<ominus>\<^sub>F x \<otimes>\<^sub>F y"
proof (intro ballI)
  fix F x y assume T0:"F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
    left-distributive\<bar>non empty-struct \<parallel>doubleLoopStr" "x be Element-of-struct F" "y be Element-of-struct F"
  have C1:"(\<ominus>\<^sub>F x) be Element-of-struct F" using T0(1,2) algstr_0_def_13[of F x] addLoopStr doubleLoopStr by auto
  have C2:"x \<otimes>\<^sub>F y be Element-of-struct F" using algstr_0_def_18[THEN conjunct1,of F x y] T0 multMagma doubleLoopStr by auto
  have C3:"(\<ominus>\<^sub>F x) \<otimes>\<^sub>F y be Element-of-struct F" using algstr_0_def_18[THEN conjunct1,of F "\<ominus>\<^sub>F x" y] T0 C1 multMagma doubleLoopStr by auto  
  
  have "(x \<otimes>\<^sub>F y) \<oplus>\<^sub>F ((\<ominus>\<^sub>F x) \<otimes>\<^sub>F y) =  (x \<oplus>\<^sub>F \<ominus>\<^sub>F x) \<otimes>\<^sub>F y" using vectsp_1_def_3a T0 C1 by auto    
  also have "\<dots>= 0\<^sub>F \<otimes>\<^sub>F y" using rlvect_1_def_10 addLoopStr doubleLoopStr T0 by auto 
  also have "\<dots>= 0\<^sub>F " using vectsp_1_th_7 T0 by auto 
  finally show "(\<ominus>\<^sub>F x) \<otimes>\<^sub>F  y = \<ominus>\<^sub>F x \<otimes>\<^sub>F y" using rlvect_1_def_10[THEN conjunct2,THEN conjunct2,rule_format,of F "x \<otimes>\<^sub>F y" "(\<ominus>\<^sub>F x) \<otimes>\<^sub>F y"] T0 C2 C3 
      addLoopStr doubleLoopStr by auto     
qed

theorem vectsp_1_th_10[rule_format]:
  "for F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
  distributive\<bar>non empty-struct \<parallel>doubleLoopStr, x,y be Element-of-struct F holds
  (\<ominus>\<^sub>F x) \<otimes>\<^sub>F  (\<ominus>\<^sub>F y) =  x \<otimes>\<^sub>F y"
proof (intro ballI)
  fix F x y assume T0:"F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
    distributive\<bar>non empty-struct \<parallel>doubleLoopStr" "x be Element-of-struct F" "y be Element-of-struct F"
  have C1:"(\<ominus>\<^sub>F y) be Element-of-struct F" using T0(1,3) algstr_0_def_13[of F y] addLoopStr doubleLoopStr by auto
  have C2:"x \<otimes>\<^sub>F y be Element-of-struct F" using algstr_0_def_18[THEN conjunct1,of F x y] T0 multMagma doubleLoopStr by auto
  have "(\<ominus>\<^sub>F x) \<otimes>\<^sub>F  (\<ominus>\<^sub>F y) = \<ominus>\<^sub>F x \<otimes>\<^sub>F  (\<ominus>\<^sub>F y)" using T0 C1 vectsp_1_th_9 vectsp_1_cl_20 by auto   
  also have "\<dots> =   \<ominus>\<^sub>F \<ominus>\<^sub>F x \<otimes>\<^sub>F y" using T0 C1 vectsp_1_th_8 vectsp_1_cl_20 by auto      
  also have "\<dots> = x \<otimes>\<^sub>F y" using T0 rlvect_1_th_17 C2 addLoopStr doubleLoopStr by auto   
  finally show "(\<ominus>\<^sub>F x) \<otimes>\<^sub>F  (\<ominus>\<^sub>F y) =  x \<otimes>\<^sub>F y" by auto
qed  
  
theorem vectsp_1_th_11[rule_format]:
  "for F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
  right-distributive\<bar>non empty-struct \<parallel>doubleLoopStr, x,y,z be Element-of-struct F holds
   x \<otimes>\<^sub>F (y \<ominus>\<^sub>F z) = x \<otimes>\<^sub>F y \<ominus>\<^sub>F x \<otimes>\<^sub>F z"
proof(intro ballI)
  fix F x y z 
  assume T0:"F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar> right-distributive\<bar>non empty-struct \<parallel>doubleLoopStr"
            "x be Element-of-struct F"
            "y be Element-of-struct F"
            "z be Element-of-struct F"
  have C0: "F be addLoopStr" "F be multMagma" using addLoopStr multMagma doubleLoopStr T0 by auto+          
  have C1:"(\<ominus>\<^sub>F z) be Element-of-struct F" using T0 algstr_0_def_13[of F z] addLoopStr doubleLoopStr by auto
  have C2:"x \<otimes>\<^sub>F y be Element-of-struct F" 
          "x \<otimes>\<^sub>F z be Element-of-struct F" using algstr_0_def_18[THEN conjunct1,of F] C0 T0 by auto    
  have "x \<otimes>\<^sub>F (y \<ominus>\<^sub>F z) = x \<otimes>\<^sub>F y \<oplus>\<^sub>F  x \<otimes>\<^sub>F (\<ominus>\<^sub>F z)" using vectsp_1_def_2a algstr_0_def_14 T0 C1 C0 by auto     
  also have "\<dots> = x \<otimes>\<^sub>F y \<ominus>\<^sub>F x \<otimes>\<^sub>F z" using vectsp_1_th_8 T0 algstr_0_def_14 C0 C2 by auto
  finally show " x \<otimes>\<^sub>F (y \<ominus>\<^sub>F z) = x \<otimes>\<^sub>F y \<ominus>\<^sub>F x \<otimes>\<^sub>F z" by auto
qed  
  
text_raw \<open>\DefineSnippet{vectsp1th12}{\<close>
theorem vectsp_1_th_12:
  "for F being add-associative \<bar> right-zeroed \<bar> 
         right-complementable \<bar> associative \<bar> commutative \<bar> 
         well-unital \<bar> almost-left-invertible \<bar>
         distributive \<bar> non empty-struct \<parallel> doubleLoopStr, 
       x,y being Element-of-struct F holds 
    x \<otimes>\<^sub>F y = 0\<^sub>F iff x = 0\<^sub>F or y = 0\<^sub>F"
proof(intro ballI) 
  fix F x y 
  assume T:"F be add-associative \<bar> right-zeroed \<bar> 
          right-complementable \<bar> associative \<bar> commutative \<bar> 
          well-unital \<bar> almost-left-invertible \<bar>
          distributive \<bar> non empty-struct \<parallel> doubleLoopStr" 
         "x be Element-of-struct F"
         "y be Element-of-struct F"
  hence A:"F be multLoopStr_0" "F be multLoopStr" "F be ZeroStr" 
  using doubleLoopStr multLoopStr_0 multLoopStr ZeroStr by auto
  have I: "x\<hungarumlaut>\<^sup>F be Element-of-struct F" 
    using algstr_0_def_30[of F x] T A by auto
  have Z: "0\<^sub>F be zero \<^sub>F \<parallel> Element-of-struct F" 
    using struct_0_def_12_a[of F] struct_0_def_6[of F] A by auto
  have "x \<otimes>\<^sub>F y = 0\<^sub>F implies x = 0\<^sub>F or y = 0\<^sub>F"
    proof(rule impI,rule disjCI2)
      assume A1:"x \<otimes>\<^sub>F y = 0\<^sub>F"
      assume A2:"x <> 0\<^sub>F" 
      have "x\<hungarumlaut>\<^sup>F \<otimes>\<^sub>F 0\<^sub>F = x\<hungarumlaut>\<^sup>F \<otimes>\<^sub>F x \<otimes>\<^sub>F y" 
        using A1 group_1_def_3a T I by auto 
      also have "\<dots> = 1\<^sub>F \<otimes>\<^sub>F y" using A2 vectsp_1_def_10 T by auto
      also have "\<dots> = y" using vectsp_1_reduce_2 T A by auto
      finally show "y = 0\<^sub>F" using vectsp_1_reduce_3[OF _ I Z] 
        T vectsp_1_cl_20 by auto    
  qed  
  thus "x \<otimes>\<^sub>F y = 0\<^sub>F iff x = 0\<^sub>F or y = 0\<^sub>F" using 
    vectsp_1_reduce_4[OF _ T(3) Z] vectsp_1_reduce_3[OF _ T(2) Z] 
    T vectsp_1_cl_20 by auto  
qed
text_raw \<open>}%EndSnippet\<close>
  
theorem vectsp_1_th_13[rule_format]:
  "for F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
  left-distributive\<bar>non empty-struct \<parallel>doubleLoopStr, x,y,z be Element-of-struct F holds
   (y \<ominus>\<^sub>F z) \<otimes>\<^sub>F x = y \<otimes>\<^sub>F x \<ominus>\<^sub>F z \<otimes>\<^sub>F x"
proof(intro ballI)
  fix F x y z 
  assume T0:"F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar> left-distributive\<bar>non empty-struct \<parallel>doubleLoopStr"
            "x be Element-of-struct F"
            "y be Element-of-struct F"
            "z be Element-of-struct F"
  have C0: "F be addLoopStr" "F be multMagma" using addLoopStr multMagma doubleLoopStr T0 by auto+          
  have C1:"(\<ominus>\<^sub>F z) be Element-of-struct F" using T0 algstr_0_def_13[of F z] addLoopStr doubleLoopStr by auto
  have C2:"y \<otimes>\<^sub>F x be Element-of-struct F" 
          "z \<otimes>\<^sub>F x be Element-of-struct F" using algstr_0_def_18[THEN conjunct1,of F] C0 T0 by auto    
  have "(y \<ominus>\<^sub>F z) \<otimes>\<^sub>F x = y \<otimes>\<^sub>F x \<oplus>\<^sub>F (\<ominus>\<^sub>F z) \<otimes>\<^sub>F x" using vectsp_1_def_3a algstr_0_def_14 T0 C1 C0 by auto     
  also have "\<dots> = y \<otimes>\<^sub>F x \<ominus>\<^sub>F z \<otimes>\<^sub>F x" using vectsp_1_th_9 T0 algstr_0_def_14 C0 C2 by auto
  finally show "(y \<ominus>\<^sub>F z) \<otimes>\<^sub>F x = y \<otimes>\<^sub>F x \<ominus>\<^sub>F z \<otimes>\<^sub>F x" by auto
qed  
  
abbreviation ModuleStr_fields_prefix ("ModuleStr'_fields _") where
 "ModuleStr_fields F \<equiv>(#carrier \<rightarrow> set';  addF\<rightarrow> BinOp-of' the' carrier; ZeroF \<rightarrow> Element-of' the' carrier;
               lmult \<rightarrow>  Function-of' [: the carrier of F,the' carrier ':], the' carrier #)"       
    
definition ModuleStr_over ("ModuleStr-over _") where 
  "struct ModuleStr-over F ModuleStr_fields F"   
  
  
lemma ModuleStr_over_well:
  assumes "F be one-sorted"
  shows "ModuleStr_fields F well defined on {carrier}\<union>{addF}\<union>{ZeroF}\<union>{lmult}" 
proof(rule  Fields_add_argM1[OF addLoopStr_well],simp add:string,simp add:string)  
  show "for X1 be  addLoopStr_fields\<parallel>Function holds ex it be Function-of [: the carrier of F, the carrier of X1:], the carrier of X1 st True" 
  proof(rule ballI)
    fix X1 assume "X1 be addLoopStr_fields\<parallel>Function"
    hence A1: "the carrier of X1 be set" "the carrier of F be set" using field assms one_sorted by auto+ 
    hence " [: the carrier of F, the carrier of X1:] be set" using zfmisc_1_def_2a by simp       
    thus "ex it be Function-of [: the carrier of F, the carrier of X1:], the carrier of X1 st True" using funct_2_cl_ex A1 by auto        
  qed
qed

schematic_goal ModuleStr_over:
   assumes "F be one_sorted"
   shows ?X by (rule struct_well_defined[OF ModuleStr_over_def ModuleStr_over_well[OF assms]])

theorem ModuleStr_over_inheritance:
  "F be one_sorted \<Longrightarrow> X be ModuleStr-over F \<Longrightarrow> X be addLoopStr" using  ModuleStr_over addLoopStr by simp

end