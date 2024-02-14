\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Rlvect_1
  imports Algstr_0
begin

definition Abelian_M ("Abelian") where rlvect_1_def_2 [THEN defattr_property]:
   "attr Abelian means (\<lambda> M. M be addMagma & (for v,w be Element-of-struct M holds v \<oplus>\<^sub>M w = w \<oplus>\<^sub>M v))"
lemmas rlvect_1_def_2a = rlvect_1_def_2[THEN iffD1,THEN conjunct2,rule_format]

definition add_associative_M ("add-associative") where rlvect_1_def_3 [THEN defattr_property]:
   "attr add-associative means (\<lambda> M. M be addMagma & (for u,v,w be Element-of-struct M holds (u \<oplus>\<^sub>M v) \<oplus>\<^sub>M w = u \<oplus>\<^sub>M (v \<oplus>\<^sub>M w)))"
lemmas rlvect_1_def_3a = rlvect_1_def_3[THEN iffD1,THEN conjunct2,rule_format]

definition right_zeroed_M ("right-zeroed") where rlvect_1_def_4 [THEN defattr_property]:
   "attr right-zeroed means (\<lambda> M. M be addLoopStr & (for v be Element-of-struct M holds v \<oplus>\<^sub>M 0\<^sub>M = v))"
lemmas rlvect_1_def_4a = rlvect_1_def_4[THEN iffD1,THEN conjunct2,rule_format]
 
theorem rlvect_1_lm_1[rule_format]: 
  "for V be non empty-struct\<bar>right-complementable\<bar>add-associative\<bar>right-zeroed\<parallel>addLoopStr,
       v, w be Element-of-struct V st v \<oplus>\<^sub>V w = 0\<^sub>V holds 
       w \<oplus>\<^sub>V v = 0\<^sub>V"
proof(intro ballI impI)
  fix V v w assume T0:"V be non empty-struct\<bar>right-complementable\<bar>add-associative\<bar>right-zeroed\<parallel>addLoopStr"
       "v be Element-of-struct V" "w be Element-of-struct V"
  assume A1: "v \<oplus>\<^sub>V w = 0\<^sub>V"
  obtain u where
    T1:"u be Element-of-struct V" and
    A2: "w \<oplus>\<^sub>V u = 0\<^sub>V" using algstr_0_def_16a[of V w] algstr_0_def_11a[of w V] T0(1,3) by auto
  have "w \<oplus>\<^sub>V v = w \<oplus>\<^sub>V (v \<oplus>\<^sub>V (w \<oplus>\<^sub>V u))" using A2 rlvect_1_def_4a[of V v] A2 T0 by auto
  also have "\<dots> = w \<oplus>\<^sub>V ((v \<oplus>\<^sub>V w) \<oplus>\<^sub>V u)" using rlvect_1_def_3a T0 T1 by auto
  also have "\<dots> =  (w \<oplus>\<^sub>V (v \<oplus>\<^sub>V w)) \<oplus>\<^sub>V u"  using rlvect_1_def_3a T0 T1 algstr_0_def_1[of V v w,THEN conjunct1] addMagma addLoopStr by auto
  also have "\<dots> = w \<oplus>\<^sub>V u" using A1 rlvect_1_def_4a[of V w] T0 T1 algstr_0_def_1[of V v w,THEN conjunct1] addMagma addLoopStr  by auto
  finally show "w \<oplus>\<^sub>V v = 0\<^sub>V" using A2 by auto
qed
 
theorem rlvect_1_th_3[rule_format]:
  "for V being add-associative\<bar>right-zeroed \<bar>right-complementable\<parallel>
  addLoopStr holds V is right-add-cancelable"
proof(rule ballI,unfold algstr_0_def_7,rule conjI,
      simp add: addMagma addLoopStr,rule ballI)
  fix V v assume T0:"V be add-associative\<bar>right-zeroed \<bar>right-complementable\<parallel>
            addLoopStr" "v be Element-of-struct V"
  obtain v1 where
    T1:"v1 be Element-of-struct V" and
    A1: "v \<oplus>\<^sub>V v1 = 0\<^sub>V" using algstr_0_def_16a[of V v] algstr_0_def_11a[of v V] T0(1,2) by auto 
  show "v is right-add-cancelable\<^sub>V"
  proof(unfold algstr_0_def_4,intro conjI ballI impI)
    show "V be addMagma" "v be Element-of-struct V" using addMagma addLoopStr T0 by simp+
    fix u w assume T2: "u be Element-of-struct V" "w be Element-of-struct V" 
    assume A2: "u \<oplus>\<^sub>V v = w \<oplus>\<^sub>V v"
    have "u = u \<oplus>\<^sub>V 0\<^sub>V" using rlvect_1_def_4a T0 T2 by auto
    also have "\<dots> =  (u \<oplus>\<^sub>V  v) \<oplus>\<^sub>V v1" using A1 rlvect_1_def_3a T0 T1 T2 by auto 
    also have "\<dots> =  w \<oplus>\<^sub>V 0\<^sub>V" using A1 A2 rlvect_1_def_3a T0 T1 T2 by auto
    also have "\<dots> =  w" using rlvect_1_def_4a T0(1) T2(2) by auto
    finally show "u = w" by auto
  qed
qed  
 
theorem rlvect_1_th_4[rule_format]:
  "for V being add-associative\<bar>right-zeroed\<bar>right-complementable\<bar>non empty-struct \<parallel> addLoopStr, 
       v being Element-of-struct V holds v \<oplus>\<^sub>V 0\<^sub>V = v & 0\<^sub>V \<oplus>\<^sub>V v = v"
proof(intro ballI conjI)
  fix V v assume T0: 
     "V be add-associative\<bar>right-zeroed\<bar>right-complementable\<bar>non empty-struct\<parallel>addLoopStr" 
     "v be Element-of-struct V"
  obtain w where
    T1:"w be Element-of-struct V" and
    A1: "v \<oplus>\<^sub>V w = 0\<^sub>V" using algstr_0_def_16a[of V v] algstr_0_def_11a[of v V] T0 by auto
  show A2: "v \<oplus>\<^sub>V 0\<^sub>V = v" using rlvect_1_def_4a T0 by simp
  have "w \<oplus>\<^sub>V v = 0\<^sub>V" using A1 rlvect_1_lm_1 T0 T1 by auto      
  thus "0\<^sub>V \<oplus>\<^sub>V v = v"  using rlvect_1_def_3a[of V v w v] T0 T1 A1 A2 by simp   
qed 
  
theorem rlvect_1_reduce_1[rule_format]:
  "let V be add-associative\<bar>right-zeroed\<bar>right-complementable\<bar>
           non empty-struct\<parallel> addLoopStr& 
      v1 be zero \<^sub>V \<parallel>Element-of-struct V &
      v2 be Element-of-struct V
   reduce v1 \<oplus>\<^sub>V v2 to v2"
proof(intro uncurry impI)
  assume T0:" V be add-associative\<bar>right-zeroed\<bar>right-complementable\<bar>
           non empty-struct\<parallel> addLoopStr"" 
      v1 be zero \<^sub>V \<parallel>Element-of-struct V""
      v2 be Element-of-struct V"
  have "v1 = 0\<^sub>V" using struct_0_def_12_a[of v1 V] T0(2) by auto 
  thus "v1 \<oplus>\<^sub>V v2 = v2" using T0 rlvect_1_th_4 by auto
qed  
  
theorem rlvect_1_reduce_2[rule_format]:
  "let V be add-associative\<bar>right-zeroed\<bar>right-complementable\<bar>
           non empty-struct\<parallel> addLoopStr& 
      v1 be zero \<^sub>V \<parallel>Element-of-struct V &
      v2 be Element-of-struct V
   reduce v2 \<oplus>\<^sub>V v1 to v2"
proof(intro uncurry impI)
  assume T0:" V be add-associative\<bar>right-zeroed\<bar>right-complementable\<bar>
           non empty-struct\<parallel> addLoopStr"" 
      v1 be zero \<^sub>V \<parallel>Element-of-struct V""
      v2 be Element-of-struct V"
  have "v1 = 0\<^sub>V" using struct_0_def_12_a[of v1 V] T0(2) by auto 
  thus "v2 \<oplus>\<^sub>V v1 = v2" using T0 rlvect_1_th_4 by auto
qed  
    
theorem rlvect_1_def_10[rule_format]:
  "let V be non empty-struct \<parallel>addLoopStr&
       v be Element-of-struct V &
       V is add-associative\<bar>right-zeroed\<bar>right-complementable
   redefine func \<ominus>\<^sub>V v \<rightarrow> Element-of-struct V means
      (\<lambda> it. v \<oplus>\<^sub>V it = 0\<^sub>V)"
proof(rule redefine_func_means_property,simp)
  assume T0:"V be non empty-struct \<parallel>addLoopStr&
       v be Element-of-struct V &
       V is add-associative\<bar>right-zeroed\<bar>right-complementable"
  thus T: "(\<ominus>\<^sub>V v) be Element-of-struct V" using algstr_0_def_13[THEN conjunct1,of V v] by auto 
  fix IT assume T11:"IT be Element-of-struct V"
  show "IT = \<ominus>\<^sub>V v iff v \<oplus>\<^sub>V IT = 0\<^sub>V"
  proof(rule iffI3)
    obtain v1 where
      T1:"v1 be Element-of-struct V" and
      A2: "v \<oplus>\<^sub>V v1 = 0\<^sub>V" using algstr_0_def_16a[of V v] algstr_0_def_11a[of v V] T0 by auto
    have A3: "V is right-add-cancelable" using T0 rlvect_1_th_3 by auto 
    have C1: "0\<^sub>V be zero \<^sub>V \<parallel> Element-of-struct V" using struct_0_def_12_a[of V] struct_0_def_6[of V] T0 addLoopStr ZeroStr by auto 
    have C2: "(v \<oplus>\<^sub>V \<ominus>\<^sub>V v) be Element-of-struct V" using T0 T algstr_0_def_1[of V v "\<ominus>\<^sub>V v"] addMagma addLoopStr by auto 
    have A4: "v is left-complementable\<^sub>V"
    proof(unfold algstr_0_def_10,rule conjI)
      show "V be addLoopStr & v be Element-of-struct V" using T0 by simp+
      show "ex y be Element-of-struct V st y \<oplus>\<^sub>V v = 0\<^sub>V"
      proof(rule bexI[of _ v1])
        show "v1 be Element-of-struct V" using T1 by simp
        have T3: "(v1 \<oplus>\<^sub>V v) be Element-of-struct V" using T1 T0 algstr_0_def_1[of V v1 v] addMagma addLoopStr by auto 
        have "(v1 \<oplus>\<^sub>V v) \<oplus>\<^sub>V v1 = v1 \<oplus>\<^sub>V 0\<^sub>V" using rlvect_1_def_3a[of V v1 v v1] T0 T1 A2 by simp
        also have "\<dots> = 0\<^sub>V \<oplus>\<^sub>V v1" using T0 T1 C1 rlvect_1_reduce_1[of V "0\<^sub>V" v1] rlvect_1_reduce_2[of V "0\<^sub>V" v1] by auto
        finally show "v1 \<oplus>\<^sub>V v = 0\<^sub>V" using  algstr_0_def_4a[OF algstr_0_def_7a[OF A3 T1], of "v1 \<oplus>\<^sub>V v" "0\<^sub>V"] T0 C1 T3 by auto
      qed
    qed 
    have "v \<oplus>\<^sub>V \<ominus>\<^sub>V v \<oplus>\<^sub>V v = v \<oplus>\<^sub>V (\<ominus>\<^sub>V v \<oplus>\<^sub>V v)" using rlvect_1_def_3a[of V v "\<ominus>\<^sub>V v" v] T0 T1 A2 T by auto
    also have "\<dots> = v \<oplus>\<^sub>V 0\<^sub>V" using algstr_0_def_7a[OF A3, of v] algstr_0_def_13[of V v] T0 A4 by auto
    also have "\<dots> = 0\<^sub>V \<oplus>\<^sub>V v" using T0 T1 C1 rlvect_1_reduce_1[of V "0\<^sub>V" v] rlvect_1_reduce_2[of V "0\<^sub>V" v] by auto
    finally show "IT =\<ominus>\<^sub>V v implies v \<oplus>\<^sub>V IT = 0\<^sub>V" using algstr_0_def_4a[OF algstr_0_def_7a[OF A3, of v],of "v \<oplus>\<^sub>V \<ominus>\<^sub>V v" "0\<^sub>V"] T0 C1 C2 by auto 
    assume A5: "v \<oplus>\<^sub>V IT = 0\<^sub>V"  
    have "IT = 0\<^sub>V \<oplus>\<^sub>V IT" using rlvect_1_reduce_1[of V "0\<^sub>V" IT] C1 T11 T0 by auto 
    also have "\<dots> = \<ominus>\<^sub>V v \<oplus>\<^sub>V v  \<oplus>\<^sub>V IT" using algstr_0_def_7a[OF A3, of v] algstr_0_def_13[of V v] T0 A4 by auto
    also have "\<dots> = \<ominus>\<^sub>V v \<oplus>\<^sub>V 0\<^sub>V" using rlvect_1_def_3a[of V "\<ominus>\<^sub>V v" v IT] T0 T T11 A2 A5 by simp
    also have "\<dots> = \<ominus>\<^sub>V v" using rlvect_1_reduce_2[of V "0\<^sub>V" "\<ominus>\<^sub>V v" ] T C1 T0 by auto 
    finally show "IT = \<ominus>\<^sub>V v" by auto
   qed    
qed
  
theorem rlvect_1_th_5[rule_format]:
  "for V be add-associative \<bar> right-zeroed \<bar> right-complementable\<bar>
       non empty-struct \<parallel> addLoopStr, 
   v being Element-of-struct V holds v \<oplus>\<^sub>V \<ominus>\<^sub>V v = 0\<^sub>V & \<ominus>\<^sub>V v \<oplus>\<^sub>V v = 0\<^sub>V"
proof(intro ballI conjI)
  fix V v assume T0:"V be add-associative \<bar> right-zeroed \<bar> right-complementable\<bar>
       non empty-struct \<parallel> addLoopStr" 
       "v be Element-of-struct V"
  thus A1: "v \<oplus>\<^sub>V \<ominus>\<^sub>V v = 0\<^sub>V" using rlvect_1_def_10 by auto
  have " (\<ominus>\<^sub>V v) be Element-of-struct V" using T0 rlvect_1_def_10 by auto
  thus "\<ominus>\<^sub>V v \<oplus>\<^sub>V v = 0\<^sub>V" using rlvect_1_lm_1 A1 T0 by auto
qed

theorem rlvect_1_th_6[rule_format]:
  "for V be add-associative \<bar> right-zeroed \<bar> right-complementable\<bar>
       non empty-struct \<parallel> addLoopStr, 
   v,w being Element-of-struct V st v \<oplus>\<^sub>V w = 0\<^sub>V holds  v = \<ominus>\<^sub>V w"
proof(intro ballI impI)
  fix V v w assume T0:"V be add-associative \<bar> right-zeroed \<bar> right-complementable\<bar>
       non empty-struct \<parallel> addLoopStr" 
       "v be Element-of-struct V" "w be Element-of-struct V"
  assume A1: "v \<oplus>\<^sub>V w = 0\<^sub>V" 
  hence "w \<oplus>\<^sub>V v = 0\<^sub>V" using T0 rlvect_1_lm_1 by auto
  thus "v = \<ominus>\<^sub>V w" using T0 rlvect_1_def_10 by auto    
qed

theorem rlvect_1_th_7[rule_format]:
  "for V be add-associative \<bar> right-zeroed \<bar> right-complementable\<bar>
       non empty-struct \<parallel> addLoopStr, 
   v,u being Element-of-struct V holds
   ex w be Element-of-struct V st v \<oplus>\<^sub>V w = u"
proof(intro ballI)
  fix V v u assume T0:"V be add-associative \<bar> right-zeroed \<bar> right-complementable\<bar>
       non empty-struct \<parallel> addLoopStr" 
       "v be Element-of-struct V" "u be Element-of-struct V"
  have T1: "(\<ominus>\<^sub>V v) be Element-of-struct V" using algstr_0_def_13[THEN conjunct1,of V v] T0 by auto
  show "ex w be Element-of-struct V st v \<oplus>\<^sub>V w = u"
    proof(rule bexI[of _ "\<ominus>\<^sub>V v \<oplus>\<^sub>V u"]) 
      show T2: "(\<ominus>\<^sub>V v \<oplus>\<^sub>V u) be Element-of-struct V" using T0 T1 algstr_0_def_1[of V "\<ominus>\<^sub>V v" u] addMagma addLoopStr by auto 
      have C1: "0\<^sub>V be zero \<^sub>V \<parallel> Element-of-struct V" using struct_0_def_12_a[of V] struct_0_def_6[of V] T0 addLoopStr ZeroStr by auto 
      have "v  \<oplus>\<^sub>V (\<ominus>\<^sub>V v \<oplus>\<^sub>V u) = v  \<oplus>\<^sub>V \<ominus>\<^sub>V v \<oplus>\<^sub>V u" using rlvect_1_def_3a T0 T1 by auto
      also have "\<dots> = 0\<^sub>V \<oplus>\<^sub>V u" using rlvect_1_def_10 T0 by simp
      also have "\<dots> = u" using rlvect_1_reduce_1[of V "0\<^sub>V" u] C1 T0 by auto  
      finally show "v  \<oplus>\<^sub>V (\<ominus>\<^sub>V v \<oplus>\<^sub>V u) = u" by auto 
    qed
qed  
  
theorem rlvect_1_th_8[rule_format]:
  "for V be add-associative \<bar> right-zeroed \<bar> right-complementable\<bar>
       non empty-struct \<parallel> addLoopStr, 
   w,v1,v2 being Element-of-struct V st 
      (w \<oplus>\<^sub>V v1 = w \<oplus>\<^sub>V v2 or v1 \<oplus>\<^sub>V w = v2 \<oplus>\<^sub>V w) holds  v1 = v2"  
proof(intro ballI impI)
  fix V w v1 v2 assume T0:"V be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
             non empty-struct\<parallel> addLoopStr" "w be Element-of-struct V" "v1 be Element-of-struct V" 
            "v2 be Element-of-struct V"
  have T1: "(\<ominus>\<^sub>V w) be Element-of-struct V" using rlvect_1_def_10 T0 by auto
  have T2: "0\<^sub>V be zero \<^sub>V \<parallel> Element-of-struct V" using struct_0_def_12_a[of V] struct_0_def_6[of V] T0 addLoopStr ZeroStr by auto   
  assume Z: "w \<oplus>\<^sub>V v1 = w \<oplus>\<^sub>V v2 or v1 \<oplus>\<^sub>V w = v2 \<oplus>\<^sub>V w"
  show "v1 = v2"
  proof (cases "v1 \<oplus>\<^sub>V w = v2 \<oplus>\<^sub>V w")
    case A1: True
      have "v1 = v1 \<oplus>\<^sub>V 0\<^sub>V" using rlvect_1_def_4a T0 by auto
      also have "\<dots> =  v1 \<oplus>\<^sub>V  (w \<oplus>\<^sub>V \<ominus>\<^sub>V w)" using rlvect_1_th_5 T0 by auto     
      also have "\<dots> =  (v1 \<oplus>\<^sub>V  w) \<oplus>\<^sub>V  \<ominus>\<^sub>V w" using rlvect_1_def_3a T0 T1 by auto 
      also have "\<dots> =  v2 \<oplus>\<^sub>V  (w \<oplus>\<^sub>V  \<ominus>\<^sub>V w)" using A1 rlvect_1_def_3a T0 T1 by auto
      also have "\<dots> =  v2 \<oplus>\<^sub>V 0\<^sub>V" using rlvect_1_th_5 T0 by auto    
      also have "\<dots> =  v2" using rlvect_1_def_4a T0 by auto
      finally show "v1 = v2" by auto
    next
      case A1: False
      have "v1 = 0\<^sub>V \<oplus>\<^sub>V v1" using rlvect_1_reduce_1[of V "0\<^sub>V" v1]  T2 T0 by auto
      also have "\<dots> =  (\<ominus>\<^sub>V w \<oplus>\<^sub>V  w) \<oplus>\<^sub>V v1 " using rlvect_1_th_5 T0 by auto     
      also have "\<dots> =  \<ominus>\<^sub>V w \<oplus>\<^sub>V ( w \<oplus>\<^sub>V v1)" using rlvect_1_def_3a T0 T1 by auto 
      also have "\<dots> =  \<ominus>\<^sub>V w \<oplus>\<^sub>V  w \<oplus>\<^sub>V v2" using A1 Z rlvect_1_def_3a T0 T1 by auto
      also have "\<dots> =  0\<^sub>V \<oplus>\<^sub>V v2" using rlvect_1_th_5 T0 by auto    
      also have "\<dots> =  v2" using rlvect_1_reduce_1[of V "0\<^sub>V" v2]  T2 T0 by auto
      finally show "v1 = v2" by auto    
  qed
qed

theorem rlvect_1_th_17[rule_format]:
  "for V be add-associative \<bar> right-zeroed \<bar> right-complementable\<bar>
       non empty-struct \<parallel> addLoopStr, 
   v being Element-of-struct V holds \<ominus>\<^sub>V \<ominus>\<^sub>V v = v"
proof(intro ballI)
  fix V v assume T0:"V be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
             non empty-struct\<parallel> addLoopStr" "v be Element-of-struct V" 
  have T1: "(\<ominus>\<^sub>V v) be Element-of-struct V" using rlvect_1_def_10 T0 by auto
  have "v \<oplus>\<^sub>V \<ominus>\<^sub>V v = 0\<^sub>V" using rlvect_1_def_10 T0 by auto
  thus "\<ominus>\<^sub>V \<ominus>\<^sub>V v = v" using rlvect_1_th_6 T0 T1 by auto   
qed

end