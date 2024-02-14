\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory funcop_1
  imports Funct_1
begin
  
definition funcop_1_def_2_prefix ("_ --> _" [90,90] 90) where
  "func X  --> y \<rightarrow> set equals [:X,{y}:]"

schematic_goal funcop_1_def_2:
  shows "?X" by (rule equals_property[OF funcop_1_def_2_prefix_def all_set])

theorem funcop_1_cl_1:
  "let X be set & y be object
   cluster X -->y \<rightarrow> Function_like \<bar>Relation_like"
proof-
  assume T0: "X be set & y be object"
  have W0:"[:X,{y}:] be Subset-of [:X,{y}:]" using Subset_of_rule by auto
  hence W1: "[:X,{y}:] be Relation" using relset_1_cl_1 T0 all_set by auto
  have "for a,b,c be object st [a,b] in [:X,{y}:] & [a,c] in [:X,{y}:] holds b=c"
  proof(intro ballI impI)
    fix a b c assume " [a,b] in [:X,{y}:] & [a,c] in [:X,{y}:] "
    hence "b in {y}" "c in {y}" using zfmisc_1_th_87 by auto
    thus "b=c" using tarski_def_1b by auto    
  qed
  hence "[:X,{y}:] is Function_like" using  funct_1_def_1 all_set  by auto
  thus "(X -->y) is Function_like \<bar>Relation_like" using  funcop_1_def_2 W1 by auto     
qed 
  
theorem funcop_1_th_7[rule_format]:
  "x in A implies (A  --> y).x = y"
proof
  have Z:"y in {y}" using tarski_def_1b by auto
  have T0:"(A --> y) be Function" using funcop_1_cl_1 all_set by auto 
  assume "x in A"
  hence "[x,y] in [:A,{y}:]" using Z zfmisc_1_th_87 all_set by auto
  hence "[x,y] in A --> y" using funcop_1_def_2 by auto  
  thus "(A --> y).x = y" using funct_1_th_1[OF T0] by auto    
qed  

theorem funcop_1_th_13[rule_format]:
  "dom (A --> y) = A & rng (A --> y) c= {y}"
proof
  have W0:"[:A,{y}:] be Subset-of [:A,{y}:]" using Subset_of_rule by auto
  hence W1: "[:A,{y}:] be Relation-of A,{y}" using relset_1_def_1 all_set by auto
  have W2: "[:A,{y}:] is A-defined \<bar> {y}-valued" using  relset_1_cl_2[of A "{y}",rule_format, OF _ W1] all_set by blast
  have W3: "[:A,{y}:] = A --> y" "(A --> y) be Function" using funcop_1_def_2 funcop_1_cl_1 all_set by auto 
      
  have A1: "dom (A --> y) c= A" using W2 W3 relat_1_def_18a by auto
  have "A c= dom (A --> y)" 
  proof(unfold tarski_def_3,intro ballI impI)
    have Z:"y in {y}" using tarski_def_1b by auto
    fix x assume "x in A"
    hence "[x,y] in [:A,{y}:]" using Z zfmisc_1_th_87 all_set by auto 
    thus "x in dom (A --> y)" using W3 by auto        
  qed    
  thus "dom (A --> y) = A" using A1 xboole_0_def_10 all_set  by auto   
  show "rng (A --> y) c= {y}" using W2 W3 relat_1_def_19a by auto    
qed    
  
definition funcop_1_def_9_prefix ("_ .--> _" [90,90] 90) where
  "func x .--> y \<rightarrow> set equals {x} --> y"

schematic_goal funcop_1_def_9:
  shows "?X" by (rule equals_property[OF funcop_1_def_9_prefix_def all_set])

end