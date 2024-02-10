\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory funcop_1
  imports funct_1
begin

func funcop_1_def_2 (infix "\<comment>>" 90) where
  mlet "X be set", "y be object"
  "func X \<comment>> y \<rightarrow> set equals [:X,{y}:]"
proof -
  show "[:X,{y}:] be set" by auto
qed

mtheorem funcop_1_cl_1[ty_func_cluster]:
  mlet "X be set", "y be object"
   "cluster X \<comment>>y \<rightarrow> Function_like \<bar>Relation_like"
proof-
  have A[ty]:"[:X,{y}:] be Subset-of [:X,{y}:]" using Subset_of_rule tarski_def_3 by mauto
  have "for a,b,c be object st [a,b] in [:X,{y}:] \<and> [a,c] in [:X,{y}:] holds b=c"
  proof(intro ballI impI)
    fix a b c assume " [a,b] in [:X,{y}:] \<and> [a,c] in [:X,{y}:] "
    hence "b in {y}" "c in {y}" using zfmisc_1_th_87 by auto
    thus "b=c" using tarski_def_1 by auto
  qed simp_all
  thm ty
  hence A: "[:X,{y}:] is Function_like" using funct_1_def_1 by auto
  thus "(X \<comment>>y) is Function_like \<bar> Relation_like" using A funcop_1_def_2[of X y] by auto
qed

reserve A for set

mtheorem funcop_1_th_7:
  "x in A \<longrightarrow> (A \<comment>> y).x = y"
proof
  have Z:"y in {y}" using tarski_def_1 by auto
  have T0:"(A \<comment>> y) be Function" by auto
  assume "x in A"
  hence "[x,y] in [:A,{y}:]" using Z zfmisc_1_th_87 by mauto
  hence "[x,y] in A \<comment>> y" using funcop_1_def_2 by auto
  thus "(A \<comment>> y).x = y" using funct_1_th_1[OF T0] by auto
qed

mtheorem funcop_1_th_13:
  "dom (A \<comment>> y) = A \<and> rng (A \<comment>>y) c= {y}"
proof
  have W0[ty]:"[:A,{y}:] be Subset-of [:A,{y}:]" using tarski_def_3 Subset_of_rule by mauto
  have W2: "[:A,{y}:] is A-defined \<bar> {y}-valued" by auto
  have W3: "[:A,{y}:] = A \<comment>>y" using funcop_1_def_2 by auto
thm ty
  have A1: "dom [:A,{y}:] c= A" using relat_1_def_18 by mauto
  have "A c= dom (A \<comment>>y)"
  proof(intro tarski_def_3b)
    have Z:"y in {y}" using tarski_def_1 by auto
    fix x assume "x in A"
    hence "[x,y] in [:A,{y}:]" using Z zfmisc_1_th_87 by auto
    thus "x in dom (A \<comment>>y)" using W3 xtuple_0_def_12 by auto
  qed simp_all
  thus "dom (A \<comment>>y) = A" using A1 xboole_0_def_10 W3 by auto
  show "rng (A \<comment>>y) c= {y}" using W3 relat_1_def_19[THEN iffD1,simplified,rule_format] by mauto
qed

func funcop_1_def_9 (infix ".\<comment>>" 300) where
  mlet "x be object", "y be object"
  "func x .\<comment>> y \<rightarrow> set equals {x}\<comment>> y"
  by simp
(*lemmas [simp] =funcop_1_def_9*)

mtheorem funcop_1_cl[ty_func_cluster]:
  mlet "x be object", "y be object"
   "cluster x .\<comment>>y \<rightarrow> Function_like \<bar>Relation_like"
proof-
  have "x .\<comment>> y = {x}\<comment>> y" using funcop_1_def_9 by auto
  thus "x .\<comment>> y is Function_like \<bar>Relation_like" by mauto
qed


end
