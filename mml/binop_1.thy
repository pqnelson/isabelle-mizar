\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory binop_1
  imports tarski funct_2
begin

func binop_0_def_1 (" _ . \<lparr> _ , _ \<rparr>"[90,90,90]) where
  mlet "f be Function", "a be object", "b be object"
  "func f . \<lparr> a , b \<rparr> \<rightarrow> set equals f.[a,b]"
proof -
  show "(f.[a,b]) be set" using all_set by simp
qed mauto

theorem binop_0_def_2:
 "let A be non empty \<bar> set \<and> B be non empty \<bar> set \<and> C be set \<and>
        f be (Function-of [:A,B:],C) \<and> a be (Element-of A) \<and> b be (Element-of B)
  redefine func f.\<lparr>a,b\<rparr>  \<rightarrow> Element-of C"
proof
  assume A0[ty]: "A be non empty \<bar> set \<and> B be non empty \<bar> set \<and> C be set \<and>
        f be (Function-of [:A,B:],C) \<and> a be (Element-of A) \<and> b be (Element-of B)"
  have "a in A" "b in B " using subset_1_def_1(1)[of A a] subset_1_def_1(1)[of B b] by auto
  hence "[a,b] in [:A,B:]" using zfmisc_1_def_2 by auto
  hence "[:A,B:] be non empty\<bar>set" "[a,b] be Element-of [:A,B:]" using Element(6) xboole_0_def_1 by auto
  hence "(f.[a,b]) be Element-of C" using funct_2_def_5A[of "[:A,B:]" "C" "f" "[a,b]"]  by mauto
  thus "f.\<lparr> a, b \<rparr> be Element-of C" using binop_0_def_1 by auto
qed

abbreviation (input) binop_1_mode_1 ("UnOp-of _" [190] 190) where
  "UnOp-of X \<equiv> Function-of X , X"

abbreviation binop_1_mode_2 ("BinOp-of _" [190] 190) where
  "BinOp-of X \<equiv> Function-of [:X,X:] , X"


mtheorem binop_0_def_20A[rule_format,ty_func]:
  mlet "A be set", "f be BinOp-of A", "a be Element-of A", "b be Element-of A"
  "redefine func f.\<lparr>a,b\<rparr> \<rightarrow> Element-of A"
proof -
  have Z: "f.\<lparr> a,b \<rparr> = f.[a,b]" using binop_0_def_1 by simp
  show "f.\<lparr>a,b\<rparr> be (Element-of A)"
    proof(cases "A={}")
      assume A1: "A={}"
       hence "f = {}" using funct_2_def_1E[of "[:A,A:]" A f] by mauto
       hence "not [a,b] in dom f" using relat_1_cl_20 empty1[of "dom f"] xb by mauto
       hence "f.[a,b] = {}" using funct_1_def_2 by simp
      thus "f.\<lparr>a,b\<rparr> be (Element-of A)" using A1 Z Element(3) by simp
    next
      assume A2: "A\<noteq>{}"
       hence "A is non empty" using xboole_0_lm_1[of A,simplified] by auto
       hence "dom f = [:A,A:]" "a in A" "b in A" using A2 funct_2_def_1[of "[:A,A:]" A f] Element_of_rule2 by auto
       hence "[a,b] in [:A,A:]" using zfmisc_1_def_2 by auto
       hence "[:A,A:] be non empty\<bar>set" "[a,b] be Element-of [:A,A:]" using Element(6) xboole_0_def_1 by auto
       hence "(f.[a,b]) be Element-of A"
         by (intro funct_2_def_5A) mauto
      thus "f.\<lparr>a,b\<rparr> be (Element-of A)" using Z by auto
    qed
  qed

lemma BinOp_ex[ex]:
  "X be set \<Longrightarrow> inhabited(BinOp-of X)"
proof-
  assume [ty]:"X be set"
  show "inhabited(BinOp-of X)" by mauto
qed

notation (input) xboole_0_def_2 ("op0")

lemma funct_5_def_4A[ty_func]:"op0 be set" by mauto

abbreviation funct_5_def_6 ("op2") where
  "op2 \<equiv>{[ op0,op0 ,op0]}"

lemma funct_5_def_6A[ty_func]:
   "op2 be set" by mauto


theorem funct_5_def_7[ty_func]:
  "op0 be Element-of {{}}" using tarski_def_1 Element(6) by mauto

theorem funct_5_def_9[ty_func]:
  "op2 be BinOp-of {{}}"
proof-
  have B1: "op2 be Function" by mauto
  hence "dom op2=[:{{}},{{}}:]" "rng op2 = {{}}" using
              relat_1_th_3[of "{}" "[{},{}]" op2] zfmisc_1_th_28 by auto
  thus B2: "op2 be BinOp-of {{}}" using funct_2_th_2[of op2,OF B1] by auto
qed

abbreviation funct_5_def_x ("op1") where
  "op1 \<equiv>{[ op0,op0]}"

lemma funct_5_def_xA[ty_func]:
   "op1 be set" by mauto

theorem funct_5_def_x[ty_func]:
  "op1 be Function-of {{}},{{}}"
proof-
  have B1: "op1 be Function" by mauto
  hence "dom op1={{}}" "rng op1 = {{}}" using
              relat_1_th_3[of "{}" "{}" op1] zfmisc_1_th_28 by auto
  thus B2: "op1 be Function-of {{}},{{}}" using funct_2_th_2[of op1,OF B1] by auto
qed


theorem funcop_1_1[ty_func]:
  "a .--> c be Function-of {a} , {c}"
proof-
  let ?ac="a .--> c"
  have A1: "[:{a},{c}:] = {[a,c]}" using zfmisc_1_th_28 by auto
  have A2: "?ac = [:{a},{c}:]" using funcop_1_def_9 funcop_1_def_2 by mauto

  have [ty]: "?ac be Function" by mauto
  have "dom ?ac={a}" "rng ?ac = {c}" using
              relat_1_th_3[of "c" a ?ac] A1 A2 zfmisc_1_th_28 by mauto
  thus B2: "?ac be Function-of {a} , {c}" using funct_2_th_2 by mauto

qed


theorem funcop_1_2[ty_func]:
  "[a,b] .--> c be Function-of [:{a},{b}:] , {c}"
proof-
  let ?abc="[a,b] .--> c"
  have A1: "[:{[a,b]},{c}:] = {[a,b,c]}" using zfmisc_1_th_28 by auto
  have A2: "?abc = [:{[a,b]},{c}:]" using funcop_1_def_9 funcop_1_def_2 by mauto

  have [ty]: "?abc be Function" by mauto
  have "dom ?abc=[:{a},{b}:]" "rng ?abc = {c}" using
              relat_1_th_3[of "c" "[a,b]" ?abc] A1 A2 zfmisc_1_th_28 by mauto
  thus B2: "?abc be Function-of [:{a},{b}:] , {c}" using funct_2_th_2 by mauto
qed

end