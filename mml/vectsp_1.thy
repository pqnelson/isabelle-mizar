theory vectsp_1
imports z2 rlvect_1 group_1
begin

mlemma Z2_cl_7[ty_func_cluster]:
  "cluster Z \<rightarrow> add-associative \<bar> right-zeroed \<bar> right-complementable \<bar> Abelian \<bar> non empty-struct"
proof(simp,intro conjI)
(*  have [ty]: "Z be doubleLoopStr" by auto *)
  show "Z is add-associative"
  proof

    fix u v w assume T1[ty]: "u be Element-of-struct Z" "v be Element-of-struct Z"  "w be Element-of-struct Z"
    have A1: "u=One \<or> u = Zero" "v=One \<or> v = Zero" "w=One \<or> w = Zero" using Z2d(3) by simp_all
    show "u \<oplus>\<^sub>Z v \<oplus>\<^sub>Z w = u \<oplus>\<^sub>Z (v \<oplus>\<^sub>Z w)" using Z2d(6,7,8,9) A1 by auto
  qed auto
  show "Z is right-zeroed"
  proof
     fix v assume [ty]:"v be Element-of-struct Z"
     hence "v=One \<or> v = Zero" using Z2d(3) by simp
     thus "v \<oplus>\<^sub>Z 0\<^sub>Z = v" using Z2d(3)[of v] Z2d(4,6,8) by mty auto
   qed auto
  show "Z is right-complementable"
  proof(intro algstr_0_def_16I algstr_0_def_11I)
    fix x assume A1[ty]:"x be Element-of-struct Z"
    show "\<exists>y be Element-of-struct Z. x \<oplus>\<^sub>Z y = 0\<^sub>Z"
      proof(rule bexI[of _ _ x])
        have "x=One \<or> x = Zero" using A1 Z2d(3) by simp
        thus "x \<oplus>\<^sub>Z x = 0\<^sub>Z" using A1 Z2d(4,6,9)  by auto
      qed auto
  qed auto
  show "Z is Abelian"
  proof
    fix u v assume T1[ty]: "u be Element-of-struct Z" "v be Element-of-struct Z"
    hence A1: "u=One \<or> u = Zero" "v=One \<or> v = Zero" using Z2d(3) by simp+
    show "u \<oplus>\<^sub>Z v = v \<oplus>\<^sub>Z u" using Z2d(6,7,8,9) A1 by auto
   qed auto
  have [ty]: "the carrier of Z is non empty" using Z2d(14) by mty auto
  thus "\<not> Z is empty-struct" using struct_0_def_1 by auto
qed

theorem vectsp_1_cl_7[ex]:
  "cluster add-associative\<bar>right-zeroed\<bar>right-complementable\<bar> Abelian for
    non empty-struct\<bar>addLoopStr"
proof
  show "Z is add-associative\<bar>right-zeroed\<bar>right-complementable\<bar>Abelian\<bar>(non empty-struct\<bar>addLoopStr)" by mty auto
qed

abbreviation(input)
  "AddGroup \<equiv> add-associative\<bar>right-zeroed\<bar>right-complementable\<bar>(non empty-struct\<bar>addLoopStr)"

abbreviation (input)
  "AbGroup \<equiv> Abelian\<bar>AddGroup"

attr vectsp_1_def_2 ("right-distributive")
   "attr right-distributive for non empty-struct\<bar>doubleLoopStr means (\<lambda> M.
     (for a,b,c be Element-of-struct M holds a \<otimes>\<^sub>M (b \<oplus>\<^sub>M c) = a \<otimes>\<^sub>M b \<oplus>\<^sub>M a \<otimes>\<^sub>M c))"

lemma "inhabited(non empty-struct\<bar>doubleLoopStr)" by auto

attr vectsp_1_def_3 ("left-distributive")
   "attr left-distributive for non empty-struct\<bar>doubleLoopStr means (\<lambda> M.
     (for a,b,c be Element-of-struct M holds (b \<oplus>\<^sub>M c) \<otimes>\<^sub>M a = b \<otimes>\<^sub>M a \<oplus>\<^sub>M c \<otimes>\<^sub>M a))"

attr vectsp_1_def_4 ("right-unital")
   "attr right-unital for non empty-struct\<bar>multLoopStr means (\<lambda> M.
     (for a be Element-of-struct M holds a \<otimes>\<^sub>M 1\<^sub>M = a))"

attr vectsp_1_def_6 ("well-unital")
   "attr well-unital for non empty-struct\<bar>multLoopStr means (\<lambda> M.
     (for a be Element-of-struct M holds a \<otimes>\<^sub>M 1\<^sub>M = a \<and> 1\<^sub>M \<otimes>\<^sub>M a = a))"

mlemma Z2_cl_15[ty_func_cluster]:
  "cluster Z \<rightarrow> well-unital"
proof
  fix a assume A1[ty]: "a be Element-of-struct Z"
  show "a \<otimes>\<^sub>Z 1\<^sub>Z = a \<and> (1\<^sub>Z) \<otimes>\<^sub>Z a = a"
    proof (cases "a=One")
      case True
       thus ?thesis using Z2d(5,11,13) Z2d(3)[of a] by auto next
      case False
        thus ?thesis using Z2d(5,11,12) Z2d(3)[of a] A1 by auto next
    qed
  qed mauto


theorem vectsp_1_cl_15[ex]:
  "cluster well-unital for non empty-struct\<bar>multLoopStr_0"
  unfolding inhabited_def
proof(intro exI)
  show "Z is well-unital\<bar>(non empty-struct\<bar>multLoopStr_0)" by mty auto
qed

mtheorem vectsp_1_reduce_1:
  mlet "L be well-unital \<bar> (non empty-struct\<bar>multLoopStr_0)",
       "x be Element-of-struct L"
  "reduce x\<otimes>\<^sub>L 1\<^sub>L to x"
  using vectsp_1_def_6E[of L x] by mauto

mtheorem vectsp_1_reduce_2:
  mlet "L be well-unital\<bar>non empty-struct\<bar>multLoopStr_0",
       "x be Element-of-struct L"
  "reduce (1\<^sub>L) \<otimes>\<^sub>L x to x"
  using vectsp_1_def_6E[of L x] by mty auto

attr vectsp_1_def_7 ("distributive")
   "attr distributive for non empty-struct\<bar>doubleLoopStr means (\<lambda> M.
     (for a,b,c be Element-of-struct M holds a \<otimes>\<^sub>M (b \<oplus>\<^sub>M c) = a \<otimes>\<^sub>M b \<oplus>\<^sub>M a \<otimes>\<^sub>M c \<and> (b \<oplus>\<^sub>M c) \<otimes>\<^sub>M a = b \<otimes>\<^sub>M a \<oplus>\<^sub>M c \<otimes>\<^sub>M a))"


attr vectsp_1_def_8 ("left-unital")
   "attr left-unital for non empty-struct\<bar>doubleLoopStr means (\<lambda> M.
     (for a be Element-of-struct M holds 1\<^sub>M \<otimes>\<^sub>M a = a))"


theorem vectsp_1_def_9:
  "let M be non empty-struct\<bar>multLoopStr_0
   redefine attr M is almost-left-invertible means
      for x be Element-of-struct M st x \<noteq> 0\<^sub>M holds ex y be Element-of-struct M st y \<otimes>\<^sub>M x = 1\<^sub>M"
proof(rule iffI3 )
  assume T0[ty]: "M be non empty-struct\<bar>multLoopStr_0"
  show "M is almost-left-invertible \<longrightarrow> (for x be Element-of-struct M st x \<noteq>0\<^sub>M holds ex y be Element-of-struct M st y \<otimes>\<^sub>M x = 1\<^sub>M)"
    using algstr_0_def_39E[of M] algstr_0_def_27E[of M] by auto
  assume A1: "for x be Element-of-struct M st x \<noteq>0\<^sub>M holds ex y be Element-of-struct M st y \<otimes>\<^sub>M x = 1\<^sub>M"
  show "M is almost-left-invertible"
  proof(intro algstr_0_def_39I algstr_0_def_27I)
    fix x assume [ty]:"x be Element-of-struct M" and "x \<noteq>0\<^sub>M"
    thus "ex y be Element-of-struct M st y \<otimes>\<^sub>M x = 1\<^sub>M" using A1 by auto
  qed auto
qed

lemmas vectsp_1_def_9a = vectsp_1_def_9[THEN iffD1,THEN bspec,simplified,rule_format]
lemmas vectsp_1_def_9b = vectsp_1_def_9[THEN iffD2]


theorem vectsp_1_cl_20[ty_cond_cluster]:
  "cluster distributive \<rightarrow> left-distributive \<bar>right-distributive for
    non empty-struct \<bar>doubleLoopStr"
proof(unfold ty_intersection, intro conjI)
  fix M assume [ty]:"M be non empty-struct \<and> M be doubleLoopStr" "M be distributive"
  show "M be left-distributive"
  proof
    fix a b c assume [ty]:"a be Element-of-struct M" "b be Element-of-struct M" "c be Element-of-struct M"
    show "(b \<oplus>\<^sub>M c) \<otimes>\<^sub>M a = b \<otimes>\<^sub>M a \<oplus>\<^sub>M c \<otimes>\<^sub>M a" using vectsp_1_def_7E[of M a b c]  by auto
  qed auto
  show "M be right-distributive"
  proof
    fix a b c assume [ty]:"a be Element-of-struct M" "b be Element-of-struct M" "c be Element-of-struct M"
    show "a \<otimes>\<^sub>M (b \<oplus>\<^sub>M c) = a \<otimes>\<^sub>M b \<oplus>\<^sub>M a \<otimes>\<^sub>M c" using vectsp_1_def_7E[of M a b c]  by auto
  qed auto
qed

theorem vectsp_1_cl_21[ty_cond_cluster]:
  "cluster left-distributive \<bar>right-distributive \<rightarrow> distributive for
    non empty-struct \<bar>doubleLoopStr"
proof
  fix M assume [ty]: " M be non empty-struct \<bar>doubleLoopStr" "M be left-distributive \<bar>right-distributive"
   fix a b c assume [ty]:"a be Element-of-struct M" "b be Element-of-struct M" "c be Element-of-struct M"
   show "a \<otimes>\<^sub>M (b \<oplus>\<^sub>M c) = a \<otimes>\<^sub>M b \<oplus>\<^sub>M a \<otimes>\<^sub>M c \<and> (b \<oplus>\<^sub>M c) \<otimes>\<^sub>M a = b \<otimes>\<^sub>M a \<oplus>\<^sub>M c \<otimes>\<^sub>M a" using vectsp_1_def_3E[of M a b c]
      vectsp_1_def_2E[of M a b c] by mty auto
 qed auto

theorem vectsp_1_cl_22[ty_func_cluster]:
  "cluster well-unital \<rightarrow> left-unital \<bar>right-unital for
    non empty-struct \<bar>doubleLoopStr"
proof(unfold ty_intersection, intro conjI)
  fix M assume [ty]:"M be non empty-struct \<and> M be doubleLoopStr" "M be well-unital"
  show "M be left-unital"
  proof
    fix a assume [ty]:"a be Element-of-struct M"
    show "1\<^sub>M \<otimes>\<^sub>M a = a" using vectsp_1_def_6E[of M a]  by auto
  qed auto
  show "M be right-unital"
  proof
    fix a assume [ty]:"a be Element-of-struct M"
    show " a \<otimes>\<^sub>M 1\<^sub>M = a" using vectsp_1_def_6E[of M a]  by auto
  qed auto
qed

theorem vectsp_1_cl_23[ty_cond_cluster]:
  "cluster left-unital \<bar>right-unital \<rightarrow> well-unital for
    non empty-struct \<bar>doubleLoopStr"
proof(intro vectsp_1_def_6I ballI)
  fix M assume [ty]:"M be non empty-struct\<bar> doubleLoopStr" "M be left-unital \<bar>right-unital"
  show "M is non empty-struct \<and> M is multLoopStr" by mauto
  fix a assume [ty]:"a be Element-of-struct M"
  show "a \<otimes>\<^sub>M 1\<^sub>M = a \<and> 1\<^sub>M \<otimes>\<^sub>M a = a" using vectsp_1_def_4E[of M a]  vectsp_1_def_8E[of M a]  by auto
qed mauto

theorem Z2_cl_24[ty_func_cluster]:
  "cluster Z \<rightarrow> commutative\<bar>associative\<bar>unital"
proof(simp, intro conjI)
  have A1[ty]: "Z be doubleLoopStr" by mty auto
  show "Z is commutative"
  proof
    fix u v assume T1[ty]: "u be Element-of-struct Z" "v be Element-of-struct Z"
    hence A1: "u=One \<or> u = Zero" "v=One \<or> v = Zero" using Z2d(3) by simp+
    show "u \<otimes>\<^sub>Z v = v \<otimes>\<^sub>Z u" using Z2d(11,12) A1 by auto
  qed auto
  show "Z is associative"
      proof
        fix u v w assume T1[ty]: "u be Element-of-struct Z" "v be Element-of-struct Z"  "w be Element-of-struct Z"
         hence "u=One \<or> u = Zero" "v=One \<or> v = Zero" "w=One \<or> w = Zero" using Z2d(3) by simp+
         thus "u \<otimes>\<^sub>Z v \<otimes>\<^sub>Z w = u \<otimes>\<^sub>Z (v \<otimes>\<^sub>Z w)" using Z2d(10,11,12,13) by auto
      qed mauto
  show "Z is unital"
  proof(intro group_1_def_1I bexI[of _ _ "1\<^sub>Z"] ballI)
    show "1\<^sub>Z be Element-of-struct Z" by (simp add:Z2d(2,5))
    fix h assume A1:"h be Element-of-struct Z"
    hence "h=One \<or> h=Zero" "1\<^sub>Z = One" using Z2d(5,3) by auto
    thus "h \<otimes>\<^sub>Z 1\<^sub>Z = h \<and> 1\<^sub>Z \<otimes>\<^sub>Z h = h" using Z2d(11,12,13) by auto
  qed auto
qed

theorem vectsp_1_cl_24[ex]:
  "cluster commutative\<bar>associative for non empty-struct \<bar>multMagma"
   unfolding inhabited_def
proof(intro exI)
   show "Z is commutative\<bar>associative\<bar>(non empty-struct \<bar>multMagma)" by mty auto
 qed


theorem vectsp_1_cl_25[ex]:
  "cluster commutative\<bar>associative\<bar>unital for non empty-struct \<bar>multLoopStr"
   unfolding inhabited_def
proof(intro exI)
   show "Z is commutative\<bar>associative\<bar>unital\<bar>(non empty-struct \<bar>multLoopStr)" by mty auto
 qed

theorem Z2_cl_26[ty_func_cluster]:
  "cluster Z \<rightarrow> almost-left-invertible\<bar>distributive\<bar>non degenerated\<bar>strict (doubleLoopStr)"
proof(simp,intro conjI)
  have A1[ty]: "Z be doubleLoopStr" by mty auto
  show "Z is almost-left-invertible"
  proof(intro algstr_0_def_39I algstr_0_def_27I bexI[of _ _ "1\<^sub>Z"])
    fix x assume [ty]:"x be Element-of-struct Z" and "x \<noteq> 0\<^sub>Z"
    thus "1\<^sub>Z \<otimes>\<^sub>Z x = 1\<^sub>Z" "1\<^sub>Z be Element-of-struct Z" using Z2d(3)[of x] Z2d(2,4,5,13) by auto
  qed auto
  show "Z is distributive"
  proof
      fix u v w assume [ty]: "u be Element-of-struct Z" "v be Element-of-struct Z"  "w be Element-of-struct Z"
      have A1: "u=One \<or> u = Zero" "v=One \<or> v = Zero" "w=One \<or> w = Zero" using Z2d(3) by mty auto
    show "u \<otimes>\<^sub>Z (v \<oplus>\<^sub>Z w) = (u \<otimes>\<^sub>Z v) \<oplus>\<^sub>Z (u \<otimes>\<^sub>Z w) \<and> (v \<oplus>\<^sub>Z w) \<otimes>\<^sub>Z u = (v \<otimes>\<^sub>Z u) \<oplus>\<^sub>Z (w \<otimes>\<^sub>Z u)"
    proof (cases "u=One")
      case True
        thus ?thesis using Z2d(6,7,8,9,10,11,12,13) A1 by auto
     next
        case False
          thus ?thesis using Z2d(6,7,8,9,10,11,12,13) A1 by auto
    qed
  qed mauto
  show "\<not> Z is degenerated" using struct_0_def_8c Z2d(4,5) by auto
  have "domain_of doubleLoopStr = dom Z"
       using doubleLoopStrD Dom_5 by auto
  thus "Z is strict (doubleLoopStr)" using strict[THEN conjunct2] by auto
qed


lemma [ex]:
"cluster associative \<bar> commutative \<bar> well-unital \<bar> distributive \<bar> almost-left-invertible for non empty-struct \<bar> doubleLoopStr"
  using inhabited_def exI[of _ Z] by mty auto

lemma [ex]:
  "cluster add-associative\<bar>right-zeroed\<bar>right-complementable\<bar>
  right-distributive for non empty-struct \<bar>doubleLoopStr"
   using inhabited_def exI[of _ Z] vectsp_1_cl_20 by mty auto

lemma [ex]:
  "cluster add-associative\<bar>right-zeroed\<bar>right-complementable\<bar>
  left-distributive for non empty-struct \<bar>doubleLoopStr"
   using inhabited_def exI[of _ Z] vectsp_1_cl_20 by mty auto



lemma [ex]:
  "cluster add-associative \<bar> right-zeroed \<bar> right-complementable \<bar> distributive for non empty-struct \<bar>doubleLoopStr"
  using inhabited_def exI[of _ Z]  by mty auto

lemma [ex]:
  "cluster add-associative \<bar> right-zeroed \<bar>
         right-complementable \<bar> associative \<bar> commutative \<bar>
         well-unital \<bar> almost-left-invertible \<bar>
         distributive for non empty-struct \<bar> doubleLoopStr"
using inhabited_def exI[of _ Z]  by mty auto


 text_raw {*\DefineSnippet{vectsp1cl26}{*}
theorem vectsp_1_cl_26:
 "cluster add-associative \<bar> right-zeroed \<bar> right-complementable \<bar>
          Abelian \<bar> commutative \<bar> associative \<bar> left-unital\<bar>
          right-unital \<bar> distributive \<bar> almost-left-invertible\<bar>
          non degenerated \<bar> well-unital \<bar> strict (doubleLoopStr)
     for non empty-struct \<bar> doubleLoopStr"
  text_raw {*}%EndSnippet*}
  unfolding inhabited_def
  by (rule exI[of _ Z]) mauto


text_raw {*\DefineSnippet{Ring}{*}
abbreviation
 "Ring \<equiv> Abelian \<bar> add-associative \<bar> right-zeroed \<bar>
          right-complementable \<bar> associative \<bar>
          well-unital \<bar> distributive \<bar>
          non empty-struct \<bar> doubleLoopStr"
text_raw {*}%EndSnippet*}
text_raw {*\DefineSnippet{SkewField}{*}
abbreviation
 "SkewField \<equiv> non degenerated \<bar>
                     almost-left-invertible \<bar> Ring"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{FIELD}{*}
abbreviation
  "Field \<equiv> commutative \<bar> SkewField"
text_raw {*}%EndSnippet*}

theorem vectsp_1_Field_Test:
  "ex R be Field st True" using inhabited_def exI[of _ Z]  by mty auto
theorem [ex]:
  "inhabited(Field)"
proof
  show "Z is Field" by mty auto
qed


theorem vectsp_1_th_5:
  "for F be associative\<bar>commutative\<bar>well-unital\<bar>distributive\<bar>
            almost-left-invertible \<bar>(non empty-struct\<bar>doubleLoopStr),
       x,y,z be Element-of-struct F
   st x \<noteq> 0\<^sub>F \<and> x \<otimes>\<^sub>F y = x \<otimes>\<^sub>F z holds y = z"
proof(intro ballI uncurry impI)
  fix F x y z assume T0[ty]: " F be associative \<bar> commutative \<bar> well-unital \<bar> distributive \<bar>
                         almost-left-invertible \<bar> (non empty-struct \<bar>doubleLoopStr)"
                 and T1[ty]: "x be Element-of-struct F"  "y be Element-of-struct F" "z be Element-of-struct F"
  have W1[ty]:  "F is left-unital" using vectsp_1_cl_22 by auto
  assume "x\<noteq>0\<^sub>F"
  then obtain x1 where T2[ty]:"x1 be Element-of-struct F" and
    A1: "x1 \<otimes>\<^sub>F x = 1\<^sub>F" using vectsp_1_def_9a[of F x] by mty auto
  have A2: "(x1 \<otimes>\<^sub>F x) \<otimes>\<^sub>F y = x1 \<otimes>\<^sub>F (x \<otimes>\<^sub>F y) \<and> x1 \<otimes>\<^sub>F (x \<otimes>\<^sub>F z) = (x1 \<otimes>\<^sub>F x) \<otimes>\<^sub>F z" using group_1_def_3E[of F] by auto
  assume "x \<otimes>\<^sub>F y = x \<otimes>\<^sub>F z"
  hence "(x1 \<otimes>\<^sub>F x) \<otimes>\<^sub>F y = z" using A1 A2 vectsp_1_def_8E W1 by auto
  thus "y=z" using A1 A2 vectsp_1_def_8E W1 by auto
qed mauto

abbreviation inv (infix "\<hungarumlaut>\<^sup>" 105) where
  "x\<hungarumlaut>\<^sup>S \<equiv> /\<^sub>S x"


theorem vectsp_1_def_10:
  "let F be associative \<bar> commutative \<bar> well-unital \<bar>
       almost-left-invertible \<bar> (non empty-struct \<bar> doubleLoopStr) \<and>
       x be Element-of-struct F \<and> x \<noteq> 0\<^sub>F
   redefine func x\<hungarumlaut>\<^sup>F \<rightarrow> Element-of-struct F means
     (\<lambda>it. it \<otimes>\<^sub>F x = 1\<^sub>F)"
proof(elim conjE, rule redefine_func_means_property,simp)
  assume [ty]: "F be associative\<bar>commutative\<bar>well-unital\<bar>almost-left-invertible
               \<bar>( non empty-struct\<bar>doubleLoopStr)"
              "x be Element-of-struct F" and
              T0: "x \<noteq> 0\<^sub>F"
  show [ty]: "x\<hungarumlaut>\<^sup>F be Element-of-struct F" by mty auto
  have [ty]: "x is left-invertible\<^sub>F" using algstr_0_def_39E T0 by auto
  then obtain x1 where [ty]: "x1 be Element-of-struct F" and
    A3: "x1 \<otimes>\<^sub>F x = 1\<^sub>F" using algstr_0_def_27E[of F x] by auto
  have A3': "x \<otimes>\<^sub>F x1 = 1\<^sub>F"
    using group_1_def_12E[of F x1 x] A3 T0 by auto
  have [ty]: "x is right-mult-cancelable\<^sub>F"
   proof(intro algstr_0_def_21I)
     fix y z assume [ty]: "y be Element-of-struct F"
                        "z be Element-of-struct F"
     assume A4: "y \<otimes>\<^sub>F x = z \<otimes>\<^sub>F x"
     have "y = y \<otimes>\<^sub>F 1\<^sub>F" using vectsp_1_def_6E by auto
     also have "\<dots> = z \<otimes>\<^sub>F x \<otimes>\<^sub>F x1"
       using A3' A4 group_1_def_3E[of F y x x1]  by auto
     also have "\<dots> = z \<otimes>\<^sub>F 1\<^sub>F"
       using A3' A4 group_1_def_3E[of F z x x1]  by auto
     also have "\<dots> = z " using vectsp_1_def_6E by auto
     finally show "y = z" by auto
   qed auto
   fix IT assume [ty]:"IT be Element-of-struct F"
   thus "IT = x\<hungarumlaut>\<^sup>F \<longleftrightarrow> IT \<otimes>\<^sub>F x = 1\<^sub>F"
     thm algstr_0_def_30 A
     using A algstr_0_def_30[of F x,simplified] algstr_0_def_30_uniq[of F x IT,simplified] by mty auto (* Jest wolne , ale dziala*)
qed

theorem vectsp_1_th_6[THEN bspec,THEN bspec,rule_format]:
  "for F be add-associative\<bar>right-zeroed\<bar>right-complementable\<bar>
  right-distributive\<bar>(non empty-struct \<bar>doubleLoopStr), x be Element-of-struct F holds
   x \<otimes>\<^sub>F 0\<^sub>F = 0\<^sub>F"
proof (intro ballI)
  fix F x assume T0[ty]:"F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
    right-distributive\<bar>(non empty-struct \<bar>doubleLoopStr)" "x be Element-of-struct F"
  have "x \<otimes>\<^sub>F 0\<^sub>F \<oplus>\<^sub>F 0\<^sub>F = x\<otimes>\<^sub>F(0\<^sub>F \<oplus>\<^sub>F 0\<^sub>F) \<oplus>\<^sub>F 0\<^sub>F" using rlvect_1_th_4[of F] by mty auto
  also have "\<dots>= x\<otimes>\<^sub>F ( 0\<^sub>F \<oplus>\<^sub>F 0\<^sub>F)" using rlvect_1_th_4[of F,THEN conjunct1] by mauto
  also have "\<dots>= x\<otimes>\<^sub>F 0\<^sub>F \<oplus>\<^sub>F x \<otimes>\<^sub>F 0\<^sub>F" by (intro vectsp_1_def_2E) mauto
  finally show " x \<otimes>\<^sub>F 0\<^sub>F = 0\<^sub>F" using rlvect_1_th_8[of F "x \<otimes>\<^sub>F 0\<^sub>F"  "0\<^sub>F" "x \<otimes>\<^sub>F 0\<^sub>F"]  by mty auto
qed mauto

theorem vectsp_1_reduce_3[simplified,rule_format]:
  "let F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
            right-distributive\<bar>non empty-struct \<bar>doubleLoopStr \<and>
       (x be Element-of-struct F \<and>
       y be zero \<^sub>F \<bar> Element-of-struct F)
   reduce x \<otimes>\<^sub>F y to y"
proof-
  assume T0[ty]: " F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
            right-distributive\<bar>non empty-struct \<bar>doubleLoopStr \<and>
       (x be Element-of-struct F \<and>
       y be zero \<^sub>F \<bar> Element-of-struct F)"
  hence "y=0\<^sub>F" using struct_0_def_12E by mauto
  thus "x \<otimes>\<^sub>F y = y" using vectsp_1_th_6[of F x] by auto
qed

theorem vectsp_1_th_7[THEN bspec,THEN bspec,rule_format]:
  "for F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
     left-distributive\<bar>(non empty-struct \<bar>doubleLoopStr), x be Element-of-struct F holds
     0\<^sub>F \<otimes>\<^sub>F x = 0\<^sub>F"
proof (intro ballI)
  fix F x assume T0[ty]:"F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
    left-distributive\<bar>(non empty-struct \<bar>doubleLoopStr)" "x be Element-of-struct F"
  have "0\<^sub>F \<otimes>\<^sub>F x \<oplus>\<^sub>F 0\<^sub>F = ( 0\<^sub>F \<oplus>\<^sub>F 0\<^sub>F)\<otimes>\<^sub>F x \<oplus>\<^sub>F 0\<^sub>F" using rlvect_1_th_4[of F "0\<^sub>F"] by mty auto
  also have "\<dots>= ( 0\<^sub>F \<oplus>\<^sub>F 0\<^sub>F)\<otimes>\<^sub>F x" using rlvect_1_th_4[of F] by mauto
  also have "\<dots>=  0\<^sub>F \<otimes>\<^sub>F x \<oplus>\<^sub>F 0\<^sub>F \<otimes>\<^sub>F x" using vectsp_1_def_3E[of F] by mty auto
  finally show " 0\<^sub>F \<otimes>\<^sub>F x= 0\<^sub>F" using rlvect_1_th_8[of F "0\<^sub>F \<otimes>\<^sub>F x" "0\<^sub>F" "0\<^sub>F \<otimes>\<^sub>F x"]  by mty auto
qed mauto

theorem vectsp_1_reduce_4[simplified,rule_format]:
  "let F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
            left-distributive\<bar>non empty-struct \<bar>doubleLoopStr \<and>
       (x be Element-of-struct F \<and>
       y be zero \<^sub>F \<bar> Element-of-struct F)
   reduce y \<otimes>\<^sub>F x to y"
proof-
  assume T0[ty]: " F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
            left-distributive\<bar>non empty-struct \<bar>doubleLoopStr \<and>
       (x be Element-of-struct F \<and>
       y be zero \<^sub>F \<bar> Element-of-struct F)"
  hence "y=0\<^sub>F" using struct_0_def_12E[of F] by mauto
  thus "y \<otimes>\<^sub>F x = y" using vectsp_1_th_7[of F x] T0 by auto
qed

theorem vectsp_1_th_8[THEN bspec,THEN bspec,THEN bspec,rule_format]:
  "for F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
  right-distributive\<bar>(non empty-struct \<bar>doubleLoopStr), x,y be Element-of-struct F holds
   x \<otimes>\<^sub>F (\<ominus>\<^sub>F y) = \<ominus>\<^sub>F x \<otimes>\<^sub>F y"
proof (intro ballI)
  fix F x y assume T0[ty]:"F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
    right-distributive\<bar>(non empty-struct \<bar>doubleLoopStr)" "x be Element-of-struct F" "y be Element-of-struct F"

  have "(x \<otimes>\<^sub>F y) \<oplus>\<^sub>F (x \<otimes>\<^sub>F (\<ominus>\<^sub>F y)) = x \<otimes>\<^sub>F (y \<oplus>\<^sub>F \<ominus>\<^sub>F y)" using vectsp_1_def_2E[of F] by mty auto
  also have "\<dots>=x \<otimes>\<^sub>F 0\<^sub>F " using rlvect_1_def_10 by auto
  also have "\<dots>= 0\<^sub>F " using vectsp_1_th_6[of F] by auto
  finally show "x \<otimes>\<^sub>F (\<ominus>\<^sub>F y) = \<ominus>\<^sub>F x \<otimes>\<^sub>F y" using
          rlvect_1_def_10[THEN conjunct2,THEN conjunct2,rule_format,of F "x \<otimes>\<^sub>F y" "x \<otimes>\<^sub>F (\<ominus>\<^sub>F y)"] by mty auto
qed auto

theorem vectsp_1_th_9[THEN bspec,THEN bspec,THEN bspec,rule_format]:
  "for F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
  left-distributive\<bar>(non empty-struct \<bar>doubleLoopStr), x,y be Element-of-struct F holds
  (\<ominus>\<^sub>F x) \<otimes>\<^sub>F y = \<ominus>\<^sub>F x \<otimes>\<^sub>F y"
proof (intro ballI)
  fix F x y assume T0[ty]:"F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
    left-distributive\<bar>(non empty-struct \<bar>doubleLoopStr)" "x be Element-of-struct F" "y be Element-of-struct F"
  have "(x \<otimes>\<^sub>F y) \<oplus>\<^sub>F ((\<ominus>\<^sub>F x) \<otimes>\<^sub>F y) =  (x \<oplus>\<^sub>F \<ominus>\<^sub>F x) \<otimes>\<^sub>F y" using vectsp_1_def_3E[of F]  by mty auto
  also have "\<dots>= 0\<^sub>F \<otimes>\<^sub>F y" using rlvect_1_def_10 by auto
  also have "\<dots>= 0\<^sub>F " using vectsp_1_th_7 T0 by auto
  finally show "(\<ominus>\<^sub>F x) \<otimes>\<^sub>F y = \<ominus>\<^sub>F x \<otimes>\<^sub>F y"
      using rlvect_1_def_10[THEN conjunct2,THEN conjunct2,rule_format,of F "x \<otimes>\<^sub>F y" "(\<ominus>\<^sub>F x) \<otimes>\<^sub>F y"] by mty auto
qed auto

theorem vectsp_1_th_10[THEN bspec,THEN bspec,THEN bspec,rule_format]:
  "for F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
  distributive\<bar>(non empty-struct \<bar>doubleLoopStr), x,y be Element-of-struct F holds
  (\<ominus>\<^sub>F x) \<otimes>\<^sub>F (\<ominus>\<^sub>F y) =  x \<otimes>\<^sub>F y"
proof (intro ballI)
  fix F x y assume T0[ty]:"F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
    distributive\<bar>(non empty-struct \<bar>doubleLoopStr)" "x be Element-of-struct F" "y be Element-of-struct F"
  have "(\<ominus>\<^sub>F x) \<otimes>\<^sub>F (\<ominus>\<^sub>F y) = \<ominus>\<^sub>F x \<otimes>\<^sub>F (\<ominus>\<^sub>F y)" using vectsp_1_th_9[of F] by mty auto
  also have "\<dots> =   \<ominus>\<^sub>F \<ominus>\<^sub>F x \<otimes>\<^sub>F y" using vectsp_1_th_8[of F] vectsp_1_cl_20 by auto
  also have "\<dots> = x \<otimes>\<^sub>F y" using rlvect_1_th_17 by mty auto
  finally show "(\<ominus>\<^sub>F x) \<otimes>\<^sub>F (\<ominus>\<^sub>F y) =  x \<otimes>\<^sub>F y" by auto
qed auto

theorem vectsp_1_th_11[THEN bspec,THEN bspec,THEN bspec,THEN bspec,rule_format]:
  "for F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
            right-distributive\<bar>(non empty-struct \<bar>doubleLoopStr),
        x,y,z be Element-of-struct F holds
   x \<otimes>\<^sub>F (y \<ominus>\<^sub>F z) = x \<otimes>\<^sub>F y \<ominus>\<^sub>F x \<otimes>\<^sub>F z"
proof(intro ballI)
  fix F x y z
  assume T0[ty]:"F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar> right-distributive\<bar>(non empty-struct \<bar>doubleLoopStr)"
            "x be Element-of-struct F"
            "y be Element-of-struct F"
            "z be Element-of-struct F"
  have "x \<otimes>\<^sub>F (y \<ominus>\<^sub>F z) = x \<otimes>\<^sub>F y \<oplus>\<^sub>F x \<otimes>\<^sub>F (\<ominus>\<^sub>F z)" using vectsp_1_def_2E algstr_0_def_14 by mty auto
  also have "\<dots> = x \<otimes>\<^sub>F y \<ominus>\<^sub>F x \<otimes>\<^sub>F z" using vectsp_1_th_8 algstr_0_def_14 by mty auto
  finally show " x \<otimes>\<^sub>F (y \<ominus>\<^sub>F z) = x \<otimes>\<^sub>F y \<ominus>\<^sub>F x \<otimes>\<^sub>F z" by auto
qed auto

text_raw {*\DefineSnippet{vectsp1th12}{*}
theorem vectsp_1_th_12[THEN bspec,THEN bspec,THEN bspec,rule_format]:
  "for F being add-associative \<bar> right-zeroed \<bar>
         right-complementable \<bar> associative \<bar> commutative \<bar>
         well-unital \<bar> almost-left-invertible \<bar>
         distributive \<bar> (non empty-struct \<bar> doubleLoopStr),
       x,y being Element-of-struct F holds
    x \<otimes>\<^sub>F y = 0\<^sub>F \<longleftrightarrow> x = 0\<^sub>F \<or> y = 0\<^sub>F"
text_raw {*}%EndSnippet*}
proof(intro ballI)
  fix F x y
  assume T[ty]:"F be add-associative \<bar> right-zeroed \<bar>
          right-complementable \<bar> associative \<bar> commutative \<bar>
          well-unital \<bar> almost-left-invertible \<bar>
          distributive \<bar> (non empty-struct \<bar> doubleLoopStr)"
         "x be Element-of-struct F"
         "y be Element-of-struct F"
  have "x \<otimes>\<^sub>F y = 0\<^sub>F \<longrightarrow> x = 0\<^sub>F \<or> y = 0\<^sub>F"
    proof(rule impI,rule disjCI2)
      assume A1:"x \<otimes>\<^sub>F y = 0\<^sub>F"
      assume A2:"x \<noteq> 0\<^sub>F"
      have "x\<hungarumlaut>\<^sup>F \<otimes>\<^sub>F 0\<^sub>F = x\<hungarumlaut>\<^sup>F \<otimes>\<^sub>F x \<otimes>\<^sub>F y" using A1 group_1_def_3E by mty auto
      also have "\<dots> = 1\<^sub>F \<otimes>\<^sub>F y" using A2 vectsp_1_def_10 by auto
      also have "\<dots> = y" using vectsp_1_reduce_2 by auto
      finally show "y = 0\<^sub>F" using vectsp_1_reduce_3 by mty auto
    qed
  thus "x \<otimes>\<^sub>F y = 0\<^sub>F \<longleftrightarrow> x = 0\<^sub>F \<or> y = 0\<^sub>F" using
    vectsp_1_reduce_4 vectsp_1_reduce_3 by mauto
qed auto


text_raw {*\DefineSnippet{vectsp1th12_ex}{*}
reserve F for Field
reserve x,y for "Element-of-struct F"
mtheorem "x \<otimes>\<^sub>F y = 0\<^sub>F \<longleftrightarrow> x = 0\<^sub>F \<or> y = 0\<^sub>F"
text_raw {*}%EndSnippet*}
proof-
  have "x \<otimes>\<^sub>F y = 0\<^sub>F \<longrightarrow> x = 0\<^sub>F \<or> y = 0\<^sub>F"
    proof(rule impI,rule disjCI2)
      assume A1:"x \<otimes>\<^sub>F y = 0\<^sub>F"
      assume A2:"x \<noteq> 0\<^sub>F"
      have "x\<hungarumlaut>\<^sup>F \<otimes>\<^sub>F 0\<^sub>F = x\<hungarumlaut>\<^sup>F \<otimes>\<^sub>F x \<otimes>\<^sub>F y"
            using A1 group_1_def_3E by mty auto
        also have "\<dots> = 1\<^sub>F \<otimes>\<^sub>F y" using A2 vectsp_1_def_10 by auto
        also have "\<dots> = y" using vectsp_1_reduce_2 by auto
       finally show "y = 0\<^sub>F" using vectsp_1_reduce_3 by mty auto
    qed
  thus "x \<otimes>\<^sub>F y = 0\<^sub>F \<longleftrightarrow> x = 0\<^sub>F \<or> y = 0\<^sub>F" using
    vectsp_1_reduce_4 vectsp_1_reduce_3 by mauto
qed


theorem vectsp_1_th_13[rule_format]:
  "for F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar>
  left-distributive\<bar>(non empty-struct \<bar>doubleLoopStr), x,y,z be Element-of-struct F holds
   (y \<ominus>\<^sub>F z) \<otimes>\<^sub>F x = y \<otimes>\<^sub>F x \<ominus>\<^sub>F z \<otimes>\<^sub>F x"
proof(intro ballI)
  fix F x y z
  assume T0[ty]:"F be add-associative\<bar>right-zeroed \<bar>right-complementable\<bar> left-distributive\<bar>(non empty-struct \<bar>doubleLoopStr)"
            "x be Element-of-struct F"
            "y be Element-of-struct F"
            "z be Element-of-struct F"
  have "(y \<ominus>\<^sub>F z) \<otimes>\<^sub>F x = y \<otimes>\<^sub>F x \<oplus>\<^sub>F (\<ominus>\<^sub>F z) \<otimes>\<^sub>F x" using vectsp_1_def_3E algstr_0_def_14 by mty auto
  also have "\<dots> = y \<otimes>\<^sub>F x \<ominus>\<^sub>F z \<otimes>\<^sub>F x" using vectsp_1_th_9 algstr_0_def_14 by mty auto
  finally show "(y \<ominus>\<^sub>F z) \<otimes>\<^sub>F x = y \<otimes>\<^sub>F x \<ominus>\<^sub>F z \<otimes>\<^sub>F x" by auto
qed auto

abbreviation ModuleStr_fields_prefix ("ModuleStr'_fields _" [110] 110) where
 "ModuleStr_fields F \<equiv>(#carrier \<rightarrow> set';  addF\<rightarrow> BinOp-of' the' carrier; ZeroF \<rightarrow> Element-of' the' carrier;
               lmult \<rightarrow>  Function-of' [: the carrier of F,the' carrier ':], the' carrier #)"


mdefinition ModuleStr_over ("ModuleStr-over _") where
  mlet "F be 1-sorted"
  "struct ModuleStr-over F ModuleStr_fields F"
:well_defined_property[of _ _ "{carrier}\<union>{addF}\<union>{ZeroF}\<union>{lmult}"]
  by (auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)
 (* :struct_well_defined
proof(rule Fields_add_argM1[OF addLoopStr_d(5)],simp add:string,simp add:string)
    fix X1 assume [ty]:"X1 be addLoopStr_fields\<bar>Struct"
    hence [ty]: "the carrier of X1 be set" "the carrier of F be set" using field by mty auto
    have "[: the carrier of F, the carrier of X1:] be set" by mty auto
    thus "inhabited(Function-of [: the carrier of F, the carrier of X1:], the carrier of X1)" by auto
  qed*)

theorem ModuleStr_over_inheritance[ty_parent]:
  "F be 1-sorted \<Longrightarrow> X be ModuleStr-over F \<Longrightarrow> X be addLoopStr" using ModuleStr_over(1) addLoopStrA by simp

end
