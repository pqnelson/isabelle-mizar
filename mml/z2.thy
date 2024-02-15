\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory z2
  imports algstr_0
begin

definition A: "Zero \<equiv> {}"
definition B: "One \<equiv> {Zero}"

lemma [simp]: "Zero \<noteq> One" using tarski_def_1[of One Zero] prefix_in_irreflexive all_set B A by auto
lemma [simp]: "[Zero,Zero]\<noteq>[Zero,One]" "[Zero,Zero]\<noteq>[One,Zero]" "[Zero,Zero]\<noteq>[One,One]"
      "[Zero,One]\<noteq>[One,Zero]" "[Zero,One]\<noteq>[One,One]" "[One,Zero]\<noteq>[One,One]"
  using xtuple_0_th_1[of Zero Zero Zero One] xtuple_0_th_1[of Zero Zero One Zero] xtuple_0_th_1[of Zero Zero One One]
        xtuple_0_th_1[of Zero One One Zero] xtuple_0_th_1[of Zero One One One] xtuple_0_th_1[of One Zero One One]by simp+

theorem DomZ2: "{[Zero,Zero]}\<union>{[Zero,One]}\<union>{[One,Zero]}\<union>{[One,One]} = [:{Zero,One},{Zero,One}:]"
  proof(unfold xboole_0_def_10[OF all_set all_set],rule conjI)
    show "{[Zero,Zero]}\<union>{[Zero,One]}\<union>{[One,Zero]}\<union>{[One,One]} \<subseteq> [:{Zero,One},{Zero,One}:]"
    proof(intro tarski_def_3b)
      fix xy assume A: "xy in {[Zero,Zero]}\<union>{[Zero,One]}\<union>{[One,Zero]}\<union>{[One,One]}"
      hence A:"xy=[Zero,Zero] \<or> xy=[Zero,One] \<or> xy = [One,Zero] \<or> xy=[One,One]" using xboole_0_def_3 tarski_def_1 by mauto
      have B: "Zero in {Zero,One} \<and> One in {Zero,One}" using tarski_def_2 by auto
      thus "xy in [:{Zero,One},{Zero,One}:]" using xboole_0_def_3 A zfmisc_1_def_2 by mty auto
   qed mauto
    show "[:{Zero,One},{Zero,One}:] \<subseteq> {[Zero,Zero]}\<union>{[Zero,One]}\<union>{[One,Zero]}\<union>{[One,One]} "
    proof (intro tarski_def_3b)
      fix xy assume "xy in [:{Zero,One},{Zero,One}:]"
      then obtain x y where
        A1: "xy=[x,y]" "x in {Zero,One} \<and> y in {Zero,One}" using zfmisc_1_def_2 by mty auto
      thus "xy in {[Zero,Zero]}\<union>{[Zero,One]}\<union>{[One,Zero]}\<union>{[One,One]}" using tarski_def_1 tarski_def_2 xboole_0_def_3 by mty auto
    qed mauto
  qed

theorem Rng_1:
  "rng {[s,D]}={D}"
proof-
  have "{[s,D]} be Relation" using relat_1_cl_7 by mauto
  thus ?thesis using relat_1_th_3[of D s "{[s,D]}"] by auto
qed

theorem Rng_2:
  "rng ({[s1,D1]} \<union> {[s2,D2]}) = {D1}\<union>{D2}"
proof-
  have A1:"{[s1,D1]} be Relation \<and> {[s2,D2]} be Relation" using relat_1_cl_7 by mauto
  have "({[s1,D1]} \<union> {[s2,D2]}) be Relation" using relat_1_cl_5 A1 by mauto
  hence "rng ({[s1,D1]} \<union> {[s2,D2]}) = (rng {[s1,D1]}) \<union> (rng {[s2,D2]})" using xtuple_th_24 relat_1_def_1E by mauto
  thus ?thesis using Rng_1 by auto
qed

theorem Rng_3:
  "rng ({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) = {D1}\<union>{D2}\<union>{D3}"
proof-
(*  have A2:"{[s1,D1]} be Relation \<and> {[s2,D2]} be Relation" using relat_1_cl_7 by mauto
    have A3: "({[s1,D1]} \<union> {[s2,D2]}) be Relation \<and>  {[s3,D3]} be Relation" using relat_1_cl_7 relat_1_cl_5 A2 by mauto
  have A4: "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) be Relation" using relat_1_cl_7 relat_1_cl_5 A3 by mauto
  hence "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) be Relation"
    using relat_1_cl_5[of "{[s1,D1]} \<union> {[s2,D2]}" "{[s3,D3]}"] by simp*)
  have "rng ({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) = (rng ({[s1,D1]}\<union>{[s2,D2]})) \<union> (rng {[s3,D3]})"
    using xtuple_th_24 by mty auto
  thus ?thesis using Rng_1 Rng_2 by auto
qed

theorem Rng_4:
  "rng ({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}) = {D1}\<union>{D2}\<union>{D3}\<union>{D4}"
proof-
(*  have A2:"{[s1,D1]} be Relation \<and> {[s2,D2]} be Relation" using relat_1_cl_7 by mauto
  have A3: "({[s1,D1]} \<union> {[s2,D2]}) be Relation \<and>  {[s3,D3]} be Relation" using relat_1_cl_7 relat_1_cl_5 A2 by mauto
   have A4: "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}) be Relation \<and>  {[s4,D4]} be Relation " using relat_1_cl_7 relat_1_cl_5 A3 by mauto
  have A5: "({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}) be Relation " using relat_1_cl_7 relat_1_cl_5 A4 by mauto*)
  have "rng ({[s1,D1]} \<union> {[s2,D2]}\<union>{[s3,D3]}\<union>{[s4,D4]}) = (rng ({[s1,D1]}\<union>{[s2,D2]}\<union>{[s3,D3]})) \<union> (rng {[s4,D4]})"
    using xtuple_th_24 relat_1_def_1I by mty auto
  thus ?thesis using Rng_1 Rng_3 by auto
qed

definition addZ2 ("addZ2") where
  "addZ2 \<equiv>
     {[[Zero,Zero],Zero]}\<union>{[[Zero,One],One]}\<union>{[[One,Zero],One]}\<union>{[[One,One],Zero]}"

theorem addZ2[ty_func]: "addZ2 be BinOp-of {Zero,One}"
proof -
  have T1:"addZ2 be Function" unfolding addZ2_def using Struct_4[of "[Zero,Zero]" ] Struct_def sel_t_def aggr_def by auto
  have T2:"dom addZ2 = [:{Zero,One},{Zero,One}:]" unfolding addZ2_def using DomZ2 Dom_4 sel_t_def aggr_def by auto
  have "rng addZ2 = {Zero}\<union>{One}\<union>{One}\<union>{Zero}" unfolding addZ2_def using Rng_4 by auto
  hence "rng addZ2 = {Zero,One}" using xboole_0_def_3 tarski_def_1 tarski_def_2 by (intro tarski_0_2a) mauto
  thus "addZ2 be BinOp-of {Zero,One}" using funct_2_th_2[OF T1] T2 by auto
qed

definition multZ2 ("multZ2") where
  "multZ2 \<equiv>
     {[[Zero,Zero],Zero]}\<union>{[[Zero,One],Zero]}\<union>{[[One,Zero],Zero]}\<union>{[[One,One],One]}"

theorem multZ2[ty_func]: "multZ2 be BinOp-of {Zero,One}"
proof -
  have T1:"multZ2 be Function" unfolding multZ2_def using Struct_4[of "[Zero,Zero]" ] Struct_def aggr_def sel_t_def by auto
  have T2:"dom multZ2 = [:{Zero,One},{Zero,One}:]"  unfolding multZ2_def using DomZ2 Dom_4 aggr_def sel_t_def by auto
  have "rng multZ2 = {Zero,One}"  unfolding multZ2_def using Rng_4 xboole_0_def_3 tarski_def_1 tarski_def_2 by (intro tarski_0_2a,simp_all) mauto
  thus "multZ2 be BinOp-of {Zero,One}" using funct_2_th_2[OF T1] T2 by simp
qed

abbreviation Z ("Z") where
  "Z \<equiv>
     [#carrier\<mapsto>{Zero,One} ; addF\<mapsto> addZ2;ZeroF\<mapsto>Zero;multF\<mapsto>multZ2;OneF\<mapsto>One#]"

theorem [ty_func]:"Z be doubleLoopStr"
proof -
  have [ty]: "Zero be Element-of {Zero,One}" "One be Element-of {Zero,One}" using Element_of_rule3 tarski_def_2 by mauto
  thus T1: "Z be doubleLoopStr" by mauto
qed

theorem Z2d:
  shows "Zero be Element-of-struct Z"
        "One be Element-of-struct Z"
        "x be Element-of-struct Z \<Longrightarrow> x = One \<or> x = Zero"
        "0\<^sub>Z = Zero" "1\<^sub>Z = One"
        "Zero\<oplus>\<^sub>Z Zero = Zero" "Zero\<oplus>\<^sub>Z One = One" "One\<oplus>\<^sub>Z Zero = One" "One\<oplus>\<^sub>Z One = Zero"
        "Zero\<otimes>\<^sub>Z Zero = Zero" "Zero\<otimes>\<^sub>Z One = Zero" "One\<otimes>\<^sub>Z Zero = Zero" "One\<otimes>\<^sub>Z One = One"
        "the carrier of Z={Zero,One}"
proof-
  have [ty]:"Z be doubleLoopStr" by mauto
  have T0: "Z be doubleLoopStr" "Z be Struct" "Z be 1-sorted" "Z be ZeroStr" "Z be OneStr" "Z be addMagma" "Z be multMagma"
        by auto
  have T1: "the carrier of Z={Zero,One}" "the ZeroF of Z=Zero" "the OneF of Z=One" "the multF of Z=multZ2" "the addF of Z=addZ2" using
     the_selector_of_1[of Z carrier "{Zero,One}"] the_selector_of_1[of Z ZeroF Zero]
     the_selector_of_1[of Z OneF One] the_selector_of_1[of Z multF multZ2]
     the_selector_of_1[of Z addF addZ2] Aggr by auto
  thus T2[ty]: "Zero be Element-of-struct Z" "One be Element-of-struct Z"
    using Element(6) tarski_def_2 by mty auto (* CK: slow "mty" *)
  have[ty]: "the carrier of Z is non empty" using T1(1) tarski_def_2 xboole_0_def_1 by auto
  show "x be Element-of-struct Z \<Longrightarrow> x = One \<or> x = Zero"
  proof-
    assume A1: "x be Element-of-struct Z"
    have "x in the carrier of Z" using A1 Element(7)[of "the carrier of Z" x] by auto
    thus ?thesis using T1(1) tarski_def_2 by auto
  qed
  show "0\<^sub>Z = Zero" "1\<^sub>Z = One" using struct_0_def_6 struct_0_def_7 T1(2-3) by auto
  have A0[ty]:"addZ2 be Function" using addZ2 by mty auto
  let ?A =" {[[Zero , Zero] , Zero]} \<union> {[[Zero , One] , One]} \<union> {[[One , Zero] , One]} \<union> {[[One , One] , Zero]}"
  have A1: "addZ2 = ?A" using addZ2 addZ2_def by simp
  have "[[Zero , Zero] , Zero] in ?A" using tarski_def_1 string by auto
  hence "[[Zero , Zero] , Zero] in addZ2" using A1 by auto+
  hence "addZ2. [Zero , Zero] = Zero" using funct_1_th_1[OF A0] by auto
  thus "Zero\<oplus>\<^sub>Z Zero = Zero" using algstr_0_def_1[of Z Zero Zero] binop_0_def_1[of addZ2] T1(5) by auto

  have "[[Zero , One] , One] in ?A" using tarski_def_1 string by auto
  hence "[[Zero , One] , One] in addZ2" using A1 by auto+
  hence "addZ2. [Zero , One] = One" using funct_1_th_1[OF A0] by auto
  thus "Zero\<oplus>\<^sub>Z One = One" using algstr_0_def_1[of Z Zero One] binop_0_def_1[of addZ2] T1(5) by auto
  have "[[One , Zero] , One] in ?A" using tarski_def_1 string by auto
  hence "[[One , Zero] , One] in addZ2" using A1 by auto+
  hence "addZ2. [One , Zero] = One" using funct_1_th_1[OF A0] by auto
  thus "One \<oplus>\<^sub>Z Zero = One" using algstr_0_def_1[of Z One Zero] binop_0_def_1[of addZ2] T1(5) by auto
  have "[[One , One] , Zero] in ?A" using tarski_def_1 string by auto
  hence "[[One , One] , Zero] in addZ2" using A1 by auto+
  hence "addZ2. [One , One] = Zero" using funct_1_th_1[OF A0] by auto
  thus "One \<oplus>\<^sub>Z One = Zero" using algstr_0_def_1[of Z One One] binop_0_def_1[of addZ2] T1(5) by auto
  have A0[ty]:"multZ2 be Function" using multZ2 by mty auto
  let ?M =" {[[Zero , Zero] , Zero]} \<union> {[[Zero , One] , Zero]} \<union> {[[One , Zero] , Zero]} \<union> {[[One , One] , One]}"
  have A1: "multZ2 = ?M" using multZ2 multZ2_def by simp
  have "[[Zero , Zero] , Zero] in ?M" using tarski_def_1 string by auto
  hence "[[Zero , Zero] , Zero] in multZ2" using A1 by auto+
  hence "multZ2. [Zero , Zero] = Zero" using funct_1_th_1[OF A0] by auto
  thus "Zero\<otimes>\<^sub>Z Zero = Zero" using algstr_0_def_18[of Z Zero Zero] binop_0_def_1[of multZ2] T1(4) by auto
  have "[[Zero , One] , Zero] in ?M" using tarski_def_1 string by auto
  hence "[[Zero , One] , Zero] in multZ2" using A1 by auto+
  hence "multZ2. [Zero , One] = Zero" using funct_1_th_1[OF A0] by auto
  thus "Zero\<otimes>\<^sub>Z One = Zero" using algstr_0_def_18[of Z Zero One] binop_0_def_1[of multZ2] T1(4) by auto
  have "[[One , Zero] , Zero] in ?M" using tarski_def_1 string by auto
  hence "[[One , Zero] , Zero] in multZ2" using A1 by auto+
  hence "multZ2. [One , Zero] = Zero" using funct_1_th_1[OF A0] by auto
  thus "One \<otimes>\<^sub>Z Zero = Zero" using algstr_0_def_18[of Z One Zero] binop_0_def_1[of multZ2] T1(4) by auto
  have "[[One , One] , One] in ?M" using tarski_def_1 string by auto
  hence "[[One , One] , One] in multZ2" using A1 by auto+
  hence "multZ2. [One , One] = One" using funct_1_th_1[OF A0] by auto
  thus "One \<otimes>\<^sub>Z One = One" using algstr_0_def_18[of Z One One] binop_0_def_1[of multZ2] T1(4) by auto
  show "the carrier of Z={Zero,One}" using T1(1) by auto
qed

end