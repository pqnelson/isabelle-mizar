\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory memstr_0
  imports struct_0 ordinal1
begin

abbreviation MemStruct_fields_prefix ("Mem-Struct'_fields _")
  where "Mem-Struct_fields N \<equiv> (#
   carrier \<rightarrow> (\<lambda>S. set);
   ZeroF \<rightarrow> (\<lambda>S. Element-of the carrier of S) ;
   Object-Kind \<rightarrow> (\<lambda>S. Function-of the carrier of S, N) ;
   ValuesF \<rightarrow>  (\<lambda>S. ManySortedSet-of N) #)"

text_raw \<open>\DefineSnippet{MemStruct}{\<close>
mdefinition MemStruct_over ("Mem-Struct-over _") where
  assumes "N be set"
"struct Mem-Struct-over N (#
   carrier \<rightarrow> (\<lambda>S. set);
   ZeroF \<rightarrow> (\<lambda>S. Element-of the carrier of S);
   Object-Kind \<rightarrow> (\<lambda>S. Function-of the carrier of S, N);
   ValuesF \<rightarrow> (\<lambda>S. ManySortedSet-of N)
#)" : well_defined_property[of _ _ "{carrier}\<union>{ZeroF}\<union>{Object-Kind}\<union>{ValuesF}"]
text_raw \<open>}%EndSnippet\<close>
  by (auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

lemmas MemStruct_overA = MemStruct_over(1)
lemmas [ex] = MemStruct_over(2,3)
lemmas MemStruct_overD = MemStruct_over(4)
lemmas MemStruct_overR = MemStruct_over(5)

theorem MemStruct_over_inheritance[ty_parent]:
  "N be set \<Longrightarrow> X be Mem-Struct-over N \<Longrightarrow> X be ZeroStr" using MemStruct_overA ZeroStrA by mauto

theorem MemStruct_over_inheritance1[ty_func]:
  "N be set \<Longrightarrow> S be Mem-Struct-over N \<Longrightarrow> the Object-Kind of S be Function-of the carrier of S, N"
   using field MemStruct_overA by mauto

theorem MemStruct_over_inheritance2[ty_func]:
  "N be set \<Longrightarrow> S be Mem-Struct-over N \<Longrightarrow> the ValuesF of S be ManySortedSet-of N"
   using field MemStruct_overA by mauto


abbreviation(input) Instruction_Counter_prefix ("IC \<^sub>_")
  where "IC \<^sub>S \<equiv> 0\<^sub>S"

abbreviation (input) Data_Locations_prefix ("Data-Locations \<^sub>_")
  where " Data-Locations \<^sub>S \<equiv>NonZero \<^sub>S"

func memstr_0_def_2 ( "the'_Values'_of _ " 190) where
mlet "N be with_zero\<bar>set","S be Mem-Struct-over N"
  "func the_Values_of S \<rightarrow> ManySortedSet-of the carrier of S equals
     the ValuesF of S \<circ> the Object-Kind of S"
proof-
  have "{} in N" using ordinal1_def_16E by auto
  hence N: "N \<noteq> {}" using xb by auto
  let ?V = "the ValuesF of S"
  let ?O = "the Object-Kind of S"
  have A2: "dom ?O = the carrier of S" using funct_2_def_1E N by mauto
  have "?O is N-valued" using relset_1_cl_2 by mty auto
  hence A1: "rng ?O c= N" using relat_1_def_19E by mauto
  have "dom ?V=N" using partfun_1_def_2E by mauto
  hence "dom (?O*?V) = the carrier of S" using A2 funct_2_lm_1[of ?O ?V] A1 by auto
  thus "(?V *` ?O ) is the' carrier(S) : total \<bar> the' carrier(S)-defined \<bar> (Function_like \<bar> (Relation_like \<bar> set))" using
     pboole_def_1_th_1[of "the carrier of S" ] by auto
qed

text_raw \<open>\DefineSnippet{memstr_0_mode_1}{\<close>
abbreviation memstr_0_mode_1 ("PartState-of _" 190) where
  "PartState-of M \<equiv> the carrier of M-defined \<bar> the_Values_of M-compatible \<bar> Function"
text_raw \<open>}%EndSnippet\<close>




theorem memstr_0_cl[simplified, rule_format,ex]:
  "let M be with_zero\<bar>set \<and> S be Mem-Struct-over M
  cluster the carrier of S-defined \<bar> the_Values_of S-compatible for Function"
proof
  assume [ty]:"M be with_zero\<bar>set \<and> S be Mem-Struct-over M"
  have "dom {} is empty" by mauto
  hence D: "dom {}={}" using xboole_0_lm_1 by mauto
  hence "dom {} \<subseteq> the carrier of S" using tarski_def_3 xb by mauto
  hence [ty]:"{} is the carrier of S-defined" using relat_1_def_18 by mauto
  have [ty]:"{} is the_Values_of S-compatible"
  proof(standard,mauto)
    fix x assume "x in dom {}"
    thus "{} . x in (the_Values_of S). x" using D xb by auto
  qed
  show "{} is the carrier of S-defined \<bar> the_Values_of S-compatible \<bar> Function" by mauto
qed


attr memstr_0_def_3 ("_ :with'_non-empty'_values")
  "N be set \<Longrightarrow>
   attr N :with_non-empty_values for Mem-Struct-over N means (\<lambda>S. (the_Values_of S) is non-empty)"


theorem I: "inhabited(A\<bar>B\<bar>C) \<Longrightarrow> inhabited(A\<bar>(B\<bar>C))" unfolding inhabited_def by simp
theorem I1: "inhabited(D\<bar>(A\<bar>(B\<bar>C))) \<Longrightarrow> inhabited(D\<bar>((A\<bar>B)\<bar>C))" unfolding inhabited_def by simp
theorem I2: "inhabited(A\<bar>B) \<Longrightarrow> inhabited(A)" unfolding inhabited_def
proof-
  assume "\<exists>\<^sub>Lx. x is A \<bar> B"
  then obtain x where "x is A\<bar>B" by auto
  hence "x is A" by auto
  thus "\<exists>\<^sub>Lx. x is A" by auto
qed
theorem I3: "inhabited(A\<bar>B) \<Longrightarrow> inhabited(B)" unfolding inhabited_def
proof-
  assume "\<exists>\<^sub>Lx. x is A \<bar> B"
  then obtain x where "x is A\<bar>B" by auto
  hence "x is B" by auto
  thus "\<exists>\<^sub>Lx. x is B" by auto
qed



theorem memstr_0_cl_1[rule_format,ex]:
  "let N be with_zero\<bar>set \<and> S be N:with_non-empty_values \<bar> Mem-Struct-over N
   cluster (the carrier of S):total for PartState-of S"
proof-
  assume A1[ty]: "N be with_zero\<bar>set \<and> S be N:with_non-empty_values \<bar> Mem-Struct-over N"
  have [ty]: "the_Values_of S be non-empty\<bar> Function " using memstr_0_def_3E by mauto
 have "inhabited(
  (the' carrier(S) : total \<bar> the' carrier(S)-defined) \<bar> the_Values_of S -compatible \<bar> Function)"
   using funct_2_cl_comp[of "the carrier of S" "the_Values_of S"] by mty auto
 hence "inhabited(
  (the' carrier(S) : total \<bar> the' carrier(S)-defined) \<bar> (the_Values_of S -compatible \<bar> Function))"
    using I by auto
  hence "inhabited(
      the' carrier(S) : total \<bar> (the' carrier(S)-defined \<bar> (the_Values_of S -compatible \<bar> Function)))"
      using I by auto
  thus "inhabited(
      the' carrier(S) : total \<bar> (the' carrier(S)-defined \<bar> the_Values_of S -compatible \<bar> Function))"
      using I1 by auto
  qed



theorem memstr_0_cl_ex[simplified,rule_format,ex]:
  "let N be with_zero\<bar>set \<and> S be N:with_non-empty_values\<bar> Mem-Struct-over N
   cluster (the carrier of S):total \<bar> (the carrier of S)-defined \<bar> the_Values_of S-compatible for Function"
proof-
  assume [ty]:"N is with_zero \<bar> set \<and> S is N :with_non-empty_values \<bar> Mem-Struct-over N"
  hence "the_Values_of S is non-empty" using memstr_0_def_3E by mauto
  thus "inhabited((the carrier of S):total \<bar> (the carrier of S)-defined \<bar> the_Values_of S-compatible\<bar> Function)"
   using funct_2_cl_comp by mauto
qed


text_raw \<open>\DefineSnippet{memstr_0_mode_2}{\<close>
abbreviation memstr_0_mode_2 ("State-of _" 190)
  where "State-of M \<equiv>
         (the carrier of M):total \<bar> (the carrier of M)-defined \<bar> the_Values_of M-compatible \<bar> Function"
text_raw \<open>}%EndSnippet\<close>

abbreviation memstr_0_mode_3 ("Object-of _" 190)
where "Object-of S \<equiv> Element-of-struct S"

func memstr_0_def_4( "ObjectKind'( _ , _ ') _ " 190) where
  mlet "N be with_zero\<bar>set ", " S be non empty-struct \<bar> Mem-Struct-over N"," o be Object-of S"
  "func ObjectKind(N,S) o \<rightarrow> Element-of N equals
    (the Object-Kind of S).o "
proof-
  have "{} in N" using ordinal1_def_16E by auto
  hence N: "N \<noteq> {}" using xb by auto
  let ?O = "the Object-Kind of S"
  have A2: "dom ?O = the carrier of S" using funct_2_def_1E N by mauto
  have "?O is N-valued" using relset_1_cl_2 by auto
  hence A1: "rng ?O c= N" using relat_1_def_19E[of N ?O] by auto
  have "the carrier of S is non empty" using struct_0_def_1 by mauto
  hence "the carrier of S \<noteq>{}" using xboole_0_def_2d xboole_0_def_1 by mauto
  hence "o in dom ?O" using A2 Element_of_rule2 by mauto
 thus "(?O .o) be Element-of N" using A1 funct_1_def_3[of ?O] Element_of_rule by auto
qed

func memstr_0_def_5 ( "Values'( _ , _ ') _ " 190) where
  "func Values(N,S) o \<rightarrow> set equals
    (the_Values_of S).o"
proof-
  show "((the_Values_of S).o) be set" using all_set by auto
qed


theorem memstr_0_cl_2:
  "let N be with_zero\<bar>set \<and>
       S be non empty-struct \<bar> N:with_non-empty_values \<bar> Mem-Struct-over N \<and>
       o be Object-of S
   cluster Values(N,S) o \<rightarrow> non empty"
 proof-
   let ?VS = "the_Values_of S"
   assume A0[ty]: "N be with_zero\<bar>set \<and>
       S be non empty-struct \<bar> N:with_non-empty_values \<bar> Mem-Struct-over N \<and>
       o be Object-of S"
   hence Vo: "Values(N,S) o =  ?VS .o" using A0 memstr_0_def_5 by simp
   have VS: "?VS be ManySortedSet-of the carrier of S" by mty auto
   hence A2: "dom ?VS = the carrier of S" using partfun_1_def_2E by mauto
   have VS1:"?VS be Function" using VS by auto
   have "the carrier of S is non empty" by mauto
   hence "o in dom ?VS" using A2 A0 Element_of1 by auto
   hence H: "?VS. o in rng ?VS" using funct_1_def_3 by mauto
   have "?VS is non-empty" using memstr_0_def_3 A0 by mauto
   hence "?VS. o \<noteq> {}" using H funct_1_def_9 by mauto
   thus "Values(N,S) o is non empty" using Vo xboole_0_lm_1 all_set by auto
 qed


func memstr_0_def_8 ( "DataPart \<^sub>_ _ " 190) where
  mlet "N be with_zero\<bar>set","S be Mem-Struct-over N","p be PartState-of S"
  "func DataPart \<^sub>S p \<rightarrow> PartState-of S equals
    p | Data-Locations \<^sub>S"
proof
  let ?D="Data-Locations \<^sub>S"
  let ?pD ="p | ?D"
  let ?V = "the_Values_of S"
 (* have W1: "?pD be Function_like" by auto *)
  have W: "dom p c= the carrier of S" using relat_1_def_18E by simp
  hence S: "dom ?pD = proj1 p \<inter> NonZero \<^sub>S" using relat_1_th_55[of ?D p] by mauto
  have "dom ?pD c= the carrier of S"
  proof(rule tarski_def_3b)
    fix x assume "x in dom ?pD"
    hence "x in proj1 p" using S xboole_0_def_4 by mauto
    thus "x in the carrier of S" using tarski_def_3a[OF _ _ W] by mty auto
  qed mauto
  hence W2: "?pD is the carrier of S -defined" using relat_1_def_18I[of "the carrier of S" ?pD] by mty auto
  have W3: "?pD is ?V -compatible"
  proof(standard,mauto)
   fix x assume A1: "x in dom ?pD"
    hence A2: "?pD. x = p .x" using funct_1_th_47 by auto
    have "x in dom p" using A1 relat_1_th_51 by auto
    hence "p. x in ?V.x" using funct_1_def_14E by auto
    thus "?pD. x in ?V. x" using A2 by auto
  qed
  thus "p | (NonZero \<^sub>S) is the' carrier(S)-defined \<bar> the_Values_of S -compatible" using W2 by mauto
qed mauto

attr memstr_0_def_9 ("_ :data-only")
  "N be with_zero\<bar>set \<Longrightarrow> S be Mem-Struct-over N
        \<Longrightarrow> attr S :data-only for PartState-of S means (\<lambda>p. dom p misses {IC \<^sub>S})"


(*  theorem funct_2_cl_com:
  "let I be set \<and> f be non-empty\<bar>I:total \<bar>I-defined\<bar>Function
   cluster I:total \<bar>I-defined\<bar> f-compatible for Function" using ex by auto
*)

mtheorem memstr_0_th_3[rule_format]:
  "for N be with_zero\<bar>set holds
      for S be Mem-Struct-over N holds
         for p be PartState-of S holds
           \<not> IC \<^sub>S in dom DataPart \<^sub>S p"
proof(intro ballI)
  fix N S p
  assume T0[ty]: "N be with_zero\<bar>set"
         "S be Mem-Struct-over N"
  show "inhabited(the carrier of S-defined \<bar> the_Values_of S -compatible \<bar> Function)" using
     memstr_0_cl by mauto
assume [ty]:"p be PartState-of S"
    show "not IC \<^sub>S in dom DataPart \<^sub>S p"
  proof
    have "S be ZeroStr" using T0 MemStruct_over_inheritance by auto
    hence A1: "NonZero \<^sub>S = ([#]S) \\ {0\<^sub>S}" using struct_0_def_17 by simp
    assume "IC \<^sub>S in dom DataPart \<^sub>S p"
    hence "IC \<^sub>S in dom (p | Data-Locations \<^sub>S)" using memstr_0_def_8 by mauto
    hence "0\<^sub>S in NonZero \<^sub>S" using relat_1_th_51 by mauto
    thus "False" using tarski_def_1 xboole_0_def_5 A1 by mauto
  qed
qed mauto

theorem memstr_0_th_4[rule_format]:
  "for N be with_zero\<bar>set holds
      for S be Mem-Struct-over N holds
         for p be PartState-of S holds
            {IC \<^sub>S}  misses dom DataPart \<^sub>S p"
proof(intro ballI)
  fix N S p
  assume T0[ty]: "N be with_zero\<bar>set"
         "S be Mem-Struct-over N"
  show "inhabited(the carrier of S-defined \<bar> the_Values_of S -compatible \<bar> Function)" using
     memstr_0_cl by mauto
  assume [ty]:"p be PartState-of S"
  have "{IC \<^sub>S}  meets dom DataPart \<^sub>S p \<longrightarrow> False"
  proof
    assume "{IC \<^sub>S}  meets dom DataPart \<^sub>S p"
    then obtain x where
      A1: "x be object" "x in {IC \<^sub>S}  \<and> x in dom DataPart \<^sub>S p" using xboole_0_th_3 all_set by auto
    hence "x = IC \<^sub>S" using tarski_def_1 by auto
    thus "False" using A1 memstr_0_th_3 T0 memstr_0_cl by mauto
  qed
  thus "{IC \<^sub>S}  misses dom DataPart \<^sub>S p" using xboole_0_antonym_meets all_set by auto
qed mauto

text_raw \<open>\DefineSnippet{memstr_0_th_6}{\<close>
theorem memstr_0_th_6:
  "for N be with_zero\<bar>set holds
      for S be Mem-Struct-over N holds
         for p be PartState-of S holds
    p is S:data-only \<longleftrightarrow> dom p c= Data-Locations \<^sub>S"
text_raw \<open>}%EndSnippet\<close>
proof(intro ballI,rule iffI3)
  fix N S p
  assume T0[ty]: "N be with_zero\<bar>set"
         "S be Mem-Struct-over N"
  show "inhabited(the carrier of S-defined \<bar> the_Values_of S -compatible \<bar> Function)" using
     memstr_0_cl by mauto
  assume [ty]:"p be PartState-of S"
   have T1: "S be ZeroStr" using T0 MemStruct_over_inheritance by auto
  hence A2: "Data-Locations \<^sub>S = ([#]S) \\ {IC \<^sub>S}" using struct_0_def_17 T0 by simp
  show "p is S:data-only \<longrightarrow> dom p c= Data-Locations \<^sub>S"
  proof(rule impI,rule tarski_def_3b)
    fix x
    assume A1: "p is S:data-only" "x in dom p"
    hence "dom p misses {IC \<^sub>S}" using memstr_0_def_9 by mauto
    hence "(dom p \<inter> {IC \<^sub>S}) is empty " using xboole_0_def_7 xboole_0_def_2 by mauto
    hence A3: "not x in {IC \<^sub>S}" using A1(2) xboole_0_def_1 xboole_0_def_4 by mauto
    have "dom p \<subseteq> the carrier of S" using relat_1_def_18 by mauto
    hence "x in [#]S" using T0 A1(2) struct_0_def_3 tarski_def_3 by mauto
    thus "x in Data-Locations \<^sub>S" using A2 A3 xboole_0_def_5 by mauto
  qed mauto
  assume A3: "dom p c= Data-Locations \<^sub>S"
   have "dom p meets {IC \<^sub>S}  \<longrightarrow> False"
  proof
    assume "dom p meets {IC \<^sub>S}"
    then obtain x where
      A1: "x be object" "x in dom p \<and> x in {IC \<^sub>S}" using xboole_0_th_3 all_set by auto
    hence "x in Data-Locations \<^sub>S" using tarski_def_3a[OF _ _ A3] by mauto
    thus "False" using A1 A2 xboole_0_def_5 by mauto
  qed
  hence "dom p misses {IC \<^sub>S}" using xboole_0_antonym_meets all_set by auto
  thus "p is S:data-only" using memstr_0_def_9 T0 by mauto
qed mauto

end