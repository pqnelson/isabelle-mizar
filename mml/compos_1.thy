\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory compos_1
  imports compos_0 "../mizar/mizar_struct" "../mizar/mizar_string"
   funct_2
begin



mdefinition COM_Struct :: "Ty"  ("COM-Struct") where
  "struct COM-Struct (# InstructionsF \<rightarrow> (\<lambda>_ . Instructions) #)"
  :well_defined_property[of _ _ "{InstructionsF}"]
  by (auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

lemmas COM_StructA = COM_Struct(1)
lemmas [ex] = COM_Struct(2,3)
lemmas COM_StructD = COM_Struct(4)

lemmas [ty_func] = COM_Struct(5)[rule_format]
lemma [ty_func]:"S be COM-Struct \<Longrightarrow> the InstructionsF of S be Instructions" using field COM_StructA by auto
lemma [ty_parent]:"S be COM-Struct \<Longrightarrow> S be Struct" using COM_StructA by auto


abbreviation compos_1_mode_1 ("Instruction-of _") where
  "Instruction-of S \<equiv> Element-of the InstructionsF of S"

func compos_1_def_10 ("halt \<^sub>_") where
  mlet "S be COM-Struct"
  "func halt \<^sub>S \<rightarrow> Instruction-of S equals
     halt the InstructionsF of S"
proof-
  have "the InstructionsF of S be Instructions" by mty auto
  have "halt the InstructionsF of S in the InstructionsF of S" using compos_0_def_10E
   compos_0_def_11 by mauto
  thus "halt the InstructionsF of S be Instruction-of S" using Element_of_rule by mauto
qed

abbreviation Instruction_Sequence ("Instruction-Sequence-of _") where
  "Instruction-Sequence-of S \<equiv> (the InstructionsF of S) -valued \<bar> ManySortedSet-of NAT"

definition compos_1_def_12 ("_ _:halts'_at _") where
  "let S be COM-Struct \<and>
       p be NAT-defined \<bar>(the InstructionsF of S)-valued\<bar>Function \<and>
       l be set
   pred p S:halts_at l means
     l in dom p \<and> p. l = halt \<^sub>S"

theorem compos_1_def_13:
  "let S be COM-Struct \<and>
       s be Instruction-Sequence-of S \<and>
       l be Nat
  redefine pred s S:halts_at l means
    s. l = halt \<^sub>S"
proof-
  assume A1[ty]: "S be COM-Struct \<and> s be the' InstructionsF(S) -valued \<bar>  ManySortedSet-of NAT \<and> l be Nat"
  have "dom s=NAT" "l in NAT" using partfun_1_def_2E ordinal1_def_12E by mauto
  thus "s S:halts_at l \<longleftrightarrow> s . l = halt \<^sub>S" using A1 compos_1_def_12_def[of S s l] by auto
qed

end

