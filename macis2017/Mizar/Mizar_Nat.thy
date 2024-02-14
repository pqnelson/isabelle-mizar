\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Mizar_Nat
  imports Mizar_string Mizar_Fraenkel "../MML/Subset_1" "../MML/Funct_1"
begin

abbreviation zero::"Set" ("0") where
  "0 \<equiv> {}"

axiomatization
  NAT 
where
  zero_nat: "0 in NAT"

definition natural_attr::Attr ("natural")
  where NAT_1[THEN defattr_property]: 
     "attr natural means (\<lambda>n. n be object & n in NAT)"

abbreviation
  "Nat \<equiv> natural\<parallel>object"

lemma NAT_non_empty: "NAT be non empty\<parallel>set"
proof-
  have "0 in NAT" " 0 be object" using zero_nat by auto
  thus "NAT be non empty\<parallel>set"  using xboole_0_def_1b[THEN iffD2] all_set by auto    
qed

lemma zero_is_nat: "0 is natural" using zero_nat using NAT_1 by simp     
lemma nat_1: "n be Element-of NAT \<Longrightarrow> n in NAT" using  NAT_non_empty NAT_1 by auto 
lemma nat_2: "n is natural \<Longrightarrow> n in NAT" using NAT_1 by auto
lemma nat_0: "0 be Element-of NAT" using zero_nat Element_of_rule by simp    

end