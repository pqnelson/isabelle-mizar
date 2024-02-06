theory mizar_FOL 
  imports FOL "~~/src/HOL/Eisbach/Eisbach_Old_Appl_Syntax"
begin

text_raw \<open>\DefineSnippet{mizar-typedecl}{\<close>
typedecl Set
typedecl Ty
text_raw \<open>}%EndSnippet\<close>
instance Set :: "term" ..
instance Ty :: "term" ..

no_notation
  IFOL.eq (infixl "=" 50) and
  IFOL.not_equal (infixl "~=" 50) and
  IFOL.not_equal (infixl "\<noteq>" 50) and
  IFOL.disj (infixr "|" 30)

abbreviation mizeq :: "Set \<Rightarrow> Set \<Rightarrow> o" (infixl "=" 50)
  where "mizeq \<equiv> IFOL.eq"

abbreviation not_eq :: "Set \<Rightarrow> Set \<Rightarrow> o" (infix "<>" 50) where
  "a <> b \<equiv> \<not> IFOL.eq(a,b)"
notation not_eq (infixl "\<noteq>" 50)

abbreviation tyeq :: "Ty \<Rightarrow> Ty \<Rightarrow> o" (infixl "=\<^sub>T" 50)
  where "tyeq \<equiv> IFOL.eq"

notation (ASCII)
  imp (infixl "implies" 25) and
  iff (infixl "iff" 25) and
  disj (infixl "or" 30) and
  Not ("not _" [40] 40)

ML \<open>
val basic_ss = FOL_basic_ss;
val main_ss = FOL_ss;
val mk_Trueprop = \<^make_judgment>;
val dest_Trueprop = \<^dest_judgment>;
val eq_const = @{const_name IFOL.eq}
\<close>

lemmas Eq_TrueI = iff_reflection_T
lemmas Eq_FalseI = iff_reflection_F

end
