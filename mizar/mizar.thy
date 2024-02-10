\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory mizar
  imports mizar_FOL
begin

declare [[eta_contract = false]]

definition If ("((_) if (_) otherwise (_))" [10] 10)
where [simp]: "If (a, b, c) \<longleftrightarrow> ((b \<longrightarrow> a) \<and> (\<not>b \<longrightarrow> c))"

lemma split_if: "P (x if Q otherwise y) \<longleftrightarrow> ((Q \<longrightarrow> P(x)) \<and> (\<not>Q \<longrightarrow> P(y)))"
  by (case_tac "Q") auto

no_notation All (binder "\<forall>" 10) and Ex (binder "\<exists>" 10)
notation All (binder "\<forall>\<^sub>L" 10) and Ex (binder "\<exists>\<^sub>L" 10)

theorem axiom:
  assumes "DefTy \<equiv> \<lambda>it. (Radix(it) \<and> (assms(it) \<longrightarrow> Cond(it)))"
  shows "DefTy(x) \<longrightarrow> Radix(x) \<and> (assms(x) \<longrightarrow> Cond(x))"
        "Radix(x) \<and> assms(x) \<and> Cond(x) \<longrightarrow> DefTy(x)"
        "Radix(x) \<and> \<not>assms(x) \<longrightarrow> Ex(\<lambda>it. DefTy(x))" using assms by auto



text_raw \<open>\DefineSnippet{mizar-consts1}{\<close>
consts
  ty_membership :: "Set \<Rightarrow> Ty \<Rightarrow> o" (infix "be" 90)
  define_ty :: "Ty \<Rightarrow> (Set \<Rightarrow> o) \<Rightarrow> (Set \<Rightarrow> o) \<Rightarrow>Ty"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{mizar-consts2}{\<close>
consts
  choice :: "Ty \<Rightarrow> Set"     ("the _" [79] 80)
text_raw \<open>}%EndSnippet\<close>

notation (input) ty_membership (infix "is" 90)

definition inhabited :: "Ty \<Rightarrow> o" where
"inhabited(D) \<longleftrightarrow> (\<exists>\<^sub>Lx. x be D)"

lemma inhabitedI[intro?]: "x be D \<Longrightarrow> inhabited(D)"
  unfolding inhabited_def by auto
text_raw \<open>\DefineSnippet{axioms-def}{\<close>
term "\<lambda>it. it be parent \<and> (cond(it) \<longrightarrow> property(it))"    
text_raw \<open>}%EndSnippet\<close>
text_raw \<open>\DefineSnippet{mizar-axioms1}{\<close>
axiomatization where
  def_ty_property: "T \<equiv> define_ty(parent, cond, property) \<Longrightarrow>
         (x be T \<longrightarrow> x be parent \<and> (cond(x) \<longrightarrow> property(x))) \<and>
         (x be parent \<and> cond(x) \<and> property(x) \<longrightarrow> x be T) \<and>
         (x be parent \<and> \<not>cond(x) \<longrightarrow> inhabited(T)) "
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{mizar-axioms2}{\<close>
axiomatization where
  choice_ax: "inhabited(M) \<Longrightarrow> (the M) be M"
text_raw \<open>}%EndSnippet\<close>

lemma def_ty_property_true:
  "x be define_ty(Radix, \<lambda>_.True ,Cond) \<longleftrightarrow> x be Radix \<and> Cond(x)"
proof
  show "x is define_ty(Radix, \<lambda>_. True, Cond) \<Longrightarrow> x is Radix \<and> Cond(x)" using
    def_ty_property[of _ Radix "\<lambda>_. True" Cond,THEN conjunct1] by simp
  show "x is Radix \<and> Cond(x) \<Longrightarrow> x is define_ty(Radix, \<lambda>_. True, Cond)" using
    def_ty_property[THEN conjunct2] by simp
qed
text \<open>
\DefineSnippet{inhabited-def}{
   @{thm [display] inhabited_def[no_vars]}
}%EndSnippet
\<close>

definition Ball :: "Ty \<Rightarrow> (Set \<Rightarrow> o) \<Rightarrow> o" where
  [simp]: "inhabited(D) \<Longrightarrow> Ball(D, P) \<longleftrightarrow> (\<forall>\<^sub>Lx. x be D \<longrightarrow> P(x))"
definition Bex :: "Ty \<Rightarrow> (Set \<Rightarrow> o) \<Rightarrow> o" where
  [simp]: "inhabited(D) \<Longrightarrow> Bex(D, P) \<longleftrightarrow> (\<exists>\<^sub>Lx. x be D \<and> P(x))"

text \<open>
\DefineSnippet{ball-def}{
   @{thm [display] Ball_def[no_vars]}
}%EndSnippet
\DefineSnippet{bex-def}{
   @{thm [display] Bex_def[no_vars]}
}%EndSnippet
\<close>

nonterminal vgs and bg and vs
syntax
  "_BallI"  :: "vgs \<Rightarrow> o \<Rightarrow> o"      ("\<forall>_. _" 10)
  "_Ball"  :: "vgs \<Rightarrow> o \<Rightarrow> o"      ("(3for _ holds _)" [0, 10] 10)
  "_Ball2" :: "vgs \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o" ("(3for _ st _ holds _)" [0, 0, 10] 10)
  "_Ball3" :: "vgs \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o" ("(3for _ st _ _)" [0, 10, 10] 10)
  "_Bex"    :: "vgs \<Rightarrow> o \<Rightarrow> o"      ("(3ex _ st _)" [0, 10] 10)
  "_BexI"   :: "vgs \<Rightarrow> o \<Rightarrow> o"      ("\<exists>_. _" 10)
  "_vgs"   :: "bg \<Rightarrow> vgs \<Rightarrow> vgs"   (infixr "," 15)
  ""       :: "bg \<Rightarrow> vgs"          ("_")
  "_nbg"   :: "vs \<Rightarrow> vgs"          ("_")
  "_bg"    :: "vs \<Rightarrow> Ty \<Rightarrow> bg"    (infix "being" 20)
  "_bg"    :: "vs \<Rightarrow> Ty \<Rightarrow> bg"    (infix "be" 20)
  "_bg"    :: "vs \<Rightarrow> Ty \<Rightarrow> bg"    (infix ":" 20)
  "_vs"    :: "pttrn \<Rightarrow> vs \<Rightarrow> vs"  (infixr "," 25)
  ""       :: "pttrn \<Rightarrow> vs"        ("_")
  "_BallML1" :: "vgs \<Rightarrow> o \<Rightarrow> o"
  "_BallML2" :: "vs \<Rightarrow> o \<Rightarrow> o"
  "_BexML1" :: "vgs \<Rightarrow> o \<Rightarrow> o"
  "_BexML2" :: "vs \<Rightarrow> o \<Rightarrow> o"
translations
  "_Ball2 (vs, c, e)" \<rightleftharpoons> "_Ball (vs, CONST imp(c, e))"
  "_Ball3 (vs, c, e)" \<rightleftharpoons> "_Ball (vs, CONST imp(c, e))"
  "_Ball (_vgs (bg, vgs), P)" \<rightleftharpoons> "_Ball (bg, _Ball (vgs, P))"
  "_Ball (_bg (_vs (v, vs), D), P)" \<rightleftharpoons> "_BallML1 (_bg (_vs (v, vs), D), P)"
  "_Ball (_nbg (vs), P)" \<rightharpoonup> "_BallML2 (vs, P)"
  "_Bex (_vgs (bg, vgs), P)" \<rightleftharpoons> "_Bex (bg, _Bex (vgs, P))"
  "_Bex (_bg (_vs (v, vs), D), P)" \<rightleftharpoons> "_BexML1 (_bg (_vs (v, vs), D), P)"
  "_Bex (_nbg (vs), P)" \<rightharpoonup> "_BexML2 (vs, P)"
  "_BallML1 (_bg (_vs (v, vs), D), P)" \<rightharpoonup> "CONST Ball(D,(%v. _Ball (_bg(vs, D), P)))"
  "_BexML1 (_bg (_vs (v, vs), D), P)" \<rightharpoonup> "CONST Bex(D,(%v. _Bex (_bg(vs, D), P)))"
  "_BallI (vs, P)" \<rightharpoonup> "_Ball (vs, P)"
  "_BexI (vs, P)" \<rightharpoonup> "_Bex (vs, P)"
  "for x being D holds P" \<rightharpoonup> "CONST mizar.Ball(D,(%x. P))"
  "ex x being D st P" \<rightharpoonup> "CONST mizar.Bex(D,(%x. P))"
  "\<forall>y being D . P" \<rightleftharpoons> "CONST mizar.Ball(D,(\<lambda>y. P))"
  "\<exists>y being D . P" \<rightleftharpoons> "CONST mizar.Bex(D,(\<lambda>y. P))"

lemma ballI [intro!]: " (\<And>x. x be D \<Longrightarrow> P(x)) \<Longrightarrow> inhabited(D) \<Longrightarrow> \<forall>x:D. P(x)"
by simp
lemma bspec [dest?]: "\<forall>x:D. P(x) \<Longrightarrow> inhabited(D) \<Longrightarrow> x be D \<Longrightarrow> P(x)"
by simp
lemma ballE [elim]: "\<forall>x:D. P(x) \<Longrightarrow> inhabited(D) \<Longrightarrow> (x be D \<Longrightarrow> P(x) \<Longrightarrow> Q) \<Longrightarrow> (\<not> x be D \<Longrightarrow> Q) \<Longrightarrow> Q"
by (unfold Ball_def) blast
lemma bexI [intro]: "inhabited(D) \<Longrightarrow> P(x) \<Longrightarrow> x be D \<Longrightarrow> \<exists>x:D. P(x)"
unfolding Bex_def by blast
lemma rev_bexI [intro?]: "inhabited(D) \<Longrightarrow> x be D \<Longrightarrow> P(x) \<Longrightarrow> \<exists>x:D. P(x)"
by (unfold Bex_def) blast
lemma bexE [elim!]: "\<exists>x:A. P(x) \<Longrightarrow> inhabited(A) \<Longrightarrow> (\<And>x. x be A \<Longrightarrow> P(x) \<Longrightarrow> Q) \<Longrightarrow> Q"
by auto

lemma atomize_conjL[atomize_elim]: "(A \<Longrightarrow> B \<Longrightarrow> C) == (A \<and> B \<Longrightarrow> C)"
  by rule iprover+
lemma atomize_conjL2[atomize_elim]: "(A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D) == (A \<and> B \<Longrightarrow> C \<Longrightarrow> D)"
  by rule iprover+
lemma atomize_conjL3[atomize_elim]: "(A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E) == (A \<and> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E)"
  by rule iprover+
lemma atomize_conjL4[atomize_elim]: "(A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E \<Longrightarrow> F) == (A \<and> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E \<Longrightarrow> F)"
  by rule iprover+
lemma atomize_conjL5[atomize_elim]: "(A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E \<Longrightarrow> F \<Longrightarrow> G) == (A \<and> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E \<Longrightarrow> F \<Longrightarrow> G)"
  by rule iprover+
lemma atomize_conjL6[atomize_elim]: "(A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E \<Longrightarrow> F \<Longrightarrow> G \<Longrightarrow> H) == (A \<and> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E \<Longrightarrow> F \<Longrightarrow> G \<Longrightarrow> H)"
  by rule iprover+
lemma atomize_conjL7[atomize_elim]: "(A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E \<Longrightarrow> F \<Longrightarrow> G \<Longrightarrow> H \<Longrightarrow> I) == (A \<and> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E \<Longrightarrow> F \<Longrightarrow> G \<Longrightarrow> H \<Longrightarrow> I)"
  by rule iprover+
lemma atomize_conjL8[atomize_elim]: "(A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E \<Longrightarrow> F \<Longrightarrow> G \<Longrightarrow> H \<Longrightarrow> I \<Longrightarrow> J) == (A \<and> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E \<Longrightarrow> F \<Longrightarrow> G \<Longrightarrow> H \<Longrightarrow> I \<Longrightarrow> J)"
  by rule iprover+
lemmas [rulify] = atomize_conjL[symmetric]  atomize_conjL2[symmetric] atomize_conjL3[symmetric] atomize_conjL4[symmetric]
                  atomize_conjL5[symmetric] atomize_conjL6[symmetric] atomize_conjL7[symmetric] atomize_conjL8[symmetric]

lemma iffI2: "A \<longrightarrow> B \<Longrightarrow> B \<longrightarrow> A \<Longrightarrow> A \<longleftrightarrow> B" by iprover
lemma iffI3: "A \<longrightarrow> B \<Longrightarrow> (B \<Longrightarrow> A) \<Longrightarrow> A \<longleftrightarrow> B" by iprover
lemma disjCI2: "(\<not> P \<Longrightarrow> Q) \<Longrightarrow> P \<or> Q" by auto

ML \<open>
fun conj_elims th =
  (case dest_Trueprop (Thm.concl_of th) of
    (Const (@{const_name conj}, _) $ _ $ _) =>
      conj_elims (th RS @{thm conjunct1}) @
      conj_elims (th RS @{thm conjunct2})
  | _ => [th])
  handle TERM _ => [th]
\<close>

section \<open> Mizar article "HIDDEN" \<close>

(* object is the root of type hierarchy *)

text_raw \<open>\DefineSnippet{hidden-axioms}{\<close>
axiomatization
  object and (*set :: Ty and*)
  prefix_in :: "Set \<Rightarrow> Set \<Rightarrow> o" (infixl "in" 50)
where
  object_root: "x be object" and
  object_exists: "inhabited(object)" (*and
  hidden_mode: "x be set \<Longrightarrow> x be object"*)
text_raw \<open>}%EndSnippet\<close>

declare object_root[simp]


lemma def_ty_property_object:
  "x be D \<Longrightarrow> x is define_ty(object, \<lambda>it .it be D, cond) \<longleftrightarrow> cond(x)"
proof
  assume "x is D" "x is define_ty(object, \<lambda>it. it is D, cond)"
  thus "cond(x)" using def_ty_property[THEN conjunct1, of _ object "\<lambda>it .it be D" cond] by simp
next
  assume "x is D" "cond(x)"
  thus "x is define_ty(object, \<lambda>it. it is D, cond)"
      using def_ty_property[THEN conjunct2, of _ object "\<lambda>it .it be D" cond] by simp
qed

text_raw \<open>\DefineSnippet{set-def}{\<close>
definition SET("set") where
  "set\<equiv>object"
text_raw \<open>}%EndSnippet\<close>


(*define_ty(Radix, assms,Cond)  *)


text_raw \<open>\DefineSnippet{set-axioms}{\<close>
lemma hidden_mode: "x be set \<Longrightarrow> x be object" 
  using SET_def by auto
text_raw \<open>}%EndSnippet\<close>


text_raw \<open>\DefineSnippet{theProp}{\<close>
abbreviation (input) theProp
  where "theProp(ty, prop) \<equiv> the define_ty(ty, \<lambda>_. True, prop)"
text_raw \<open>}%EndSnippet\<close>

definition NON ("non _" [102] 101)
  where "non A \<equiv> define_ty(object, \<lambda>_. True,\<lambda> x . \<not> x be A)"

lemma non_property: "x be non A \<longleftrightarrow> \<not> x be A"
  using def_ty_property_true NON_def by simp

text \<open>
\DefineSnippet{non-def-a}{
   @{thm [display] NON_def[no_vars]}
}%EndSnippet
\<close>

text \<open>
\DefineSnippet{non-def-b}{
   @{thm [display] non_property[no_vars]}
}%EndSnippet
\<close>

definition ty_intersection (infixl "\<bar>" 100) where
  "t1 \<bar> t2 \<equiv> define_ty(object,\<lambda>_.True, \<lambda>x. x be t1 \<and> x be t2)"

lemma ty_intersection: "x be t1 \<bar> t2 \<longleftrightarrow> x be t1 \<and> x be t2"
  using def_ty_property_true ty_intersection_def by simp

text \<open>
\DefineSnippet{tyintersection}{
   @{thm [display] ty_intersection[no_vars]}
}%EndSnippet
\<close>

lemmas [simp] = ty_intersection non_property

end
