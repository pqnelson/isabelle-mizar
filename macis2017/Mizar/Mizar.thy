\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Mizar
  imports FOL
begin

declare [[eta_contract = false]]

(* Weaker bi-implication intro rule
   corresponds to the unfolded thesis in many Mizar proofs *)
lemma iffI2: "A \<longrightarrow> B \<Longrightarrow> B \<longrightarrow> A \<Longrightarrow> A \<longleftrightarrow> B" by iprover
lemma iffI3: "A \<longrightarrow> B \<Longrightarrow> (B \<Longrightarrow> A) \<Longrightarrow>A \<longleftrightarrow> B" by iprover
lemma disjCI2: "(\<not> P \<Longrightarrow> Q) \<Longrightarrow> P \<or> Q" by auto

(* TODO: Larry once did: "if(P,Q,R) == P&Q | ~P&R", maybe better for CNF? *)
definition If ("((_) if (_) otherwise (_))" [10] 10)
where [simp]: "If (a, b, c) \<longleftrightarrow> ((b \<longrightarrow> a) \<and> (\<not>b \<longrightarrow> c))"

lemma split_if: "P (x if Q otherwise y) \<longleftrightarrow> ((Q \<longrightarrow> P(x)) \<and> (\<not>Q \<longrightarrow> P(y)))"
  by (case_tac "Q") auto

(* Remove Isabelle/FOL notations, to properly introduce the Mizar ones
   with the correct Mizar binding strengths *)
no_notation
  conj (infixr "&" 35) (* and
  conj (infixr "\<and>" 35) and
  disj (infixr "|" 30) and
  disj (infixr "\<or>" 30) and
  imp (infixr "-->" 25) and
  imp (infixr "\<longrightarrow>" 25) and
  Not ("~ _" [40] 40) and
  Not ("\<not> _" [40] 40) and
  All (binder "ALL " 10) and
  Ex (binder "Ex " 10)*)
no_syntax
  "_Let" :: "[letbinds, 'a] => 'a" ("(let (_)/ in (_))" 10)

no_notation
  not_equal (infixl "<>" 50) and
  not_equal (infixl "\<noteq>" 50) and
  IFOL.eq   (infixl "=" 50)

syntax
  "IFOL.imp" :: "o \<Rightarrow> o \<Rightarrow> o" (infixl "implies" 25)
  "IFOL.iff" :: "o \<Rightarrow> o \<Rightarrow> o" (infixl "iff" 25)
  "IFOL.disj" :: "o \<Rightarrow> o \<Rightarrow> o" (infixl "or" 30)
  "IFOL.conj" :: "o \<Rightarrow> o \<Rightarrow> o" (infixl "&" 35)
  "IFOL.Not" :: "o \<Rightarrow> o" ("not _" [40] 40)

(* Cannot directly import the theory, because of different application syntax *)
(*ML_file "~~/src/Tools/adhoc_overloading.ML"*)

(* Mizar concrete instances of objects and sets, such as "{}" or "{x}" *)
typedecl Set
instance Set  :: "term" ..
(* Mizar modes, such as "object", "set", "Relation", "Element of NAT" *)
typedecl Mode
instance Mode :: "term" ..
(* Mizar attributes, such as "empty", "non empty", "onto" *)
typedecl Attr
instance Attr :: "term" ..

(* The checker's implementation of eq-classes implies reflexivity and subst,
  which is same as Isabelle/FOL's one, just for one type. *)
abbreviation mizeq :: "Set \<Rightarrow> Set \<Rightarrow> o" (infixl "=" 50)
where "mizeq(a,b) == IFOL.eq(a,b)"

consts
  (* Mode prefixed by some attributes *)
  attr_mode :: "Attr \<Rightarrow> Mode \<Rightarrow> Mode" (infix " \<parallel> " 100) 
  (* Attribute prefixed by more attributes *)
  attr_attr :: "Attr \<Rightarrow> Attr \<Rightarrow> Attr" (infixr " \<bar> " 110) 
  (* Definite description operator used for definitions by 'means' and 'equals' *)
 (* the1 :: "('a \<Rightarrow> o) \<Rightarrow> 'a"*)
  (* Define a predicate over sets as an attribute *)
  define_attr :: "(Set \<Rightarrow> o) \<Rightarrow> Attr"
  define_mode :: "(Set \<Rightarrow> o) \<Rightarrow> Mode"
  (* Hilbert operator, used in very few articles, for example to define "{}" *)
  prefix_the :: "Mode \<Rightarrow> Set" ("the _" [79] 80)
  (* Predicates that are used for the Mizar type system *)
  is_mode :: "Set \<Rightarrow> Mode \<Rightarrow> o" (infix "be" 90)
  is_attr :: "Set \<Rightarrow> Attr \<Rightarrow> o" (infix "is" 90)

abbreviation the_Mode ("theM _" [79] 80)
  where "theM A \<equiv> the define_mode(A)"

axiomatization where
  attr_mode[simp]: "x be (a1 \<parallel> m) iff (x is a1 & x be m)" and
  attr_attr[simp]: "x is (a1 \<bar> a2)  iff x is a1 & x is a2" and
  defattr_property: "A \<equiv> define_attr(P) \<Longrightarrow> (x is A) iff P(x)" and
  defmode_property: "M \<equiv> define_mode(P) \<Longrightarrow> (x be M) iff P(x)" and
  the_property: "\<exists>x. (x be M) \<Longrightarrow> (the M) be M" 

syntax "_provided"  :: "'a \<Rightarrow> 'a \<Rightarrow> prop" (infix "provided" 0)
parse_ast_translation \<open> [(@{syntax_const "_provided"}, (fn ctxt => fn [p, q] =>
  Ast.Appl [Ast.Constant @{const_syntax "Pure.imp"},
    Ast.Appl [Ast.Constant @{const_syntax "IFOL.Trueprop"}, q],
    Ast.Appl [Ast.Constant @{const_syntax "IFOL.Trueprop"}, p]
  ]))] \<close>

definition Ball :: "Mode \<Rightarrow> (Set \<Rightarrow> o) \<Rightarrow> o" where
  [simp]: "Ball(D, P) iff (\<forall>x. x be D implies P(x))"
definition Bex :: "Mode \<Rightarrow> (Set \<Rightarrow> o) \<Rightarrow> o" where
  [simp]: "Bex(D, P) iff (\<exists>x. x be D & P(x))"

nonterminal vgs and bg and vs
syntax
  "_Ball"  :: "vgs \<Rightarrow> o \<Rightarrow> o"      ("(3for _ holds _)" [0, 10] 10)
  "_Ball2" :: "vgs \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o" ("(3for _ st _ holds _)" [0, 0, 10] 10)
  "_Ball3" :: "vgs \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o" ("(3for _ st _ _)" [0, 10, 10] 10)
  "_Bex"    :: "vgs \<Rightarrow> o \<Rightarrow> o"      ("(3ex _ st _)" [0, 10] 10)
  "_vgs"   :: "bg \<Rightarrow> vgs \<Rightarrow> vgs"   (infixr "," 15)
  ""       :: "bg \<Rightarrow> vgs"          ("_")
  "_nbg"   :: "vs \<Rightarrow> vgs"          ("_")
  "_bg"    :: "vs \<Rightarrow> Mode \<Rightarrow> bg"    (infix "being" 20)
  "_bg"    :: "vs \<Rightarrow> Mode \<Rightarrow> bg"    (infix "be" 20)
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
  "for x being D holds P" \<rightleftharpoons> "CONST Mizar.Ball(D,(%x. P))"
  "_Bex (_vgs (bg, vgs), P)" \<rightleftharpoons> "_Bex (bg, _Bex (vgs, P))"
  "_Bex (_bg (_vs (v, vs), D), P)" \<rightleftharpoons> "_BexML1 (_bg (_vs (v, vs), D), P)"
  "_Bex (_nbg (vs), P)" \<rightharpoonup> "_BexML2 (vs, P)"
  "ex x being D st P" \<rightleftharpoons> "CONST Mizar.Bex(D,(%x. P))"
  "_BallML1 (_bg (_vs (v, vs), D), P)" \<rightharpoonup> "CONST Ball(D,(%v. _Ball (_bg(vs, D), P)))"
  "_BexML1 (_bg (_vs (v, vs), D), P)" \<rightharpoonup> "CONST Bex(D,(%v. _Bex (_bg(vs, D), P)))"

no_notation All (binder "\<forall>" 10) and Ex (binder "\<exists>" 10)
notation (output) All (binder "\<forall>" 10) and Ex (binder "\<exists>" 10)
syntax "_Ball" :: "vgs => o => o"      ("(3\<forall>_./ _)" [0, 10] 10)
syntax "_Bex" :: "vgs => o => o"      ("(3\<exists>_./ _)" [0, 10] 10)

lemma ballI [intro!]: "(\<And>x. x be D \<Longrightarrow> P(x)) \<Longrightarrow> for x being D holds P(x)"
by simp
lemma bspec [dest?]: "for x being D holds P(x) \<Longrightarrow> x be D \<Longrightarrow> P(x)"
by simp
lemma ballE [elim]: "for x being D holds P(x) \<Longrightarrow> (P(x) \<Longrightarrow> Q) \<Longrightarrow> (not x be D \<Longrightarrow> Q) \<Longrightarrow> Q"
by (unfold Ball_def) blast
lemma bexI [intro]: "P(x) ==> x be D ==> ex x being D st P(x)"
unfolding Bex_def by blast
lemma rev_bexI [intro?]: "x be D ==> P(x) ==> ex x being D st P(x)"
by (unfold Bex_def) blast
lemma bexE [elim!]: "ex x being A st P(x) ==> (\<And>x. x be A ==> P(x) ==> Q) ==> Q"
by (unfold Bex_def) blast

lemma atomize_ball:  "(\<And>x. x be D \<Longrightarrow> P(x)) == Trueprop(for x being D holds P(x))"
by (simp only: Ball_def atomize_all atomize_imp)
lemmas [rulify] = atomize_ball[symmetric]

lemma atomize_conjL[atomize_elim]: "(A ==> B ==> C) == (A & B ==> C)"
  by rule iprover+
lemmas [rulify] = atomize_conjL[symmetric]

end