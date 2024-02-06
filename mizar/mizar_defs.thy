theory mizar_defs
imports mizar_ty
begin

text_raw {*\DefineSnippet{means_prefix}{*}
abbreviation (input) means_prefix   ("func _ \<rightarrow> _ means _" [0,0] 10)
  where "func df \<rightarrow> ty means prop \<equiv> df = theProp(ty, prop)"
text_raw {*}%EndSnippet*}

text {*
\DefineSnippet{means_prefix_display}{
  @{term [display] "func df \<rightarrow> ty means prop 
    \<equiv> df = theProp (ty,prop)"}
}%EndSnippet
*}

text_raw {*\DefineSnippet{equals_prefix}{*}
abbreviation (input) equals_prefix   ("func _ \<rightarrow> _ equals _" [10,10] 10)
where "func df \<rightarrow> ty equals term \<equiv>
   func df \<rightarrow> ty means \<lambda>it. it = term"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{assume_means_prefix}{*}
abbreviation (input) as_means   ("assume _ func _ \<rightarrow> _ means _" [0,0,0,0] 10)
where "assume as func df \<rightarrow> ty means prop \<equiv>
  df = the define_ty(ty, \<lambda>_. as, prop)"
text_raw {*}%EndSnippet*}

abbreviation (input) assume_equals_prefix
   ("assume _ func _ \<rightarrow> _ equals _" [0,0,0,0] 10)
where "assume as func def \<rightarrow> type equals term \<equiv>
  def = the define_ty (type, \<lambda>_.as,\<lambda>it.(it = term))"

text_raw {*\DefineSnippet{attr_prefix}{*}
abbreviation (input) attr_prefix   ("attr _ for _ means _" [10,10,10] 10)
  where "attr df for ty means prop \<equiv> 
             (df \<equiv> define_ty(object, \<lambda>it .it be ty, prop))"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{mode_prefix}{*}
abbreviation (input) mode_prefix   ("mode _ \<rightarrow> _ means _" [10,10,10] 10)
  where "mode df \<rightarrow> ty means prop \<equiv> (df \<equiv> define_ty(ty, \<lambda>_.True, prop))"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{assume_mode_prefix}{*}
abbreviation (input) assumemode_prefix   ("assume _ mode _ \<rightarrow> _ means _" [10,10,10,10] 10)
  where "assume as mode df \<rightarrow> ty means prop \<equiv> (df \<equiv> define_ty(ty,\<lambda>_.as,prop))"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{cluster_functorial}{*}
abbreviation (input) cluster_prefix_functorial
   ("let _ cluster _ \<rightarrow> _" [10,10,10] 10)
where "let lt cluster fun \<rightarrow> attrs
      \<equiv> (lt \<Longrightarrow> fun is attrs)"
text_raw {*}%EndSnippet*}
  


text_raw {*\DefineSnippet{cluster_existence}{*}
abbreviation (input) cluster_prefix_existential
   ("let _ cluster _ for _" [10,10,10] 10)
where "let lt cluster attrs for ty
      \<equiv> (lt \<Longrightarrow> inhabited(attrs \<bar> ty))"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{cluster_conditional}{*}
abbreviation (input) cluster_prefix_conditional
   ("let _ cluster _ \<rightarrow> _ for _" [10,10,10,10] 10)
where "let lt cluster attrs \<rightarrow> attrs2 for ty
      \<equiv> ( \<And>X. lt \<Longrightarrow> X be ty \<Longrightarrow>  X be attrs \<Longrightarrow> X be attrs2)"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{cluster_functorialfor }{*}
abbreviation (input) cluster_prefix_functorial_for
   ("let _ cluster _ \<rightarrow> _ fors _ " [10,10,10,10] 10)
where "let lt cluster fun \<rightarrow> attrs fors ty
      \<equiv> (lt \<Longrightarrow> fun be ty \<Longrightarrow> fun be attrs)"
text_raw {*}%EndSnippet*}
  
 lemma cluster_prefix_functorial_for_property:
assumes coherence: "\<And> it. it be ty \<Longrightarrow>
             ((it = term) \<longrightarrow> it be attrs)"
shows "let lt cluster term \<rightarrow> attrs fors ty"
  using coherence by auto  
  
  
  
abbreviation (input) cluster_prefix_attrs2 ("cluster _ \<rightarrow> _ for _" [10,10,10] 10)
where "cluster attrs1 \<rightarrow> attrs2 for ty \<equiv> ( \<And>X. X be ty \<Longrightarrow>  X be attrs1 \<Longrightarrow> X be attrs2)"

abbreviation (input) cluster_prefix_attrs ("let _ cluster \<rightarrow> _ for _" [10,10,10] 10)
where "let lt cluster \<rightarrow> attrs for ty \<equiv> ( \<And>X. lt \<Longrightarrow> X be ty \<Longrightarrow> X be attrs)"

abbreviation (input) cluster_prefix_fun ("cluster _ \<rightarrow> _" [10,10] 10)
where "cluster term \<rightarrow> attrs \<equiv> term is attrs"

abbreviation (input) cluster_prefix_ex ("cluster _ for _" [10,10] 10)
where "cluster attrs for ty \<equiv> inhabited(attrs \<bar> ty)"

text_raw {*\DefineSnippet{redefine_mode_means}{*}
abbreviation (input) redefine_mode_means ("let _ redefine mode _ \<rightarrow> _ means _" [10,10,10,10] 10)
  where "let lt redefine mode df \<rightarrow> ty means newProp \<equiv> 
       ( lt \<Longrightarrow> ( \<And> x. x be df \<Longrightarrow> (x be ty \<and> newProp (x))))"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{redefine_func_coherence_means}{*}
abbreviation (input) redefine_func_coherence_means ("redefine func _ \<rightarrow> _ " [10,10] 10)
where "redefine func df \<rightarrow> ty \<equiv> (df be ty)"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{let_redefine_func_coherence_means}{*}
abbreviation (input) let_redefine_func_coherence_means ("let _ redefine func _ \<rightarrow> _ " [10,10,10] 10)
where "let lt redefine func df \<rightarrow> ty \<equiv> ( lt \<longrightarrow> df be ty)"
text_raw {*}%EndSnippet*}


text_raw {*\DefineSnippet{redefine_attr_means}{*}
abbreviation (input) redefine_attr_means ("let _ redefine attr _ means _" [10,10,10] 10)
where "let lt redefine attr df means newProp \<equiv> ( lt \<Longrightarrow> df \<longleftrightarrow>  newProp)"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{redefine_pred_means}{*}
abbreviation (input) redefine_pred ("let _ redefine pred _ means _" [10,10,10] 10)
where "let lt redefine pred df means newProp \<equiv> ( lt \<Longrightarrow> (df \<longleftrightarrow> newProp))"
text_raw {*}%EndSnippet*}

abbreviation (input) synonym_prefix ("let _ synonym _ for _" [10,10,10] 10)
where "let lt synonym term1 for term2 \<equiv> (lt \<Longrightarrow> (term1 = term2))"

abbreviation (input) antonym_prefix ("let _ antonym _ for _" [10,10] 10)
where "let lt antonym pred1 for pred2 \<equiv> (lt \<Longrightarrow> (pred1 \<longleftrightarrow> \<not> pred2))"

abbreviation (input) pred_prefix ("let _ pred _ means _" [10,10,10] 10)
where "let lt pred def means exp \<equiv> (lt \<Longrightarrow>  def \<longleftrightarrow> exp)"

text_raw {*\DefineSnippet{reduce_prefix}{*}
abbreviation (input) let_reduce_prefix
   ("let _ reduce _ to _" [10,10,10] 10)
where "let lt reduce term to subterm
      \<equiv> (lt \<Longrightarrow> (term = subterm))"
text_raw {*}%EndSnippet*}

abbreviation (input) reduce_prefix
   ("reduce _ to _" [10,10] 10)
where "reduce term to subterm \<equiv> (term = subterm)"


abbreviation (input) prefix_asymmetry ("asymmetry _ _")
where "asymmetry dom R \<equiv> for x1,x2 being dom holds \<not> (R(x1,x2) \<and> R(x2,x1))"

abbreviation (input) prefix_irreflexive ("irreflexive _ _")
where "irreflexive dom R \<equiv> \<forall>x:dom. \<not>R(x,x)"

abbreviation (input) prefix_reflexive ("reflexive _ _")
where "reflexive dom R \<equiv> \<forall>x:dom. R(x,x)"

abbreviation (input) prefix_symmetry ("symmetry _ _")
where "symmetry dom R \<equiv> for x1,x2 being dom st R(x1,x2) holds R(x2,x1)"

abbreviation (input) prefix_connectedness ("connectedness _ _")
where "connectedness dom R \<equiv> for x1,x2 being dom holds R(x1,x2) \<or> R(x2,x1)"

abbreviation (input) prefix_involutiveness ("involutiveness _ _")
where "involutiveness dom U \<equiv> for x being dom holds U(U(x)) = x"

abbreviation (input) prefix_projectivity ("projectivity _ _")
where "projectivity dom U \<equiv> for x being dom holds U(U(x)) = U(x)"

abbreviation (input) prefix_idempotence ("idempotence _ _")
where "idempotence dom B \<equiv> for x being dom holds B(x,x) = x"

abbreviation (input) prefix_commutativity ("commutativity _ _")
where "commutativity dom B \<equiv> \<forall>x1:dom. \<forall>x2:dom. B(x1,x2) = B(x2,x1)"


section "PROPERTY"

text_raw {*\DefineSnippet{means_property}{*}
lemma means_property:
  assumes df: "func df \<rightarrow> ty means prop"
    and m: "inhabited(ty)"
    and ex: "\<exists>x:ty. prop(x)"
    and un: "\<And>x y. x be ty \<Longrightarrow> y be ty \<Longrightarrow>
                prop(x) \<Longrightarrow> prop(y) \<Longrightarrow> x = y"
  shows "df be ty \<and> prop(df) \<and> (x be ty \<and> prop(x) \<longrightarrow> x = df)"
text_raw {*}%EndSnippet*}
  unfolding df
proof (intro conjI)
  have e: "\<exists>\<^sub>Lx. x be define_ty(ty,\<lambda>_. True,prop)" using Bex_def[OF m] ex def_ty_property_true by auto
  hence f: "(theProp(ty,prop)) be define_ty(ty,\<lambda>_. True,prop)" using choice_ax inhabited_def by auto
  thus g: "(theProp(ty,prop)) be ty" using def_ty_property_true e object_root by auto
  show h: "prop(theProp(ty,prop))" using def_ty_property_true e f object_root by auto
  show "x be ty \<and> prop(x) \<longrightarrow> x = theProp(ty,prop)" using un g h by auto
qed
text_raw {*\DefineSnippet{equals_property}{*}
lemma equals_property:
assumes df: "func df \<rightarrow> ty equals term"
   and coherence: "term be ty"
 shows "df be ty \<and> df = term"
text_raw {*}%EndSnippet*}
proof -
  have i: "inhabited(ty)" using inhabited_def coherence by auto
  have ex: "\<exists>x:ty. x = term" using coherence i by auto
  show "df be ty \<and> (df = term)"
  using means_property[OF df i ex] by auto
qed

text_raw {*\DefineSnippet{mode_property}{*}
lemma mode_property:
  assumes df: "mode df \<rightarrow> ty means prop"
      and m: "inhabited(ty)"
      and ex: "\<exists>x:ty. prop(x)"
  shows "(x be df \<longleftrightarrow> (x be ty \<and> prop(x))) \<and> inhabited(df)"
  text_raw {*}%EndSnippet*}
proof-
   obtain x where
    "x be ty \<and> prop(x)" using ex m by auto
   hence "x be df" using ex def_ty_property_true df by auto
   thus ?thesis using ex def_ty_property_true df inhabited_def by auto
 qed

lemma mode_property_intro:
  assumes df: "mode df \<rightarrow> ty means prop"
 and m: "inhabited(ty)"
 and ex: "ex x being ty st prop(x)"
shows "inhabited(df) \<and> (x be df \<longrightarrow> x be ty) \<and>
       (x be df \<longrightarrow> prop(x)) \<and>
       (prop(x) \<longrightarrow> x be ty \<longrightarrow> x be df)"
using mode_property df m ex by auto

text_raw {*\DefineSnippet{attr_property}{*}
lemma attr_property:
  assumes df:"attr df for ty means prop"
  shows "X be ty \<Longrightarrow> (X is df \<longleftrightarrow> prop(X))"
        "X be ty \<Longrightarrow> prop(X) \<Longrightarrow> X is df"
        "X be ty \<Longrightarrow> X is df \<Longrightarrow> prop(X)"
          using def_ty_property_object df by auto
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{redefine_func_means}{*}
abbreviation (input) redefine_func_means ("let _ redefine func _ \<rightarrow> _ means _" [10,10,10,10] 10)
  where "let lt redefine func df \<rightarrow> ty means newProp \<equiv>
   ( lt \<Longrightarrow> ( df be ty \<and> newProp (df) \<and> (\<forall>\<^sub>L x . x be ty \<and> newProp (x) \<longrightarrow> x=df)))"
text_raw {*}%EndSnippet*}


text_raw {*\DefineSnippet{redefine_func_means_property}{*}
  lemma redefine_func_means_property:
assumes lt: "lt"
assumes coherence: "df be ty"
assumes compatibility: "\<And> it. it be ty \<Longrightarrow>
             ((it = df) \<longleftrightarrow> newProp(it))"
shows "( df be ty \<and> newProp (df) \<and> (\<forall>\<^sub>L x . x be ty \<and> newProp (x) \<longrightarrow> x=df))"
  using coherence compatibility lt by auto
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{redefine_attr_means_property}{*}
lemma redefine_attr_means_property:
assumes lt: "lt"
assumes compatibility: "A \<longleftrightarrow> newProp"
shows "let lt redefine attr A means newProp" using compatibility lt by simp
text_raw {*}%EndSnippet*}




(*"assume as func def \<rightarrow> ty means cond*)


text_raw {*\DefineSnippet{assume_means_property}{*}
lemma assume_means_property:
assumes df: "assume as func df \<rightarrow> ty means prop"
   and assume_ex: "as \<Longrightarrow> \<exists>x:ty. prop(x)"
   and assume_un: "\<And>x y. as \<Longrightarrow> x be ty \<Longrightarrow> y be ty \<Longrightarrow>
       prop(x) \<Longrightarrow> prop(y) \<Longrightarrow> x = y"
   and mode_ex: "inhabited(ty)"
shows
   "df be ty \<and> (as \<longrightarrow> prop(df)) \<and> (as \<and> x be ty \<and> prop(x) \<longrightarrow> x = df)"
text_raw {*}%EndSnippet*}
proof (cases "as")
   assume r: "as"
   hence rdf: " df =  theProp(ty,prop)" using df by simp
   have un1: "\<And>x y. x be ty \<Longrightarrow> y be ty \<Longrightarrow>
     prop(x) \<Longrightarrow> prop(y) \<Longrightarrow> x = y" using assume_un r by simp
   show "df be ty \<and> (as \<longrightarrow> prop(df)) \<and> (as \<and> x be ty \<and> prop(x) \<longrightarrow> x = df)"
     using means_property[OF rdf mode_ex assume_ex[OF r]] assume_un r by auto
next
  assume nR: "not as"
  have "(the ty) be ty" using choice_ax mode_ex by auto
  hence "inhabited(define_ty(ty,\<lambda>_. as,prop))" using def_ty_property[THEN conjunct2] using nR by simp
  hence "df be define_ty(ty,\<lambda>_. as,prop)" using choice_ax df inhabited_def by auto
  thus "df be ty \<and> (as \<longrightarrow> prop(df)) \<and> (as \<and> x be ty \<and> prop(x) \<longrightarrow> x = df)"
    using def_ty_property[THEN conjunct1] nR by auto
qed

lemma assume_equals_property:
assumes df: "assume as func df \<rightarrow> ty equals term"
   and assume_coherence: "as \<Longrightarrow> term be ty"
   and mode_ex: "inhabited(ty)"
shows
   "df be ty \<and> (as \<longrightarrow> df = term)"
proof-
  have assume_ex: "as \<Longrightarrow> ex x being ty st x=term" using assume_coherence mode_ex by auto
      show "df be ty \<and> (as \<longrightarrow> df = term)" using assume_means_property[OF df assume_ex,OF _ _ mode_ex] by auto
    qed





text_raw {*\DefineSnippet{assume_mode_property}{*}
lemma assume_mode_property:
  assumes df: "assume as mode df \<rightarrow> ty means prop"
     and m: "inhabited(ty)"
     and assume_ex: "as \<Longrightarrow> ex x being ty st prop(x)"
  shows
     "(x be df \<longrightarrow> (x be ty \<and> (as \<longrightarrow> prop(x))))
       \<and> (x be ty \<and> as \<and> prop(x) \<longrightarrow> x be df)
       \<and> inhabited(df)"
text_raw {*}%EndSnippet*}
proof (cases "as")
   assume r: "as"
   hence rdf:"df \<equiv>  define_ty(ty,\<lambda>_.True, prop)" using df by simp
   show "(x be df \<longrightarrow> (x be ty \<and> (as \<longrightarrow> prop(x))))
       \<and> (x be ty \<and> as \<and> prop(x) \<longrightarrow> x be df) \<and> inhabited(df)"
     using mode_property[OF rdf m assume_ex[OF r]] by auto
  next
    assume nr:"not as"
    have "(the ty) be ty" using choice_ax m by auto
    thus "(x be df \<longrightarrow> (x be ty \<and> (as \<longrightarrow> prop(x))))
     \<and> (x be ty \<and> as \<and> prop(x) \<longrightarrow> x be df)  \<and> inhabited(df)"
     using def_ty_property[OF df,of x]
          def_ty_property[OF df,of "the ty",THEN conjunct2] nr by blast
 qed



lemmas [simp] = choice_ax


end
