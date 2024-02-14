\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Mizar_Defs
  imports Mizar_Reserve
begin

(* W tym pliku wprowadzimy: *)
(*
mdefinition ("{_}")
  "let y be object"
func "{y}" \<rightarrow> set means
  "for x holds x in it iff x = y"
existence .
uniqueness .
*)

  
text_raw \<open>\DefineSnippet{means_property}{\<close>    
lemma means_property:
assumes df: "f = theM(\<lambda>x. x be D & P(x))"
    and ex: "ex x being D st P (x)"
    and un: "\<And>x y. x be D \<Longrightarrow> y be D \<Longrightarrow>
         P (x) \<Longrightarrow> P (y) \<Longrightarrow> x = y"
 shows "f be D & P(f) & (x be D & P(x) implies x = f)"
text_raw \<open>}%EndSnippet\<close> 
unfolding df
proof
  let ?P = "\<lambda>x. x be D & P(x)"
  have e: "Ex(\<lambda>x. x be define_mode(?P))" using ex defmode_property by auto
  hence "(theM ?P) be define_mode(?P)" using the_property by auto
  thus "(theM ?P) be D & P(theM ?P)" using defmode_property e by auto
  thus "x be D & P(x) implies x = theM ?P" using un by auto
qed

  
text_raw \<open>\DefineSnippet{equals_propert}{\<close>   
lemma equals_property:
assumes df: "f = theM(\<lambda>x. x be D & x=g)"
   and coherence: "g be D"
 shows "f be D & f = g"
text_raw \<open>}%EndSnippet\<close>
proof -
  have ex: "ex x being D st x=g" using coherence by auto
  show "f be D & (f = g)"
  using means_property[OF df ex] by auto
qed

text_raw \<open>\DefineSnippet{mode_property}{\<close>    
lemma mode_property:
assumes df: "M \<equiv> define_mode(\<lambda>x. x be D & P(x))"
 and ex: "ex x being D st P (x)"
 shows "(x be M iff (x be D & P(x))) & Ex (\<lambda>x. x be M)"
text_raw \<open>}%EndSnippet\<close>
 using ex defmode_property[OF df] by auto

       
    
text_raw \<open>\DefineSnippet{redefine_func_means_property}{\<close>
lemma redefine_func_means_property:
assumes lt: "lt"
assumes coherence: "F be M"
assumes compatibility: "\<And> it. it be M \<Longrightarrow>
             ((it = F) \<longleftrightarrow> newCondition(it))"
shows "F be M \<and> newCondition(F) \<and> (for x be M st newCondition(x) holds x=F)"
  using coherence compatibility lt by auto 
text_raw \<open>}%EndSnippet\<close>
  
    
text_raw \<open>\DefineSnippet{means_prefix}{\<close>
abbreviation (input) means_prefix
   ("func _ \<rightarrow> _ means _" [0,0] 10)
where " func pat \<rightarrow> type means condition \<equiv>
   pat = theM (\<lambda>it. (it be type & condition(it)))"
text_raw \<open>}%EndSnippet\<close>

  
text_raw \<open>\DefineSnippet{equals_prefix}{\<close>
abbreviation (input) equals_prefix
   ("func _ \<rightarrow> _ equals _" [10,10] 10)
where "func pat \<rightarrow> type equals def \<equiv>
   pat = theM (\<lambda>it. it be type & it = def)"
text_raw \<open>}%EndSnippet\<close>

  
(* Here we could use the following syntax translation instead of an abbreviation to introduce a
   named lambda.*)
text_raw \<open>\DefineSnippet{attr_prefix}{\<close>
abbreviation (input) attr_prefix ("attr _ means _" [10,10] 10)
  where "attr def means exp \<equiv> (def \<equiv> define_attr(\<lambda>it. exp(it)))"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{mode_prefix}{\<close>
abbreviation (input) mode_prefix ("mode _ \<rightarrow> _ means _" [10,10,10] 10)
where "mode M \<rightarrow> b means c \<equiv> (M \<equiv> define_mode(\<lambda>it.(it be b & c(it))))"
text_raw \<open>}%EndSnippet\<close>
  
text_raw \<open>\DefineSnippet{cluster_functorial}{\<close>
abbreviation (input) cluster_prefix_functorial 
   ("let _ cluster _ \<rightarrow> _" [10,10,10] 10)
where "let lt cluster fun \<rightarrow> attrs 
      \<equiv> (lt \<Longrightarrow> fun is attrs)"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{cluster_existence}{\<close>
abbreviation (input) cluster_prefix_existential
   ("let _ cluster _ for _" [10,10,10] 10)
where "let lt cluster attrs for type 
      \<equiv> (lt \<Longrightarrow> (Ex (\<lambda> X. X be attrs \<parallel> type)))"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{cluster_conditional}{\<close>
abbreviation (input) cluster_prefix_conditional 
   ("let _ cluster _ \<rightarrow> _ for _" [10,10,10,10] 10)
where "let lt cluster attrs \<rightarrow> attrs2 for type 
      \<equiv> (lt \<Longrightarrow> ( \<And>X. (X be type \<and> X is attrs) \<Longrightarrow> X is attrs2))"
text_raw \<open>}%EndSnippet\<close>

abbreviation (input) cluster_prefix_attrs2 ("cluster _ \<rightarrow> _ for _" [10,10,10] 10)
where "cluster attrs1 \<rightarrow> attrs2 for type \<equiv> (for X being type st X  is attrs1 holds X is attrs2)"

abbreviation (input) cluster_prefix_attrs ("let _ cluster \<rightarrow> _ for _" [10,10,10] 10)
where "let lt cluster \<rightarrow> attrs for type \<equiv> (lt implies (for X being type holds X is attrs))"

abbreviation (input) cluster_prefix_fun ("cluster _ \<rightarrow> _" [10,10] 10)
where "cluster fun \<rightarrow> attrs \<equiv> fun is attrs"

abbreviation (input) cluster_prefix_ex ("cluster _ for _" [10,10] 10)
where "cluster attrs for type \<equiv> (ex X being type st X is attrs)"

text_raw \<open>\DefineSnippet{redefine_pred_means}{\<close>
abbreviation (input) redefine_pred ("let _ redefine pred _ means _" [10,10,10] 10)
where "let lt redefine pred P means newCondition  \<equiv> ( lt \<Longrightarrow> (P \<longleftrightarrow> newCondition))"
text_raw \<open>}%EndSnippet\<close>
  
text_raw \<open>\DefineSnippet{redefine_func_means}{\<close>
abbreviation (input) redefine_func_means ("let _ redefine func _ \<rightarrow> _ means _" [10,10,10,10] 10)
where "let lt redefine func F \<rightarrow> M means newCondition  \<equiv> ( lt \<Longrightarrow> F be M \<and> newCondition (F)\<and>(for x be M st newCondition (x) holds x=F))"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{redefine_attr_means}{\<close>
abbreviation (input) redefine_attr_means ("let _ redefine attr _ means _" [10,10,10] 10)
where "let lt redefine attr A means newCondition  \<equiv> ( lt \<Longrightarrow> A \<longleftrightarrow>  newCondition)"
text_raw \<open>}%EndSnippet\<close>  

text_raw \<open>\DefineSnippet{redefine_attr_means_property}{\<close>
lemma redefine_attr_means_property:
assumes lt: "lt"
assumes compatibility: "A \<longleftrightarrow> newCondition"
shows "A \<longleftrightarrow> newCondition" using compatibility lt by simp
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{redefine_pred_means_property}{\<close>
lemma redefine_pred_means_property:
assumes lt: "lt"
assumes compatibility: "P \<longleftrightarrow> newCondition"
shows "P \<longleftrightarrow> newCondition" using compatibility lt by simp
text_raw \<open>}%EndSnippet\<close>
  
text_raw \<open>\DefineSnippet{redefine_mode_means}{\<close>
abbreviation (input) redefine_mode_means ("let _ redefine mode _ \<rightarrow> _ means _" [10,10,10,10] 10)
where "let lt redefine mode M \<rightarrow> M1 means newCondition  \<equiv> ( lt \<Longrightarrow> ( \<And> x. x be M \<Longrightarrow> (x be M1 & newCondition (x))))"
text_raw \<open>}%EndSnippet\<close>  

text_raw \<open>\DefineSnippet{redefine_func_coherence_means}{\<close>
abbreviation (input) redefine_func_coherence_means ("let _ redefine func _ \<rightarrow> _ " [10,10,10] 10)
where "let lt redefine func F \<rightarrow> M  \<equiv> ( lt \<Longrightarrow> F be M)"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{reduce_prefix}{\<close>
abbreviation (input) reduce_prefix 
   ("let _ reduce _ to _" [10,10,10] 10)
where "let lt reduce term to subterm 
      \<equiv> (lt implies (term = subterm))"
text_raw \<open>}%EndSnippet\<close>

abbreviation (input) synonym_prefix ("let _ synonym _ for _" [10,10,10] 10)
where "let lt synonym term1 for term2 \<equiv> (lt \<Longrightarrow> (term1 = term2))"

abbreviation (input) antonym_prefix ("let _ antonym _ for _" [10,10] 10)
where "let lt antonym pred1 for pred2 \<equiv> (lt \<Longrightarrow> (pred1 \<equiv> not pred2))"

abbreviation (input) pred_prefix ("let _ pred _ means _" [10,10,10] 10)
where "let lt pred def means exp \<equiv> (lt ==>  def iff exp)"  

text_raw \<open>\DefineSnippet{assume_means_property}{\<close>
lemma assume_means_property:
assumes df: "f = theM(\<lambda>x. (x be D & (R implies P (x))))"
   and q: Q
   and assume_ex: "R \<Longrightarrow> ex x being D st P(x)"
   and assume_un: "\<And>x y. R \<Longrightarrow> x be D \<Longrightarrow> y be D \<Longrightarrow> 
       P (x) \<Longrightarrow> P (y) \<Longrightarrow> x = y"
   and mode_ex: "ex x being  D st True"
shows
   "f be D & (R implies P(f) & (x be D & (P (x)) implies x = f))"
text_raw \<open>}%EndSnippet\<close>
proof (cases "R")
   assume r: "R"
   hence rdf: " f =  theM(\<lambda>x. (x be D & P (x)))" using df by simp
   have un1: "\<And>x y. x be D \<Longrightarrow> y be D \<Longrightarrow> 
     P (x) \<Longrightarrow> P (y) \<Longrightarrow> x = y" using assume_un r by simp
   show "f be D & (R implies P (f) & (x be D & P (x) implies x = f))"
     using means_property[OF rdf assume_ex[OF r]] assume_un r by auto
next
  assume nR: "not R"
  let ?P = "\<lambda>x. (x be D & (R implies P (x)))"
  have "(the D) be define_mode(?P)" using defmode_property the_property mode_ex nR by auto
  hence "f be define_mode(?P) " using the_property df by auto
  hence "f be D" using defmode_property  by auto
  thus "f be D & (R implies P(f) & (x be D & P (x) implies x = f))" 
  using nR by auto
qed
    
lemma assume_equals_property:
assumes df: "f = theM(\<lambda>x. (x be D & (R implies x = term)))"
   and q: Q
   and assume_coherence: "R \<Longrightarrow> term be D"
   and mode_ex: "ex x being D st True"
shows
   "f be D & (R implies f = term)"
proof-
  have assume_ex: "R \<Longrightarrow> ex x being D st x=term" using assume_coherence by auto 
      show "f be D & (R implies f = term)" using assume_means_property[OF df q assume_ex,OF  _ _ mode_ex] by auto
qed

text_raw \<open>\DefineSnippet{assume_means_prefix}{\<close>
abbreviation(input) assume_means_prefix
   ("assume _ func _ \<rightarrow> _ means _" [0,0,0,0] 10)
where "assume as func def \<rightarrow> type means condition \<equiv>
  def = theM (\<lambda>it.(it be type & (as implies condition (it))))"
text_raw \<open>}%EndSnippet\<close>

abbreviation(input) assume_equals_prefix
   ("assume _ func _ \<rightarrow> _ equals _" [0,0,0,0] 10)
where "assume as func def \<rightarrow> type equals term \<equiv>
  def = theM (\<lambda>it.(it be type & (as implies it = term)))"

text_raw \<open>\DefineSnippet{assume_mode_property}{\<close>
lemma assume_mode_property:
assumes df: "M \<equiv> define_mode(\<lambda>x. (x be D & (R implies P (x))))"
   and q: Q
   and assume_ex: "R \<Longrightarrow> ex x being D st P(x)"
   and mode_ex: "ex x being D st True"
shows
   "(x be M iff (x be D & (R implies P(x)))) & Ex (\<lambda>x. x be M)"
text_raw \<open>}%EndSnippet\<close>
proof (cases "R")
   assume r: "R"
   hence rdf: "M \<equiv>  define_mode(\<lambda>x. (x be D & P (x)))" using df by simp
   show "(x be M iff (x be D & (R implies P(x)))) & Ex (\<lambda>x. x be M)"
     using assume_ex[OF r] defmode_property[OF rdf,of ] r by auto
  next
   assume "not R"
   thus "(x be M iff (x be D & (R implies P(x)))) & Ex (\<lambda>x. x be M)"
     using the_property mode_ex defmode_property[OF df] by auto
qed
  
text_raw \<open>\DefineSnippet{assume_mode_prefix}{\<close>
abbreviation (input) assume_mode_prefix
   ("assume _ mode _ \<rightarrow> _ means _" [0,0,0,0] 10)
where "assume as mode M \<rightarrow> type means cond \<equiv>
   (M \<equiv> define_mode(\<lambda>it. it be type & (as implies cond(it))))"
text_raw \<open>}%EndSnippet\<close>

abbreviation (input) prefix_asymmetry ("asymmetry _ _")
where "asymmetry dom R \<equiv> for x1,x2 being dom holds not (R(x1,x2) & R(x2,x1))"
  
abbreviation (input) prefix_irreflexive ("irreflexive _ _")
where "irreflexive dom R \<equiv> for x being dom holds not (R(x,x))"
  
abbreviation (input) prefix_reflexive ("reflexive _ _")
where "reflexive dom R \<equiv> for x being dom holds R(x,x)"

abbreviation (input) prefix_symmetry ("symmetry _ _")
where "symmetry dom R \<equiv> for x1,x2 being dom st R(x1,x2) holds R(x2,x1)"

abbreviation (input) prefix_connectedness ("connectedness _ _")
where "connectedness dom R \<equiv> for x1,x2 being dom holds R(x1,x2) or R(x2,x1)"
  
abbreviation (input) prefix_involutiveness ("involutiveness _ _")
where "involutiveness dom U \<equiv> for x being dom holds U(U(x)) = x"

abbreviation (input) prefix_projectivity ("projectivity _ _")
where "projectivity dom U \<equiv> for x being dom holds U(U(x)) = U(x)"

abbreviation (input) prefix_commutativity ("commutativity _ _")
where "commutativity dom B \<equiv> for x1,x2 being dom holds B(x1,x2) = B(x2,x1)"
  
abbreviation (input) prefix_idempotence ("idempotence _ _")
where "idempotence dom B \<equiv> for x being dom holds B(x,x) = x"
  
end