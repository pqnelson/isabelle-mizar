\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Partfun_1
  imports Funct_1
begin

mtheorem partfun_cl_1:
  "let X be set & Y be set 
   cluster empty \<bar> Function_like for Relation-of X,Y"
  proof
    assume "X be set & Y be set"
    have A1: "{} is empty \<bar> Function_like" by (simp add: funct_1_def_1)          
    thus "{} be  (empty \<bar> Function_like) \<parallel> (Relation-of X,Y)" using A1 zfmisc_1_def_1 subset_1_def_1 subset_1_def_2 relset_1_def_1 all_set by auto
  qed

text_raw \<open>\DefineSnippet{PartFuncprefix}{\<close>
abbreviation PartFunc_prefix ("( PartFunc-of _,_ )" 105)
  where " PartFunc-of X,Y \<equiv> Function_like \<parallel> (Relation-of X,Y)"
text_raw \<open>}%EndSnippet\<close>
text_raw \<open>\DefineSnippet{ partfun1def2a}{\<close>
definition total :: "Set \<Rightarrow>Attr" ( " _ : total "[90] 190) 
  where partfun_1_def_2a[THEN defattr_property,simp]:
  "attr X :total means 
      (\<lambda> IT. IT be X-defined \<parallel> Relation & dom IT = X)"
text_raw \<open>}%EndSnippet\<close>

definition nontotal :: "Set \<Rightarrow>Attr" ( "non  _ : total "[90] 190) where partfun_1_def_2b[THEN defattr_property,simp]:
  "non X :total \<equiv> define_attr (\<lambda> IT. IT be (X-defined \<parallel> Relation) & dom IT <> X)"  

end