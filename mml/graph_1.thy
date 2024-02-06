theory graph_1
imports struct_0
begin
  mdefinition MultiGraphStruct :: "Ty" ("MultiGraphStruct") where
  "struct MultiGraphStruct
      (#carrier \<rightarrow> set';
        carrier` \<rightarrow> set';
        Source \<rightarrow> Function-of' the' carrier`, the' carrier;
        Target \<rightarrow> Function-of' the' carrier`, the' carrier #)"
  :well_defined_property[of _ _ "{carrier}\<union>{carrier`}\<union>{Source}\<union>{Target}"]
  by (auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

lemmas MultiGraphStructA = MultiGraphStruct(1)
lemmas [ex] = MultiGraphStruct(2,3)
lemmas MultiGraphStructD = MultiGraphStruct(4)
lemmas [ty_func] = MultiGraphStruct(5)

theorem MultiGraphStruct_inheritance[ty_parent]:
  "X be MultiGraphStruct \<Longrightarrow> X be 2-sorted" using MultiGraphStructA two_sortedA by simp

theorem MultiGraphStruct_inheritance1[ty_func]:
  "X be MultiGraphStruct \<Longrightarrow> (the Source of X) be Function-of the carrier` of X, the carrier of X"
       using field MultiGraphStructA by auto

theorem MultiGraphStruct_inheritance2[ty_func]:
  "X be MultiGraphStruct \<Longrightarrow> (the Target of X) be Function-of the carrier` of X, the carrier of X"
       using field MultiGraphStructA by auto

lemma MultiGraphStruct_ag[ty_func]:
  "X be set \<Longrightarrow> Y be set \<Longrightarrow> S be Function-of Y,X \<Longrightarrow> T be Function-of Y,X \<Longrightarrow>
       [#carrier\<mapsto> X ; carrier`\<mapsto>Y; Source\<mapsto>S; Target\<mapsto>T #] be MultiGraphStruct"
proof-
  assume A1[ty]: "X be set" "Y be set" "S be Function-of Y,X" "T be Function-of Y,X"
  let ?A= "[#carrier\<mapsto> X ; carrier`\<mapsto>Y; Source\<mapsto>S; Target\<mapsto>T #]"
  have [ty]: "?A be Struct" using Struct_4 by (simp add:string)
  have T:"the carrier of ?A=X" using the_selector_of_1[of ?A carrier "X"] Aggr by auto
  have T1:"the carrier` of ?A=Y" using the_selector_of_1[of ?A "carrier`" "Y"] Aggr by auto
  have [ty]:"?A is (carrier \<rightarrow> set')" using Field_1[of ?A carrier X ] Aggr by auto
  have [ty]:"?A is (carrier` \<rightarrow> set')" using Field_1[of ?A "carrier`" Y ] Aggr by auto
  have [ty]:"?A is (Source \<rightarrow> Function-of' the' carrier`, the' carrier)" using Field_1[of ?A Source S ] T T1 Aggr by auto
  have [ty]:"?A is (Target \<rightarrow> Function-of' the' carrier`, the' carrier)" using Field_1[of ?A Target T ] T T1 Aggr by auto
  thus ?thesis using MultiGraphStructA by auto
qed

abbreviation graph_1_mode_1_prefix ("Vertex-of _" [150] 150)
  where "Vertex-of X \<equiv> Element-of (the carrier of X)"

abbreviation graph_1_mode_2_prefix ("Edge-of _" [150] 150)
  where "Edge-of X \<equiv> Element-of (the carrier` of X)"


func graph_1_def_1 ("dom \<^bsub>_\<^esub> _" [999,105] 105) where
 mlet "C be MultiGraphStruct", "f be Edge-of C"
 "func dom\<^bsub>C\<^esub> f \<rightarrow> Vertex-of C means
     (\<lambda>it. it = (the Source of C) . f if (C is non void-struct \<bar>non empty-struct)
        otherwise it = the Vertex-of C)"
proof-
  show "ex x be Vertex-of C st (x = (the Source of C) . f if
           C is non void-struct \<bar> non empty-struct otherwise x = (the Vertex-of C))"
  proof(cases "C is non void-struct \<bar> non empty-struct")
    case [ty]:True
      show ?thesis using funct_2_def_5A[of "the carrier` of C" "the carrier of C" "the Source of C"] by mauto
  next
     case False thus ?thesis by auto
    qed
qed mauto

func graph_1_def_2 ("cod \<^bsub>_\<^esub> _" [999,105] 105) where
 mlet "C be MultiGraphStruct", "f be Edge-of C"
 "func cod\<^bsub>C\<^esub>f \<rightarrow> Vertex-of C means
     (\<lambda>it. it = (the Target of C) . f if (C is non void-struct \<bar>non empty-struct)
        otherwise it = the Vertex-of C)"
proof-
  show "ex x be Vertex-of C st (x = (the Target of C) . f if
           C is non void-struct \<bar> non empty-struct otherwise x = (the Vertex-of C))"
  proof(cases "C is non void-struct \<bar> non empty-struct")
    case [ty]:True
     show ?thesis using funct_2_def_5A[of "the carrier` of C" "the carrier of C" "the Target of C"] by mauto
  next
    case False thus ?thesis by auto
    qed
qed mauto

text_raw {*\DefineSnippet{redefine_func_equals}{*}
abbreviation (input) redefine_func_equals ("let _ redefine func _ \<rightarrow> _ equals _" [10,10,10,10] 10)
  where "let lt redefine func F \<rightarrow> M equals term \<equiv>
   ( lt \<longrightarrow> ( F be M \<and> F = term))"
text_raw {*}%EndSnippet*}

theorem graph_1_def_3[simplified,rule_format]:
  "let C be non void-struct \<bar> non empty-struct \<bar> MultiGraphStruct \<and> f be Edge-of C
   redefine func dom\<^bsub>C\<^esub>f \<rightarrow> Vertex-of C equals
      (the Source of C) . f"
proof
  assume [ty]: "C be non void-struct \<bar> non empty-struct \<bar> MultiGraphStruct \<and> f be Edge-of C"
  have A: "dom\<^bsub>C\<^esub> f is Vertex-of C" by mauto
  thus "dom\<^bsub>C\<^esub> f is Vertex-of C \<and> dom\<^bsub>C\<^esub> f = (the Source of C) . f" using graph_1_def_1 by auto
qed

theorem graph_1_def_4[simplified,rule_format]:
  "let C be non void-struct \<bar> non empty-struct \<bar> MultiGraphStruct \<and> f be Edge-of C
   redefine func cod\<^bsub>C\<^esub>f \<rightarrow> Vertex-of C equals
      (the Target of C) . f"
proof
  assume [ty]: "C be non void-struct \<bar> non empty-struct \<bar> MultiGraphStruct \<and> f be Edge-of C"
  have A: "cod\<^bsub>C\<^esub> f is Vertex-of C" by mauto
  thus "cod\<^bsub>C\<^esub> f is Vertex-of C \<and> cod\<^bsub>C\<^esub> f = (the Target of C) . f" using graph_1_def_2 by auto
qed

end
