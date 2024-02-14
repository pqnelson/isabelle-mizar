\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory extpro_1
  imports compos_1 Memstr_0 funcop_1
begin

lemma AMI_Struct_over_well_1:
  assumes "N be set" 
  shows "Mem-Struct_fields N \<bar> (# InstructionsF \<rightarrow> \<lambda>_. Instructions #) well defined on {carrier} \<union>{ZeroF}\<union>{Object-Kind}\<union>{ValuesF}\<union>{InstructionsF}"
proof(rule Fields_add_0_arg_Mode[OF MemStruct_over_well[OF assms]],simp add:string)
  show "ex x being Instructions st True" 
  proof (rule bexI[of _ "{[[{},{}],{}]}"])
    show "{[[{},{}],{}]} be Instructions" using Instructions_ex by simp
    show "True" by simp                        
  qed
qed
  
lemma AMI_Struct_over_well_1_ord:
assumes "N be set" 
  shows "(# carrier \<rightarrow> \<lambda>S. set;
   ZeroF \<rightarrow> \<lambda>S. Element-of the carrier of S;
   InstructionsF \<rightarrow> \<lambda>_. Instructions;
   Object-Kind \<rightarrow> \<lambda>S. Function-of the carrier of S, N;
   ValuesF \<rightarrow>  \<lambda>S. ManySortedSet-of N#)
   well defined on {carrier} \<union>{ZeroF}\<union>{InstructionsF}\<union>{Object-Kind}\<union>{ValuesF} "
proof-
  have A0: "{carrier} \<union>{ZeroF}\<union>{Object-Kind}\<union>{ValuesF}\<union>{InstructionsF} =  {carrier} \<union>{ZeroF}\<union>{InstructionsF}\<union>{Object-Kind}\<union>{ValuesF}"  by auto
  have A1: "\<And>X. X is Mem-Struct_fields N \<bar> (# InstructionsF \<rightarrow> \<lambda>_. Instructions #)
            iff X is (# carrier \<rightarrow> \<lambda>S. set;
   ZeroF \<rightarrow> \<lambda>S. Element-of the carrier of S;
   InstructionsF \<rightarrow> \<lambda>_. Instructions;
   Object-Kind \<rightarrow> \<lambda>S. Function-of the carrier of S, N;
   ValuesF \<rightarrow>  \<lambda>S. ManySortedSet-of N#)" 
     by auto
  show ?thesis using  well_defined_order[OF A1 AMI_Struct_over_well_1[OF assms]] A0 by auto
qed 
  
abbreviation AMI_Struct_fields_prefix ("AMI-Struct'_fields _") 
  where "AMI-Struct_fields N\<equiv>
        (# carrier \<rightarrow> \<lambda>S. set;
           ZeroF \<rightarrow> \<lambda>S. Element-of the carrier of S;
           InstructionsF \<rightarrow> \<lambda>_. Instructions;
           Object-Kind \<rightarrow> \<lambda>S. Function-of the carrier of S, N;
           ValuesF \<rightarrow>  \<lambda>S. ManySortedSet-of N;
           Execution \<rightarrow> \<lambda>S. Action-of the InstructionsF of S, 
                                          product ((the ValuesF of S)*`the Object-Kind of S)#)"
   
lemma AMI_Struct_over_well:
  assumes "N be set"  
  shows " AMI-Struct_fields N well defined on {carrier} \<union>{ZeroF}\<union>{InstructionsF}\<union>{Object-Kind}\<union>{ValuesF}\<union>{Execution}"
proof(rule Fields_add_3_arg_Mode[OF  AMI_Struct_over_well_1_ord[OF assms]],simp add:string,simp add:string,simp add:string,simp add:string,intro ballI)
  fix X1 assume "X1 be (# carrier \<rightarrow> \<lambda>S. set;
    ZeroF \<rightarrow> \<lambda>S. Element-of the carrier of S;
    InstructionsF \<rightarrow> \<lambda>_. Instructions;
    Object-Kind \<rightarrow> \<lambda>S. Function-of the carrier of S, N;
    ValuesF \<rightarrow>  \<lambda>S. ManySortedSet-of N#)\<parallel> Function" 
  show "ex it be Action-of the InstructionsF of X1, 
          product ((the ValuesF of X1)*`the Object-Kind of X1) st True" using funct_2_cl_ex all_set by auto
qed

text_raw \<open>\DefineSnippet{AMI_Struct_over}{\<close>
definition AMI_Struct_over ("AMI-Struct-over _") where
  "struct AMI-Struct-over N (# 
     carrier \<rightarrow> \<lambda>S. set;
     ZeroF \<rightarrow> \<lambda>S. Element-of the carrier of S;
     InstructionsF \<rightarrow> \<lambda>_. Instructions;
     Object-Kind \<rightarrow> \<lambda>S. Function-of the carrier of S, N;
     ValuesF \<rightarrow>  \<lambda>S. ManySortedSet-of N;
     Execution \<rightarrow> \<lambda>S. Action-of the InstructionsF of S, 
          product ((the ValuesF of S)*`the Object-Kind of S)#)"
text_raw \<open>}%EndSnippet\<close>
schematic_goal AMI_Struct_over:
  assumes "N be set"
  shows ?X by (rule struct_well_defined[OF AMI_Struct_over_def AMI_Struct_over_well[OF assms]])

theorem AMI_Struct_over_inheritance:
  assumes "N be set"          
          "X be AMI-Struct-over N"
  shows  "X be COM-Struct" "X be Mem-Struct-over N" using  MemStruct_over AMI_Struct_over COM_Struct assms by auto
  
lemma AMI_Struct_over_ag[rule_format]: 
"N be set \<Longrightarrow>
 C be set \<Longrightarrow> Z be Element-of C \<Longrightarrow> I be  Instructions \<Longrightarrow> 
 O be (Function-of C, N) \<Longrightarrow> V be ManySortedSet-of N \<Longrightarrow>
 E be Action-of I,product (V*`O) \<Longrightarrow>
  ({[carrier,C]}\<union>{[ZeroF,Z]}\<union>{[InstructionsF,I]}\<union>{[ Object-Kind,O]}\<union>{[ValuesF,V]}\<union>{[Execution,E]}) be AMI-Struct-over N" 
proof-
  assume A1: "N be set" "C be set" "Z be Element-of C" "I be  Instructions"
    "O be Function-of C, N"  "V be ManySortedSet-of N"
    "E be Action-of I,product (V*`O)"
  let ?A= "({[carrier,C]}\<union>{[ZeroF,Z]}\<union>{[InstructionsF,I]}\<union>{[ Object-Kind,O]}\<union>{[ValuesF,V]}\<union>{[Execution,E]})"
  have T1: "?A be Function" using Function_6[of carrier ZeroF InstructionsF "Object-Kind" ValuesF Execution] by (simp add:string)
  have "the carrier of ?A=C" "the InstructionsF of ?A=I" "the ValuesF of ?A=V" "the  Object-Kind of ?A=O" using 
     the_selector_of_1[OF T1, of carrier C] 
     the_selector_of_1[OF T1, of InstructionsF I]
     the_selector_of_1[OF T1, of ValuesF V]
     the_selector_of_1[OF T1, of "Object-Kind" O]
tarski_def_1 by auto    
  thus ?thesis using T1 AMI_Struct_over Field_1[OF T1,of carrier C]  Field_1[OF T1,of ZeroF Z] 
      Field_1[of ?A InstructionsF I] Field_1[of ?A "Object-Kind" O ] Field_1[of ?A ValuesF V] 
      Field_1[of ?A Execution E] A1 string by auto
qed
  
text_raw \<open>\DefineSnippet{Trivial-AMI}{\<close>   
definition extpro_1_def_1 ("Trivial-AMI _") where
  "func Trivial-AMI N \<rightarrow> strict AMI-Struct-over N\<parallel>AMI-Struct-over N 
     means (\<lambda>it.
      the carrier of it = {0} & 
        the ZeroF of it = 0 &
the InstructionsF of it = {[0,{},{}]} &
  the Object-Kind of it = {0} --> 0  &
      the ValuesF of it = N --> NAT &
    the Execution of it = {[0,{},{}]} --> id product(N --> NAT \<circ> {0} --> 0))"
text_raw \<open>}%EndSnippet\<close>  
schematic_goal extpro_1_def_1:
  assumes "N be with_zero\<parallel> set" shows "?X"
proof (induct rule: means_property[OF extpro_1_def_1_def, of N,case_names existence uniqueness])
  case existence
  let ?h = "[0,{},{}]"
  let ?IT = "{[carrier,{0}]}\<union>
             {[ZeroF, 0]}\<union>
             {[InstructionsF,{?h}]}\<union>
             {[Object-Kind,{0} --> 0]}\<union>
             {[ValuesF,N --> NAT]}\<union>
             {[Execution,{?h} --> id product( (N --> NAT) *` ({0} --> 0))]}"
   have T1: "?IT be Function" using Function_6[of carrier ZeroF InstructionsF "Object-Kind" ValuesF Execution] by (simp add:string) 
   have W1: "the carrier of ?IT={0}" using the_selector_of_1[OF T1, of carrier "{0}"] tarski_def_1 by auto    
   have A1:"{0} be set" by auto 
   have W2: "the ZeroF of ?IT=0" using the_selector_of_1[OF T1, of ZeroF "0"] tarski_def_1 by auto    
   have A2:"0 be Element-of {0}" using Element_of_rule[of 0 "{0}"] tarski_def_1b by auto 

   have W3: "the InstructionsF of ?IT={?h}" using the_selector_of_1[OF T1, of InstructionsF "{?h}"] tarski_def_1 by auto    
   have A3:"{?h} be Instructions" using Instructions_ex by auto 

   have W4:  "the Object-Kind of ?IT={0} --> 0" using the_selector_of_1[OF T1, of "Object-Kind" "{0} --> 0"] tarski_def_1 by auto 
       
   have B1:"0 in N" using assms with_zero by auto                     
   hence  A4:"({0} --> 0) be Function-of {0}, N" using funcop_cl by auto
 
   have W5: "the ValuesF of ?IT=N --> NAT" using the_selector_of_1[OF T1, of ValuesF "N --> NAT"] tarski_def_1 by auto    
  have "dom (N --> NAT) = N" "(N --> NAT) be Function" using funcop_1_th_13 all_set funcop_1_cl_1 by auto  
  hence A5:"(N --> NAT) be ManySortedSet-of N" using pboole_def_1_th_1 by auto 
      
   let ?E = "id product( (N --> NAT) *` ({0}--> 0))"
   have W6: "the Execution of ?IT={?h} --> ?E" using the_selector_of_1[OF T1, of Execution "{?h} --> ?E"] tarski_def_1 by auto    
   have A6:"({?h} --> ?E) be Action-of {?h}, product ((N --> NAT)*`({0} --> 0))" 
   proof-
     have E:"?E be Function" using funct_1_cl_4 relat_1_def_8 all_set by auto    
     have "dom ?E = product( (N --> NAT) *` ({0}--> 0))"
          "rng ?E = product( (N --> NAT) *` ({0} --> 0))" using relat_1_id_dom relat_1_id_rng all_set by auto  
     hence "?E in  Funcs(product ((N --> NAT)*`({0}--> 0)),product ((N --> NAT)*`({0}--> 0)))" using funct_2_def_2 all_set E by auto
       thus ?thesis using funcop_cl[of "?E" _ "{?h}"] by auto
   qed
   have A7: "?IT be AMI-Struct-over N" using AMI_Struct_over_ag[OF _ A1 A2 A3 A4 A5 A6] assms by auto 
   have "dom ?IT = {carrier}\<union>{ZeroF}\<union>{InstructionsF}\<union>
           {Object-Kind}\<union>{ValuesF}\<union>{Execution}" using Dom_6[of carrier _ ZeroF _ InstructionsF] by auto   
  hence "dom ?IT = domain_of AMI-Struct-over N" using AMI_Struct_over[of N] assms by auto
  hence "?IT is (strict AMI-Struct-over N)" using A7 strict by auto
  thus "ex it be strict AMI-Struct-over N\<parallel>AMI-Struct-over N st (the carrier of it) = {0}  & 
     (the ZeroF of it) = 0 &
     (the InstructionsF of it) = {?h} &
     (the Object-Kind of it) = ({0}--> 0)  &
     (the ValuesF of it) = (N --> NAT) &
     (the Execution of it) = ({?h} --> id product( (N --> NAT) *` ({0}--> 0)))" using W1 W2 W3 W4 W5 W6 A7 by auto
next
  case uniqueness
      let ?h = "[0,{},{}]"
  fix it1 it2 assume 
    A1: "it1 be strict AMI-Struct-over N\<parallel>AMI-Struct-over N"
    "it2 be strict AMI-Struct-over N\<parallel>AMI-Struct-over N" 
    "(the carrier of it1) = {0}  & (the ZeroF of it1) = 0 &
     (the InstructionsF of it1) = {?h} & (the Object-Kind of it1) = ({0}--> 0)  &
     (the ValuesF of it1) = (N --> NAT) &
     (the Execution of it1) = ({?h}--> id product( (N --> NAT) *` ({0}--> 0)))"
   "(the carrier of it2) = {0}  & (the ZeroF of it2) = 0 &
     (the InstructionsF of it2) = {?h} & (the Object-Kind of it2) = ({0}--> 0)  &
     (the ValuesF of it2) = (N --> NAT) &
     (the Execution of it2) = ({?h}--> id product( (N --> NAT) *` ({0}--> 0)))"
  show "it1=it2"
     proof(rule Equal_strict[of _ _ "AMI-Struct-over N"])
    show "it1 be Function"  "it2 be Function" using A1(1,2) strict AMI_Struct_over assms by auto 
    show "it1 is strict AMI-Struct-over N" "it2 is strict AMI-Struct-over N" using A1(1,2) by auto
    fix selector
    assume "selector in domain_of AMI-Struct-over N"
    hence "selector in {carrier}\<union>{ZeroF}\<union>{InstructionsF}\<union>
           {Object-Kind}\<union>{ValuesF}\<union>
             {Execution}" using AMI_Struct_over assms by auto
    hence A2: "selector = carrier or selector = ZeroF or selector =InstructionsF or
           selector =Object-Kind or selector =ValuesF or selector = Execution" using tarski_def_1 by auto  
    have "the carrier of it1 = the carrier of it2" 
         "the ZeroF of it1=the ZeroF of it2" 
       "the InstructionsF of it1=the InstructionsF of it2"
       "the Object-Kind of it1=the Object-Kind of it2"
       "the ValuesF of it1=the ValuesF of it2"
       "the Execution of it1=the Execution of it2" using A1(3,4) by auto
    thus "the selector of it1 = the selector of it2" using A2  by auto
   qed
 qed   

theorem extpro_1_cl_1:
  "let N be with_zero\<parallel>set
   cluster Trivial-AMI N \<rightarrow> N:with_non-empty_values"
proof(unfold memstr_0_def_3,rule conjI)
  assume A1: "N be with_zero\<parallel>set" 
  let ?T = "Trivial-AMI N"
  let ?VT =  "the_Values_of ?T"
  show T1: "?T be Mem-Struct-over N" using extpro_1_def_1 AMI_Struct_over_inheritance A1 by auto    
  have A0: "the ValuesF of ?T = N  --> NAT" 
       "(the Object-Kind of ?T) = ({0}--> 0)" using A1 extpro_1_def_1 by auto      
  have V: "the ValuesF of ?T be ManySortedSet-of N" using A1 T1 MemStruct_over field by auto
  have V1: "the ValuesF of ?T be Function" using A1 T1 MemStruct_over field by auto
  have O: "the Object-Kind of ?T be Function-of the carrier of ?T, N" using A1 T1 MemStruct_over field by auto
  hence O1: "the Object-Kind of ?T be Function" using all_set relset_1_cl_1 relset_1_def_1 by auto
  have T2: "?VT be ManySortedSet-of the carrier of ?T" 
      "?VT = (the ValuesF of ?T)*`(the Object-Kind of ?T)" using T1 A1 memstr_0_def_2[of N ?T] by auto     
  have "{} in rng ?VT implies False"
  proof
    have VT: "?VT be Function" using T2 by simp
    assume A: "{} in rng ?VT"
    obtain n where
       A3: "n be object" "n in dom ?VT" "{} = ?VT.n" using T2(1) funct_1_def_3[OF VT,THEN conjunct2,THEN conjunct1,rule_format,THEN iffD1, OF object_root A] by blast          
    have "dom (the ValuesF of ?T) = N" using A0(1) funcop_1_th_13 by auto  
    hence A4: "(the Object-Kind of ?T).n in N" using 
         funct_1_th_11[OF O1 V1,THEN iffD1, OF ] T2 A3(2) by auto
    have "?VT.n =  (the ValuesF of ?T). ((the Object-Kind of ?T).n)" using 
         funct_1_th_12[OF O1 V1 ] T2 A3(2) by auto
    thus "False" using NAT_non_empty xboole_0_def_2c funcop_1_th_7[OF A4] A0(1) A3 by auto     
  qed  
  thus "the_Values_of ?T  is non-empty" using funct_1_def_9 T2 by auto                
qed
  
text_raw \<open>\DefineSnippet{extpro_1_def_2}{\<close>   
definition extpro_1_def_2( "Exec \<^sub>_'(_ ,  _')" 190) where
  "func Exec \<^sub>S(I,s) \<rightarrow> State-of S equals
    ((the Execution of S).I).s "
text_raw \<open>}%EndSnippet\<close>
schematic_goal extpro_1_def_2:
  assumes "N be with_zero\<parallel>set" 
           "S be N:with_non-empty_values \<parallel> AMI-Struct-over N"
           "I be Instruction-of S" 
           "s be State-of S" 
  shows "?X"   
proof (rule equals_property[OF extpro_1_def_2_def,of S I s])
  let ?E = "the Execution of S"
  let ?EI = "?E.I"
  let ?EIs = "?EI.s" 
  have T0:"S be Mem-Struct-over N" "S be COM-Struct" using assms(1,2) AMI_Struct_over_inheritance by auto
  hence T1: "(the ValuesF of S)*`the Object-Kind of S = the_Values_of S" 
        "the_Values_of S be non-empty\<parallel>ManySortedSet-of the carrier of S"        
    using memstr_0_def_2[of N S] memstr_0_def_3 assms(1,2) by auto
  have I1: "the InstructionsF of S be Instructions" using T0 field COM_Struct by auto
  have E1: "?E be Action-of the InstructionsF of S,product (the_Values_of S)" using 
     assms(1,2)  field[of S Execution] AMI_Struct_over[of N] T1(1)
    by auto
  hence E2: "?E be Function" using all_set relset_1_cl_1 relset_1_def_1 by auto
  have P1:"product (the_Values_of S) is non empty" using T1 card_3_cl by auto
  hence "product (the_Values_of S)<>{}" by auto       
  have "Funcs(product (the_Values_of S),product (the_Values_of S)) is non empty" 
    using funct_2_cl_Funcs all_set by auto  
  hence "Funcs(product (the_Values_of S),product (the_Values_of S)) <>{}" 
     using xboole_0_def_1b by auto  
  hence DE: "dom ?E = the InstructionsF of S" 
     using funct_2_def_1a[of ?E "the InstructionsF of S"] E1  xboole_0_def_1b by auto     
  have "I in the InstructionsF of S" using assms(3) Instructions_non_empty I1 by auto    
  hence Y: "?EI in rng ?E" using funct_1_def_3[OF E2] DE by auto
  have "rng ?E c= Funcs(product (the_Values_of S),product (the_Values_of S))" using E1 relat_1_def_19a relset_1_cl_2 
      all_set by auto 
  hence r: "?EI in  Funcs(product (the_Values_of S),product (the_Values_of S))" using Y by auto 
  obtain EI where
     ei: "EI be Function" "?EI = EI & dom EI = product (the_Values_of S) & rng EI c= product (the_Values_of S)"  
    using  funct_2_def_2[of "product (the_Values_of S)" "product (the_Values_of S)",
       OF all_set all_set,THEN conjunct1,THEN conjunct2,rule_format, of "?EI",THEN iffD1, OF  object_root r] by blast
  have DD:"dom (the_Values_of S) = the carrier of S" 
          " dom s =the carrier of S" using T1 partfun_1_def_2a assms(4) by auto    
  have "for y being object st y in dom (the_Values_of S) holds s. y in (the_Values_of S). y"  using funct_1_def_14 assms(4) T1
       by auto 
  hence "s in product (the_Values_of S)" using assms(4) card_3_def_5[of "the_Values_of S"] DD T1 by auto
  hence "EI. s in rng EI" using ei funct_1_def_3[OF ei(1)]  all_set by auto
  hence u: "EI. s in product (the_Values_of S)" using ei by auto
  have T3: "the_Values_of S be Function" using T1 by auto
  obtain EIs where
     eis: "EIs be Function" "EI. s = EIs & dom EIs = dom (the_Values_of S) & 
         (for y being object st y in dom (the_Values_of S) holds EIs. y in (the_Values_of S). y)"
    using  card_3_def_5[THEN conjunct1,THEN conjunct2,rule_format, of "the_Values_of S" "EI. s",THEN iffD1,
       OF T3 object_root u] by blast
  have W1:"?EIs be ManySortedSet-of the carrier of S" using DD eis ei pboole_def_1_th_1 by auto
  have  "?EIs is (the_Values_of S)-compatible" unfolding funct_1_def_14
  proof(intro conjI ballI impI)
    show "?EIs be Function" "the_Values_of S  be Function" using T1 eis ei by auto
    fix y assume "y in  dom ?EIs"  
    thus  "?EIs. y in (the_Values_of S). y" using eis ei by auto  
    qed
  thus "?EIs be State-of S" using W1 by auto    
qed

text_raw \<open>\DefineSnippet{extpro_1_def_3}{\<close>  
definition extpro_1_def_3("halting _") where 
  "attr halting S means (\<lambda>I. 
        I be Instruction-of S & 
        (for s be State-of S holds  Exec \<^sub>S(I,s) = s))"
text_raw \<open>}%EndSnippet\<close> 
lemmas extpro_1_def_3 = extpro_1_def_3_def[THEN defattr_property]
 
text_raw \<open>\DefineSnippet{extpro_1_def_4}{\<close>
definition extpro_1_def_4 ("halting'_on _") where
  "attr halting_on N means (\<lambda>S. 
      S be N:with_non-empty_values \<parallel> AMI-Struct-over N &        
      halt \<^sub>S is halting S)"
text_raw \<open>}%EndSnippet\<close>
  
lemmas extpro_1_def_4 = extpro_1_def_4_def[THEN defattr_property]
  
text_raw \<open>\DefineSnippet{extpro_1_cl}{\<close> 
theorem extpro_1_cl:
  "for N be with_zero\<parallel>set,
       I be Instruction-of Trivial-AMI N,
       s be State-of Trivial-AMI N holds
    Exec \<^sub>Trivial-AMI N(I,s) = s"
text_raw \<open>}%EndSnippet\<close>
proof(intro ballI)
  fix N I s 
  let ?T = "Trivial-AMI N" 
  assume A1:"N be with_zero\<parallel>set"
         "I be Instruction-of ?T"
          "s be State-of ?T"
  have A2: "?T be N:with_non-empty_values \<parallel> AMI-Struct-over N" using extpro_1_cl_1 extpro_1_def_1 A1(1) by auto
  have E: "Exec \<^sub>?T(I,s) = ((the Execution of ?T).I).s" using  extpro_1_def_2[OF A1(1) A2 A1(2,3)] by auto
  have  "I be Element-of {[0,{},{}]}" using extpro_1_def_1[OF A1(1)] A1 by simp 
  hence A5: "I in {[0,{},{}]}" using xboole_0_def_1b tarski_def_1b by auto    
  hence A3: "(the Execution of ?T).I = id product( (N --> NAT) *` ({0}--> 0))" using funcop_1_def_9 funcop_1_th_7 extpro_1_def_1 A1(1) by auto
  have "the ValuesF of ?T = (N--> NAT)" 
       "(the Object-Kind of ?T) = ({0}--> 0)" using extpro_1_def_1[OF A1(1)] A1 by auto
  hence  A4: "(N --> NAT) *` ({0}--> 0) = the_Values_of ?T" 
        "the_Values_of ?T be non-empty\<parallel>ManySortedSet-of the carrier of ?T"        
    using memstr_0_def_2[of N ?T] memstr_0_def_3 A1 A2 by auto
  have "dom s = the carrier of ?T & dom the_Values_of ?T=the carrier of ?T" using A4 A1 partfun_1_def_2a by auto
  hence "s in product(the_Values_of ?T)" using funct_1_def_14[of s "the_Values_of ?T"] A1 A4(2) card_3_def_5[of "the_Values_of ?T"]  by auto
  thus "Exec \<^sub>?T(I,s) = s" using A5 A4 A3 E funct_1_th_18 by auto        
qed

text_raw \<open>\DefineSnippet{extpro_1_cl_2}{\<close> 
theorem extpro_1_cl_2:
  "let N be with_zero\<parallel>set
   cluster Trivial-AMI N \<rightarrow> halting_on N"
text_raw \<open>}%EndSnippet\<close>
proof(unfold extpro_1_def_4 extpro_1_def_3,intro conjI)
  let ?T = "Trivial-AMI N"
  assume A: "N be with_zero\<parallel>set"
  thus "?T be N:with_non-empty_values \<parallel> AMI-Struct-over N " using extpro_1_cl_1 extpro_1_def_1 by auto
  hence "?T be COM-Struct" using AMI_Struct_over_inheritance A by auto
  thus W1:"halt \<^sub>?T be Instruction-of ?T" using compos_1_def_10[of ?T] by auto
  show "for s be State-of Trivial-AMI N holds
    Exec \<^sub>Trivial-AMI N(halt \<^sub>?T,s) = s" using extpro_1_cl A W1 by auto  
qed

notation
  compos_1_def_10 ("halt\<^bsub>_\<^esub>")

text_raw \<open>\DefineSnippet{extpro_1}{\<close>   
theorem extpro_1:
  assumes "N be with_zero\<parallel>set"  
  shows "halt\<^bsub>Trivial-AMI N\<^esub> is halting Trivial-AMI N"
text_raw \<open>}%EndSnippet\<close> unfolding extpro_1_def_3
proof
  let ?T = "Trivial-AMI N"
  have "?T be N:with_non-empty_values \<parallel> AMI-Struct-over N " using extpro_1_cl_1 extpro_1_def_1 assms by auto
  hence "?T be COM-Struct" using AMI_Struct_over_inheritance assms by auto
  thus  "halt \<^sub>?T be Instruction-of ?T" using compos_1_def_10[of ?T] by auto
  thus "for s be State-of Trivial-AMI N holds
    Exec \<^sub>Trivial-AMI N(halt \<^sub>?T,s) = s" using extpro_1_cl assms by auto  
qed

end