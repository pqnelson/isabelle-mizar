\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Enumset_1
  imports Tarski
begin

reserve x1 for object

mtheorem enumset1_th_29:
  "{ x1,x1 } = { x1 }"
proof-
  have A1: "x1 be set" using tarski_0_1 by simp 
  {
    fix x
    have "x in { x1,x1 } iff x = x1" using tarski_def_2 by auto
    hence "x in { x1,x1 } iff x in { x1 }" using tarski_def_1 by auto
  }
  thus "{ x1,x1 } = { x1 }" using tarski_th_2[OF A1] by auto
qed

end