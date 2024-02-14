\<^marker>\<open>creator "Cezary Kaliszyk"\<close>
\<^marker>\<open>creator "Karol Pąk"\<close>
theory Xfamily
  imports Xboole_0
begin

theorem xfamily_sch_3:
  assumes "X1 be set" "X2 be set"
    "for x being set holds x in X1 iff P(x)"
    "for x being set holds x in X2 iff P(x)"
  shows "X1 = X2" using xboole_0_sch_3 assms tarski_0_1 by auto

end