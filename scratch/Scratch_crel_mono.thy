theory Scratch_crel_mono
  imports "../DP_CRelVS"
begin

context dp_consistency
begin

lemma crel_vs_mono:
  fixes R0 R1
  assumes "R0 \<le> R1"
  shows "crel_vs R0 \<le> crel_vs R1"
  using assms by (fastforce intro: crel_vs_intro elim: crel_vs_elim)

end

end