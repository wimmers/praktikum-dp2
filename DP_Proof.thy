theory DP_Proof
  imports "./DP_CRelVS" "~~/src/HOL/Eisbach/Eisbach_Tools"
begin           

method dp_match uses consistency induct simp simp\<^sub>T =
  ( rule dp_consistency.consistentDP_intro[OF consistency],
    rule induct,
    unfold simp\<^sub>T;
    rule dp_consistency.crel_vs_checkmem[OF consistency],
    unfold simp,
    ((match premises in _[transfer_rule]: _ (multi) \<Rightarrow> transfer_prover)
      | (match conclusion in _ \<Rightarrow> transfer_prover)))

end