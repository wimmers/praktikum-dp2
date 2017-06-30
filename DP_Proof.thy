theory DP_Proof
  imports "./DP_Consistency" "~~/src/HOL/Eisbach/Eisbach_Tools"
begin

method dp_match uses induct simp simp\<^sub>T =
  ( rule dp_consistency.consistentDP_intro,
    induct_tac rule: induct,
    unfold simp\<^sub>T;
    rule dp_consistency.consistentS_checkmem,
    unfold simp,
    ((match premises in _[transfer_rule]: _ (multi) \<Rightarrow> transfer_prover)
      | (match conclusion in _ \<Rightarrow> transfer_prover)))

end