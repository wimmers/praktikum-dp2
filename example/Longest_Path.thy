theory Longest_Path
  imports "../DP_Lifting" "../DP_Consistency" "../DP_Proof"
begin

context (* Longest path *)
  fixes v :: "nat \<Rightarrow> nat"
    and p :: "nat \<Rightarrow> nat"
  assumes p_lt: "p (Suc j) < Suc j"
begin


text \<open>Dimensionality given by i\<close>
function wis :: "nat \<Rightarrow> nat" where
  "wis 0 = 0" |
  "wis (Suc i) = max (wis (p (Suc i)) + v i) (wis i)"
  by pat_completeness auto
termination
  by (relation "(\<lambda>p. size p) <*mlex*> {}") (auto intro: wf_mlex mlex_less simp: p_lt)

function wis\<^sub>T :: "nat \<Rightarrow>\<^sub>T nat" where
  "wis\<^sub>T$ 0 =CHECKMEM= \<langle>0\<rangle>" |
  "wis\<^sub>T$ (Suc i) =CHECKMEM= max\<^sub>T . (plus\<^sub>T . (wis\<^sub>T (p (Suc i))) . \<langle>v i\<rangle>) . (wis\<^sub>T i)"
  by pat_completeness auto
termination
  by (relation "(\<lambda>p. size p) <*mlex*> {}") (auto intro: wf_mlex mlex_less simp: p_lt)

interpretation wis: dp_consistency wis .

lemma "wis.consistentDP wis\<^sub>T"
  by (dp_match induct: wis.induct simp: wis.simps simp\<^sub>T: wis\<^sub>T.simps)
end

end