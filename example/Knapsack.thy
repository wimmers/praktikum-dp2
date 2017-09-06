theory Knapsack
  imports "../DP_CRelVS" "../DP_Proof"
begin
context (* Knapsack *)
  fixes w :: "nat \<Rightarrow> nat"
begin
  
fun su :: "nat\<times>nat \<Rightarrow> nat" where
  "su (0, W) = (if W < w 0 then 0 else w 0)" |
  "su (Suc i, W) = (if W < w (Suc i)
    then su (i, W)
    else max (su (i, W)) (w i + su (i, W - w i)))"
  
fun su\<^sub>T :: "nat\<times>nat \<Rightarrow>\<^sub>T nat" where
  "su\<^sub>T$ (0, W) =CHECKMEM= If\<^sub>T . \<langle>W < w 0\<rangle> . \<langle>0\<rangle> . \<langle>w 0\<rangle>" |
  "su\<^sub>T$ (Suc i, W) =CHECKMEM= If\<^sub>T . \<langle>W < w (Suc i)\<rangle>
    . (su\<^sub>T (i, W))
    . (max\<^sub>T . (su\<^sub>T (i, W)) . (plus\<^sub>T . \<langle>w i\<rangle> . (su\<^sub>T (i, W - w i))))"

interpretation su: dp_consistency su .

lemma "su.consistentDP su\<^sub>T"
  by (dp_match induct: su\<^sub>T.induct simp: su.simps simp\<^sub>T: su\<^sub>T.simps)

end
end