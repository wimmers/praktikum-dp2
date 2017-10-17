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
ML_file \<open>../scratch/Transform.ML\<close>
local_setup \<open>
lift_fun NONE;
\<close>
print_theorems

interpretation su: dp_consistency su .

lemma "su.consistentDP su\<^sub>T"
  by (dp_match induct: su\<^sub>T.induct simp: su.simps simp\<^sub>T: su\<^sub>T.simps)

end
end