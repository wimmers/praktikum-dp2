theory Bellman_Ford
  imports "../DP_Lifting" "../DP_CRelVS" "../DP_Proof"
begin                                        
  
consts n :: nat
consts W :: "nat \<Rightarrow> nat \<Rightarrow> int"
term 0 (**)
  
  (*
fun bf :: "nat\<times>nat \<Rightarrow> int" where
  "bf (0,j) = W 0 j"
| "bf (Suc k, j) = fold min [bf (k, i) + W i j. i \<leftarrow> [0..<n]] (bf (k, j))"
term 0 (**)
*)
  
fun bf :: "nat\<times>nat \<Rightarrow> int" where
  "bf (0, j) = W 0 j"
| "bf (Suc k, j) =
    fold
      (min)
      (map
          (\<lambda>i. plus (W i j) (bf (k, i)))
          (upt 0 n))
      (bf (k, j))"
thm bf.simps
thm bf.induct
term 0 (**)

ML_file \<open>../scratch/Transform.ML\<close>
local_setup \<open>
lift_fun NONE
\<close>
print_theorems

interpretation bf: dp_consistency bf .

lemma "bf.consistentDP bf\<^sub>T"
  by (dp_match induct: bf\<^sub>T.crel_vs_induct simp: bf.simps simp\<^sub>T: bf\<^sub>T.simps)
end
