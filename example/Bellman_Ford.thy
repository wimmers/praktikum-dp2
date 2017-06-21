theory Bellman_Ford
  imports "../DP_Lifting" "../DP_Consistency"
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
      min
      (map
        (\<lambda>i. plus (bf (k, i)) (W i j))
        (upt 0 n))
      (bf (k, j))"
thm bf.simps
term 0 (**)
  
fun bf\<^sub>T :: "nat\<times>nat \<Rightarrow>\<^sub>T int" where
  "bf\<^sub>T$ (0, j) =CHECKMEM= \<langle>W 0 j\<rangle>"
| "bf\<^sub>T$ (Suc k, j) =CHECKMEM=
    \<langle>fold\<^sub>T\<rangle>
    . \<langle>min\<^sub>T\<rangle>
    . (\<langle>map\<^sub>T\<rangle>
      . \<langle>\<lambda>i. \<langle>plus\<^sub>T\<rangle> . (bf\<^sub>T (k, i)) . \<langle>W i j\<rangle>\<rangle>
      . (\<langle>upt\<^sub>T\<rangle> . \<langle>0\<rangle> . \<langle>n\<rangle>))
    . (bf\<^sub>T (k, j))"
term 0 (**)
  
interpretation bf: dp_consistency bf .
context
  includes lifting_syntax
begin
lemma "bf.consistentDP bf\<^sub>T"
  apply (rule bf.consistentDP_intro, induct_tac rule: bf\<^sub>T.induct, unfold bf\<^sub>T.simps; rule bf.consistentS_checkmem, unfold bf.simps)
  subgoal premises [transfer_rule] by transfer_prover
  subgoal premises prems[transfer_rule]
    apply transfer_prover_start
                        apply transfer_step
                        apply transfer_step
                        apply transfer_step
                        apply transfer_step
                        apply transfer_step
                        apply transfer_step
                        apply transfer_step
                        apply transfer_step
                        apply transfer_step
                        apply transfer_step
                        apply transfer_step
                        apply transfer_step
      (* going wrong here *)
      (* bf\<^sub>T (Pair k i) should be proved directly by prems(1) rather than be separated *)
    oops
end
