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
        (\<lambda>i. plus (id (\<lambda>i'. bf (k, i')) i) (W i j))
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
      . \<langle>\<lambda>i. \<langle>plus\<^sub>T\<rangle> . (id (\<lambda>i'. bf\<^sub>T (k, i')) i) . \<langle>W i j\<rangle>\<rangle>
      . (\<langle>upt\<^sub>T\<rangle> . \<langle>0\<rangle> . \<langle>n\<rangle>))
    . (bf\<^sub>T (k, j))"

term 0 (**)
thm bf\<^sub>T.induct
  
interpretation bf: dp_consistency bf .

context
  includes lifting_syntax
begin

lemma bf_induct:
  "\<lbrakk>\<And>j. P (0, j);
    \<And>k j. \<lbrakk>\<And>(x::nat) i. P (k, i);
            P (k, j)
           \<rbrakk> \<Longrightarrow> P (Suc k, j)
    \<rbrakk> \<Longrightarrow> P (x::nat\<times>nat)"
  by (fact bf\<^sub>T.induct)

lemma bf_inductS:
  "\<lbrakk>\<And>j. bf.consistentS op = (bf (0, j)) (bf\<^sub>T (0, j));
    \<And>k j. \<lbrakk>(op = ===> bf.consistentS op =) (\<lambda>i. bf (k, i)) (\<lambda>i. bf\<^sub>T (k, i));
            bf.consistentS op = (bf (k, j)) (bf\<^sub>T (k, j))
           \<rbrakk> \<Longrightarrow> bf.consistentS op = (bf (Suc k, j)) (bf\<^sub>T (Suc k, j))
    \<rbrakk> \<Longrightarrow> bf.consistentS op = (bf (x::nat\<times>nat)) (bf\<^sub>T x)"
  unfolding rel_fun_def by (metis bf_induct[of "\<lambda>x. bf.consistentS op = (bf x) (bf\<^sub>T x)"])
  
term 0 (**)
lemma "bf.consistentDP bf\<^sub>T"
proof ((rule bf.consistentDP_intro, induct_tac rule: bf_inductS, unfold bf\<^sub>T.simps; rule bf.consistentS_checkmem, unfold bf.simps), goal_cases)
  case [transfer_rule]: 1 show ?case by transfer_prover
next
  case prems[transfer_rule]: (2 _ k j)
    show ?case
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
                          apply transfer_step
                         apply transfer_step
                        apply transfer_step
                       apply transfer_step
                      apply transfer_step
                     apply transfer_step
        apply transfer_step
    term 0 (**
  subgoal premises [transfer_rule] by transfer_prover
  subgoal premises prems[transfer_rule]
    apply transfer
      
    thm prems
    apply transfer_prover_start
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
    thm prems
    oops
    thm bf.induct bf\<^sub>T.induct
      thm bf_induct[of "\<lambda>x. bf.consistentS op = (bf x) (bf\<^sub>T x)"]
end
