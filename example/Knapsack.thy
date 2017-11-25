theory Knapsack
  imports "../DP_CRelVS" "../DP_Proof"
begin

context (* Subset Sum *)
  fixes w :: "nat \<Rightarrow> nat"
begin

context (* Knapsack *)
  fixes v :: "nat \<Rightarrow> nat"
begin

fun knapsack :: "nat\<times>nat \<Rightarrow> nat" where
  "knapsack (0, W) = 0" |
  "knapsack (Suc i, W) = (if W < w (Suc i)
    then knapsack (i, W)
    else max (knapsack (i, W)) (v (Suc i) + knapsack (i, W - w (Suc i))))"

no_notation fun_app_lifted (infixl "." 999)

text \<open>
  The correctness proof closely follows Kleinberg & Tardos: "Algorithm Design",
  chapter "Dynamic Programming"
\<close>

definition
  "OPT n W = Max {\<Sum> i \<in> S. v i | S. S \<subseteq> {1..n} \<and> (\<Sum> i \<in> S. w i) \<le> W}"

lemma OPT_0:
  "OPT 0 W = 0"
  unfolding OPT_def by auto

lemma OPT_Suc:
  "OPT (Suc i) W = (
    if W < w (Suc i)
    then OPT i W
    else max(v (Suc i) + OPT i (W - w (Suc i))) (OPT i W)
  )"
proof -
  have OPT_in: "OPT n W \<in> {\<Sum> i \<in> S. v i | S. S \<subseteq> {1..n} \<and> (\<Sum> i \<in> S. w i) \<le> W}" for n W
    unfolding OPT_def by - (rule Max_in; force)
  from OPT_in[of "Suc i" W] obtain S where S:
    "S \<subseteq> {1..Suc i}" "sum w S \<le> W" and [simp]: "OPT (Suc i) W = sum v S"
    by auto
  have "OPT i W \<le> OPT (Suc i) W"
    unfolding OPT_def by (force intro: Max_mono)
  have "sum v S = OPT i W" if "W < w (Suc i)"
  proof -
    have "Suc i \<notin> S"
    proof (rule ccontr, simp)
      assume "Suc i \<in> S"
      then have "sum w S \<ge> w (Suc i)"
        using S(1) by (subst sum.remove) (auto intro: finite_subset[OF _ finite_atLeastAtMost])
      with \<open>W < _\<close> \<open>_ \<le> W\<close> show False
        by simp
    qed
    with S have "OPT i W \<ge> sum v S"
      unfolding OPT_def by (auto simp: atLeastAtMostSuc_conv intro!: Max_ge)
    with \<open>OPT i W \<le> _\<close> show ?thesis
      by simp
  qed
  moreover have
    "OPT (Suc i) W = max(v (Suc i) + OPT i (W - w (Suc i))) (OPT i W)" if "w (Suc i) \<le> W"
  proof (cases "Suc i \<in> S")
    case True
    then have [simp]:
      "sum v S = v (Suc i) + sum v (S - {Suc i})" "sum w S = w (Suc i) + sum w (S - {Suc i})"
      using S(1) by (auto intro: finite_subset[OF _ finite_atLeastAtMost] sum.remove)
    have "sum v S' \<le> sum v (S - {Suc i})" if "S' \<subseteq> {Suc 0..i}" "sum w S' \<le> W - w (Suc i)" for S'
    proof -
      have "sum v S' + v (Suc i) \<in> {\<Sum> i \<in> S. v i | S. S \<subseteq> {1..Suc i} \<and> (\<Sum> i \<in> S. w i) \<le> W}"
        using that \<open>w (Suc i) \<le> W\<close>
        apply simp
        apply (rule exI[where x = "S' \<union> {Suc i}"])
        apply clarsimp
        by ((subst sum.insert_if, auto intro: finite_subset[OF _ finite_atLeastAtMost]))+
      then have "sum v S' + v (Suc i) \<le> OPT (Suc i) W"
        unfolding OPT_def by auto
      then show ?thesis
        by simp
    qed
    then have "OPT i (W - w (Suc i)) = sum v (S - {Suc i})"
      unfolding OPT_def using S by (fastforce intro!: Max_eqI)
    with \<open>OPT i W \<le> _\<close> show ?thesis
      by simp
  next
    case False
    with S have "OPT (Suc i) W \<le> OPT i W"
      by (simp, auto simp: atLeastAtMostSuc_conv OPT_def intro!: Max_ge)
    with \<open>OPT i W \<le> _\<close> have "OPT (Suc i) W = OPT i W"
      by simp
    moreover have "v (Suc i) + local.OPT i (W - w (Suc i)) \<le> OPT (Suc i) W"
    proof -
      from OPT_in[of i "W - w (Suc i)"] guess S'
        by clarify
      then show ?thesis
        unfolding OPT_def
        apply -
        apply (rule Max_ge)
         apply force
        apply (rule CollectI, rule exI[where x = "S' \<union> {Suc i}"])
        using \<open>w (Suc i) \<le> W\<close>
        by simp ((subst sum.insert_if; auto intro: finite_subset[OF _ finite_atLeastAtMost]))+
    qed
    with \<open>_ = OPT i W\<close> show ?thesis
      by simp
  qed
  ultimately show ?thesis
    by auto
qed

theorem knapsack_correct:
  "OPT n W = knapsack (n, W)"
  by (induction n arbitrary: W; auto simp: OPT_0 OPT_Suc)

notation fun_app_lifted (infixl "." 999)

ML_file \<open>../scratch/Transform.ML\<close>
local_setup \<open>
lift_fun NONE;
\<close>
print_theorems

interpretation knapsack: dp_consistency knapsack .

lemma "knapsack.consistentDP knapsack\<^sub>T"
  by (dp_match induct: knapsack\<^sub>T.induct simp: knapsack.simps simp\<^sub>T: knapsack\<^sub>T.simps)

end (* Knapsack *)

fun su :: "nat\<times>nat \<Rightarrow> nat" where
  "su (0, W) = 0" |
  "su (Suc i, W) = (if W < w (Suc i)
    then su (i, W)
    else max (su (i, W)) (w (Suc i) + su (i, W - w (Suc i))))"

lemma su_knapsack:
  "su (n, W) = knapsack w (n, W)"
  by (induction n arbitrary: W; simp)

lemma su_correct:
  "Max {\<Sum> i \<in> S. w i | S. S \<subseteq> {1..n} \<and> (\<Sum> i \<in> S. w i) \<le> W} = su (n, W)"
  unfolding su_knapsack knapsack_correct[symmetric] OPT_def ..

local_setup \<open>
lift_fun NONE;
\<close>
print_theorems

interpretation su: dp_consistency su .

lemma "su.consistentDP su\<^sub>T"
  by (dp_match induct: su\<^sub>T.induct simp: su.simps simp\<^sub>T: su\<^sub>T.simps)

end (* Subset Sum *)

end (* Theory *)