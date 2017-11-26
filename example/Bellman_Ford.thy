theory Bellman_Ford
  imports "../DP_Lifting" "../DP_CRelVS" "../DP_Proof" "HOL-Library.Extended"
begin                                        

context
  fixes n :: nat and W :: "nat \<Rightarrow> nat \<Rightarrow> int"
begin

context
  fixes t :: nat -- "Final node"
begin

text \<open>
  The correctness proof closely follows Kleinberg & Tardos: "Algorithm Design",
  chapter "Dynamic Programming"
\<close>

definition weight :: "nat list \<Rightarrow> int" where
  "weight xs = snd (fold (\<lambda> i (j, x). (i, W i j + x)) (rev xs) (t, 0))"

definition
  "OPT i v = (
    Min (
      {Fin (weight (v # xs)) | xs. length xs + 1 \<le> i \<and> set xs \<subseteq> {0..n}} \<union>
      {if t = v then Fin 0 else \<infinity>}
    )
  )"

lemma weight_Cons [simp]:
  "weight (v # w # xs) = W v w + weight (w # xs)"
  by (simp add: case_prod_beta' weight_def)

lemma weight_single [simp]:
  "weight [v] = W v t"
  by (simp add: weight_def)

(* XXX Generalize to the right type class *)
lemma Min_add_right:
  "Min S + (x :: int extended) = Min ((\<lambda> y. y + x) ` S)" (is "?A = ?B") if "finite S" "S \<noteq> {}"
proof -
  have "?A \<le> ?B"
    using that by (force intro: Min.boundedI add_right_mono)
  moreover have "?B \<le> ?A"
    using that by (force intro: Min.boundedI)
  ultimately show ?thesis
    by simp
qed

lemma OPT_0:
  "OPT 0 v = (if t = v then Fin 0 else \<infinity>)"
  unfolding OPT_def by simp

lemma OPT_Suc:
  "OPT (Suc i) v = min (OPT i v) (Min {OPT i w + Fin (W v w) | w. w \<le> n})" if "t \<le> n"
proof -
  have fin': "finite {xs. length xs \<le> i \<and> set xs \<subseteq> {0..n}}" for i
    by (auto intro: finite_subset[OF _ finite_lists_length_le[OF finite_atLeastAtMost]])
  have fin: "finite {Fin (weight (v # xs)) |xs. length xs \<le> i \<and> set xs \<subseteq> {0..n}}"
    for v i using [[simproc add: finite_Collect]] by (auto intro: finite_subset[OF _ fin'])
  have OPT_in: "OPT i v \<in>
    {Fin (weight (v # xs)) | xs. length xs + 1 \<le> i \<and> set xs \<subseteq> {0..n}} \<union>
    {if t = v then Fin 0 else \<infinity>}"
    if "i > 0" for i v
    using that unfolding OPT_def
    by - (rule Min_in, auto 4 3 intro: finite_subset[OF _ fin, of _ v "Suc i"])
  have le_1: "OPT i v \<ge> OPT (Suc i) v"
    unfolding OPT_def using fin by (auto 4 3 intro: Min_antimono)
  have subs:
    "(\<lambda>y. y + Fin (W v w)) ` {Fin (weight (w # xs)) |xs. length xs + 1 \<le> i \<and> set xs \<subseteq> {0..n}}
    \<subseteq> {Fin (weight (v # xs)) |xs. length xs + 1 \<le> Suc i \<and> set xs \<subseteq> {0..n}}" if \<open>w \<le> n\<close> for v w
    using \<open>w \<le> n\<close> apply clarify
    subgoal for _ _ xs
      by (rule exI[where x = "w # xs"]) auto
    done
  have "OPT i t + Fin (W v t) \<ge> OPT (Suc i) v"
    unfolding OPT_def using subs[OF \<open>t \<le> n\<close>, of v] that
    by (subst Min_add_right)
       (auto 4 3
         simp: Bellman_Ford.weight_single
         intro: exI[where x = "[]"] finite_subset[OF _ fin[of _ "Suc i"]] intro!: Min_antimono
       )
  moreover have "OPT i w + Fin (W v w) \<ge> OPT (Suc i) v" if "w \<le> n" \<open>w \<noteq> t\<close> \<open>t \<noteq> v\<close> for w
    unfolding OPT_def using subs[OF \<open>w \<le> n\<close>, of v] that
    by (subst Min_add_right)
       (auto 4 3 intro: finite_subset[OF _ fin[of _ "Suc i"]] intro!: Min_antimono)
  moreover have "OPT i w + Fin (W t w) \<ge> OPT (Suc i) t" if "w \<le> n" \<open>w \<noteq> t\<close> for w
    unfolding OPT_def
    apply (subst Min_add_right)
      prefer 3
    using \<open>w \<noteq> t\<close>
      apply simp
      apply (cases "i = 0")
       apply (simp; fail)
    using subs[OF \<open>w \<le> n\<close>, of t]
    by (subst (2) Min_insert)
       (auto 4 4
         intro: finite_subset[OF _ fin[of _ "Suc i"]] exI[where x = "[]"] intro!: Min_antimono
       )
  ultimately have le_2: "Min {local.OPT i w + Fin (W v w) |w. w \<le> n} \<ge> OPT (Suc i) v"
    by (auto intro!: Min.boundedI)
  from OPT_in[of "Suc i" v] consider
    "OPT (Suc i) v = \<infinity>" | "t = v" "OPT (Suc i) v = Fin 0" |
    xs where "OPT (Suc i) v = Fin (weight (v # xs))" "length xs \<le> i" "set xs \<subseteq> {0..n}"
    by (auto split: if_split_asm)
  then show ?thesis
  proof cases
    case 1
    with le_1 le_2 show ?thesis
      by (force intro: sym[OF Min_eqI])
  next
    case 2
    then have "OPT i v \<le> OPT (Suc i) v"
      unfolding OPT_def using [[simproc add: finite_Collect]]
      by (auto 4 4 intro: finite_subset[OF _ fin', of _ "Suc i"] intro!: Min_le)
    with le_1 le_2 show ?thesis
      by (auto intro: sym[OF min_absorb1])
  next
    case xs: 3
    note [simp] = xs(1)
    show ?thesis
    proof (cases "length xs = i")
      case True
      show ?thesis
      proof (cases "i = 0")
        case True
        with xs have "OPT (Suc i) v = Fin (W v t)"
          by simp
        also have "Fin (W v t) = OPT i t + Fin (W v t)"
          unfolding OPT_def using \<open>i = 0\<close> by auto
        also have "\<dots> \<ge> Min {OPT i w + Fin (W v w) |w. w \<le> n}"
          using \<open>t \<le> n\<close> by (auto intro: Min_le)
        finally show ?thesis
          using le_1 le_2 by clarsimp (rule min_absorb2 sym)+
      next
        case False
        with \<open>_ = i\<close> have "xs \<noteq> []"
          by auto
        with xs have "Fin (weight xs) \<ge> OPT i (hd xs)"
          unfolding OPT_def
          by (intro Min_le[rotated] UnI1 CollectI exI[where x = "tl xs"])
             (auto 4 3 intro: finite_subset[OF _ fin, of _ "hd xs" "Suc i"] dest: list.set_sel(2))
        have "Min {OPT i w + Fin (W v w) |w. w \<le> n} \<le> Fin (W v (hd xs)) + OPT i (hd xs)"
          using \<open>set xs \<subseteq> _\<close> \<open>xs \<noteq> []\<close> by (force simp: add.commute intro: Min_le)
        also have "\<dots> \<le> Fin (W v (hd xs) + weight xs)"
          using \<open>_ \<ge> OPT i (hd xs)\<close> by (metis add_left_mono plus_extended.simps(1))
        also from \<open>xs \<noteq> []\<close> have "\<dots> = OPT (Suc i) v"
          by (cases xs) auto
        finally show ?thesis
          using le_1 le_2 by clarsimp (rule min_absorb2 sym)+
      qed
    next
      case False
      with xs have "OPT i v \<le> OPT (Suc i) v"
        by (auto 4 4 intro: Min_le finite_subset[OF _ fin, of _ v "Suc i"] simp: OPT_def)
      with le_1 le_2 show ?thesis
        by (force intro: Min.boundedI sym[OF min_absorb1])
    qed
  qed
qed


fun bf :: "nat\<times>nat \<Rightarrow> int extended" where
  "bf (0, j) = (if t = j then Fin 0 else \<infinity>)"
| "bf (Suc k, j) =
    fold
      (min)
      (map
          (\<lambda>i. plus (Fin (W j i)) (bf (k, i)))
          (upt 0 (Suc n)))
      (bf (k, j))"
thm bf.simps
thm bf.induct

lemma bf_correct:
  "OPT i j = bf (i, j)" if \<open>t \<le> n\<close>
proof (induction i arbitrary: j)
  case 0
  then show ?case
    by (simp add: OPT_0)
next
  case (Suc i)
  have *:
    "{bf (i, w) + Fin (W j w) |w. w \<le> n} = set (map (\<lambda>w. Fin (W j w) + bf (i, w)) [0..<Suc n])"
    by (fastforce simp: add.commute image_def)
  from Suc \<open>t \<le> n\<close> show ?case
    by (simp add: OPT_Suc del: upt_Suc, subst Min.set_eq_fold[symmetric], auto simp: *)
qed


ML_file \<open>../scratch/Transform.ML\<close>
local_setup \<open>
lift_fun NONE
\<close>
print_theorems

interpretation bf: dp_consistency bf .

lemma "bf.consistentDP bf\<^sub>T"
  by (dp_match induct: bf\<^sub>T.crel_vs_induct simp: bf.simps simp\<^sub>T: bf\<^sub>T.simps)

end (* Final Node *)

end (* Bellman Ford *)

end (* Theory *)