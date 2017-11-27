theory Bellman_Ford
  imports "../DP_Lifting" "../DP_CRelVS" "../DP_Proof" "HOL-Library.Extended" "TA_Impl.TA_Impl_Misc"
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
  "OPT (Suc i) v = min (OPT i v) (Min {OPT i w + Fin (W v w) | w. w \<le> n})" (is "?lhs = ?rhs")
  if "t \<le> n"
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

  have "OPT i v \<ge> OPT (Suc i) v"
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
  ultimately have "Min {local.OPT i w + Fin (W v w) |w. w \<le> n} \<ge> OPT (Suc i) v"
    by (auto intro!: Min.boundedI)
  with \<open>OPT i v \<ge> _\<close> have "?lhs \<le> ?rhs"
    by simp

  from OPT_in[of "Suc i" v] consider
    "OPT (Suc i) v = \<infinity>" | "t = v" "OPT (Suc i) v = Fin 0" |
    xs where "OPT (Suc i) v = Fin (weight (v # xs))" "length xs \<le> i" "set xs \<subseteq> {0..n}"
    by (auto split: if_split_asm)
  then have "?lhs \<ge> ?rhs"
  proof cases
    case 1
    then show ?thesis
      by simp
  next
    case 2
    then have "OPT i v \<le> OPT (Suc i) v"
      unfolding OPT_def using [[simproc add: finite_Collect]]
      by (auto 4 4 intro: finite_subset[OF _ fin', of _ "Suc i"] intro!: Min_le)
    then show ?thesis
      by (rule min.coboundedI1)
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
          by (rule min.coboundedI2)
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
          by (rule min.coboundedI2)
      qed
    next
      case False
      with xs have "OPT i v \<le> OPT (Suc i) v"
        by (auto 4 4 intro: Min_le finite_subset[OF _ fin, of _ v "Suc i"] simp: OPT_def)
      then show ?thesis
        by (rule min.coboundedI1)
    qed
  qed
  with \<open>?lhs \<le> ?rhs\<close> show ?thesis
    by (rule order.antisym)
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


fun bf_path :: "nat \<times> nat \<Rightarrow> int extended \<times> nat option" where
  "bf_path (0, j) = (if t = j then Fin 0 else \<infinity>, None)"
| "bf_path (Suc k, j) =
    fold
      (\<lambda> (v, i) (v', i'). if v \<le> v' then (v, i) else (v', i'))
      (map
          (\<lambda>i. (plus (Fin (W j i)) (fst(bf_path (k, i))), Some i))
          (upt 0 (Suc n)))
      (fst (bf_path (k, j)), None)"

local_setup \<open>
lift_fun NONE
\<close>
print_theorems

interpretation bf_path: dp_consistency bf_path .

lemma "bf_path.consistentDP bf_path\<^sub>T"
  by (dp_match induct: bf_path\<^sub>T.crel_vs_induct simp: bf_path.simps simp\<^sub>T: bf_path\<^sub>T.simps)

definition extract_path :: "nat \<Rightarrow> (nat \<times> nat \<Rightarrow> nat option) \<Rightarrow> nat \<Rightarrow> nat list" where
  "extract_path bound mem i =
    rev (snd (
      fold
      (\<lambda> j (v, xs). case mem (j, v) of None \<Rightarrow> (v, xs) | Some i \<Rightarrow> (i, v # xs)) (rev [1..<Suc bound])
      (i, [])
    ))"

lemma extract_path_inner_append:
  "snd (fold (\<lambda> j (v, xs).
    case mem (j, v) of None \<Rightarrow> (v, xs) | Some i \<Rightarrow> (i, v # xs)) (rev [1..<bound]) (i, ys)) @ xs
  = snd (fold (\<lambda> j (v, xs).
    case mem (j, v) of None \<Rightarrow> (v, xs) | Some i \<Rightarrow> (i, v # xs)) (rev [1..<bound]) (i, ys @ xs))"
  by (induction bound arbitrary: i ys) (auto split: option.split)

lemma hd_extract_path:
  "hd (extract_path i mem v) = v" if "extract_path i mem v \<noteq> []"
proof -
  define f where "f \<equiv> (\<lambda> j (v, xs). case mem (j, v) of None \<Rightarrow> (v, xs) | Some i \<Rightarrow> (i, v # xs))"
  have
    "(\<exists> as. snd (fold f (rev [1..<bound]) (v, ys)) = as @ v # ys)
    \<or> snd (fold f (rev [1..<bound]) (v, ys)) = ys" for bound ys
  proof (induction bound arbitrary: v ys)
    case 0
    then show ?case
      by simp
  next
    case (Suc bound)
    then show ?case
      apply simp
      apply (subst (2) f_def)
      apply (clarsimp split: option.split, safe)
      subgoal
       by (force simp: f_def)
      subgoal premises prems for x
        using prems(1) [of x "v # ys"] by fastforce
      done
  qed
  from that this[of "Suc i" "[]"] show ?thesis
    unfolding extract_path_def f_def[symmetric] by auto
qed

lemma weight_empty[simp]: "weight [] = 0"
  unfolding weight_def by simp

lemma fold_neq_startD:
  "\<exists> acc'. \<exists> x \<in> set xs. fold f xs acc = f x acc'" if "fold f xs acc \<noteq> acc"
  using that by (induction xs arbitrary: acc; force)

lemma bf_pathD:
  assumes "bf_path (Suc i, v) \<noteq> (fst (bf_path (i, v)), None)"
  obtains w where "bf_path (Suc i, v) = (Fin (W v w) + fst (bf_path (i, w)), Some w)"
proof -
  {
    fix i v k
    define xs where "xs b = (map (\<lambda>k. (Fin (W v k) + fst (bf_path (i, k)), Some k)) [0..<b])" for b
    define f where
      "f = (\<lambda>(v :: int extended, i :: nat option) (v', i'). if v \<le> v' then (v, i) else (v', i'))"
    have xs_Suc: "xs (Suc b) = xs b @ [(Fin (W v b) + fst (bf_path (i, b)), Some b)]" for b
      unfolding xs_def by simp
    have *: "f a b = a \<or> f a b = b" for a b
      unfolding f_def by (auto split: prod.split_asm)
    then have f_split: "P (f a b) \<longleftrightarrow> (f a b = a \<longrightarrow> P a) \<and> (f a b = b \<longrightarrow> P b)" for P a b
      by metis
    assume "fold f (xs k) (fst (bf_path (i, v)), None) \<noteq>
    (fst (bf_path (i, v)), None)"
    then have
      "\<exists> w. fold f (xs k) (fst (bf_path (i, v)), None) = (Fin (W v w) + fst (bf_path (i, w)), Some w)"
      apply (induction k)
       apply (simp add: xs_def; fail)
      by (subst f_split) (auto simp: xs_Suc)
  } note * = this
  show ?thesis
    using assms by (simp only: bf_path.simps) (drule *, auto intro: that)
qed  

lemma extract_path_empty:
  "bf_path (i, v) = bf_path (0, v)" if "extract_path i (snd o bf_path) v = []"
  using that
proof (induction i arbitrary: v)
  case 0
  then show ?case
    by simp
next
  case (Suc i)
  show ?case
  proof (cases "bf_path (Suc i, v) = (fst (bf_path (i, v)), None)")
    case True
    then have "extract_path (Suc i) (snd \<circ> bf_path) v = extract_path i (snd o bf_path) v"
      unfolding extract_path_def by simp
    with Suc show ?thesis
      by (simp only: True, simp)
  next
    case False
    then obtain w where "bf_path (Suc i, v) = (Fin (W v w) + fst (bf_path (i, w)), Some w)"
      by (fastforce elim: bf_pathD)
    then have "extract_path (Suc i) (snd \<circ> bf_path) v \<noteq> []"
      unfolding extract_path_def
      by (simp del: bf_path.simps) (rule fold_acc_preserv, auto split: option.split prod.split)
    with Suc.prems show ?thesis
      by metis
  qed
qed

lemma bf_path_bf[simp]:
  "fst (bf_path (i, v)) = bf (i, v)"
  apply (induction i arbitrary: v)
   apply simp
  apply (simp only: bf_path.simps bf.simps)
  subgoal premises prems for i v
  proof -
    define f1 where
      "f1 \<equiv> \<lambda>(v :: int extended, i :: nat option) (v', i'). if v \<le> v' then (v, i) else (v', i')"
    define f2 where "f2 \<equiv> \<lambda>ia. (Fin (W v ia) + bf (i, ia), Some ia)"
    define f3 where "f3 \<equiv> \<lambda>ia. Fin (W v ia) + bf (i, ia)"
    have [simp]: "fst (f2 i) = f3 i" for i
      unfolding f2_def f3_def by simp
    have [simp]: "fst (f1 a b) = min (fst a) (fst b)" for a b
      unfolding f1_def min_def by (auto split: prod.split)
    have "fst (fold f1 (map f2 [0..<Suc n]) (bf (i, v), None)) =
           fold min (map f3 [0..<Suc n]) (bf (i, v))" for i v n
      by (induction n; simp)
    then show ?thesis
      by (simp add: f1_def f2_def f3_def)
  qed
  done

lemma extract_path_empty':
  "bf (i, v) = bf (0, v)" if "extract_path i (snd o bf_path) v = []"
  by (subst bf_path_bf[symmetric]) (simp add: extract_path_empty[OF that])

lemma extract_path_correct:
  "Fin (weight (extract_path i (snd o bf_path) v)) = bf (i, v)" if "bf (i, v) \<noteq> \<infinity>"
  using that
proof (induction i arbitrary: v)
case 0
  then show ?case
    unfolding extract_path_def by (simp split: if_split_asm)
next
  case (Suc i)
  show ?case
  proof (cases "bf_path (Suc i, v) = (bf (i, v), None)")
    case True
    then have "bf (Suc i, v) = bf (i, v)"
      using bf_path_bf[of "Suc i" v] by (simp del: bf_path.simps bf.simps)
    moreover with Suc.prems have "bf (i, v) \<noteq> \<infinity>"
      by auto
    moreover from True have
      "extract_path (Suc i) (snd \<circ> bf_path) v = extract_path i (snd o bf_path) v"
      unfolding extract_path_def by simp
    ultimately show ?thesis
      by (auto dest: Suc.IH simp only:)
  next
    case False
    then obtain w where "bf_path (Suc i, v) = (Fin (W v w) + bf (i, w), Some w)"
      using bf_pathD by auto
    then have
      "extract_path (Suc i) (snd \<circ> bf_path) v = v # extract_path i (snd o bf_path) w"
      unfolding extract_path_def
      by (auto simp del: bf_path.simps bf.simps split: option.split)
         (subst extract_path_inner_append[simplified], simp)+
    moreover from \<open>bf_path _ = _\<close> Suc.prems have "bf (Suc i, v) = Fin (W v w) + bf (i, w)"
      using bf_path_bf[of "Suc i" v] by (simp del: bf_path.simps bf.simps)
    moreover with Suc.prems have "bf (i, w) \<noteq> \<infinity>"
      by auto
    moreover have
      "weight (v # extract_path i (snd \<circ> bf_path) w) =
        (if extract_path i (snd \<circ> bf_path) w = []
         then W v t else W v w + weight (extract_path i (snd \<circ> bf_path) w)
        )"
      using hd_extract_path[of i "snd \<circ> bf_path" w]
      by (cases "extract_path i (snd \<circ> bf_path) w"; simp add: hd_extract_path)
    ultimately show ?thesis
      apply -
      apply (drule Suc.IH)
      apply (simp only: weight_Cons split: if_split)
      apply (rule conjI)
      apply (auto simp: extract_path_empty'; fail)
       apply (auto simp only: plus_extended.simps(1)[symmetric]; fail)
      done
  qed
qed

definition extract_path' :: "nat \<Rightarrow> (nat \<times> nat \<rightharpoonup> nat option) \<Rightarrow> nat \<Rightarrow> nat list option" where
  "extract_path' bound mem i =
    map_option (rev o snd) (
      fold
      (\<lambda> j acc.
        case acc of
          None \<Rightarrow> None |
          Some (v, xs) \<Rightarrow> case mem (j,v) of
            None \<Rightarrow> None |
            Some None \<Rightarrow> Some (v, xs) |
            Some (Some i) \<Rightarrow> Some (i, v # xs)) (rev [1..<Suc bound]
      )
      (Some (i, []))
    )"

lemma
  "extract_path i (snd \<circ> bf_path) v = xs"
  if "extract_path' i (map_option snd o m) v = Some xs" "bf_path.cmem m"
proof -
  define f1 where
    "f1 \<equiv> (\<lambda> j (v, xs). case (snd \<circ> bf_path) (j, v) of None \<Rightarrow> (v, xs) | Some i \<Rightarrow> (i, v # xs))"
  define f2 where "f2 \<equiv>
    (\<lambda> j acc.
        case acc of
          None \<Rightarrow> None |
          Some (v, xs) \<Rightarrow> case (map_option snd o m) (j,v) of
            None \<Rightarrow> None |
            Some None \<Rightarrow> Some (v, xs) |
            Some (Some i) \<Rightarrow> Some (i, v # xs)
      )
  "
  have f2_f1: "f1 j acc = acc'" if "f2 j (Some acc) = Some acc'" for j acc acc'
    using that \<open>bf_path.cmem m\<close>
    by (auto simp: f1_def f2_def split: option.splits prod.splits elim: bf_path.cmem_elim)
  have [simp]: "f2 j None = None" for j
    unfolding f2_def by auto
  have [simp]: "fold f2 xs None = None" for xs
    by (induction xs; simp)

  have "rev (snd (fold f1 (rev [1..<Suc i]) acc)) = xs"
    if "map_option (rev \<circ> snd) (fold f2 (rev [1..<Suc i]) (Some acc)) = Some xs" "bf_path.cmem m"
    for acc
    using that
    apply (induction i arbitrary: acc xs)
     apply (simp; fail)
    apply clarsimp
    subgoal for i a b a' b'
      by (cases "f2 (Suc i) (Some (a, b))"; fastforce dest: f2_f1)
    done
  with that show ?thesis
    unfolding extract_path_def extract_path'_def f1_def[symmetric] f2_def[symmetric] by simp
qed

end (* Final Node *)

end (* Bellman Ford *)

end (* Theory *)