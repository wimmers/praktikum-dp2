theory Memory
  imports "../DP_CRelVS"
begin

lemma lift_pI[intro?]:
  "lift_p P f" if "\<And> heap x heap'. P heap \<Longrightarrow> runState f heap = (x, heap') \<Longrightarrow> P heap'"
  unfolding lift_p_def by (auto intro: that)

lemma mem_correct_default:
  "mem_correct (\<lambda> k. do {m \<leftarrow> get; return (m k)}) (\<lambda> k v. do {m \<leftarrow> get; put (m(k\<mapsto>v))}) (\<lambda> _. True)"
  by standard
     (auto simp: map_le_def mem_defs.map_of_def bind_def get_def return_def put_def lift_p_def)

lemma mem_correct_rbt_mapping:
  "mem_correct
    (\<lambda> k. do {m \<leftarrow> get; return (Mapping.lookup m k)})
    (\<lambda> k v. do {m \<leftarrow> get; put (Mapping.update k v m)})
    (\<lambda> _. True)"
  by standard
     (auto simp:
        map_le_def mem_defs.map_of_def bind_def get_def return_def put_def lookup_update' lift_p_def
     )

datatype ('k, 'v) pair_storage = Pair_Storage 'k 'k 'v 'v

(* XXX Move *)
lemma map_add_mono:
  "(m1 ++ m2) \<subseteq>\<^sub>m (m1' ++ m2')" if "m1 \<subseteq>\<^sub>m m1'" "m2 \<subseteq>\<^sub>m m2'" "dom m1 \<inter> dom m2' = {}"
  using that unfolding map_le_def map_add_def dom_def by (auto split: option.splits)

lemma map_add_upd2:
  "f(x \<mapsto> y) ++ g = (f ++ g)(x \<mapsto> y)" if "dom f \<inter> dom g = {}" "x \<notin> dom g"
  apply (subst map_add_comm)
   defer
   apply simp
   apply (subst map_add_comm)
  using that
  by auto

locale mem_correct_empty = mem_correct +
  fixes empty
  assumes empty_correct: "map_of empty \<subseteq>\<^sub>m Map.empty" and P_empty: "P empty"

context mem_correct_empty
begin

context
  fixes key :: "'a \<Rightarrow> 'k"
begin

text \<open>We assume that look-ups happen on the older row, so it is biased towards the second entry.\<close>
definition
  "lookup_pair k =
    State (\<lambda> mem.
    (
      case mem of Pair_Storage k1 k2 m1 m2 \<Rightarrow> let k' = key k in
        if k' = k2 then case runState (lookup k) m2 of (v, m) \<Rightarrow> (v, Pair_Storage k1 k2 m1 m)
        else if k' = k1 then case runState (lookup k) m1 of (v, m) \<Rightarrow> (v, Pair_Storage k1 k2 m m2)
        else (None, mem)
    )
    )
  "

text \<open>We assume that updates happen on the newer row, so it is biased towards the first entry.\<close>
definition
  "update_pair k v =
    State (\<lambda> mem.
    (
      case mem of Pair_Storage k1 k2 m1 m2 \<Rightarrow> let k' = key k in
        if k' = k1 then case runState (update k v) m1 of (_, m) \<Rightarrow> ((), Pair_Storage k1 k2 m m2)
        else if k' = k2 then case runState (update k v) m2 of (_, m) \<Rightarrow> ((),Pair_Storage k1 k2 m1 m)
        else case runState (update k v) empty of (_, m) \<Rightarrow> ((), Pair_Storage k' k1 m m1)
    )
    )
  "

interpretation pair: mem_defs lookup_pair update_pair .

definition
  "inv_pair p = (case p of Pair_Storage k1 k2 m1 m2 \<Rightarrow>
    key ` dom (map_of m1) \<subseteq> {k1} \<and> key ` dom (map_of m2) \<subseteq> {k2} \<and> k1 \<noteq> k2 \<and> P m1 \<and> P m2
  )"

lemma map_of_le_pair:
  "pair.map_of (Pair_Storage k1 k2 m1 m2) \<subseteq>\<^sub>m (map_of m1 ++ map_of m2)"
  if "inv_pair (Pair_Storage k1 k2 m1 m2)"
  using that
  unfolding pair.map_of_def
  unfolding lookup_pair_def inv_pair_def map_of_def map_le_def dom_def map_add_def
  by (auto 4 6 split: prod.split_asm if_split_asm option.split simp: Let_def)

lemma pair_le_map_of:
  "map_of m1 ++ map_of m2 \<subseteq>\<^sub>m pair.map_of (Pair_Storage k1 k2 m1 m2)"
  if "inv_pair (Pair_Storage k1 k2 m1 m2)"
  using that
  unfolding pair.map_of_def
  unfolding lookup_pair_def inv_pair_def map_of_def map_le_def dom_def map_add_def
  by (auto 4 5 split: prod.split_asm if_split_asm option.split simp: Let_def)

lemma map_of_eq_pair:
  "map_of m1 ++ map_of m2 = pair.map_of (Pair_Storage k1 k2 m1 m2)"
  if "inv_pair (Pair_Storage k1 k2 m1 m2)"
  using that
  unfolding pair.map_of_def
  unfolding lookup_pair_def inv_pair_def map_of_def map_le_def dom_def map_add_def
  by (auto 4 7 split: prod.split_asm if_split_asm option.split simp: Let_def)

lemma inv_pair_neq[simp, dest]:
  False if "inv_pair (Pair_Storage k k x y)"
  using that unfolding inv_pair_def by auto

lemma inv_pair_P_D1:
  "P m1" if "inv_pair (Pair_Storage k1 k2 m1 m2)"
  using that unfolding inv_pair_def by auto

lemma inv_pair_P_D2:
  "P m2" if "inv_pair (Pair_Storage k1 k2 m1 m2)"
  using that unfolding inv_pair_def by auto

lemma inv_pair_domD[intro]:
  "dom (map_of m1) \<inter> dom (map_of m2) = {}" if "inv_pair (Pair_Storage k1 k2 m1 m2)"
  using that unfolding inv_pair_def by fastforce

lemma dom_empty[simp]:
  "dom (map_of empty) = {}"
  using empty_correct by (auto dest: map_le_implies_dom_le)

lemma
  "mem_correct lookup_pair update_pair inv_pair"
proof (standard, goal_cases)
  case (1 k) -- "Lookup invariant"
  with lookup_inv[of k] show ?case
    unfolding lookup_pair_def Let_def
    by (auto intro!: lift_pI split: pair_storage.split_asm if_split_asm prod.split_asm)
       (auto dest: lift_p_P simp: inv_pair_def,
         (force dest!: lookup_correct[of _ k] map_le_implies_dom_le)+
       )
next
  case (2 k v) -- "Update invariant"
  with update_inv[of k v] update_correct[OF P_empty, of k v] P_empty show ?case
    unfolding update_pair_def Let_def
    by (auto intro!: lift_pI split: pair_storage.split_asm if_split_asm prod.split_asm)
       (auto dest: lift_p_P simp: inv_pair_def,
         (force dest: lift_p_P dest!: update_correct[of _ k v] map_le_implies_dom_le)+
       )
next
  case (3 m k)
  {
    fix m1 v1 m1' m2 v2 m2' k1 k2
    assume assms:
      "runState (lookup k) m1 = (v1, m1')" "runState (lookup k) m2 = (v2, m2')"
      "inv_pair (Pair_Storage k1 k2 m1 m2)"
    from assms have "P m1" "P m2"
      by (auto intro: inv_pair_P_D1 inv_pair_P_D2)
    have [intro]: "map_of m1' \<subseteq>\<^sub>m map_of m1" "map_of m2' \<subseteq>\<^sub>m map_of m2"
      using lookup_correct[OF \<open>P m1\<close>, of k] lookup_correct[OF \<open>P m2\<close>, of k] assms by auto
    from inv_pair_domD[OF assms(3)] have 1: "dom (map_of m1') \<inter> dom (map_of m2) = {}"
      by (metis (no_types) \<open>map_of m1' \<subseteq>\<^sub>m map_of m1\<close> disjoint_iff_not_equal domIff map_le_def)
    have inv1: "inv_pair (Pair_Storage (key k) k2 m1' m2)" if "k2 \<noteq> key k" "k1 = key k"
      using that \<open>P m1\<close> \<open>P m2\<close> unfolding inv_pair_def
      apply clarsimp
      apply safe
      subgoal for x' y
        using assms(1,3) lookup_correct[OF \<open>P m1\<close>, of k, THEN map_le_implies_dom_le]
        unfolding inv_pair_def by auto
      subgoal for x' y
        using assms(3) unfolding inv_pair_def by fastforce
      using lookup_inv[of k] assms unfolding lift_p_def by force
    have inv2: "inv_pair (Pair_Storage k1 (key k) m1 m2')" if "k2 = key k" "k1 \<noteq> key k"
      using that \<open>P m1\<close> \<open>P m2\<close> unfolding inv_pair_def
      apply clarsimp
      apply safe
      subgoal for x' y
        using assms(3) unfolding inv_pair_def by fastforce
      subgoal for x x' y
        using assms(2,3) lookup_correct[OF \<open>P m2\<close>, of k, THEN map_le_implies_dom_le]
        unfolding inv_pair_def by fastforce
      using lookup_inv[of k] assms unfolding lift_p_def by force
    have A:
      "pair.map_of (Pair_Storage (key k) k2 m1' m2) \<subseteq>\<^sub>m pair.map_of (Pair_Storage (key k) k2 m1 m2)"
      if "k2 \<noteq> key k" "k1 = key k"
      using inv1 assms(3) 1
      by (auto intro: map_add_mono map_le_refl simp: that map_of_eq_pair[symmetric])
    have B:
      "pair.map_of (Pair_Storage k1 (key k) m1 m2') \<subseteq>\<^sub>m pair.map_of (Pair_Storage k1 (key k) m1 m2)"
      if "k2 = key k" "k1 \<noteq> key k"
      using inv2 assms(3) that
      by (auto intro: map_add_mono map_le_refl simp: map_of_eq_pair[symmetric] dest: inv_pair_domD)
    note A B
  }
  with \<open>inv_pair m\<close> show ?case
    by (auto split: pair_storage.split if_split prod.split simp: Let_def lookup_pair_def)
next
  case (4 m k v)
  {
    fix m1 v1 m1' m2 v2 m2' m3 k1 k2
    assume assms:
      "runState (update k v) m1 = ((), m1')" "runState (update k v) m2 = ((), m2')"
      "runState (update k v) empty = ((), m3)"
      "inv_pair (Pair_Storage k1 k2 m1 m2)"
    from assms have "P m1" "P m2"
      by (auto intro: inv_pair_P_D1 inv_pair_P_D2)
    from assms(3) P_empty update_inv[of k v] have "P m3"
      unfolding lift_p_def by auto
    have [intro]: "map_of m1' \<subseteq>\<^sub>m map_of m1(k \<mapsto> v)" "map_of m2' \<subseteq>\<^sub>m map_of m2(k \<mapsto> v)"
      using update_correct[OF \<open>P m1\<close>, of k v] update_correct[OF \<open>P m2\<close>, of k v] assms by auto
    have "map_of m3 \<subseteq>\<^sub>m map_of empty(k \<mapsto> v)"
      using assms(3) update_correct[OF P_empty, of k v] by auto
    also have "\<dots> \<subseteq>\<^sub>m map_of m2(k \<mapsto> v)"
      using empty_correct by (auto elim: map_le_trans intro!: map_le_upd)
    finally have "map_of m3 \<subseteq>\<^sub>m map_of m2(k \<mapsto> v)" .
    have 1: "dom (map_of m1) \<inter> dom (map_of m2(k \<mapsto> v)) = {}" if "k1 \<noteq> key k"
      using assms(4) that by (force simp: inv_pair_def)
    have 2: "dom (map_of m3) \<inter> dom (map_of m1) = {}" if "k1 \<noteq> key k"
      using \<open>local.map_of m3 \<subseteq>\<^sub>m local.map_of empty(k \<mapsto> v)\<close> assms(4) that
      by (fastforce dest!: map_le_implies_dom_le simp: inv_pair_def)
    have inv: "inv_pair (Pair_Storage (key k) k1 m3 m1)" if "k2 \<noteq> key k" "k1 \<noteq> key k"
      using that \<open>P m1\<close> \<open>P m2\<close> \<open>P m3\<close> unfolding inv_pair_def
      apply clarsimp
      apply safe
      subgoal for x x' y
        using assms(3) update_correct[OF P_empty, of k v, THEN map_le_implies_dom_le]
          empty_correct
        by (auto dest: map_le_implies_dom_le)
      subgoal for x x' y
        using assms(4) unfolding inv_pair_def by fastforce
      done
    have A:
      "pair.map_of (Pair_Storage (key k) k1 m3 m1) \<subseteq>\<^sub>m pair.map_of (Pair_Storage k1 k2 m1 m2)(k \<mapsto> v)"
      if "k2 \<noteq> key k" "k1 \<noteq> key k"
      using inv assms(4) \<open>map_of m3 \<subseteq>\<^sub>m map_of m2(k \<mapsto> v)\<close> 1
      apply (simp add: that map_of_eq_pair[symmetric])
      apply (subst map_add_upd[symmetric], subst Map.map_add_comm, rule 2, rule that)
      by (rule map_add_mono; auto)
    have inv1: "inv_pair (Pair_Storage (key k) k2 m1' m2)" if "k2 \<noteq> key k" "k1 = key k"
      using that \<open>P m1\<close> \<open>P m2\<close> unfolding inv_pair_def
      apply clarsimp
      apply safe
      subgoal for x' y
        using assms(1,4) update_correct[OF \<open>P m1\<close>, of k v, THEN map_le_implies_dom_le]
        unfolding inv_pair_def by auto
      subgoal for x' y
        using assms(4) unfolding inv_pair_def by fastforce
      using update_inv[of k v] assms unfolding lift_p_def by force
    have inv2: "inv_pair (Pair_Storage k1 (key k) m1 m2')" if "k2 = key k" "k1 \<noteq> key k"
      using that \<open>P m1\<close> \<open>P m2\<close> unfolding inv_pair_def
      apply clarsimp
      apply safe
      subgoal for x' y
        using assms(4) unfolding inv_pair_def by fastforce
      subgoal for x x' y
        using assms(2,4) update_correct[OF \<open>P m2\<close>, of k v, THEN map_le_implies_dom_le]
        unfolding inv_pair_def by fastforce
      using update_inv[of k v] assms unfolding lift_p_def by force
    have C:
      "pair.map_of (Pair_Storage (key k) k2 m1' m2) \<subseteq>\<^sub>m
       pair.map_of (Pair_Storage (key k) k2 m1 m2)(k \<mapsto> v)"
      if "k2 \<noteq> key k" "k1 = key k"
      using inv1[OF that] assms(4) \<open>inv_pair m\<close>
      by (simp add: that map_of_eq_pair[symmetric])
         (subst map_add_upd2[symmetric]; force simp: inv_pair_def intro: map_add_mono map_le_refl)
    have B:
      "pair.map_of (Pair_Storage k1 (key k) m1 m2') \<subseteq>\<^sub>m
       pair.map_of (Pair_Storage k1 (key k) m1 m2)(k \<mapsto> v)"
      if "k2 = key k" "k1 \<noteq> key k"
      using inv2[OF that] assms(4)
      by (simp add: that map_of_eq_pair[symmetric])
         (subst map_add_upd[symmetric]; rule map_add_mono; force simp: inv_pair_def)
    note A B C
  }
  with \<open>inv_pair m\<close> show ?case
    by (auto split: pair_storage.split if_split prod.split simp: Let_def update_pair_def)
qed

end (* Key function *)

end (* Lookup & Update w/ Empty *)

lemma mem_correct_empty_default:
  "mem_correct_empty
    (\<lambda> k. do {m \<leftarrow> get; return (m k)}) (\<lambda> k v. do {m \<leftarrow> get; put (m(k\<mapsto>v))}) (\<lambda> _. True) Map.empty"
  by (intro mem_correct_empty.intro[OF mem_correct_default] mem_correct_empty_axioms.intro)
     (auto simp: mem_defs.map_of_def map_le_def bind_def get_def return_def)

lemma mem_correct_rbt_empty_mapping:
  "mem_correct_empty
    (\<lambda> k. do {m \<leftarrow> get; return (Mapping.lookup m k)})
    (\<lambda> k v. do {m \<leftarrow> get; put (Mapping.update k v m)})
    (\<lambda> _. True)
    Mapping.empty"
  by (intro mem_correct_empty.intro[OF mem_correct_rbt_mapping] mem_correct_empty_axioms.intro)
     (auto simp: mem_defs.map_of_def map_le_def bind_def get_def return_def lookup_empty)

locale dp_consistency_default =
  fixes dp :: "'param \<Rightarrow> 'result"
begin

sublocale dp_consistency
  "\<lambda> k. do {m \<leftarrow> get; return (m k)}" "\<lambda> k v. do {m \<leftarrow> get; put (m(k\<mapsto>v))}" "\<lambda> _. True" dp
  by (intro dp_consistency.intro mem_correct_default)

sublocale rbt: dp_consistency
  "\<lambda> k. do {m \<leftarrow> get; return (Mapping.lookup m k)}"
  "\<lambda> k v. do {m \<leftarrow> get; put (Mapping.update k v m)}" "\<lambda> _. True" dp
  by (intro dp_consistency.intro mem_correct_rbt_mapping)

end (* DP Consistency Default *)

end (* Theory *)