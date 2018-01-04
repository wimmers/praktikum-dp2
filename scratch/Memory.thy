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


(*
locale mem_correct_empty = mem_correct +
  fixes empty
  assumes empty_correct: "map_of empty \<subseteq>\<^sub>m Map.empty" and P_empty: "P empty"

context mem_correct_empty
begin
*)

locale pair_mem_defs =
  fixes lookup1 lookup2 :: "'a =='mem \<Longrightarrow> 'v option"
    and update1 update2 :: "'a \<Rightarrow> 'v =='mem \<Longrightarrow> unit"
    and move12 :: "'k1 \<Rightarrow> ('mem, unit) state"
    and get_k1 get_k2 :: "('mem, 'k1) state"
    and P :: "'mem \<Rightarrow> bool"
  fixes key1 :: "'k \<Rightarrow> 'k1" and key2 :: "'k \<Rightarrow> 'a"
begin

text \<open>We assume that look-ups happen on the older row, so it is biased towards the second entry.\<close>
definition
  "lookup_pair k = do {
     let k' = key1 k;
     k2 \<leftarrow> get_k2;
     if k' = k2
     then lookup2 (key2 k)
     else do {
       k1 \<leftarrow> get_k1;
       if k' = k1
       then lookup1 (key2 k)
       else return None
     }
   }
   "

text \<open>We assume that updates happen on the newer row, so it is biased towards the first entry.\<close>
definition
  "update_pair k v = do {
    let k' = key1 k;
    k1 \<leftarrow> get_k1;
    if k' = k1
    then update1 (key2 k) v
    else do {
      k2 \<leftarrow> get_k2;
      if k' = k2
      then update2 (key2 k) v
      else (move12 k' \<then> update1 (key2 k) v)
    }
  }
  "

sublocale pair: mem_defs lookup_pair update_pair .

sublocale mem1: mem_defs lookup1 update1 .

sublocale mem2: mem_defs lookup2 update2 .

definition
  "inv_pair heap \<equiv>
    let
      k1 = fst (runState get_k1 heap);
      k2 = fst (runState get_k2 heap)
    in
    (\<forall> k \<in> dom (mem1.map_of heap). \<exists> k'. key1 k' = k1 \<and> key2 k' = k) \<and>
    (\<forall> k \<in> dom (mem2.map_of heap). \<exists> k'. key1 k' = k2 \<and> key2 k' = k) \<and>
    k1 \<noteq> k2 \<and> P heap
  "

definition
  "map_of1 m k = (if key1 k = fst (runState get_k1 m) then mem1.map_of m (key2 k) else None)"

definition
  "map_of2 m k = (if key1 k = fst (runState get_k2 m) then mem2.map_of m (key2 k) else None)"

end (* Pair Mem Defs *)

locale pair_mem = pair_mem_defs +
  assumes get_state:
    "runState get_k1 m = (k, m') \<Longrightarrow> m' = m"
    "runState get_k2 m = (k, m') \<Longrightarrow> m' = m"
  assumes move12_correct:
    "P m \<Longrightarrow> runState (move12 k1) m = (x, m') \<Longrightarrow> mem1.map_of m' \<subseteq>\<^sub>m Map.empty"
    "P m \<Longrightarrow> runState (move12 k1) m = (x, m') \<Longrightarrow> mem2.map_of m' \<subseteq>\<^sub>m mem1.map_of m"
  assumes move12_keys:
    "runState (move12 k1) m = (x, m') \<Longrightarrow> fst (runState get_k1 m') = k1"
    "runState (move12 k1) m = (x, m') \<Longrightarrow> fst (runState get_k2 m') = fst (runState get_k1 m)"
  assumes move12_inv:
    "lift_p P (move12 k1)"
  assumes lookup_inv:
    "lift_p P (lookup1 k')" "lift_p P (lookup2 k')"
  assumes update_inv:
    "lift_p P (update1 k' v)" "lift_p P (update2 k' v)"
  assumes lookup_keys:
    "P m \<Longrightarrow> runState (lookup1 k') m = (v', m') \<Longrightarrow>
     fst (runState get_k1 m') = fst (runState get_k1 m)"
    "P m \<Longrightarrow> runState (lookup1 k') m = (v', m') \<Longrightarrow>
     fst (runState get_k2 m') = fst (runState get_k2 m)"
    "P m \<Longrightarrow> runState (lookup2 k') m = (v', m') \<Longrightarrow>
     fst (runState get_k1 m') = fst (runState get_k1 m)"
    "P m \<Longrightarrow> runState (lookup2 k') m = (v', m') \<Longrightarrow>
     fst (runState get_k2 m') = fst (runState get_k2 m)"
  assumes update_keys:
    "P m \<Longrightarrow> runState (update1 k' v) m = (x, m') \<Longrightarrow>
     fst (runState get_k1 m') = fst (runState get_k1 m)"
    "P m \<Longrightarrow> runState (update1 k' v) m = (x, m') \<Longrightarrow>
     fst (runState get_k2 m') = fst (runState get_k2 m)"
    "P m \<Longrightarrow> runState (update2 k' v) m = (x, m') \<Longrightarrow>
     fst (runState get_k1 m') = fst (runState get_k1 m)"
    "P m \<Longrightarrow> runState (update2 k' v) m = (x, m') \<Longrightarrow>
     fst (runState get_k2 m') = fst (runState get_k2 m)"
  assumes
    lookup_correct:
      "P m \<Longrightarrow> mem1.map_of (snd (runState (lookup1 k') m)) \<subseteq>\<^sub>m (mem1.map_of m)"
      "P m \<Longrightarrow> mem2.map_of (snd (runState (lookup1 k') m)) \<subseteq>\<^sub>m (mem2.map_of m)"
      "P m \<Longrightarrow> mem1.map_of (snd (runState (lookup2 k') m)) \<subseteq>\<^sub>m (mem1.map_of m)"
      "P m \<Longrightarrow> mem2.map_of (snd (runState (lookup2 k') m)) \<subseteq>\<^sub>m (mem2.map_of m)"
  assumes
    update_correct:
      "P m \<Longrightarrow> mem1.map_of (snd (runState (update1 k' v) m)) \<subseteq>\<^sub>m (mem1.map_of m)(k' \<mapsto> v)"
      "P m \<Longrightarrow> mem2.map_of (snd (runState (update2 k' v) m)) \<subseteq>\<^sub>m (mem2.map_of m)(k' \<mapsto> v)"
      "P m \<Longrightarrow> mem2.map_of (snd (runState (update1 k' v) m)) \<subseteq>\<^sub>m mem2.map_of m"
      "P m \<Longrightarrow> mem1.map_of (snd (runState (update2 k' v) m)) \<subseteq>\<^sub>m mem1.map_of m"
begin

lemma map_of_le_pair:
  "pair.map_of m \<subseteq>\<^sub>m map_of1 m ++ map_of2 m"
  if "inv_pair m"
  using that
  unfolding pair.map_of_def map_of1_def map_of2_def
  unfolding lookup_pair_def inv_pair_def map_of_def map_le_def dom_def map_add_def
  unfolding bind_def
  by (auto 4 4
        simp: mem2.map_of_def mem1.map_of_def runState_return Let_def
        dest: get_state split: prod.split_asm if_split_asm
     )

lemma pair_le_map_of:
  "map_of1 m ++ map_of2 m \<subseteq>\<^sub>m pair.map_of m"
  if "inv_pair m"
  using that
  unfolding pair.map_of_def map_of1_def map_of2_def
  unfolding lookup_pair_def inv_pair_def map_of_def map_le_def dom_def map_add_def
  unfolding bind_def
  by (auto
        simp: mem2.map_of_def mem1.map_of_def runState_return Let_def
        dest: get_state split: prod.splits if_split_asm option.split
     )

lemma map_of_eq_pair:
  "map_of1 m ++ map_of2 m = pair.map_of m"
  if "inv_pair m"
  using that
  unfolding pair.map_of_def map_of1_def map_of2_def
  unfolding lookup_pair_def inv_pair_def map_of_def map_le_def dom_def map_add_def
  unfolding bind_def
  by (auto 4 4
        simp: mem2.map_of_def mem1.map_of_def runState_return Let_def
        dest: get_state split: prod.splits option.split
     )

lemma inv_pair_neq[simp]:
  False if "inv_pair m" "fst (runState get_k1 m) = fst (runState get_k2 m)"
  using that unfolding inv_pair_def by auto

lemma inv_pair_P_D:
  "P m" if "inv_pair m"
  using that unfolding inv_pair_def by (auto simp: Let_def)

lemma inv_pair_domD[intro]:
  "dom (map_of1 m) \<inter> dom (map_of2 m) = {}" if "inv_pair m"
  using that unfolding inv_pair_def map_of1_def map_of2_def by (auto split: if_split_asm)

lemma move12_correct1:
  "map_of1 heap' \<subseteq>\<^sub>m Map.empty" if "runState (move12 k1) heap = (x, heap')" "P heap"
  using move12_correct[OF that(2,1)] unfolding map_of1_def by (auto simp: move12_keys map_le_def)

lemma move12_correct2:
  "map_of2 heap' \<subseteq>\<^sub>m map_of1 heap" if "runState (move12 k1) heap = (x, heap')" "P heap"
  using move12_correct(2)[OF that(2,1)] that unfolding map_of1_def map_of2_def
  by (auto simp: move12_keys map_le_def)

lemma dom_empty[simp]:
  "dom (map_of1 heap') = {}" if "runState (move12 k1) heap = (x, heap')" "P heap"
  using move12_correct1[OF that] by (auto dest: map_le_implies_dom_le)

lemma inv_pair_lookup1:
  "inv_pair m'" if "runState (lookup1 k) m = (v, m')" "inv_pair m"
  using that lookup_inv[of k] inv_pair_P_D[OF \<open>inv_pair m\<close>] unfolding inv_pair_def
  by (auto 4 4
        simp: Let_def lookup_keys
        dest: lift_p_P lookup_correct[of _ k, THEN map_le_implies_dom_le]
     )

lemma inv_pair_lookup2:
  "inv_pair m'" if "runState (lookup2 k) m = (v, m')" "inv_pair m"
  using that lookup_inv[of k] inv_pair_P_D[OF \<open>inv_pair m\<close>] unfolding inv_pair_def
  by (auto 4 4
        simp: Let_def lookup_keys
        dest: lift_p_P lookup_correct[of _ k, THEN map_le_implies_dom_le]
     )

lemma inv_pair_update1:
  "inv_pair m'"
  if "runState (update1 (key2 k) v) m = (v', m')" "inv_pair m" "fst (runState get_k1 m) = key1 k"
  using that update_inv[of "key2 k" v] inv_pair_P_D[OF \<open>inv_pair m\<close>] unfolding inv_pair_def
  apply (auto
        simp: Let_def update_keys
        dest: lift_p_P update_correct[of _ "key2 k" v, THEN map_le_implies_dom_le]
     )
   apply (frule update_correct[of _ "key2 k" v, THEN map_le_implies_dom_le]; auto 13 2; fail)
  apply (frule update_correct[of _ "key2 k" v, THEN map_le_implies_dom_le]; auto 13 2; fail)
  done

lemma inv_pair_update2:
  "inv_pair m'"
  if "runState (update2 (key2 k) v) m = (v', m')" "inv_pair m" "fst (runState get_k2 m) = key1 k"
  using that update_inv[of "key2 k" v] inv_pair_P_D[OF \<open>inv_pair m\<close>] unfolding inv_pair_def
  apply (auto
        simp: Let_def update_keys
        dest: lift_p_P update_correct[of _ "key2 k" v, THEN map_le_implies_dom_le]
     )
   apply (frule update_correct[of _ "key2 k" v, THEN map_le_implies_dom_le]; auto 13 2; fail)
  apply (frule update_correct[of _ "key2 k" v, THEN map_le_implies_dom_le]; auto 13 2; fail)
  done

lemma inv_pair_move12:
  "inv_pair m'"
  if "runState (move12 (key1 k)) m = (v', m')" "inv_pair m" "fst (runState get_k1 m) \<noteq> key1 k"
  using that move12_inv[of "key1 k"] inv_pair_P_D[OF \<open>inv_pair m\<close>] unfolding inv_pair_def
  apply (auto
        simp: Let_def move12_keys
        dest: lift_p_P move12_correct[of _ "key1 k", THEN map_le_implies_dom_le]
     )
  apply (blast dest: move12_correct[of _ "key1 k", THEN map_le_implies_dom_le])
  done

lemma mem_correct_pair:
  "mem_correct lookup_pair update_pair inv_pair"
  if injective: "\<forall> k k'. key1 k = key1 k' \<and> key2 k = key2 k' \<longrightarrow> k = k'"
proof (standard, goal_cases)
  case (1 k) -- "Lookup invariant"
  show ?case
    unfolding lookup_pair_def Let_def
    by (auto 4 4
        intro!: lift_pI
        dest: get_state inv_pair_lookup1 inv_pair_lookup2
        simp: bind_def runState_return
        split: pair_storage.split_asm if_split_asm prod.split_asm
        )
next
  case (2 k v) -- "Update invariant"
  show ?case
    unfolding update_pair_def Let_def
    apply (auto 4 4
        intro!: lift_pI intro: inv_pair_update1 inv_pair_update2
        dest: get_state
        simp: bind_def get_state runState_return
        split: pair_storage.split_asm if_split_asm prod.split_asm
        )+
    apply (elim inv_pair_update1 inv_pair_move12)
      apply (((subst get_state, assumption)+)?, auto intro: move12_keys dest: get_state; fail)+
    done
next
  case (3 m k)
  {
    let ?m = "snd (runState (lookup2 (key2 k)) m)"
    have "map_of1 ?m \<subseteq>\<^sub>m map_of1 m"
      by (smt 3 domIff inv_pair_P_D local.lookup_keys lookup_correct map_le_def map_of1_def surjective_pairing)
    moreover have "map_of2 ?m \<subseteq>\<^sub>m map_of2 m"
      by (smt 3 domIff inv_pair_P_D local.lookup_keys lookup_correct map_le_def map_of2_def surjective_pairing)
    moreover have "dom (map_of1 ?m) \<inter> dom (map_of2 m) = {}"
      using 3 \<open>map_of1 ?m \<subseteq>\<^sub>m map_of1 m\<close> inv_pair_domD map_le_implies_dom_le by fastforce
    moreover have "inv_pair ?m"
      using 3 inv_pair_lookup2 surjective_pairing by metis
    ultimately have "pair.map_of ?m \<subseteq>\<^sub>m pair.map_of m"
      apply (subst map_of_eq_pair[symmetric])
       defer
       apply (subst map_of_eq_pair[symmetric])
      by (auto intro: 3 map_add_mono)
  }
  moreover
  {
    let ?m = "snd (runState (lookup1 (key2 k)) m)"
    have "map_of1 ?m \<subseteq>\<^sub>m map_of1 m"
      by (smt 3 domIff inv_pair_P_D local.lookup_keys lookup_correct map_le_def map_of1_def surjective_pairing)
    moreover have "map_of2 ?m \<subseteq>\<^sub>m map_of2 m"
      by (smt 3 domIff inv_pair_P_D local.lookup_keys lookup_correct map_le_def map_of2_def surjective_pairing)
    moreover have "dom (map_of1 ?m) \<inter> dom (map_of2 m) = {}"
      using 3 \<open>map_of1 ?m \<subseteq>\<^sub>m map_of1 m\<close> inv_pair_domD map_le_implies_dom_le by fastforce
    moreover have "inv_pair ?m"
      using 3 inv_pair_lookup1 surjective_pairing by metis
    ultimately have "pair.map_of ?m \<subseteq>\<^sub>m pair.map_of m"
      apply (subst map_of_eq_pair[symmetric])
       defer
       apply (subst map_of_eq_pair[symmetric])
      by (auto intro: 3 map_add_mono)
  }
  ultimately show ?case
    by (auto
        split:if_split prod.split
        simp: Let_def lookup_pair_def bind_def runState_return dest: get_state intro: map_le_refl
        )
next
  case prems: (4 m k v)
  let ?m1 = "snd (runState (update1 (key2 k) v) m)"
  let ?m2 = "snd (runState (update2 (key2 k) v) m)"
  from prems have disjoint: "dom (map_of1 m) \<inter> dom (map_of2 m) = {}"
    by (simp add: inv_pair_domD)
  show ?case
    apply (auto
        intro: map_le_refl dest: get_state
        split: pair_storage.split if_split prod.split
        simp: Let_def update_pair_def bind_def runState_return
        )
  proof goal_cases
    case (1 m')
    then have "m' = m"
      by (rule get_state)
    from 1 prems have "map_of1 ?m1 \<subseteq>\<^sub>m map_of1 m(k \<mapsto> v)"
      by (smt inv_pair_P_D map_le_def map_of1_def surjective_pairing domIff
          fst_conv fun_upd_apply injective update_correct update_keys
          )
    moreover from prems have "map_of2 ?m1 \<subseteq>\<^sub>m map_of2 m"
      by (smt domIff inv_pair_P_D update_correct update_keys map_le_def map_of2_def surjective_pairing)
    moreover from prems have "dom (map_of1 ?m1) \<inter> dom (map_of2 m) = {}"
      by (smt inv_pair_P_D[OF \<open>inv_pair m\<close>] domIff Int_emptyI eq_snd_iff inv_pair_neq 
          map_of1_def map_of2_def update_keys(1)
          )
    moreover from 1 prems have "k \<notin> dom (map_of2 m)"
      using inv_pair_neq map_of2_def by fastforce
    moreover from 1 prems have "inv_pair ?m1"
      using inv_pair_update1 fst_conv surjective_pairing by metis
    ultimately show "pair.map_of (snd (runState (update1 (key2 k) v) m')) \<subseteq>\<^sub>m pair.map_of m(k \<mapsto> v)"
      unfolding \<open>m' = m\<close> using disjoint
      apply (subst map_of_eq_pair[symmetric])
       defer
       apply (subst map_of_eq_pair[symmetric], rule prems)
       apply (subst map_add_upd2[symmetric])
      by (auto intro: map_add_mono)
  next
    case (2 k1 m' m'')
    then have "m' = m" "m'' = m"
      by (auto dest: get_state)
    from 2 prems have "map_of2 ?m2 \<subseteq>\<^sub>m map_of2 m(k \<mapsto> v)"
      unfolding \<open>m' = m\<close> \<open>m'' = m\<close>
      by (smt inv_pair_P_D map_le_def map_of2_def surjective_pairing domIff
          fst_conv fun_upd_apply injective update_correct update_keys
          )
    moreover from prems have "map_of1 ?m2 \<subseteq>\<^sub>m map_of1 m"
      by (smt domIff inv_pair_P_D update_correct update_keys map_le_def map_of1_def surjective_pairing)
    moreover from 2 have "dom (map_of1 ?m2) \<inter> dom (map_of2 m(k \<mapsto> v)) = {}"
      unfolding \<open>m' = m\<close>
      by (smt domIff \<open>map_of1 ?m2 \<subseteq>\<^sub>m map_of1 m\<close> disjoint_iff_not_equal fst_conv fun_upd_apply
          map_le_def map_of1_def map_of2_def
          )
    moreover from 2 prems have "inv_pair ?m2"
      unfolding \<open>m' = m\<close>
      using inv_pair_update2 fst_conv surjective_pairing by metis
    ultimately show "pair.map_of (snd (runState (update2 (key2 k) v) m'')) \<subseteq>\<^sub>m pair.map_of m(k \<mapsto> v)"
      unfolding \<open>m' = m\<close> \<open>m'' = m\<close>
      apply (subst map_of_eq_pair[symmetric])
       defer
       apply (subst map_of_eq_pair[symmetric], rule prems)
       apply (subst map_add_upd[symmetric])
      by (rule map_add_mono)
  next
    case (3 k1 m1 k2 m2 m3)
    then have "m1 = m" "m2 = m"
      by (auto dest: get_state)
    let ?m3 = "snd (runState (update1 (key2 k) v) m3)"
    from 3 prems have "map_of1 ?m3 \<subseteq>\<^sub>m map_of2 m(k \<mapsto> v)"
      unfolding \<open>m2 = m\<close>
      by (smt inv_pair_P_D map_le_def map_of1_def surjective_pairing domIff
          fst_conv fun_upd_apply injective
          inv_pair_move12 move12_correct move12_keys update_correct update_keys
          )
    moreover have "map_of2 ?m3 \<subseteq>\<^sub>m map_of1 m"
    proof -
      from prems 3 have "P m" "P m3"
        unfolding \<open>m1 = m\<close> \<open>m2 = m\<close>
        using inv_pair_P_D[OF prems] by (auto elim: lift_p_P[OF move12_inv])
      from 3(3)[unfolded \<open>m2 = m\<close>] have "mem2.map_of ?m3 \<subseteq>\<^sub>m mem1.map_of m"
        by - (erule map_le_trans[OF update_correct(3)[OF \<open>P m3\<close>] move12_correct(2)[OF \<open>P m\<close>]])
      with 3 prems show ?thesis
        unfolding \<open>m1 = m\<close> \<open>m2 = m\<close> map_le_def map_of2_def
        apply auto
        apply (frule move12_keys(2), simp)
        by (metis
            domI inv_pair_def map_of1_def surjective_pairing
            inv_pair_move12 move12_keys(2) update_keys(2)
            )
    qed
    moreover from prems 3 have "dom (map_of1 ?m3) \<inter> dom (map_of1 m) = {}"
      unfolding \<open>m1 = m\<close> \<open>m2 = m\<close>
      by (smt inv_pair_P_D disjoint_iff_not_equal map_of1_def surjective_pairing domIff
          fst_conv inv_pair_move12 move12_keys update_keys
          )
    moreover from 3 have "k \<notin> dom (map_of1 m)"
      by (simp add: domIff map_of1_def)
    moreover from 3 prems have "inv_pair ?m3"
      unfolding \<open>m2 = m\<close>
      by (metis inv_pair_move12 inv_pair_update1 move12_keys(1) fst_conv surjective_pairing)
    ultimately show ?case
      unfolding \<open>m1 = m\<close> \<open>m2 = m\<close> using disjoint
      apply (subst map_of_eq_pair[symmetric])
       defer
       apply (subst map_of_eq_pair[symmetric])
        apply (rule prems)
       apply (subst (2) map_add_comm)
        defer
        apply (subst map_add_upd2[symmetric])
          apply (auto intro: map_add_mono)
      done
  qed
qed

end (* Pair Mem *)


locale mem_correct_empty = mem_correct +
  fixes empty
  assumes empty_correct: "map_of empty \<subseteq>\<^sub>m Map.empty" and P_empty: "P empty"

context mem_correct_empty
begin

context
  fixes key1 :: "'k \<Rightarrow> 'k1" and key2 :: "'k \<Rightarrow> 'a"
begin

text \<open>We assume that look-ups happen on the older row, so it is biased towards the second entry.\<close>
definition
  "lookup_pair k =
    State (\<lambda> mem.
    (
      case mem of Pair_Storage k1 k2 m1 m2 \<Rightarrow> let k' = key1 k in
        if k' = k2 then case runState (lookup (key2 k)) m2 of (v, m) \<Rightarrow> (v, Pair_Storage k1 k2 m1 m)
        else if k' = k1 then case runState (lookup (key2 k)) m1 of (v, m)
          \<Rightarrow> (v, Pair_Storage k1 k2 m m2)
        else (None, mem)
    )
    )
  "

text \<open>We assume that updates happen on the newer row, so it is biased towards the first entry.\<close>
definition
  "update_pair k v =
    State (\<lambda> mem.
    (
      case mem of Pair_Storage k1 k2 m1 m2 \<Rightarrow> let k' = key1 k in
        if k' = k1 then case runState (update (key2 k) v) m1 of (_, m)
          \<Rightarrow> ((), Pair_Storage k1 k2 m m2)
        else if k' = k2 then case runState (update (key2 k) v) m2 of (_, m)
          \<Rightarrow> ((),Pair_Storage k1 k2 m1 m)
        else case runState (update (key2 k) v) empty of (_, m) \<Rightarrow> ((), Pair_Storage k' k1 m m1)
    )
    )
  "

interpretation pair: mem_defs lookup_pair update_pair .

definition
  "inv_pair p = (case p of Pair_Storage k1 k2 m1 m2 \<Rightarrow>
    (\<forall> k \<in> dom (map_of m1). \<exists> k'. key1 k' = k1 \<and> key2 k' = k) \<and>
    (\<forall> k \<in> dom (map_of m2). \<exists> k'. key1 k' = k2 \<and> key2 k' = k) \<and>
    k1 \<noteq> k2 \<and> P m1 \<and> P m2
  )"

definition
  "inv_pair_weak p = (case p of Pair_Storage k1 k2 m1 m2 \<Rightarrow>
    P m1 \<and> P m2
  )"

definition
  "map_of' m k1 k = (if key1 k = k1 then map_of m (key2 k) else None)"

lemma map_of_le_pair:
  "pair.map_of (Pair_Storage k1 k2 m1 m2) \<subseteq>\<^sub>m map_of' m1 k1 ++ map_of' m2 k2"
  if "inv_pair (Pair_Storage k1 k2 m1 m2)"
  using that
  unfolding pair.map_of_def map_of'_def
  unfolding lookup_pair_def inv_pair_def map_of_def map_le_def dom_def map_add_def
  by (auto split: prod.split_asm if_split_asm option.split simp: Let_def)

lemma pair_le_map_of:
  "map_of' m1 k1 ++ map_of' m2 k2 \<subseteq>\<^sub>m pair.map_of (Pair_Storage k1 k2 m1 m2)"
  if "inv_pair (Pair_Storage k1 k2 m1 m2)"
  using that
  unfolding pair.map_of_def map_of'_def
  unfolding lookup_pair_def inv_pair_def map_of_def map_le_def dom_def map_add_def
  by (auto split: prod.splits if_split_asm option.split simp: Let_def)

lemma map_of_eq_pair:
  "map_of' m1 k1 ++ map_of' m2 k2 = pair.map_of (Pair_Storage k1 k2 m1 m2)"
  if "inv_pair (Pair_Storage k1 k2 m1 m2)"
  using that
  unfolding pair.map_of_def map_of'_def
  unfolding lookup_pair_def inv_pair_def map_of_def map_le_def dom_def map_add_def
  by (auto split: prod.splits if_split_asm option.split simp: Let_def)

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
  "dom (map_of' m1 k1) \<inter> dom (map_of' m2 k2) = {}" if "inv_pair (Pair_Storage k1 k2 m1 m2)"
  using that unfolding inv_pair_def map_of'_def by (auto split: if_split_asm)

lemma dom_empty[simp]:
  "dom (map_of empty) = {}"
  using empty_correct by (auto dest: map_le_implies_dom_le)

(* Unused *)
lemma dom_unequal_keys:
  "dom (map_of' m1 k1) \<inter> dom (map_of' m2 k2) = {}" if "k1 \<noteq> k2"
  using that unfolding map_of'_def by (auto split: if_split_asm)

definition
  "lookup1 k \<equiv> State (\<lambda> mem.
    case mem of Pair_Storage k1 k2 m1 m2 \<Rightarrow>
      case runState (lookup k) m1 of (v, m) \<Rightarrow> (v, Pair_Storage k1 k2 m m2))"

definition
  "lookup2 k \<equiv> State (\<lambda> mem.
    case mem of Pair_Storage k1 k2 m1 m2 \<Rightarrow>
      case runState (lookup k) m2 of (v, m) \<Rightarrow> (v, Pair_Storage k1 k2 m1 m))"

definition
  "update1 k v \<equiv> State (\<lambda> mem.
    case mem of Pair_Storage k1 k2 m1 m2 \<Rightarrow>
      case runState (update k v) m1 of (_, m) \<Rightarrow> ((), Pair_Storage k1 k2 m m2))"

definition
  "update2 k v \<equiv> State (\<lambda> mem.
    case mem of Pair_Storage k1 k2 m1 m2 \<Rightarrow>
      case runState (update k v) m2 of (_, m) \<Rightarrow> ((), Pair_Storage k1 k2 m1 m))"

definition
  "move12 k \<equiv> State (\<lambda> mem. case mem of Pair_Storage k1 k2 m1 m2 \<Rightarrow> ((), Pair_Storage k k1 empty m1))"

definition
  "get_k1 \<equiv> State (\<lambda> mem. case mem of Pair_Storage k1 k2 m1 m2 \<Rightarrow> (k1, mem))"

definition
  "get_k2 \<equiv> State (\<lambda> mem. case mem of Pair_Storage k1 k2 m1 m2 \<Rightarrow> (k2, mem))"

lemma map_of_lookup1[simp]:
  "mem_defs.map_of lookup1 (Pair_Storage k1 k2 m1 m2) = map_of m1"
  unfolding mem_defs.map_of_def lookup1_def by (auto split: prod.split)

lemma map_of_lookup2[simp]:
  "mem_defs.map_of lookup2 (Pair_Storage k1 k2 m1 m2) = map_of m2"
  unfolding mem_defs.map_of_def lookup2_def by (auto split: prod.split)

lemma inv_pair_weakD1:
  "P m1" if "inv_pair_weak (Pair_Storage k1 k2 m1 m2)"
  using that unfolding inv_pair_weak_def by auto

lemma inv_pair_weakD2:
  "P m2" if "inv_pair_weak (Pair_Storage k1 k2 m1 m2)"
  using that unfolding inv_pair_weak_def by auto

lemma lookup_correct':
  "P m \<Longrightarrow> runState (lookup k) m = (v, m') \<Longrightarrow> map_of m' \<subseteq>\<^sub>m (map_of m)"
  using lookup_correct[of m k] by auto

lemma update_correct':
  "P m \<Longrightarrow> runState (update k v) m = (v', m') \<Longrightarrow> map_of m' \<subseteq>\<^sub>m (map_of m)(k \<mapsto> v)"
  using update_correct[of m k v] by auto

lemma pair_mem: "pair_mem lookup1 lookup2 update1 update2 move12 get_k1 get_k2 inv_pair_weak"
  apply standard
                      apply (auto split: pair_storage.splits simp: empty_correct get_k1_def get_k2_def move12_def; fail)+
                      apply (auto intro!: lift_pI simp: inv_pair_weak_def move12_def P_empty lookup1_def lookup2_def update1_def update2_def split: pair_storage.splits prod.split_asm elim: lift_p_P[OF lookup_inv] lift_p_P[OF update_inv]; fail)+
                 apply (auto split: pair_storage.split prod.split_asm simp: update1_def update2_def lookup1_def lookup2_def get_k1_def get_k2_def; fail)+
  by (auto elim: update_correct' lookup_correct' dest: inv_pair_weakD1 inv_pair_weakD2 split: pair_storage.split prod.split simp: update1_def update2_def lookup1_def lookup2_def; fail)+

interpretation pair: pair_mem lookup1 lookup2 update1 update2 move12 get_k1 get_k2 inv_pair_weak
  by (rule pair_mem)

lemma lookup_pair_alt_def:
  "lookup_pair = pair.lookup_pair"
  unfolding pair.lookup_pair_def lookup_pair_def
  by (intro ext)
     (auto
       split: pair_storage.split prod.split
       simp: lookup1_def lookup2_def bind_def runState_return Let_def get_k1_def get_k2_def
     )

lemma update_pair_alt_def:
  "update_pair = pair.update_pair"
  unfolding pair.update_pair_def update_pair_def
  by (intro ext)
     (auto
       split: pair_storage.split prod.split
       simp:
        move12_def lookup1_def lookup2_def update1_def update2_def bind_def runState_return
        Let_def get_k1_def get_k2_def
     )

lemma mem_correct_pair:
  "mem_correct lookup_pair update_pair inv_pair"
  if injective: "\<forall> k k'. key1 k = key1 k' \<and> key2 k = key2 k' \<longrightarrow> k = k'"
proof (standard, goal_cases)
  case (1 k) -- "Lookup invariant"
  with lookup_inv[of "key2 k"] show ?case
    unfolding lookup_pair_def Let_def
    by (auto intro!: lift_pI split: pair_storage.split_asm if_split_asm prod.split_asm)
       (auto dest: lift_p_P simp: inv_pair_def,
        auto 4 3 dest!: map_le_implies_dom_le lookup_correct[of _ "key2 k"]
       )
next
  case (2 k v) -- "Update invariant"
  with update_inv[of "key2 k" v] update_correct[OF P_empty, of "key2 k" v] P_empty show ?case
    unfolding update_pair_def Let_def
    by (auto intro!: lift_pI split: pair_storage.split_asm if_split_asm prod.split_asm)
       (auto dest: lift_p_P simp: inv_pair_def,
        (force dest!: map_le_implies_dom_le update_correct[of _ "key2 k" v])+
       )
next
  case (3 m k)
  {
    fix m1 v1 m1' m2 v2 m2' k1 k2
    assume assms:
      "runState (lookup (key2 k)) m1 = (v1, m1')" "runState (lookup (key2 k)) m2 = (v2, m2')"
      "inv_pair (Pair_Storage k1 k2 m1 m2)"
    from assms have "P m1" "P m2"
      by (auto intro: inv_pair_P_D1 inv_pair_P_D2)
    have "map_of m1' \<subseteq>\<^sub>m map_of m1" "map_of m2' \<subseteq>\<^sub>m map_of m2"
      using lookup_correct[OF \<open>P m1\<close>, of "key2 k"] lookup_correct[OF \<open>P m2\<close>, of "key2 k"] assms
      by auto
    then have  "map_of' m1' k1 \<subseteq>\<^sub>m map_of' m1 k1" "map_of' m2' k2 \<subseteq>\<^sub>m map_of' m2 k2"
      unfolding map_of'_def map_le_def by auto
    from inv_pair_domD[OF assms(3)] have 1: "dom (map_of' m1' k1) \<inter> dom (map_of' m2 k2) = {}"
      by (metis (no_types) \<open>map_of' m1' k1 \<subseteq>\<^sub>m map_of' m1 k1\<close> disjoint_iff_not_equal domIff map_le_def)
    have inv1: "inv_pair (Pair_Storage (key1 k) k2 m1' m2)" if "k2 \<noteq> key1 k" "k1 = key1 k"
      using that \<open>P m1\<close> \<open>P m2\<close> unfolding inv_pair_def
      apply clarsimp
      apply safe
      subgoal for x' y
        using assms(1,3) lookup_correct[OF \<open>P m1\<close>, of "key2 k", THEN map_le_implies_dom_le]
        unfolding inv_pair_def by auto
      subgoal for x' y
        using assms(3) unfolding inv_pair_def by fastforce
      using lookup_inv[of "key2 k"] assms unfolding lift_p_def by force
    have inv2: "inv_pair (Pair_Storage k1 (key1 k) m1 m2')" if "k2 = key1 k" "k1 \<noteq> key1 k"
      using that \<open>P m1\<close> \<open>P m2\<close> unfolding inv_pair_def
      apply clarsimp
      apply safe
      subgoal for x' y
        using assms(3) unfolding inv_pair_def by fastforce
      subgoal for x x'
        using assms(2,3) lookup_correct[OF \<open>P m2\<close>, of "key2 k", THEN map_le_implies_dom_le]
        unfolding inv_pair_def by (auto 7 2)
      using lookup_inv[of "key2 k"] assms unfolding lift_p_def by force
    have A:
      "pair.map_of (Pair_Storage (key1 k) k2 m1' m2) \<subseteq>\<^sub>m
       pair.map_of (Pair_Storage (key1 k) k2 m1 m2)"
      if "k2 \<noteq> key1 k" "k1 = key1 k"
      using inv1 assms(3) 1 \<open>map_of' m1' k1 \<subseteq>\<^sub>m map_of' m1 k1\<close>
      by (auto intro: map_add_mono map_le_refl simp: that map_of_eq_pair[symmetric])
    have B:
      "pair.map_of (Pair_Storage k1 (key1 k) m1 m2') \<subseteq>\<^sub>m pair.map_of (Pair_Storage k1 (key1 k) m1 m2)"
      if "k2 = key1 k" "k1 \<noteq> key1 k"
      using inv2 assms(3) that \<open>map_of' m2' k2 \<subseteq>\<^sub>m map_of' m2 k2\<close>
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
      "runState (update (key2 k) v) m1 = ((), m1')" "runState (update (key2 k) v) m2 = ((), m2')"
      "runState (update (key2 k) v) empty = ((), m3)"
      "inv_pair (Pair_Storage k1 k2 m1 m2)"
    from assms have "P m1" "P m2"
      by (auto intro: inv_pair_P_D1 inv_pair_P_D2)
    from assms(3) P_empty update_inv[of "key2 k" v] have "P m3"
      unfolding lift_p_def by auto
    have "map_of m1' \<subseteq>\<^sub>m map_of m1(key2 k \<mapsto> v)" "map_of m2' \<subseteq>\<^sub>m map_of m2(key2 k \<mapsto> v)"
      using update_correct[OF \<open>P m1\<close>, of "key2 k" v] update_correct[OF \<open>P m2\<close>, of "key2 k" v] assms
      by auto
    with injective have [intro]:
      "map_of' m1' (key1 k) \<subseteq>\<^sub>m map_of' m1 (key1 k)(k \<mapsto> v)"
      "map_of' m2' (key1 k) \<subseteq>\<^sub>m map_of' m2 (key1 k)(k \<mapsto> v)"
      unfolding map_of'_def map_le_def by (fastforce split: if_split_asm)+
    have "map_of m3 \<subseteq>\<^sub>m map_of empty(key2 k \<mapsto> v)"
      using assms(3) update_correct[OF P_empty, of "key2 k" v] by auto
    also have "\<dots> \<subseteq>\<^sub>m map_of m2(key2 k \<mapsto> v)"
      using empty_correct by (auto elim: map_le_trans intro!: map_le_upd)
    finally have "map_of m3 \<subseteq>\<^sub>m map_of m2(key2 k \<mapsto> v)" .
    from \<open>map_of m3 \<subseteq>\<^sub>m map_of empty(key2 k \<mapsto> v)\<close> have *: "k' = key2 k"
      if "map_of m3 k' = Some v'" for k' v'
      using that dom_empty unfolding map_le_def by (fastforce split: if_split_asm)
    from \<open>map_of m3 \<subseteq>\<^sub>m map_of empty(key2 k \<mapsto> v)\<close> have **: "v' = v"
      if "map_of m3 k' = Some v'" for k' v'
      using *[OF that] that unfolding map_le_def by (fastforce split: if_split_asm)
    have "map_of' m3 (key1 k) \<subseteq>\<^sub>m (map_of' empty (key1 k))(k \<mapsto> v)"
      unfolding map_of'_def map_le_def by (auto simp: injective * **)
    also have "\<dots> \<subseteq>\<^sub>m map_of' m2 k2(k \<mapsto> v)" if "k2 \<noteq> key1 k"
      using that unfolding map_of'_def map_le_def apply auto
      using dom_empty by blast
    finally have m3_le: "map_of' m3 (key1 k) \<subseteq>\<^sub>m map_of' m2 k2(k \<mapsto> v)" if "k2 \<noteq> key1 k" using that .
    have inv: "inv_pair (Pair_Storage (key1 k) k1 m3 m1)" if "k2 \<noteq> key1 k" "k1 \<noteq> key1 k"
      using that \<open>P m1\<close> \<open>P m2\<close> \<open>P m3\<close> unfolding inv_pair_def
      apply clarsimp
      apply safe
      subgoal for x x'
        using assms(3) update_correct[OF P_empty, of "key2 k" v, THEN map_le_implies_dom_le]
          empty_correct
        by (auto dest: map_le_implies_dom_le)
      subgoal for x x'
        using assms(4) unfolding inv_pair_def by fastforce
      done
    have A:
      "pair.map_of (Pair_Storage (key1 k) k1 m3 m1) \<subseteq>\<^sub>m pair.map_of (Pair_Storage k1 k2 m1 m2)(k \<mapsto> v)"
      if "k2 \<noteq> key1 k" "k1 \<noteq> key1 k"
      using inv assms(4) m3_le
      apply (simp add: that map_of_eq_pair[symmetric])
      apply (subst map_add_upd[symmetric])
      apply (subst Map.map_add_comm)
      subgoal
        using that unfolding map_of'_def by (auto split: if_split_asm)
      apply (rule map_add_mono)
        apply auto[]
      subgoal
        using that
        unfolding map_of'_def map_le_def by (auto split: if_split_asm)
      subgoal
        using that unfolding map_of'_def by (auto split: if_split_asm)
      done
    have inv1: "inv_pair (Pair_Storage (key1 k) k2 m1' m2)" if "k2 \<noteq> key1 k" "k1 = key1 k"
      using that \<open>P m1\<close> \<open>P m2\<close> unfolding inv_pair_def
      apply clarsimp
      apply safe
      subgoal for x' y
        using assms(1,4) update_correct[OF \<open>P m1\<close>, of "key2 k" v, THEN map_le_implies_dom_le]
        unfolding inv_pair_def by auto
      subgoal for x' y
        using assms(4) unfolding inv_pair_def by fastforce
      using update_inv[of "key2 k" v] assms unfolding lift_p_def by force
    have inv2: "inv_pair (Pair_Storage k1 (key1 k) m1 m2')" if "k2 = key1 k" "k1 \<noteq> key1 k"
      using that \<open>P m1\<close> \<open>P m2\<close> unfolding inv_pair_def
      apply clarsimp
      apply safe
      subgoal for x' y
        using assms(4) unfolding inv_pair_def by fastforce
      subgoal for x x'
        using assms(2,4) update_correct[OF \<open>P m2\<close>, of "key2 k" v, THEN map_le_implies_dom_le]
        unfolding inv_pair_def by (auto 7 2)
      using update_inv[of "key2 k" v] assms unfolding lift_p_def by force
    have C:
      "pair.map_of (Pair_Storage (key1 k) k2 m1' m2) \<subseteq>\<^sub>m
       pair.map_of (Pair_Storage (key1 k) k2 m1 m2)(k \<mapsto> v)"
      if "k2 \<noteq> key1 k" "k1 = key1 k"
      using inv1[OF that] assms(4)
      by (simp add: that map_of_eq_pair[symmetric]; subst map_add_upd2[symmetric])
         (use that in \<open>auto split: if_split_asm simp: map_of'_def intro: map_add_mono\<close>)
    have B:
      "pair.map_of (Pair_Storage k1 (key1 k) m1 m2') \<subseteq>\<^sub>m
       pair.map_of (Pair_Storage k1 (key1 k) m1 m2)(k \<mapsto> v)"
      if "k2 = key1 k" "k1 \<noteq> key1 k"
      using inv2[OF that] assms(4) \<open>inv_pair m\<close>
      by (simp add: that map_of_eq_pair[symmetric]; subst map_add_upd[symmetric])
         (rule map_add_mono; use that in \<open>auto split: if_split_asm simp: map_of'_def\<close>)
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