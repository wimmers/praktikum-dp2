theory Memory_Heap
  imports State_Heap Memory
begin

instance array :: (heap) heap ..

context
  fixes size :: nat
    and to_index :: "('k2 :: heap) \<Rightarrow> nat"
begin

definition
  "mem_empty = (Array.new size (None :: ('v :: heap) option))"

context
  fixes mem :: "('v :: heap) option array"
begin

definition
  "mem_lookup k = (let i = to_index k in
    if i < size then Array.nth mem i else return None
  )"

definition
  "mem_update k v = (let i = to_index k in
    if i < size then (Array.upd i (Some v) mem \<bind> (\<lambda> _. return ()))
    else return ()
  )
  "

definition
  "P heap = (Array.length heap mem = size)"

context assumes injective: "\<forall> a b. to_index a = to_index b \<and> to_index b < size \<longrightarrow> a = b"
begin

lemma mem_heap_correct: "heap_correct P mem_update mem_lookup"
  apply standard
  subgoal lookup_inv
    unfolding State_Heap.lift_p_def P_def mem_lookup_def by (simp add: Let_def execute_simps)
  subgoal update_inv
    unfolding State_Heap.lift_p_def P_def mem_update_def by (simp add: Let_def execute_simps)
  subgoal for k heap
    unfolding heap_mem_defs.map_of_heap_def map_le_def mem_lookup_def
    by (auto simp: execute_simps P_def Let_def split: if_split_asm)
  subgoal for heap k
    unfolding heap_mem_defs.map_of_heap_def map_le_def mem_lookup_def mem_update_def
    apply (auto simp: execute_simps P_def Let_def length_def split: if_split_asm)
    apply (subst (asm) nth_list_update_neq)
    using injective apply auto
    done
  done

end (* Injectivity *)

end (* Fixed array *)

context
  fixes key1 :: "'k \<Rightarrow> ('k1 :: heap)" and key2 :: "'k \<Rightarrow> 'k2"
    and m_ref1 m_ref2 :: "('v :: heap) option array ref"
    and k_ref1 k_ref2 :: "('k1 :: heap) ref"
begin

text \<open>We assume that look-ups happen on the older row, so this is biased towards the second entry.\<close>
definition
  "lookup_pair k = (
    let k' = key1 k in
      (
      !k_ref2 \<bind> (\<lambda> k2.
      if k' = k2 then
        !m_ref2 \<bind> (\<lambda> m2. mem_lookup m2 (key2 k))
      else
        !k_ref1 \<bind> (\<lambda> k1.
        if k' = k1 then
          !m_ref1 \<bind> (\<lambda> m1. mem_lookup m1 (key2 k))
        else
          return None))
      )
      )
   "

text \<open>We assume that updates happen on the newer row, so this is biased towards the first entry.\<close>
definition
  "update_pair k v = (
    let k' = key1 k in
      (
      Heap_Monad.bind (!k_ref1) (\<lambda> k1.
      if k' = k1 then
        Heap_Monad.bind (!m_ref1) (\<lambda> m. mem_update m (key2 k) v)
      else
        Heap_Monad.bind (!k_ref2) (\<lambda> k2.
        if k' = k2 then
          Heap_Monad.bind (!m_ref2) (\<lambda> m. mem_update m (key2 k) v)
        else
          Heap_Monad.bind (!k_ref1) (\<lambda> k1.
            Heap_Monad.bind mem_empty (\<lambda> m.
              Heap_Monad.bind (!m_ref1) (\<lambda> m1.
                k_ref2 := k1 \<then> k_ref1 := k' \<then> m_ref2 := m1 \<then> m_ref1 := m
              )
            )
          ) \<then> Heap_Monad.bind (!m_ref1) (\<lambda> m. mem_update m (key2 k) v)
        )
      )
    )
   )
   "

definition
  "inv_pair_weak heap = (
    let
      m1 = Ref.get heap m_ref1;
      m2 = Ref.get heap m_ref2
    in Array.length heap m1 = size \<and> Array.length heap m2 = size
      \<and> Ref.present heap k_ref1 \<and> Ref.present heap k_ref2
      \<and> Ref.present heap m_ref1 \<and> Ref.present heap m_ref2
      \<and> Array.present heap m1 \<and> Array.present heap m2
      \<and> m1 =!!= m2
  )"

lemma inv_pair_lengthD1:
  "Array.length heap (Ref.get heap m_ref1) = size" if "inv_pair_weak heap"
  using that unfolding inv_pair_weak_def by (auto simp: Let_def)

lemma inv_pair_lengthD2:
  "Array.length heap (Ref.get heap m_ref2) = size" if "inv_pair_weak heap"
  using that unfolding inv_pair_weak_def by (auto simp: Let_def)

lemma inv_pair_presentD:
  "Array.present heap (Ref.get heap m_ref1)" "Array.present heap (Ref.get heap m_ref2)"
  if "inv_pair_weak heap"
  using that unfolding inv_pair_weak_def by (auto simp: Let_def)

lemma inv_pair_presentD2:
  "Ref.present heap m_ref1" "Ref.present heap m_ref2"
  "Ref.present heap k_ref1" "Ref.present heap k_ref2"
  if "inv_pair_weak heap"
  using that unfolding inv_pair_weak_def by (auto simp: Let_def)

lemma inv_pair_not_eqD:
  "Ref.get heap m_ref1 =!!= Ref.get heap m_ref2" if "inv_pair_weak heap"
  using that unfolding inv_pair_weak_def by (auto simp: Let_def)

definition "lookup1 k \<equiv> state_of (!m_ref1 \<bind> (\<lambda> m. mem_lookup m k))"

definition "lookup2 k \<equiv> state_of (!m_ref2 \<bind> (\<lambda> m. mem_lookup m k))"

definition "update1 k v \<equiv> state_of (!m_ref1 \<bind> (\<lambda> m. mem_update m k v))"

definition "update2 k v \<equiv> state_of (!m_ref2 \<bind> (\<lambda> m. mem_update m k v))"

definition "move12 k \<equiv>
  state_of (Heap_Monad.bind (!k_ref1) (\<lambda> k1.
    Heap_Monad.bind mem_empty (\<lambda> m. Heap_Monad.bind (!m_ref1) (\<lambda> m1.
      k_ref2 := k1 \<then> k_ref1 := k \<then> m_ref2 := m1 \<then> m_ref1 := m))))"

definition "get_k1 \<equiv> state_of (!k_ref1)"

definition "get_k2 \<equiv> state_of (!k_ref2)"

lemma runState_state_of[simp]:
  "runState (state_of p) m = the (execute p m)"
  unfolding state_of_def by simp

context assumes injective: "\<forall> a b. to_index a = to_index b \<and> to_index b < size \<longrightarrow> a = b"
begin

context
  assumes disjoint[simp]:
    "m_ref1 =!= m_ref2" "m_ref1 =!= k_ref1" "m_ref1 =!= k_ref2"
    "m_ref2 =!= k_ref1" "m_ref2 =!= k_ref2"
    "k_ref1 =!= k_ref2"
begin

lemmas [simp] = disjoint[THEN noteq_sym]

lemma [simp]:
  "Array.get (snd (Array.alloc xs heap)) a = Array.get heap a" if "Array.present heap a"
  using that unfolding Array.alloc_def Array.present_def
  apply (simp add: Let_def)
  apply (subst Array.get_set_neq)
  subgoal
    by (simp add: Array.noteq_def)
  subgoal
    unfolding Array.get_def by simp
  done

lemma [simp]:
  "Ref.get (snd (Array.alloc xs heap)) r = Ref.get heap r" if "Ref.present heap r"
  using that unfolding Array.alloc_def Ref.present_def
  by (simp add: Let_def Ref.get_def Array.set_def)

lemma alloc_present:
  "Array.present (snd (Array.alloc xs heap)) a" if "Array.present heap a"
  using that unfolding Array.present_def Array.alloc_def by (simp add: Let_def Array.set_def)

lemma alloc_present':
  "Ref.present (snd (Array.alloc xs heap)) r" if "Ref.present heap r"
  using that unfolding Ref.present_def Array.alloc_def by (simp add: Let_def Array.set_def)

lemma length_get_upd[simp]:
  "length (Array.get (Array.update a i x heap) r) = length (Array.get heap r)"
  unfolding Array.get_def Array.update_def Array.set_def by simp

interpretation pair: pair_mem lookup1 lookup2 update1 update2 move12 get_k1 get_k2 inv_pair_weak
  apply standard
  subgoal
    by (simp add: execute_simps get_k1_def)
  subgoal
    by (simp add: execute_simps get_k2_def)
  subgoal
    by (auto simp:
      move12_def mem_empty_def mem_defs.map_of_def map_le_def lookup1_def mem_lookup_def
      execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
    )
  subgoal for m k1 x m'
    apply (frule inv_pair_lengthD1)
    apply (auto simp:
      move12_def mem_empty_def mem_defs.map_of_def map_le_def lookup1_def lookup2_def mem_lookup_def
      execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
      simp: inv_pair_presentD inv_pair_presentD2
    )
    done
  subgoal
    by (auto simp:
      move12_def mem_empty_def mem_defs.map_of_def map_le_def lookup1_def lookup2_def get_k1_def mem_lookup_def
      execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
      simp: inv_pair_presentD inv_pair_presentD2
    )
  subgoal
    by (auto simp:
      move12_def mem_empty_def mem_defs.map_of_def map_le_def lookup1_def lookup2_def get_k1_def get_k2_def mem_lookup_def
      execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
      simp: inv_pair_presentD inv_pair_presentD2
    )
  subgoal
    apply (rule lift_pI)
    unfolding inv_pair_weak_def Memory_Heap.P_def
    apply (auto simp:
      move12_def mem_empty_def mem_defs.map_of_def map_le_def lookup1_def lookup2_def get_k1_def get_k2_def mem_lookup_def
      execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
      simp: inv_pair_presentD inv_pair_presentD2 
      intro: alloc_present alloc_present'
      elim: present_alloc_noteq[THEN Array.noteq_sym]
    )
    done
  subgoal
    apply (rule lift_pI)
    unfolding inv_pair_weak_def Memory_Heap.P_def
    apply (auto simp:
      move12_def mem_empty_def mem_defs.map_of_def map_le_def lookup1_def lookup2_def get_k1_def get_k2_def mem_lookup_def
      execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
      simp: inv_pair_presentD inv_pair_presentD2 
      intro: alloc_present alloc_present'
      split: if_split_asm
    )
    done
  subgoal
    apply (rule lift_pI)
    unfolding inv_pair_weak_def Memory_Heap.P_def
    apply (auto simp:
      move12_def mem_empty_def mem_defs.map_of_def map_le_def lookup1_def lookup2_def get_k1_def get_k2_def mem_lookup_def
      execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
      simp: inv_pair_presentD inv_pair_presentD2 
      intro: alloc_present alloc_present'
      split: if_split_asm
    )
    done
  subgoal
    apply (rule lift_pI)
    unfolding inv_pair_weak_def Memory_Heap.P_def
    apply (auto simp:
      move12_def mem_empty_def mem_defs.map_of_def map_le_def update1_def lookup1_def lookup2_def get_k1_def get_k2_def mem_update_def mem_lookup_def
      execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
      simp: inv_pair_presentD inv_pair_presentD2 
      intro: alloc_present alloc_present'
      split: if_split_asm
    )
    done
  subgoal
    apply (rule lift_pI)
    unfolding inv_pair_weak_def Memory_Heap.P_def
    apply (auto simp:
      move12_def mem_empty_def mem_defs.map_of_def map_le_def update1_def update2_def lookup1_def lookup2_def get_k1_def get_k2_def mem_update_def mem_lookup_def
      execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
      simp: inv_pair_presentD inv_pair_presentD2 
      intro: alloc_present alloc_present'
      split: if_split_asm
    )
    done
  subgoal
    apply (frule inv_pair_lengthD1)
    apply (auto simp:
      move12_def mem_empty_def mem_defs.map_of_def map_le_def update1_def update2_def lookup1_def lookup2_def get_k1_def get_k2_def mem_update_def mem_lookup_def
      execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
      simp: inv_pair_presentD inv_pair_presentD2 
      intro: alloc_present alloc_present'
      split: if_split_asm
    )
    done
  subgoal
    apply (frule inv_pair_lengthD1)
    apply (auto simp:
      move12_def mem_empty_def mem_defs.map_of_def map_le_def update1_def update2_def lookup1_def lookup2_def get_k1_def get_k2_def mem_update_def mem_lookup_def
      execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
      simp: inv_pair_presentD inv_pair_presentD2 
      intro: alloc_present alloc_present'
      split: if_split_asm
    )
    done
  subgoal
    apply (frule inv_pair_lengthD2)
    apply (auto simp:
      move12_def mem_empty_def mem_defs.map_of_def map_le_def update1_def update2_def lookup1_def lookup2_def get_k1_def get_k2_def mem_update_def mem_lookup_def
      execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
      simp: inv_pair_presentD inv_pair_presentD2 
      intro: alloc_present alloc_present'
      split: if_split_asm
    )
    done
   subgoal
    apply (frule inv_pair_lengthD2)
    apply (auto simp:
      move12_def mem_empty_def mem_defs.map_of_def map_le_def update1_def update2_def lookup1_def lookup2_def get_k1_def get_k2_def mem_update_def mem_lookup_def
      execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
      simp: inv_pair_presentD inv_pair_presentD2 
      intro: alloc_present alloc_present'
      split: if_split_asm
    )
     done
   subgoal
    apply (frule inv_pair_lengthD1)
    apply (auto simp:
      move12_def mem_empty_def mem_defs.map_of_def map_le_def update1_def update2_def lookup1_def lookup2_def get_k1_def get_k2_def mem_update_def mem_lookup_def
      execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
      simp: inv_pair_presentD inv_pair_presentD2 
      intro: alloc_present alloc_present'
      split: if_split_asm
    )
     done
  subgoal
    apply (frule inv_pair_lengthD1)
    apply (auto simp:
      move12_def mem_empty_def mem_defs.map_of_def map_le_def update1_def update2_def lookup1_def lookup2_def get_k1_def get_k2_def mem_update_def mem_lookup_def
      execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
      simp: inv_pair_presentD inv_pair_presentD2 
      intro: alloc_present alloc_present'
      split: if_split_asm
    )
    done
  subgoal
    apply (frule inv_pair_lengthD2)
    apply (auto simp:
      move12_def mem_empty_def mem_defs.map_of_def map_le_def update1_def update2_def lookup1_def lookup2_def get_k1_def get_k2_def mem_update_def mem_lookup_def
      execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
      simp: inv_pair_presentD inv_pair_presentD2 
      intro: alloc_present alloc_present'
      split: if_split_asm
    )
    done
  subgoal
    apply (frule inv_pair_lengthD2)
    apply (auto simp:
      move12_def mem_empty_def mem_defs.map_of_def map_le_def update1_def update2_def lookup1_def lookup2_def get_k1_def get_k2_def mem_update_def mem_lookup_def
      execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
      simp: inv_pair_presentD inv_pair_presentD2 
      intro: alloc_present alloc_present'
      split: if_split_asm
    )
    done
  subgoal
    apply (frule inv_pair_lengthD1)
    apply (auto simp:
      move12_def mem_empty_def mem_defs.map_of_def map_le_def update1_def update2_def lookup1_def lookup2_def get_k1_def get_k2_def mem_update_def mem_lookup_def
      execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
      simp: inv_pair_presentD inv_pair_presentD2 
      intro: alloc_present alloc_present'
      split: if_split_asm
    )
    done
  subgoal
    apply (frule inv_pair_lengthD1)
    apply (auto simp:
      move12_def mem_empty_def mem_defs.map_of_def map_le_def update1_def update2_def lookup1_def lookup2_def get_k1_def get_k2_def mem_update_def mem_lookup_def
      execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
      simp: inv_pair_presentD inv_pair_presentD2 
      intro: alloc_present alloc_present'
      split: if_split_asm
    )
    done
  subgoal
    apply (frule inv_pair_lengthD2)
    apply (auto simp:
      move12_def mem_empty_def mem_defs.map_of_def map_le_def update1_def update2_def lookup1_def lookup2_def get_k1_def get_k2_def mem_update_def mem_lookup_def
      execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
      simp: inv_pair_presentD inv_pair_presentD2 
      intro: alloc_present alloc_present'
      split: if_split_asm
    )
    done
  subgoal
    apply (frule inv_pair_lengthD2)
    apply (auto simp:
      move12_def mem_empty_def mem_defs.map_of_def map_le_def update1_def update2_def lookup1_def lookup2_def get_k1_def get_k2_def mem_update_def mem_lookup_def
      execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
      simp: inv_pair_presentD inv_pair_presentD2 
      intro: alloc_present alloc_present'
      split: if_split_asm
    )
    done
  subgoal
    apply (frule inv_pair_lengthD1)
    apply (frule inv_pair_lengthD2)
    apply (auto simp:
      move12_def mem_empty_def mem_defs.map_of_def map_le_def update1_def update2_def Memory_Heap.lookup1_def lookup2_def get_k1_def get_k2_def mem_update_def Memory_Heap.mem_lookup_def
      execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
      simp: inv_pair_presentD inv_pair_presentD2 
      intro: alloc_present alloc_present'
      split: if_split_asm
    )
    using injective
    apply (subst (asm) nth_list_update_neq)
    by auto
 subgoal
    apply (frule inv_pair_lengthD1)
    apply (frule inv_pair_lengthD2)
    apply (auto simp:
      move12_def mem_empty_def mem_defs.map_of_def map_le_def update1_def update2_def Memory_Heap.lookup1_def Memory_Heap.lookup2_def get_k1_def get_k2_def mem_update_def Memory_Heap.mem_lookup_def
      execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
      simp: inv_pair_presentD inv_pair_presentD2 
      intro: alloc_present alloc_present'
      split: if_split_asm
    )
    using injective
    apply (subst (asm) nth_list_update_neq)
    by auto
  subgoal
    apply (frule inv_pair_lengthD1)
    apply (frule inv_pair_lengthD2)
    apply (frule inv_pair_not_eqD)
    apply (auto simp:
      move12_def mem_empty_def mem_defs.map_of_def map_le_def update1_def update2_def Memory_Heap.lookup1_def Memory_Heap.lookup2_def get_k1_def get_k2_def mem_update_def Memory_Heap.mem_lookup_def
      execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
      simp: inv_pair_presentD inv_pair_presentD2 
      intro: alloc_present alloc_present'
      split: if_split_asm
      dest: Array.noteq_sym
    )
    done
   subgoal for m k' v
    apply (frule inv_pair_lengthD1)
     apply (frule inv_pair_lengthD2)
     apply (frule inv_pair_not_eqD)
    apply (auto simp:
      move12_def mem_empty_def mem_defs.map_of_def map_le_def update1_def update2_def Memory_Heap.lookup1_def Memory_Heap.lookup2_def get_k1_def get_k2_def mem_update_def Memory_Heap.mem_lookup_def
      execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
      simp: inv_pair_presentD inv_pair_presentD2 
      intro: alloc_present alloc_present'
      split: if_split_asm
    )
     done
   done

lemma state_of_bind:
  "runState (state_of m1 \<bind> (\<lambda> x. state_of (m2 x))) heap = runState (state_of (m1 \<bind> (\<lambda> x. m2 x))) heap"
  if "success m1 heap"
  (* by (smt Heap_cases Monad.bind_def execute_bind(1) old.prod.case option.sel state.sel state_of_def success_def that) *)
(* Generated by sledgehammer *)
proof -
obtain aa :: "heap \<Rightarrow> 'a Heap \<Rightarrow> 'a" and hh :: "heap \<Rightarrow> 'a Heap \<Rightarrow> heap" where
  "\<forall>x0 x1. (\<exists>v2 v3. execute x1 x0 = Some (v2, v3)) = (execute x1 x0 = Some (aa x0 x1, hh x0 x1))"
  by moura
then have f1: "execute m1 heap = Some (aa heap m1, hh heap m1)"
by (meson Heap_cases success_def that)
  then have
    "runState (state_of m1 \<bind> (\<lambda> x. state_of (m2 x))) heap =
      (case (aa heap m1, hh heap m1) of (a, x) \<Rightarrow> runState (state_of (m2 a)) x)"
    by (simp add: Monad.bind_def)
  then show ?thesis
    using f1 by (simp add: execute_bind(1))
qed

interpretation heap_mem_defs inv_pair_weak lookup_pair update_pair .

definition
  "mem_lookup1 k = (!m_ref1 \<bind> (\<lambda>m2. mem_lookup m2 k))"

definition
  "mem_lookup2 k = (!m_ref2 \<bind> (\<lambda>m2. mem_lookup m2 k))"

definition "get_k1' \<equiv> !k_ref1"

definition "get_k2' \<equiv> !k_ref2"

definition "update1' k v \<equiv> !m_ref1 \<bind> (\<lambda> m. mem_update m k v)"

definition "update2' k v \<equiv> !m_ref2 \<bind> (\<lambda> m. mem_update m k v)"

definition "move12' k \<equiv>
  Heap_Monad.bind (!k_ref1) (\<lambda> k1.
    Heap_Monad.bind mem_empty (\<lambda> m. Heap_Monad.bind (!m_ref1) (\<lambda> m1.
      k_ref2 := k1 \<then> k_ref1 := k \<then> m_ref2 := m1 \<then> m_ref1 := m)))"

lemma rel_state_ofI:
  "rel_state op = (state_of m) m" if
  "\<forall> heap. inv_pair_weak heap \<longrightarrow> success m heap"
  "lift_p inv_pair_weak m"
  using that unfolding rel_state_def
  by (auto split: option.split intro: lift_p_P'' simp: success_def)

lemma lift_p_success:
  "State_Heap.lift_p inv_pair_weak m"
  if "DP_CRelVS.lift_p inv_pair_weak (state_of m)" "\<forall> heap. inv_pair_weak heap \<longrightarrow> success m heap"
  using that
  unfolding lift_p_def DP_CRelVS.lift_p_def
  by (auto simp: success_def split: option.split)

lemma rel_state_ofI2:
  "rel_state op = (state_of m) m" if
  "\<forall> heap. inv_pair_weak heap \<longrightarrow> success m heap"
  "DP_CRelVS.lift_p inv_pair_weak (state_of m)"
  using that by (blast intro: rel_state_ofI lift_p_success)

lemma success_bind_I:
  assumes "success f h"
    and "\<And> x h'. execute f h = Some (x, h') \<Longrightarrow> success (g x) h'"
  shows "success (f \<bind> g) h"
  by (rule successE[OF assms(1)]) (auto elim: assms(2) intro: success_bind_executeI)

context
  includes lifting_syntax
begin

lemma [transfer_rule]:
  "(op = ===> rel_state op =) move12 move12'"
  unfolding move12_def move12'_def
  apply (intro rel_funI)
  apply simp
  apply (rule rel_state_ofI2)
  subgoal
    by (auto
        simp: mem_empty_def inv_pair_lengthD1 execute_simps Let_def
        intro: success_intros intro!: success_bind_I
       )
  subgoal
    using pair.move12_inv unfolding move12_def .
  done

lemma [transfer_rule]:
  "(op = ===> rel_state (rel_option op =)) lookup1 mem_lookup1"
  unfolding lookup1_def mem_lookup1_def
  apply (intro rel_funI)
  apply (simp add: option.rel_eq)
  apply (rule rel_state_ofI2)
  subgoal
    by (auto 4 4
        simp: mem_lookup_def inv_pair_lengthD1 execute_simps Let_def
        intro: success_bind_executeI success_returnI Array.success_nthI
       )
  subgoal
    using pair.lookup_inv(1) unfolding lookup1_def .
  done

lemma [transfer_rule]:
  "(op = ===> rel_state (rel_option op =)) lookup2 mem_lookup2"
  unfolding lookup2_def mem_lookup2_def
  apply (intro rel_funI)
  apply (simp add: option.rel_eq)
  apply (rule rel_state_ofI2)
  subgoal
    by (auto 4 3
        simp: mem_lookup_def inv_pair_lengthD2 execute_simps Let_def
        intro: success_intros intro!: success_bind_I
       )
  subgoal
    using pair.lookup_inv(2) unfolding lookup2_def .
  done

lemma [transfer_rule]:
  "rel_state (op =) get_k1 get_k1'"
  unfolding get_k1_def get_k1'_def
  apply (rule rel_state_ofI2)
  subgoal
    by (auto intro: success_lookupI)
  subgoal
    unfolding get_k1_def[symmetric] by (auto dest: pair.get_state(1) intro: lift_pI)
  done

lemma [transfer_rule]:
  "rel_state (op =) get_k2 get_k2'"
  unfolding get_k2_def get_k2'_def
  apply (rule rel_state_ofI2)
  subgoal
    by (auto intro: success_lookupI)
  subgoal
    unfolding get_k2_def[symmetric] by (auto dest: pair.get_state(2) intro: lift_pI)
  done

lemma [transfer_rule]:
  "(op = ===> op = ===> rel_state (op =)) update1 update1'"
  unfolding update1_def update1'_def
  apply (intro rel_funI)
  apply simp
  apply (rule rel_state_ofI2)
  subgoal
    by (auto 4 3
        simp: mem_update_def inv_pair_lengthD1 execute_simps Let_def
        intro: success_intros intro!: success_bind_I
       )
  subgoal
    using pair.update_inv(1) unfolding update1_def .
  done

lemma [transfer_rule]:
  "(op = ===> op = ===> rel_state (op =)) update2 update2'"
  unfolding update2_def update2'_def
  apply (intro rel_funI)
  apply simp
  apply (rule rel_state_ofI2)
  subgoal
    by (auto 4 3
        simp: mem_update_def inv_pair_lengthD2 execute_simps Let_def
        intro: success_intros intro!: success_bind_I
       )
  subgoal
    using pair.update_inv(2) unfolding update2_def .
  done

lemma [transfer_rule]:
  "(op = ===> rel_state (rel_option op =)) lookup1 mem_lookup1"
  unfolding lookup1_def mem_lookup1_def
  apply (intro rel_funI)
  apply (simp add: option.rel_eq)
  apply (rule rel_state_ofI2)
  subgoal
    by (auto 4 3
        simp: mem_lookup_def inv_pair_lengthD1 execute_simps Let_def
        intro: success_intros intro!: success_bind_I
       )
  subgoal
    using pair.lookup_inv(1) unfolding lookup1_def .
  done

lemma rel_state_lookup:
  "(op = ===> rel_state op =) pair.lookup_pair lookup_pair"
  unfolding pair.lookup_pair_def lookup_pair_def
  unfolding
    mem_lookup1_def[symmetric] mem_lookup2_def[symmetric]
    get_k2_def[symmetric] get_k2'_def[symmetric]
    get_k1_def[symmetric] get_k1'_def[symmetric]
  by transfer_prover

lemma rel_state_update:
  "(op = ===> op = ===> rel_state op =) pair.update_pair update_pair"
  unfolding pair.update_pair_def update_pair_def
  unfolding move12'_def[symmetric]
  unfolding
    update1'_def[symmetric] update2'_def[symmetric]
    get_k2_def[symmetric] get_k2'_def[symmetric]
    get_k1_def[symmetric] get_k1'_def[symmetric]
  by transfer_prover

end (* Lifting Syntax *)

end (* Disjoint *)

end (* Injectivity *)

end (* Refs *)

end (* Key functions & Size *)

end (* Theory *)