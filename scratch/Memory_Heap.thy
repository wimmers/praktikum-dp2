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
          Heap_Monad.bind mem_empty (\<lambda> m.
            Heap_Monad.bind (!m_ref1) (\<lambda> m1.
              k_ref2 := k1 \<then> k_ref1 := k' \<then> m_ref2 := m1 \<then> m_ref1 := m
            )
          )
        )
      )
    )
   )
   "

definition
  "inv_pair heap = (
    let
      k1 = Ref.get heap k_ref1;
      k2 = Ref.get heap k_ref2;
      m1 = Ref.get heap m_ref1;
      m2 = Ref.get heap m_ref2
    in
    (\<forall> k \<in> dom (heap_mem_defs.map_of_heap (mem_lookup m1) heap). \<exists> k'. key1 k' = k1 \<and> key2 k' = k) \<and>
    (\<forall> k \<in> dom (heap_mem_defs.map_of_heap (mem_lookup m2) heap). \<exists> k'. key1 k' = k2 \<and> key2 k' = k) \<and>
    k1 \<noteq> k2 \<and> P TYPE('v) m1 heap \<and> P TYPE('v) m2 heap
  )"

definition
  "inv_pair_weak heap = (
    let
      m1 = Ref.get heap m_ref1;
      m2 = Ref.get heap m_ref2
    in P TYPE('v) m1 heap \<and> P TYPE('v) m2 heap
      \<and> Array.length heap m1 = size \<and> Array.length heap m2 = size
      \<and> Ref.present heap k_ref1 \<and> Ref.present heap k_ref2
      \<and> Ref.present heap m_ref1 \<and> Ref.present heap m_ref2
      \<and> Array.present heap m1 \<and> Array.present heap m2
      \<and> m1 =!!= m2
  )"

lemma inv_pair_P_D1: "P TYPE('v) (Ref.get heap m_ref1) heap" if "inv_pair heap"
  using that unfolding inv_pair_def by (auto simp: Let_def)

lemma inv_pair_P_D2: "P TYPE('v) (Ref.get heap m_ref2) heap" if "inv_pair heap"
  using that unfolding inv_pair_def by (auto simp: Let_def)

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

interpretation m1: heap_correct
  "P TYPE('v) (Ref.get heap m_ref1)"
  "mem_update (Ref.get heap m_ref1)"
  "mem_lookup (Ref.get heap m_ref1)"
  by (rule mem_heap_correct[OF injective])

interpretation m2: heap_correct
  "P TYPE('v) (Ref.get heap m_ref2)"
  "mem_update (Ref.get heap m_ref2)"
  "mem_lookup (Ref.get heap m_ref2)"
  by (rule mem_heap_correct[OF injective])

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

 thm pair.lookup_pair_def pair.update_pair_def

lemma state_of_bind:
  "(state_of m1 \<bind> (\<lambda> x. state_of (m2 x))) = state_of (m1 \<bind> (\<lambda> x. m2 x))"
  

lemma
  "runState (pair.update_pair k v) heap = runState (state_of (update_pair k v)) heap"
  unfolding pair.update_pair_def update_pair_def
  unfolding get_k1_def update1_def get_k2_def update2_def lookup1_def lookup2_def move12_def
  apply simp

lemma
  "pair.update_pair k v = state_of (update_pair k v)"
  unfolding pair.update_pair_def update_pair_def state_of_def
  

lemma mem_correct_pair:
  "heap_correct inv_pair update_pair lookup_pair"
proof (standard, goal_cases)
  case (1 k) -- "Lookup invariant"
  show ?case
    unfolding lookup_pair_def Let_def State_Heap.lift_p_def
    apply (auto intro!: lift_pI split: option.split simp: execute_simps)
    using m1.lookup_inv m2.lookup_inv
              apply (auto 7 2 dest: inv_pair_P_D1 inv_pair_P_D2 elim: lift_p_None[rotated 2])
    unfolding inv_pair_def using injective
    by (auto simp: execute_simps P_def Memory_Heap.mem_lookup_def Let_def split: if_split_asm)
next
  case (2 k v) -- "Update invariant"
  show ?case
    unfolding update_pair_def Let_def State_Heap.lift_p_def mem_empty_def
    apply (auto intro!: lift_pI split: option.split simp: execute_simps)
                        apply (auto intro!: lift_pI split: option.split prod.split_asm simp: execute_simps bind_def; fail)
    using m1.update_inv m2.update_inv
                        apply (auto 7 2 dest: inv_pair_P_D1 inv_pair_P_D2 elim: lift_p_None[rotated 2])
using m1.update_inv m2.update_inv
               apply (auto 9 2 dest: inv_pair_P_D1 inv_pair_P_D2 elim: lift_p_None[rotated 2])
unfolding inv_pair_def using injective
       apply (auto simp: execute_simps P_def Memory_Heap.mem_update_def Let_def split: if_split_asm; fail)+
      defer
      defer
  defer
unfolding inv_pair_def using injective
      apply (auto simp: execute_simps P_def Memory_Heap.mem_update_def Let_def split: if_split_asm; fail)+

    oops
                   apply (auto intro!: lift_pI split: option.split prod.split_asm simp: execute_simps bind_def; fail)
                  apply (auto intro!: lift_pI split: option.split prod.split_asm simp: execute_simps bind_def; fail)
                 apply (auto intro!: lift_pI split: option.split prod.split_asm simp: execute_simps bind_def; fail)
                apply (auto intro!: lift_pI split: option.split prod.split_asm simp: execute_simps bind_def; fail)
apply (auto intro!: lift_pI split: option.split prod.split_asm simp: execute_simps bind_def; fail)
    oops
    using m1.lookup_inv m2.lookup_inv
              apply (auto 7 2 dest: inv_pair_P_D1 inv_pair_P_D2 elim: lift_p_None[rotated 2])
    unfolding inv_pair_def using injective
    by (auto simp: execute_simps P_def Memory_Heap.mem_lookup_def Let_def split: if_split_asm)
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

definition
  "inv_pair heap = (
    let
      k1 = Ref.get heap k_ref1;
      k2 = Ref.get heap k_ref2;
      m1 = Ref.get heap m_ref1;
      m2 = Ref.get heap m_ref2
    in
      key1 ` dom (heap_mem_defs.map_of_heap (mem_lookup m1) heap) \<subseteq> {k1} \<and>
      key1 ` dom (heap_mem_defs.map_of_heap (mem_lookup m2) heap) \<subseteq> {k2} \<and>
      k1 \<noteq> k2
  )"

definition
  "inv_pair = (!k_ref1 \<bind> (\<lambda> k1. !k_ref2 \<bind> (\<lambda> k2. !m_ref1 \<bind> (\<lambda> m1. !m_ref2 \<bind> (\<lambda> m2.
    True
    ))))
  )"

end

end (* Injectivity *)

locale heap_mem_empty_defs =
  heap_mem_defs P lookup update for P and lookup and update :: "'k \<Rightarrow> 'v \<Rightarrow> unit Heap" +
  fixes empty :: ""
begin

end (* Theory *)