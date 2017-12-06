theory Memory_Heap
  imports State_Heap
begin

context
  fixes size :: nat
    and to_index :: "('k :: heap) \<Rightarrow> nat"
  assumes injective: "\<forall> a b. to_index a = to_index b \<and> to_index b < size \<longrightarrow> a = b"
begin

definition
  "mem_empty = (Array.new size (None :: ('a :: heap) option))"

context
  fixes mem :: "('a :: heap) option array"
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

lemma mem_heap_corect: "heap_correct P mem_update mem_lookup"
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

end (* Fixed array *)

end (* Injectivity *)

end (* Theory *)