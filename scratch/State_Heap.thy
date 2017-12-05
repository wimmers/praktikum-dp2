theory State_Heap
  imports "../DP_Lifting" "../DP_CRelVS" "../DP_Proof" "HOL-Imperative_HOL.Imperative_HOL"
begin

definition lift_p :: "(heap \<Rightarrow> bool) \<Rightarrow> 'a Heap \<Rightarrow> bool" where
  "lift_p P f =
    (\<forall> heap. P heap \<longrightarrow> (case execute f heap of None \<Rightarrow> False | Some (_, heap) \<Rightarrow> P heap))"

context
  fixes P f heap
  assumes lift: "lift_p P f" and P: "P heap"
begin

lemma execute_cases:
  "case execute f heap of None \<Rightarrow> False | Some (_, heap) \<Rightarrow> P heap"
  using lift P unfolding lift_p_def by auto

lemma execute_cases':
  "case execute f heap of Some (_, heap) \<Rightarrow> P heap"
  using execute_cases by (auto split: option.split)

lemma lift_p_None[simp, dest]:
  False if "execute f heap = None"
  using that execute_cases by auto

lemma lift_p_P:
  "case the (execute f heap) of (_, heap) \<Rightarrow> P heap"
  using execute_cases by (auto split: option.split_asm)

lemma lift_p_P':
  "P heap'" if "the (execute f heap) = (v, heap')"
  using that lift_p_P by auto

lemma lift_p_the_Some[simp]:
  "execute f heap = Some (v, heap')" if "the (execute f heap) = (v, heap')"
  using that execute_cases by (auto split: option.split_asm)

lemma lift_p_E:
  obtains v heap' where "execute f heap = Some (v, heap')" "P heap'"
  using execute_cases by (cases "execute f heap") auto

end

definition "state_of s \<equiv> State (\<lambda> heap. the (execute s heap))"

locale heap_mem_defs =
  fixes P :: "heap \<Rightarrow> bool"
    and lookup :: "'k \<Rightarrow> 'v option Heap"
    and update :: "'k \<Rightarrow> 'v \<Rightarrow> unit Heap"
begin

definition rel_state :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> (heap, 'a) state \<Rightarrow> 'b Heap \<Rightarrow> bool" where
  "rel_state R f g \<equiv>
    \<forall> heap. P heap \<longrightarrow>
      (case runState f heap of (v1, heap1) \<Rightarrow> case execute g heap of
        Some (v2, heap2) \<Rightarrow> R v1 v2 \<and> heap1 = heap2 \<and> P heap2 | None \<Rightarrow> False)"

definition "lookup' k \<equiv> State (\<lambda> heap. the (execute (lookup k) heap))"

definition "update' k v \<equiv> State (\<lambda> heap. the (execute (update k v) heap))"

definition "heap_get = Heap_Monad.Heap (\<lambda> heap. Some (heap, heap))"

definition checkmem_heap :: "'k \<Rightarrow> 'v Heap \<Rightarrow> 'v Heap" where
  "checkmem_heap param calc \<equiv>
    Heap_Monad.bind (lookup param) (\<lambda> x.
    case x of
      Some x \<Rightarrow> return x
    | None \<Rightarrow> Heap_Monad.bind calc (\<lambda> x.
        Heap_Monad.bind (update param x) (\<lambda> _.
        return x
      )
    )
  )
  "

definition map_of_heap where
  "map_of_heap heap k = fst (the (execute (lookup k) heap))"

end (* Heap Mem Defs *)

locale heap_inv = heap_mem_defs _ lookup for lookup :: "'k \<Rightarrow> 'v option Heap"  +
  assumes lookup_inv: "lift_p P (lookup k)"
  assumes update_inv: "lift_p P (update k v)"
begin

lemma rel_state_lookup:
  "rel_state (op =) (lookup' k) (lookup k)"
  unfolding rel_state_def lookup'_def using lookup_inv[of k] by (auto intro: lift_p_P')

lemma rel_state_update:
  "rel_state (op =) (update' k v) (update k v)"
  unfolding rel_state_def update'_def using update_inv[of k v] by (auto intro: lift_p_P')

lemma rel_state_elim:
  assumes "rel_state R f g" "P heap"
  obtains heap' v v' where
    "runState f heap = (v, heap')" "execute g heap = Some (v', heap')" "R v v'" "P heap'"
  apply atomize_elim
  using assms unfolding rel_state_def
  apply auto
  apply (cases "runState f heap")
  apply auto
  apply (auto split: option.split_asm)
  done

lemma rel_state_intro:
  assumes
    "\<And> heap v heap'. P heap \<Longrightarrow> runState f heap = (v, heap')
      \<Longrightarrow> \<exists> v'. R v v' \<and> execute g heap = Some (v', heap')"
    "\<And> heap v heap'. P heap \<Longrightarrow> runState f heap = (v, heap') \<Longrightarrow> P heap'"
  shows "rel_state R f g"
  unfolding rel_state_def
  apply auto
  apply (frule assms(1)[rotated])
   apply (auto intro: assms(2))
  done

context
  includes lifting_syntax
begin

lemma transfer_lookup:
  "(op = ===> rel_state (op =)) lookup' lookup"
  unfolding rel_fun_def by (auto intro: rel_state_lookup)

lemma transfer_update:
  "(op = ===> op = ===> rel_state (op =)) update' update"
  unfolding rel_fun_def by (auto intro: rel_state_update)

lemma transfer_bind[transfer_rule]:
  "(rel_state R ===> (R ===> rel_state Q) ===> rel_state Q) Monad.bind Heap_Monad.bind"
  unfolding rel_fun_def Monad.bind_def Heap_Monad.bind_def
  by (force elim!: rel_state_elim intro!: rel_state_intro)

lemma transfer_return[transfer_rule]:
  "(R ===> rel_state R) Monad.return Heap_Monad.return"
  unfolding rel_fun_def Monad.return_def Heap_Monad.return_def
  by (fastforce intro: rel_state_intro elim: rel_state_elim simp: execute_heap)

lemma fun_app_lifted_transfer:
  "(rel_state (R ===> rel_state Q) ===> rel_state R ===> rel_state Q)
      (op .) (\<lambda> f\<^sub>T' x\<^sub>T'. f\<^sub>T' \<bind> (\<lambda> f. x\<^sub>T' \<bind> (\<lambda> x. f x)))"
  unfolding fun_app_lifted_def by transfer_prover

lemma transfer_get[transfer_rule]:
  "rel_state op = Monad.get heap_get"
  unfolding Monad.get_def heap_get_def by (auto intro: rel_state_intro)

lemma transfer_checkmem_heap:
  "(op = ===> rel_state op = ===> rel_state op =)
    (mem_defs.checkmem lookup' update') checkmem_heap"
  supply [transfer_rule] = transfer_lookup transfer_update
  unfolding mem_defs.checkmem_def checkmem_heap_def by transfer_prover

end (* Lifting Syntax *)

end (* Heap Invariant *)

locale heap_correct =
  heap_inv +
  assumes
    lookup_correct: "map_of_heap (snd (the (execute (lookup k) m))) \<subseteq>\<^sub>m (map_of_heap m)"
      and
    update_correct: "map_of_heap (snd (the (execute (update k v) m))) \<subseteq>\<^sub>m (map_of_heap m)(k \<mapsto> v)"
begin

lemma lookup'_correct:
  "mem_defs.map_of lookup' (snd (runState (lookup' k) m)) \<subseteq>\<^sub>m (mem_defs.map_of lookup' m)"
  unfolding mem_defs.map_of_def map_le_def lookup'_def
  by simp (metis (mono_tags, lifting) domIff lookup_correct map_le_def map_of_heap_def)

lemma update'_correct:
  "mem_defs.map_of lookup' (snd (runState (update' k v) m)) \<subseteq>\<^sub>m mem_defs.map_of lookup' m(k \<mapsto> v)"
  unfolding mem_defs.map_of_def map_le_def lookup'_def update'_def using update_correct[of k v m]
  by (auto split: if_split_asm simp: map_le_def map_of_heap_def)

lemma lookup'_inv:
  "DP_CRelVS.lift_p P (lookup' k)"
  unfolding DP_CRelVS.lift_p_def lookup'_def by (auto elim: lift_p_P'[OF lookup_inv])

lemma update'_inv:
  "DP_CRelVS.lift_p P (update' k v)"
  unfolding DP_CRelVS.lift_p_def update'_def by (auto elim: lift_p_P'[OF update_inv])

lemma mem_correct_heap: "mem_correct lookup' update' P"
  by (intro mem_correct.intro lookup'_correct update'_correct lookup'_inv update'_inv)

end (* Heap correct *)

lemma rel_fun_comp:
  includes lifting_syntax
  assumes "(R1 ===> S1) f g" "(R2 ===> S2) g h"
  shows "(R1 OO R2 ===> S1 OO S2) f h"
  using assms by (auto intro!: rel_funI dest!: rel_funD)

lemma rel_fun_comp1:
  includes lifting_syntax
  assumes "(R1 ===> S1) f g" "(R2 ===> S2) g h" "R' = R1 OO R2"
  shows "(R' ===> S1 OO S2) f h"
  using assms rel_fun_comp by metis

lemma rel_fun_comp2:
  includes lifting_syntax
  assumes "(R1 ===> S1) f g" "(R2 ===> S2) g h" "S' = S1 OO S2"
  shows "(R1 OO R2 ===> S') f h"
  using assms rel_fun_comp by metis

locale dp_heap =
  heap_correct  _ _ lookup for lookup :: "'k \<Rightarrow> 'v option Heap" +
  fixes dp :: "'k \<Rightarrow> 'v"
begin

interpretation state: mem_correct lookup' update' P
  by (rule mem_correct_heap)

interpretation dp_consistency lookup' update' P dp ..

definition "crel_vs' R v f \<equiv>
  \<forall>heap. P heap \<and> cmem heap \<longrightarrow>
    (case execute f heap of None \<Rightarrow> False | Some (v', heap') \<Rightarrow> P heap' \<and> R v v' \<and> cmem heap')
"

lemma crel_vs'_execute_None:
  False if "crel_vs' R a b" "execute b heap = None" "P heap" "cmem heap"
  using that unfolding crel_vs'_def by auto

lemma crel_vs'_execute_Some:
  assumes "crel_vs' R a b" "P heap" "cmem heap"
  obtains x heap' where "execute b heap = Some (x, heap')" "P heap'"
  using assms unfolding crel_vs'_def by (cases "execute b heap") auto

lemma crel_vs'_executeD:
  assumes "crel_vs' R a b" "P heap" "cmem heap"
  obtains x heap' where "execute b heap = Some (x, heap')" "P heap'" "cmem heap'" "R a x"
  using assms unfolding crel_vs'_def by (cases "execute b heap") auto

lemma crel_vs_state_of:
  "crel_vs R a (state_of b)" if "crel_vs' R a b"
  unfolding crel_vs_def state_of_def by (auto elim: crel_vs'_executeD[OF that])

lemma crel_vs'I: "crel_vs' R a b" if "(crel_vs R OO rel_state (op =)) a b"
  using that by (auto 4 3 elim: crel_vs_elim rel_state_elim simp: crel_vs'_def)

context
  includes lifting_syntax
begin

lemma transfer'_return:
  "(R ===> crel_vs' R) (\<lambda> x. x) return"
proof -
  have "(R ===> (crel_vs R OO rel_state (op =))) (\<lambda> x. x) return"
    by (rule rel_fun_comp1 return_transfer transfer_return)+ auto
  then show ?thesis
    by (blast intro: rel_fun_mono crel_vs'I)
qed

lemma crel_vs_return:
  "crel_vs' R x (return y)" if "R x y"
  using that by (rule transfer'_return[unfolded rel_fun_def, rule_format])

lemma bind_transfer[transfer_rule]:
  "(crel_vs' R0 ===> (R0 ===> crel_vs' R1) ===> crel_vs' R1) (\<lambda>v f. f v) (op \<bind>)"
  unfolding rel_fun_def bind_def
  by safe (subst crel_vs'_def, auto 4 4 elim: crel_vs'_execute_Some elim!: crel_vs'_executeD)

lemma crel_vs'_update:
  "crel_vs' op = () (update param (dp param))"
  by (rule crel_vs'I relcomppI crel_vs_update rel_state_update)+

lemma crel_vs'_lookup:
  "crel_vs'
    (\<lambda> v v'. case v' of None \<Rightarrow> True | Some v' \<Rightarrow> v = v' \<and> v = dp param) (dp param) (lookup param)"
  by (rule crel_vs'I relcomppI crel_vs_lookup rel_state_lookup)+

lemma crel_vs'_eq_eq_onp:
  "crel_vs' (eq_onp (\<lambda> x. x = v)) v s" if "crel_vs' op = v s"
  using that unfolding crel_vs'_def by (auto split: option.split simp: eq_onp_def)

lemma crel_vs_bind_eq:
  "\<lbrakk>crel_vs' op = v s; crel_vs' R (f v) (sf v)\<rbrakk> \<Longrightarrow> crel_vs' R (f v) (s \<bind> sf)"
  by (erule bind_transfer[unfolded rel_fun_def, rule_format, OF crel_vs'_eq_eq_onp])
     (auto simp: eq_onp_def)

lemma crel_vs'_checkmem:
  "crel_vs' op = (dp param) (checkmem_heap param s)" if "crel_vs' op = (dp param) s"
  unfolding checkmem_heap_def
  by (rule bind_transfer[unfolded rel_fun_def, rule_format, OF crel_vs'_lookup])
     (auto 4 3 split: option.split_asm intro: crel_vs_bind_eq crel_vs'_update crel_vs_return that)

lemma transfer_fun_app_lifted[transfer_rule]:
  "(crel_vs' (R0 ===> crel_vs' R1) ===> crel_vs' R0 ===> crel_vs' R1)
    (\<lambda> f x. f x) (\<lambda> f\<^sub>T' x\<^sub>T'. f\<^sub>T' \<bind> (\<lambda> f. x\<^sub>T' \<bind> (\<lambda> x. f x)))"
  unfolding fun_app_lifted_def by transfer_prover

end (* Lifting Syntax *)

end (* Dynamic Programming Problem *)

context heap_correct
begin

context
  fixes dp :: "'a \<Rightarrow> 'b"
begin

interpretation state: mem_correct lookup' update' P
  by (rule mem_correct_heap)

interpretation dp_consistency lookup' update' P dp ..

definition "crel_vs1 R v f \<equiv>
  \<forall>heap. P heap \<longrightarrow>
    (case execute f heap of None \<Rightarrow> False | Some (v', heap') \<Rightarrow> P heap' \<and> (cmem heap \<longrightarrow> R v v' \<and> cmem heap'))
"

lemma crel_vs1_execute_None:
  False if "crel_vs1 R a b" "execute b heap = None" "P heap"
  using that unfolding crel_vs1_def by auto

lemma crel_vs1_execute_Some:
  assumes "crel_vs1 R a b" "P heap"
  obtains x heap' where "execute b heap = Some (x, heap')" "P heap'"
  using assms unfolding crel_vs1_def by (cases "execute b heap") auto

lemma crel_vs1_executeD:
  assumes "crel_vs1 R a b" "P heap" "cmem heap"
  obtains x heap' where "execute b heap = Some (x, heap')" "P heap'" "cmem heap'" "R a x"
  using assms unfolding crel_vs1_def by (cases "execute b heap") auto

lemma rel_state_state_of:
  "rel_state op = (state_of b) b" if "crel_vs1 R a b"
  unfolding rel_state_def state_of_def
  by (auto split: option.split elim: crel_vs1_execute_Some[OF that])

lemma crel_vs1_state_of:
  "crel_vs R a (state_of b)" if "crel_vs1 R a b"
  unfolding crel_vs_def state_of_def by (auto elim: crel_vs1_executeD[OF that])

lemma crel_vs1_alt_def:
  "crel_vs1 R = (crel_vs R OO rel_state (op =))"
proof (intro ext)
  fix a b
  have "(crel_vs R OO rel_state (op =)) a b" if "crel_vs1 R a b"
    using that by - (rule relcomppI; erule crel_vs1_state_of rel_state_state_of)
  moreover have "crel_vs1 R a b" if "(crel_vs R OO rel_state (op =)) a b"
    using that by (auto 4 3 elim: crel_vs_elim rel_state_elim simp: crel_vs1_def)
  ultimately show "crel_vs1 R a b = (crel_vs R OO rel_state (op =)) a b" ..
qed

context
  includes lifting_syntax
begin

lemma transfer_return1:
  "(R ===> crel_vs1 R) (\<lambda> x. x) return"
  unfolding crel_vs1_alt_def by (rule rel_fun_comp1 return_transfer transfer_return)+ auto

lemma crel_vs_return1:
  "\<lbrakk>R x y\<rbrakk> \<Longrightarrow> crel_vs1 R x (return y)"
  by (rule transfer_return1[unfolded rel_fun_def, rule_format])
term 0 (**)

lemma rel_fun_relcompp:
  "((R1 ===> S1) OO (R2 ===> S2)) a b \<Longrightarrow> ((R1 OO R2) ===> (S1 OO S2)) a b"
  unfolding OO_def rel_fun_def by blast

lemma rel_fun_comp1':
  assumes "(R1 ===> S1) f g" "(R2 ===> S2) g h" "\<And> a b. R' a b \<Longrightarrow> (R1 OO R2) a b"
  shows "(R' ===> S1 OO S2) f h"
  by (auto intro: assms rel_fun_mono[OF rel_fun_comp1])

lemma rel_fun_comp2':
  assumes "(R1 ===> S1) f g" "(R2 ===> S2) g h" "\<And> a b. (S1 OO S2) a b \<Longrightarrow> S' a b"
  shows "(R1 OO R2 ===> S') f h"
  by (auto intro: assms rel_fun_mono[OF rel_fun_comp1])

lemma crel_vs_rel_state:
  "(R0 ===> crel_vs R1) x (state_of o y)" if "(R0 ===> crel_vs R1 OO rel_state op =) x y"
  using that
  unfolding state_of_def
  apply -
  apply (rule rel_funI)
  apply (drule rel_funD, assumption)
  apply (erule relcomppE)
  apply auto
  apply (rule crel_vs_intro)
  apply auto
   apply (erule rel_state_elim, assumption)
    apply (erule crel_vs_elim)
      apply assumption+
    apply simp
  subgoal premises prems for x' y' b M v' M'
  proof -
    from prems(2,3) have "crel_vs1 R1 (x x') (y y')"
      unfolding crel_vs1_alt_def by (rule relcomppI)
    with prems show ?thesis
      by (auto elim: crel_vs1_executeD)
  qed
  subgoal premises prems for x' y' b M v' M'
  proof -
    from prems(2,3) have "crel_vs1 R1 (x x') (y y')"
      unfolding crel_vs1_alt_def by (rule relcomppI)
    with prems show ?thesis
      by (auto elim: crel_vs1_executeD)
  qed
  done

lemma bind_transfer1:
  "(crel_vs1 R0 ===> (R0 ===> crel_vs1 R1) ===> crel_vs1 R1) (\<lambda>v f. f v) (op \<bind>)"
  if "\<And> x. R0 x x"
  unfolding crel_vs1_alt_def
  apply (rule rel_fun_comp2')
    apply (rule bind_transfer)
   apply (rule transfer_bind)
  apply (drule rel_fun_relcompp)
  apply (erule rel_fun_mono)
   defer
   apply assumption
  apply (intro impI relcomppI)
   apply (erule crel_vs_rel_state)
  by (auto 4 4 dest: rel_funD intro: that elim: rel_state_state_of simp: crel_vs1_alt_def[symmetric])

end (* Lifting Syntax *)

end (* Dynamic Programming Problem *)

end (* Correctness *)

end (* Theory *)