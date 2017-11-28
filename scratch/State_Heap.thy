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

lemma lift_p_P'[intro]:
  "P heap'" if "the (execute f heap) = (v, heap')"
  using that lift_p_P by auto

lemma lift_p_the_Some[simp]:
  "execute f heap = Some (v, heap')" if "the (execute f heap) = (v, heap')"
  using that execute_cases by (auto split: option.split_asm)

end

context
  fixes P :: "heap \<Rightarrow> bool"
    and lookup :: "heap \<Rightarrow> 'k \<Rightarrow> 'v option"
    (* and lookup :: "'k \<Rightarrow> 'v option Heap" *)
    and update :: "'k \<Rightarrow> 'v \<Rightarrow> 'something Heap"
  (* assumes lookup_inv: "lift_p P (lookup k)" *)
  assumes update_inv: "lift_p P (update k v)"
begin

definition rel_state :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> (heap, 'a) state \<Rightarrow> 'b Heap \<Rightarrow> bool" where
  "rel_state R f g \<equiv>
    \<forall> heap. P heap \<longrightarrow>
      (case runState f heap of (v1, heap1) \<Rightarrow> case execute g heap of
        Some (v2, heap2) \<Rightarrow> R v1 v2 \<and> heap1 = heap2 \<and> P heap2 | None \<Rightarrow> False)"

definition "lookup1 k \<equiv> State (\<lambda> heap. (lookup heap k, heap))"

definition "lookup2 k \<equiv> Heap_Monad.Heap (\<lambda> heap. Some (lookup heap k, heap))"

definition "update' k v \<equiv> State (\<lambda> heap. the (execute (update k v) heap))"

lemma rel_state_update:
  "rel_state (op =) (update' k v) (update k v)"
  unfolding rel_state_def update'_def using update_inv[of k v] by auto

lemma
  "rel_state (op =) (lookup1 k) (lookup2 k)"
  unfolding rel_state_def lookup1_def lookup2_def by auto

context
  includes lifting_syntax
begin

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

definition
  "heap_get = Heap_Monad.Heap (\<lambda> heap. Some (heap, heap))"

lemma transfer_get[transfer_rule]:
  "rel_state op = Monad.get heap_get"
  unfolding Monad.get_def heap_get_def by (auto intro: rel_state_intro)

definition checkmem_heap :: "'k \<Rightarrow> 'v Heap \<Rightarrow> 'v Heap" where
  "checkmem_heap param calc \<equiv>
    Heap_Monad.bind heap_get (\<lambda> M.
    case lookup M param of
      Some x \<Rightarrow> return x
    | None \<Rightarrow> Heap_Monad.bind calc (\<lambda> x.
        Heap_Monad.bind (update param x) (\<lambda> _.
        return x
      )
    )
  )
  "

lemma
  "(op = ===> rel_state op = ===> rel_state op =)
    (mem_defs.checkmem lookup (\<lambda> heap k v. snd (the (execute (update k v) heap)))) checkmem_heap"
  unfolding mem_defs.checkmem_def checkmem_heap_def

  unfolding rel_fun_def
  apply auto
  apply (rule transfer_bind[unfolded rel_fun_def, rule_format])
   apply (rule transfer_get[unfolded rel_fun_def, rule_format])
  apply (rule option.case_transfer[unfolded rel_fun_def, rule_format, where R = "op ="])
  subgoal for x xa y xb ya
    unfolding Monad.bind_def Heap_Monad.bind_def Monad.get_def Heap_Monad.return_def return_def
    apply (auto split: option.splits)
    apply (rule rel_state_intro)
     apply (auto split: option.splits)
       apply (auto elim: rel_state_elim; fail)
      apply (erule rel_state_elim)
       apply assumption
      apply (auto split: prod.split_asm)[]
    using lift_p_None[OF update_inv[of x]]
      apply blast
     apply (auto split: prod.split_asm simp: execute_heap Monad.return_def put_def)[]
      apply (force elim: rel_state_elim)
     apply (force elim: rel_state_elim)
    apply (auto split: prod.split_asm simp: execute_heap Monad.return_def put_def)[]
    subgoal for heap v x2
      apply (auto 4 4 split: option.split_asm dest: execute_cases[OF update_inv, of _ x v] elim: rel_state_elim)
      done
    done
  subgoal
    apply (rule transfer_return[unfolded rel_fun_def, rule_format])
    by simp
  subgoal
    by (auto intro: option.rel_refl)
  done

end

end