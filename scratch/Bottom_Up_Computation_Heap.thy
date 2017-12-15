theory Bottom_Up_Computation_Heap
  imports Bottom_Up_Computation State_Heap
begin

context
  fixes cnt :: "'a \<Rightarrow> bool" and nxt :: "'a \<Rightarrow> 'a"
begin

definition
  "iter_heap f \<equiv>
    wfrec
      {(nxt x, x) | x. cnt x}
      (\<lambda> rec x. if cnt x then Heap_Monad.bind (f x) (\<lambda> _. rec (nxt x)) else return ())"

context
  fixes sizef :: "'a \<Rightarrow> nat"
  assumes terminating:
    "finite {x. cnt x}" "\<forall> x. cnt x \<longrightarrow> sizef x < sizef (nxt x)"
begin

lemma iter_heap_unfold:
  "iter_heap f x = (if cnt x then Heap_Monad.bind (f x) (\<lambda> _. iter_heap f (nxt x)) else return ())"
  unfolding iter_heap_def by (simp add: wfrec_fixpoint[OF wellfounded[OF terminating]] adm_wf_def)

end (* Termination *)

end (* Iterator *)

context dp_heap
begin

context
  includes lifting_syntax
  fixes cnt :: "'a \<Rightarrow> bool" and nxt :: "'a \<Rightarrow> 'a"
  fixes sizef :: "'a \<Rightarrow> nat"
  assumes terminating:
    "finite {x. cnt x}" "\<forall> x. cnt x \<longrightarrow> sizef x < sizef (nxt x)"
begin

lemma crel_vs_iterate_state:
  "crel_vs' op = () (iter_heap cnt nxt f x)" if "(op = ===> crel_vs' R) g f"
  using wellfounded[OF terminating]
proof induction
  case (less x)
  have unit_expand: "() = (\<lambda> a f. f a) () (\<lambda> _. ())" ..
  from less show ?case
    by (subst iter_heap_unfold[OF terminating])
       (auto intro:
          bind_transfer[unfolded rel_fun_def, rule_format, unfolded unit_expand]
          crel_vs'_return that[unfolded rel_fun_def, rule_format]
       )
qed

lemma crel_vs'_bind_ignore:
  "crel_vs' R a (Heap_Monad.bind d (\<lambda> _. b))" if "crel_vs' R a b" "crel_vs' S c d"
proof -
  have unit_expand: "a = (\<lambda> a f. f a) () (\<lambda> _. a)" ..
  show ?thesis
    by (subst unit_expand)
       (rule bind_transfer[unfolded rel_fun_def, rule_format, unfolded unit_expand] that)+
qed

lemma crel_vs'_iterate_and_compute:
  assumes "(op = ===> crel_vs' R) g f"
  shows "crel_vs' R (g x) (Heap_Monad.bind (iter_heap cnt nxt f y) (\<lambda> _. f x))"
  by (rule
        crel_vs'_bind_ignore crel_vs_iterate_state HOL.refl
        assms[unfolded rel_fun_def, rule_format] assms
     )+

end (* Lifting Syntax & Terminating Iterator *)

end (* DP Heap *)

end (* Theory *)