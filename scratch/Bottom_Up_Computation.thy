theory Bottom_Up_Computation
  imports "../DP_CRelVS"
begin

fun iterate_state where
  "iterate_state f [] = return ()" |
  "iterate_state f (x # xs) = do {f x; iterate_state f xs}"

context
  fixes cnt :: "'a \<Rightarrow> bool" and nxt :: "'a \<Rightarrow> 'a"
begin

definition
  "iter_state f \<equiv>
    wfrec
      {(nxt x, x) | x. cnt x}
      (\<lambda> rec x. if cnt x then do {f x; rec (nxt x)} else return ())"

definition
  "iterator_to_list \<equiv>
    wfrec {(nxt x, x) | x. cnt x} (\<lambda> rec x. if cnt x then x # rec (nxt x) else [])
  "

context
  fixes sizef :: "'a \<Rightarrow> nat"
  assumes terminating:
    "finite {x. cnt x}" "\<forall> x. cnt x \<longrightarrow> sizef x < sizef (nxt x)"
begin

lemma admissible:
  "adm_wf
      {(nxt x, x) | x. cnt x}
      (\<lambda> rec x. if cnt x then do {f x; rec (nxt x)} else return ())"
  unfolding adm_wf_def by auto

lemma wellfounded:
  "wf {(nxt x, x) | x. cnt x}" (is "wf ?S")
proof -
  from terminating have "acyclic ?S"
    by (auto intro: acyclicI_order[where f = sizef])
  moreover have "finite ?S"
    using [[simproc add: finite_Collect]] terminating(1) by auto
  ultimately show ?thesis
    by - (rule finite_acyclic_wf)
qed

lemma iter_state_unfold:
  "iter_state f x = (if cnt x then do {f x; iter_state f (nxt x)} else return ())"
  unfolding iter_state_def by (simp add: wfrec_fixpoint[OF wellfounded admissible])

lemma iterator_to_list_unfold:
  "iterator_to_list x = (if cnt x then x # iterator_to_list (nxt x) else [])"
  unfolding iterator_to_list_def by (simp add: adm_wf_def wfrec_fixpoint[OF wellfounded])

lemma iter_state_iterate_state:
  "iter_state f x = iterate_state f (iterator_to_list x)"
  apply (induction "iterator_to_list x" arbitrary: x)
   apply (simp add: iterator_to_list_unfold split: if_split_asm)
   apply (simp add: iter_state_unfold)
  apply (subst (asm) (3) iterator_to_list_unfold)
  apply (simp split: if_split_asm)
  apply (auto simp: iterator_to_list_unfold iter_state_unfold)
  done

end (* Termination *)

end (* Iterator *)

context dp_consistency
begin

context
  includes lifting_syntax
begin

lemma crel_vs_iterate_state:
  "crel_vs op = () (iterate_state f xs)" if "(op = ===>\<^sub>T R) g f"
proof (induction xs)
  case Nil
  then show ?case by (simp; rule crel_vs_return; simp; fail)
next
  case (Cons x xs)
  have unit_expand: "() = (\<lambda> a f. f a) () (\<lambda> _. ())" ..
  from Cons show ?case
    by simp
      (rule
        bind_transfer[unfolded rel_fun_def, rule_format, unfolded unit_expand]
        that[unfolded rel_fun_def, rule_format] HOL.refl
      )+
qed

lemma crel_vs_bind_ignore:
  "crel_vs R a (do {d; b})" if "crel_vs R a b" "crel_vs S c d"
proof -
  have unit_expand: "a = (\<lambda> a f. f a) () (\<lambda> _. a)" ..
  show ?thesis
    by (subst unit_expand)
       (rule bind_transfer[unfolded rel_fun_def, rule_format, unfolded unit_expand] that)+
qed

lemma crel_vs_iterate_and_compute:
  assumes "(op = ===>\<^sub>T R) g f"
  shows "crel_vs R (g x) (do {iterate_state f xs; f x})"
  by (rule
        crel_vs_bind_ignore crel_vs_iterate_state HOL.refl
        assms[unfolded rel_fun_def, rule_format] assms
     )+

context
  fixes cnt :: "'a \<Rightarrow> bool" and nxt :: "'a \<Rightarrow> 'a"
  fixes sizef :: "'a \<Rightarrow> nat"
  assumes terminating:
    "finite {x. cnt x}" "\<forall> x. cnt x \<longrightarrow> sizef x < sizef (nxt x)"
begin

lemma crel_vs_iter_and_compute:
  assumes "(op = ===>\<^sub>T R) g f"
  shows "crel_vs R (g x) (do {iter_state cnt nxt f x; f x})"
  unfolding iter_state_iterate_state[OF terminating] using crel_vs_iterate_and_compute[OF assms] .

end (* Terminating Iterator *)

end (* Lifting Syntax *)

end (* Consistency *)

context
  fixes m :: nat -- "Width of a row"
    and n :: nat -- "Number of rows"
begin

lemma
  "finite {(x, y). x \<le> n \<and> y \<le> m}"
  by auto

lemma
  "\<forall> x y. (\<lambda> (x, y). x \<le> n \<and> y \<le> m) (x, y) \<longrightarrow>
    (\<lambda> (x, y). x * (m + 1) + y) (x, y) <
    (\<lambda> (x, y). x * (m + 1) + y) ((\<lambda> (x, y). if y < m then (x, y + 1) else (x + 1, 0)) (x, y))"
  by auto

end

end (* Theory *)