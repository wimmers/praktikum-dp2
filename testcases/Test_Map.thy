theory Test_Map
  imports "../DP_Lifting"
begin

function f :: "nat \<Rightarrow> int" where
  "f 0 = 0"
| "f (Suc i) = undefined (map f [0..<Suc i])"
  by pat_completeness auto
termination
  apply (relation "measure size")
  by (auto intro: wf_mlex mlex_less )

lemma [fundef_cong]:
  fixes f g
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> f x = g x" "xs = ys"
  shows   "map\<^sub>T' f xs = map\<^sub>T' g ys"
  using assms
  apply (induction xs arbitrary: ys)
  subgoal
    by auto
  subgoal for x xs ys
    by (cases ys) auto
  done

function f\<^sub>T :: "nat \<Rightarrow>\<^sub>T int" where
  "f\<^sub>T 0 = return 0"
| "f\<^sub>T (Suc i) = undefined (map\<^sub>T' f\<^sub>T [0..<Suc i])"
  by pat_completeness auto
termination
  apply (relation "size <*mlex*> {}")
  by (auto intro: wf_mlex mlex_less )

(*
lemma [fundef_cong]:
  fixes f g x y
  assumes "\<And> f' g'. f' \<in> set_state f \<Longrightarrow> g' \<in> set_state g \<Longrightarrow> f' y = g' y" "x = y"
  shows "f . (return x) = g . (return y)"
    using assms unfolding fun_app_lifted_def by simp
*)

thm set_state_def
     (*
lemma [fundef_cong]:
  fixes f g x y
  assumes
    "\<And> f' g' x' y'. f' \<in> set_state f \<Longrightarrow> g' \<in> set_state g \<Longrightarrow> x' \<in> set_state x \<Longrightarrow> y' \<in> set_state y
    \<Longrightarrow> f' x' = g' y'"
  shows "f . x = g . y"
    using assms unfolding fun_app_lifted_def sorry *)
(*
lemma [fundef_cong]:
  fixes f g
  assumes "\<And>x xs'. xs' \<in> set_state xs \<Longrightarrow> x \<in> set xs' \<Longrightarrow> f . (return x) = g . (return x)" "xs = ys"
  shows   "map\<^sub>T . f . xs = map\<^sub>T . g . ys"
    sorry
*)
(*
lemma [fundef_cong]:
  fixes f g
  assumes
    "\<And>x xs' f' g'. xs' \<in> set_state xs \<Longrightarrow> x \<in> set xs' \<Longrightarrow> f' \<in> set_state f \<Longrightarrow> g' \<in> set_state g
    \<Longrightarrow> f' x = g' x" "xs = ys"
  shows   "map\<^sub>T . f . xs \<equiv> map\<^sub>T . g . ys"
    sorry
 *)
(*
lemma [fundef_cong]:
  fixes f g x y
  assumes "\<And> x. do { f' \<leftarrow> f; x' \<leftarrow> x; f' x' } = do { g' \<leftarrow> g; x' \<leftarrow> x; g' x' }" "x = y"
  shows "f . (return x) = g . (return y)"
    using assms unfolding fun_app_lifted_def by simp

lemma [fundef_cong]:
  fixes f g
  assumes "\<And>x xs'. xs' \<in> set_state xs \<Longrightarrow> x \<in> set xs' \<Longrightarrow> f . (return x) = g . (return x)" "xs = ys"
  shows   "map\<^sub>T . f . xs = map\<^sub>T . g . ys"
    sorry
*)

(*
lemma [fundef_cong]:
  fixes f g
  assumes
    "\<And>x xs'. xs' \<in> set_state xs \<Longrightarrow> x \<in> set xs' \<Longrightarrow> do { f' \<leftarrow> f; f' x} = do { g' \<leftarrow> g; g' x}"
    "xs = ys"
  shows   "map\<^sub>T . f . xs = map\<^sub>T . g . ys"
  sorry
*)

term map\<^sub>T' term map\<^sub>T
lemma map\<^sub>T_map\<^sub>T':
  "(map\<^sub>T . (return ff)) = \<langle>map\<^sub>T' ff\<rangle>"
  unfolding map\<^sub>T_def lift_3_def
    sorry

lemma [fundef_cong]:
  fixes f g
  assumes
    "\<And>x xs'. xs' \<in> set_state xs \<Longrightarrow> x \<in> set xs' \<Longrightarrow> f x = g x" "xs = ys"
  shows "map\<^sub>T . (return f) . xs = map\<^sub>T . (return g) . ys"
  using assms(2)
  unfolding map\<^sub>T_map\<^sub>T'
  apply simp
  unfolding fun_app_lifted_def
  apply (simp add: left_identity)
  unfolding bind_def
  apply simp
  apply (rule ext)
  subgoal for M
    apply (cases "runState ys M")
    apply auto
    using assms(1)
    apply auto
    subgoal premises prems for xs M'
      using prems(2-)
      apply (induction xs arbitrary: ys)
       apply simp
      apply simp
      sorry
    done
  done

function f\<^sub>T' :: "nat \<Rightarrow>\<^sub>T int" where
  "f\<^sub>T' 0 = return 0"
| "f\<^sub>T' (Suc i) = undefined (map\<^sub>T . (return f\<^sub>T') . (return ([0..<Suc i])))"
  by pat_completeness auto
termination
  apply (relation "measure size")
   apply simp
  apply (simp add: Monad.return_def)
    by auto