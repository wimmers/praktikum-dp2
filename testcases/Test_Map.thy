theory Test_Map
  imports "../DP_Lifting"
begin
  
function f :: "nat \<Rightarrow> int" where
  "f 0 = 0"
| "f (Suc i) = undefined [f i. i \<leftarrow> [0..<Suc i]]"
  by pat_completeness auto
termination
  apply (relation "size <*mlex*> {}")
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
    
term "op ."
term 0 (**
    
function f\<^sub>T :: "nat \<Rightarrow>\<^sub>T int" where
  "f\<^sub>T 0 = \<langle>0\<rangle>"
| "f\<^sub>T (Suc i) = undefined (map\<^sub>T' (f\<^sub>T) [0..<Suc i])"
  by pat_completeness auto
termination
  apply (relation "size <*mlex*> {}")
  by (auto intro: wf_mlex mlex_less )