theory Bellman_Ford
  imports "../DP_Lifting" "../DP_CRelVS" "../DP_Proof"
begin
  
consts n :: nat
consts W :: "nat \<Rightarrow> nat \<Rightarrow> int"
term 0 (**)
  
  (*
fun bf :: "nat\<times>nat \<Rightarrow> int" where
  "bf (0,j) = W 0 j"
| "bf (Suc k, j) = fold min [bf (k, i) + W i j. i \<leftarrow> [0..<n]] (bf (k, j))"
term 0 (**)
*)
  
fun bf :: "nat\<times>nat \<Rightarrow> int" where
  "bf (0, j) = W 0 j"
| "bf (Suc k, j) =
    fold
      (min)
      (map
          (\<lambda>i. plus (W i j) (bf (k, i)))
          (upt 0 n))
      (bf (k, j))"
thm bf.simps
thm bf.induct
term 0 (**)
  
lemma map\<^sub>T_return_return_cong[fundef_cong]:
  fixes f g xs
  assumes "\<And>x. x\<in>set xs \<Longrightarrow> f x = g x"
  shows "map\<^sub>T . \<langle>f\<rangle> . \<langle>xs\<rangle> = map\<^sub>T . \<langle>g\<rangle> . \<langle>xs\<rangle>"
  sorry
term 0 (**)
  
fun bf\<^sub>T :: "nat\<times>nat \<Rightarrow>\<^sub>T int" where
  "bf\<^sub>T$ (0, j) =CHECKMEM= \<langle>W 0 j\<rangle>"
| "bf\<^sub>T$ (Suc k, j) =CHECKMEM=
    fold\<^sub>T
    . min\<^sub>T
    . (map\<^sub>T
      . (\<lambda>\<^sub>Ti. plus\<^sub>T . \<langle>W i j\<rangle> . (bf\<^sub>T (k, i)))
      . \<langle>upt 0 n\<rangle>)
    . (bf\<^sub>T (k, j))"
thm bf\<^sub>T.simps
thm bf\<^sub>T.induct
term 0 (**)
  
interpretation bf: dp_consistency bf .
context
  includes lifting_syntax
begin

abbreviation K :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "K x \<equiv> eq_onp (op = x)"
term 0 (**)

lemma bf_induct:
  "\<lbrakk>\<And>j. P (0, j);
    \<And>k j. \<lbrakk>\<And>x. x \<in> set [0..<n] \<Longrightarrow> P (k, x);
           P (k, j)
           \<rbrakk> \<Longrightarrow> P (Suc k, j)
   \<rbrakk> \<Longrightarrow> P (x::nat\<times>nat)"
  by (fact bf\<^sub>T.induct)

lemma bf_inductS:
  "\<lbrakk>\<And>j. bf.crel_vs op = (bf (0, j)) (bf\<^sub>T (0, j));
    \<And>k j. \<lbrakk>\<And>x. x \<in> set [0..<n] \<Longrightarrow> bf.crel_vs op = (bf (k, x)) (bf\<^sub>T (k, x));
           bf.crel_vs op = (bf (k, j)) (bf\<^sub>T (k, j))
           \<rbrakk> \<Longrightarrow> bf.crel_vs op = (bf (Suc k, j)) (bf\<^sub>T (Suc k, j))
   \<rbrakk> \<Longrightarrow> bf.crel_vs op = (bf (x::nat\<times>nat)) (bf\<^sub>T x)"
  by (fact bf_induct)


lemma bf_inductS':
  "\<lbrakk>\<And>j. bf.crel_vs op = (bf (0, j)) (bf\<^sub>T (0, j));
    \<And>k j. \<lbrakk>K k k k;
           K j j j;
           (rel_prod (K k) (eq_onp (\<lambda>x. x\<in>set [0..<n])) ===> bf.crel_vs op =) bf bf\<^sub>T;
           (rel_prod (K k) (K j) ===> bf.crel_vs op =) bf bf\<^sub>T
           \<rbrakk> \<Longrightarrow> bf.crel_vs op = (bf (Suc k, j)) (bf\<^sub>T (Suc k, j))
   \<rbrakk> \<Longrightarrow> bf.crel_vs op = (bf (x::nat\<times>nat)) (bf\<^sub>T x)"
  unfolding eq_onp_def rel_prod.simps using bf_inductS by blast

thm eq_onp_to_eq
  
lemma "bf.consistentDP bf\<^sub>T"
  apply ( rule dp_consistency.consistentDP_intro,
    rule bf.induct,
    unfold bf\<^sub>T.simps;
    rule dp_consistency.crel_vs_checkmem,
    unfold bf.simps)
   apply (dp_step) apply (solves \<open>simp\<close>)
    
    oops
lemma 
  assumes A
  shows B
    thm  bf.fun_app_lifted_transfer[THEN rel_funD, THEN rel_funD]
    apply (use \<open>A\<close>)
  term 0 (*
  apply ( rule dp_consistency.consistentDP_intro,
    induct_tac rule: bf_inductS,
    unfold bf\<^sub>T.simps;
    rule dp_consistency.crel_vs_checkmem,
    unfold bf.simps)
  subgoal
    apply (rule bf.return_transfer[THEN rel_funD])
    apply (rule refl)
    done
  subgoal premises prems
    apply (rule bf.fun_app_lifted_transfer[THEN rel_funD, THEN rel_funD]) back
     apply (rule bf.fun_app_lifted_transfer[THEN rel_funD, THEN rel_funD])
      apply (rule bf.fun_app_lifted_transfer[THEN rel_funD, THEN rel_funD, where f=fold])
       apply (rule bf.fold_transfer)
      apply (rule bf.min_transfer)
     apply (rule bf.map_transfer_inset_unfolded'[where ?R0.0="op ="])
      apply (rule bf.fun_app_lifted_transfer[THEN rel_funD, THEN rel_funD]) back
       apply (rule bf.fun_app_lifted_transfer[THEN rel_funD, THEN rel_funD])
        apply (rule bf.plus_transfer)
       apply (rule bf.crel_vs_return)
       apply (rule cong) back back
        apply (rule cong)
         apply (rule refl)
        apply (assumption)
       apply (rule refl)
    subgoal premises prems'
      unfolding prems'(1)
      apply (rule prems(1))
      apply (fact prems'(2)[unfolded prems'(1)])
      done
     apply (rule bf.crel_vs_return)
     apply (unfold list.rel_eq)
     apply (rule refl)
    apply (fact prems(2))
    done
  done

end