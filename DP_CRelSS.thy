theory DP_CRelSS
  imports "./DP_CRelVS" "./DP_CPredS"
begin
term int
term fold
  
locale dp_cong =
  fixes cmem :: "('param \<rightharpoonup> 'result) \<Rightarrow> bool"
begin
context
  includes lifting_syntax
begin
term 0 (**)


definition crel_ss :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('param \<rightharpoonup> 'result, 'a) state \<Rightarrow> ('param \<rightharpoonup> 'result, 'b) state \<Rightarrow> bool" where
  "crel_ss R s0 s1 \<equiv> (eq_onp cmem ===> rel_prod R (eq_onp cmem)) (runState s0) (runState s1)"
  
lemma crel_ss_intro:
  fixes R s0 s1
  assumes "\<And>M v0 M0 v1 M1. \<lbrakk>cmem M; runState s0 M = (v0,M0); runState s1 M = (v1,M1)\<rbrakk> \<Longrightarrow> R v0 v1 \<and> M0=M1 \<and> cmem M1"
  shows "crel_ss R s0 s1"
  unfolding crel_ss_def eq_onp_def rel_fun_def rel_prod_conv by (auto split: prod.split dest: assms)
term 0 (**)

lemma crel_ss_elim:
  fixes R s0 s1
  assumes "crel_ss R s0 s1" "cmem M"
  obtains v0 M0 v1 M1 where "runState s0 M = (v0, M0)" "runState s1 M = (v1, M1)" "R v0 v1" "M0=M1" "cmem M1"
  using assms unfolding crel_ss_def eq_onp_def rel_fun_def by (blast elim: rel_prod.cases)
    
term 0 (**)
  
lemma id\<^sub>T_cong[transfer_rule]:
  fixes R x y
  shows "(R ===> crel_ss R) return return"
  unfolding rel_fun_def return_def by (fastforce intro: crel_ss_intro)
thm id\<^sub>T_cong[THEN rel_funD]
term 0 (**)
  
lemma bind_cong[transfer_rule]:
  fixes R0 R1
  shows "(crel_ss R0 ===> (R0 ===> crel_ss R1) ===> crel_ss R1) (op \<bind>) (op \<bind>)"
  unfolding rel_fun_def bind_def by (fastforce intro!: crel_ss_intro elim!: crel_ss_elim)
thm bind_cong[THEN rel_funD, THEN rel_funD]
term 0 (**)

lemma app\<^sub>T_cong[transfer_rule]:
  fixes R0 R1
  shows "(crel_ss (R0 ===> crel_ss R1) ===> crel_ss R0 ===> crel_ss R1) (op .) (op .)"
  unfolding fun_app_lifted_def by transfer_prover
thm app\<^sub>T_cong[THEN rel_funD, THEN rel_funD]
term 0 (**)

lemma lift_33_cong[transfer_rule]:
  fixes R0 R1 R2
  shows "((R0 ===> R1 ===> R2) ===> crel_ss (R0 ===> crel_ss (R1 ===> crel_ss R2))) lift_33 lift_33"
  unfolding lift_33_def by transfer_prover
term 0 (**)
    
lemma Cons\<^sub>T_cong[transfer_rule]:
  fixes R
  shows "(crel_ss (R ===> crel_ss ((list_all2 R) ===> crel_ss (list_all2 R)))) Cons\<^sub>T Cons\<^sub>T"
  unfolding Cons\<^sub>T_def by transfer_prover
    
term 0 (**)
lemma map\<^sub>T_cong:
  assumes "crel_ss (list_all2 R0) xs\<^sub>T ys\<^sub>T"
  assumes "crel_ss (\<lambda>f g. crel_ss (list_all2 (\<lambda>x y. R0 x y \<longrightarrow> crel_ss R1 (f x) (g y))) xs\<^sub>T ys\<^sub>T) f\<^sub>T g\<^sub>T"
  shows "crel_ss (list_all2 R1) (map\<^sub>T . f\<^sub>T . xs\<^sub>T) (map\<^sub>T . g\<^sub>T . ys\<^sub>T)"
proof -
  {
    fix M assume "cmem M"
    have map\<^sub>T': "runState map\<^sub>T M = (\<lambda>f. \<langle>map\<^sub>T' f\<rangle>, M)"
      unfolding map\<^sub>T_def lift_3_def return_def by auto
    obtain f Mf g Mg where
      crel_xs_ys: "crel_ss (list_all2 (\<lambda>x y. R0 x y \<longrightarrow> crel_ss R1 (f x) (g y))) xs\<^sub>T ys\<^sub>T"
      and f_g: "runState f\<^sub>T M = (f, Mf)" "runState g\<^sub>T M = (g, Mg)" "Mf = Mg" "cmem Mg"
      using crel_ss_elim[OF assms(2) \<open>cmem M\<close>] .
    obtain xs Mxs ys Mys where
      crel_x_y: "list_all2 (\<lambda>x y. R0 x y \<longrightarrow> crel_ss R1 (f x) (g y)) xs ys"
      and xs_ys: "runState xs\<^sub>T Mf = (xs, Mxs)" "runState ys\<^sub>T Mg = (ys, Mys)" "Mxs = Mys" "cmem Mys"
      unfolding \<open>Mf = Mg\<close> using crel_ss_elim[OF crel_xs_ys \<open>cmem Mg\<close>] .
    have "list_all2 R0 xs ys"
      using assms(1) \<open>cmem Mg\<close> xs_ys \<open>Mf = Mg\<close> by (auto elim: crel_ss_elim)
    with crel_x_y have "list_all2 (\<lambda>x y. crel_ss R1 (f x) (g y)) xs ys"
      by (simp add: list_all2_conv_all_nth)
    hence *:"crel_ss (list_all2 R1) (map\<^sub>T' f xs) (map\<^sub>T' g ys)"
      proof (induction xs ys rule: list_all2_induct)
        case Nil
        then show ?case by (auto intro: crel_ss_intro simp: return_def)
      next
        case (Cons x xs y ys)
        show ?case unfolding map\<^sub>T'.simps supply [transfer_rule]=Cons by transfer_prover
      qed
    obtain mxs Mmxs mys Mmys where
      rel_mxs_mys: "list_all2 R1 mxs mys"
      and mxs_mys: "runState (map\<^sub>T' f xs) Mxs = (mxs, Mmxs)"
                   "runState (map\<^sub>T' g ys) Mys = (mys, Mmys)"
                   "Mmxs = Mmys" "cmem Mmys"
      unfolding \<open>Mxs = Mys\<close> using crel_ss_elim[OF * \<open>cmem Mys\<close>] .
        
    fix mxs' Mmxs' mys' Mmys'
    assume "runState (map\<^sub>T . f\<^sub>T . xs\<^sub>T) M = (mxs', Mmxs')" "runState (map\<^sub>T . g\<^sub>T . ys\<^sub>T) M = (mys', Mmys')"
    then have "mxs = mxs'" "mys = mys'" "Mmxs = Mmxs'" "Mmys = Mmys'"
      unfolding
        map\<^sub>T'[THEN fun_app_lifted_dest, OF f_g(1) runState_return, THEN fun_app_lifted_dest, OF xs_ys(1) mxs_mys(1)]
        map\<^sub>T'[THEN fun_app_lifted_dest, OF f_g(2) runState_return, THEN fun_app_lifted_dest, OF xs_ys(2) mxs_mys(2)]
      by auto
    hence "list_all2 R1 mxs' mys' \<and> Mmxs' = Mmys' \<and> cmem Mmys'"
      using rel_mxs_mys mxs_mys by auto
  } from this[THEN crel_ss_intro] show ?thesis .
qed
  
thm map\<^sub>T_cong
  
interpretation cpred: dp_pred cmem .

lemma crel_ss_cpred_s: 
  "cpred.cpred_s (list_all (\<lambda>x. R x x)) xs\<^sub>T \<longleftrightarrow> crel_ss (list_all2 (\<lambda>x y. x = y \<longrightarrow> R x y)) xs\<^sub>T xs\<^sub>T"
  unfolding crel_ss_def cpred.cpred_s_def_alt
  unfolding rel_fun_def 
  unfolding rel_prod_conv 
  unfolding list.pred_rel eq_onp_def list_all2_conv_all_nth
  by auto
    
corollary wtf: "cpred.cpred_s (list_all (\<lambda>x. R (f x) (g x))) xs\<^sub>T \<longleftrightarrow> crel_ss (list_all2 (\<lambda>x y. x = y \<longrightarrow> R (f x) (g y))) xs\<^sub>T xs\<^sub>T"
  using crel_ss_cpred_s .

corollary map\<^sub>T_cong':
  assumes "crel_ss (op =) xs\<^sub>T xs\<^sub>T"
  assumes "crel_ss (\<lambda>f g. cpred.cpred_s (\<lambda>xs. \<forall>x\<in>set xs. crel_ss R1 (f x) (g x)) xs\<^sub>T) f\<^sub>T g\<^sub>T"
  shows "crel_ss (list_all2 R1) (map\<^sub>T . f\<^sub>T . xs\<^sub>T) (map\<^sub>T . g\<^sub>T . xs\<^sub>T)"
  using assms(1)[folded list.rel_eq] assms(2)
  unfolding list_all_iff[symmetric]
  unfolding wtf
  by (fact map\<^sub>T_cong)

    
    term 0 (**
fun test :: "nat \<Rightarrow> nat" where
  "test 0 = 0"
| "test (Suc n) = fold (op +) (map test [0..<Suc n]) 0"
  
(*
fun test\<^sub>T :: "nat \<Rightarrow>\<^sub>T nat" where
  "test\<^sub>T 0 = \<langle>0\<rangle>"
| "test\<^sub>T (Suc n) = fold\<^sub>T (map\<^sub>T . \<langle>test\<^sub>T\<rangle> . \<langle>[0..<Suc n]\<rangle>)"
*)

function test\<^sub>T :: "nat \<Rightarrow> ((nat \<rightharpoonup> nat) \<Rightarrow> (nat \<times> (nat \<rightharpoonup> nat)))" where
  "test\<^sub>T 0 M = runState (checkmem 0 \<langle>0\<rangle>) M"
| "test\<^sub>T (Suc n) M = runState (checkmem (Suc n) (fold\<^sub>T . plus\<^sub>T . (map\<^sub>T . \<langle>\<lambda>x. State (test\<^sub>T x)\<rangle> . \<langle>[0..<Suc n]\<rangle>) . \<langle>0\<rangle>)) M"
  by pat_completeness auto
    
    lemma ""
  *)
    
end
end

fun test :: "nat \<Rightarrow> nat" where
  "test 0 = 0"
| "test (Suc n) = fold (op +) (map test [0..<Suc n]) 0"
  
function (domintros) test\<^sub>T :: "nat \<Rightarrow> ((nat \<rightharpoonup> nat) \<Rightarrow> (nat \<times> (nat \<rightharpoonup> nat)))" where
  "test\<^sub>T 0 M = runState (checkmem 0 \<langle>0\<rangle>) M"
| "test\<^sub>T (Suc n) M = runState (checkmem (Suc n) (fold\<^sub>T . plus\<^sub>T . (map\<^sub>T . \<langle>\<lambda>x. State (test\<^sub>T x)\<rangle> . \<langle>[0..<Suc n]\<rangle>) . \<langle>0\<rangle>)) M"
  by pat_completeness auto
    
interpretation dp: dp_consistency test .

lemma
  fixes n M
  assumes "dp.cmem M"
  shows "test\<^sub>T_dom (n, M)"
  apply (induction n)
  subgoal using  test\<^sub>T.domintros(1)  by simp
  subgoal for m 
    oops
      
lemma xx:
  fixes a P
  assumes "P 0"
  assumes "\<And>n. (\<And>x. x < Suc n \<Longrightarrow> P x) \<Longrightarrow> P (Suc n)"
  shows "\<And>x. x\<le>a \<Longrightarrow> P x"
  apply (induction a)
  subgoal using assms(1) by simp
  subgoal for a x
    apply (cases "x = Suc a")
    subgoal using assms(2) by simp
    subgoal by simp
    done
  done

corollary
  fixes a P
  assumes "P 0"
  assumes "\<And>n. (\<And>x. x < Suc n \<Longrightarrow> P x) \<Longrightarrow> P (Suc n)"
  shows "P a" 
proof -
  from assms xx have "\<And>x. x\<le>a \<Longrightarrow> P x"
    by blast
  thus ?thesis by auto
qed

lemma "set_state s = fst ` (range (runState s))"
  find_theorems set_state
end