theory Scratch
  imports "../DP_Consistency"
begin
term int
term fold
  
context dp_consistency
begin
context
  includes lifting_syntax
begin
term 0 (**)


definition ceq :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('param \<rightharpoonup> 'result, 'a) state \<Rightarrow> ('param \<rightharpoonup> 'result, 'a) state \<Rightarrow> bool" where
  "ceq R s0 s1 \<equiv> (eq_onp consistentM ===> rel_prod R (eq_onp consistentM)) (runState s0) (runState s1)"
  
lemma ceq_intro:
  fixes R s0 s1
  assumes "\<And>M v0 M0 v1 M1. \<lbrakk>consistentM M; runState s0 M = (v0,M0); runState s1 M = (v1,M1)\<rbrakk> \<Longrightarrow> R v0 v1 \<and> M0=M1 \<and> consistentM M1"
  shows "ceq R s0 s1"
  unfolding ceq_def eq_onp_def rel_fun_def rel_prod_conv by (auto split: prod.split dest: assms)
term 0 (**)

lemma ceq_elim:
  fixes R s0 s1
  assumes "ceq R s0 s1" "consistentM M"
  obtains v0 M0 v1 M1 where "runState s0 M = (v0, M0)" "runState s1 M = (v1, M1)" "R v0 v1" "M0=M1" "consistentM M1"
  using assms unfolding ceq_def eq_onp_def rel_fun_def by (blast elim: rel_prod.cases)
    
term 0 (**)
  
lemma id\<^sub>T_cong:
  fixes R x y
  shows "(R ===> ceq R) return return"
  unfolding rel_fun_def return_def by (fastforce intro: ceq_intro)
thm id\<^sub>T_cong[THEN rel_funD]
term 0 (**)
  
lemma bind_cong[transfer_rule]:
  fixes R0 R1
  shows "(ceq R0 ===> (R0 ===> ceq R1) ===> ceq R1) (op \<bind>) (op \<bind>)"
  unfolding rel_fun_def bind_def by (fastforce intro!: ceq_intro elim!: ceq_elim)
thm bind_cong[THEN rel_funD, THEN rel_funD]
term 0 (**)

lemma app\<^sub>T_cong[transfer_rule]:
  shows "(ceq (R0 ===> ceq R1) ===> ceq R0 ===> ceq R1) (op .) (op .)"
  unfolding fun_app_lifted_def by transfer_prover
thm app\<^sub>T_cong[THEN rel_funD, THEN rel_funD]
term 0 (**)
  
lemma map\<^sub>T_cong:
  assumes "ceq R0 xs\<^sub>T ys\<^sub>T"
  assumes "\<And>M. consistentM M \<Longrightarrow> case (runState f\<^sub>T M, runState g\<^sub>T M) of ((f, Mf), (g, Mg)) \<Rightarrow>
            Mf = Mg \<and> consistentM Mg \<and> (case runState ys\<^sub>T Mg of (ys, Mys) \<Rightarrow> (\<forall>x\<in>set ys. ceq R1 (f x) (g x)))"
  shows "ceq (list_all2 R1) (map\<^sub>T . f\<^sub>T . xs\<^sub>T) (map\<^sub>T . g\<^sub>T . ys\<^sub>T)"



















