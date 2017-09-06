theory DP_CPredS
  imports "./DP_CRelVS"
begin
context dp_consistency
begin
context 
  includes lifting_syntax
begin
  
definition cpred_s :: "('a \<Rightarrow> bool) \<Rightarrow> ('param \<rightharpoonup> 'result, 'a) state \<Rightarrow> bool" where
  "cpred_s P s \<equiv> \<forall>M. cmem M \<longrightarrow> (case runState s M of (v', M') \<Rightarrow> P v' \<and> cmem M')"
  
definition cpred_s_alt :: "('a \<Rightarrow> bool) \<Rightarrow> ('param \<rightharpoonup> 'result, 'a) state \<Rightarrow> bool" where
  "cpred_s_alt P s \<equiv> pred_fun cmem (pred_prod P cmem) (runState s)"
  
lemma "cpred_s_alt = cpred_s"
  unfolding cpred_s_def cpred_s_alt_def
  by (fastforce split: pred_prod_split)
term 0(**)

notation pred_fun (infixr "...>" 55)

abbreviation pred_fun_lifted :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a ==_\<Longrightarrow> 'b) \<Rightarrow> bool" (infixr "...>\<^sub>T" 55) where
  "A ...>\<^sub>T B \<equiv> A ...> cpred_s B"

  
lemma cpred_s_intro:
  assumes "\<And>M v' M'. \<lbrakk>cmem M; runState v\<^sub>T M = (v', M')\<rbrakk> \<Longrightarrow> P v' \<and> cmem M'"
  shows "cpred_s P v\<^sub>T"
  unfolding cpred_s_def using assms by blast

lemma cpred_s_elim:
  assumes "cpred_s P v\<^sub>T" "cmem M"
  obtains v' M' where "runState v\<^sub>T M = (v', M')" "P v'" "cmem M'"
  using assms unfolding cpred_s_def by blast
term 0 (**)

lemma cpred_s_return:
  "P v \<Longrightarrow> cpred_s P \<langle>v\<rangle>"
  unfolding return_def by (fastforce intro: cpred_s_intro)

lemma return_transferP:
  "(P ...> cpred_s P) return"
  unfolding pred_fun_def by (metis cpred_s_return)
    
lemma bind_transferP:
  "(cpred_s P0 ...> (P0 ...>\<^sub>T P1) ...> cpred_s P1) (op \<bind>)"
  unfolding bind_def pred_fun_def by (fastforce intro: cpred_s_intro elim: cpred_s_elim split: prod.split)
    
lemma fun_app_lifted_transferP:
  "(cpred_s (R0 ...>\<^sub>T R1) ...> cpred_s P0 ...> cpred_s P1) (op .)"
  unfolding fun_app_lifted_def
  oops 
end
end
end