theory DP_Pred
  imports "./DP_Consistency"
begin
context dp_consistency
begin
context 
  includes lifting_syntax
begin
  
definition consistentPred :: "('a \<Rightarrow> bool) \<Rightarrow> ('param \<rightharpoonup> 'result, 'a) state \<Rightarrow> bool" where
  "consistentPred P s \<equiv> \<forall>M. consistentM M \<longrightarrow> (case runState s M of (v', M') \<Rightarrow> P v' \<and> consistentM M')"
  
definition consistentPred_alt :: "('a \<Rightarrow> bool) \<Rightarrow> ('param \<rightharpoonup> 'result, 'a) state \<Rightarrow> bool" where
  "consistentPred_alt P s \<equiv> pred_fun consistentM (pred_prod P consistentM) (runState s)"
  
lemma "consistentPred_alt = consistentPred"
  unfolding consistentPred_def consistentPred_alt_def
  by (fastforce split: pred_prod_split)
term 0(**)

notation pred_fun (infixr "...>" 55)

abbreviation pred_fun_lifted :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a ==_\<Longrightarrow> 'b) \<Rightarrow> bool" (infixr "...>\<^sub>T" 55) where
  "A ...>\<^sub>T B \<equiv> A ...> consistentPred B"

  
lemma consistentPred_intro:
  assumes "\<And>M v' M'. \<lbrakk>consistentM M; runState v\<^sub>T M = (v', M')\<rbrakk> \<Longrightarrow> P v' \<and> consistentM M'"
  shows "consistentPred P v\<^sub>T"
  unfolding consistentPred_def using assms by blast

lemma consistentPred_elim:
  assumes "consistentPred P v\<^sub>T" "consistentM M"
  obtains v' M' where "runState v\<^sub>T M = (v', M')" "P v'" "consistentM M'"
  using assms unfolding consistentPred_def by blast
term 0 (**)

lemma consistentPred_return:
  "P v \<Longrightarrow> consistentPred P \<langle>v\<rangle>"
  unfolding return_def by (fastforce intro: consistentPred_intro)

lemma return_transferP:
  "(P ...> consistentPred P) return"
  unfolding pred_fun_def by (metis consistentPred_return)
    
lemma bind_transferP:
  "(consistentPred P0 ...> (P0 ...>\<^sub>T P1) ...> consistentPred P1) (op \<bind>)"
  unfolding bind_def pred_fun_def by (fastforce intro: consistentPred_intro elim: consistentPred_elim split: prod.split)
    
lemma fun_app_lifted_transferP:
  "(consistentPred (R0 ...>\<^sub>T R1) ...> consistentPred P0 ...> consistentPred P1) (op .)"
  unfolding fun_app_lifted_def
  oops 
end
end
end