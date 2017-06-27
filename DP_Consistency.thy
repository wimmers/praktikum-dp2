theory DP_Consistency
  imports "./Monad" "./DP_Lifting"
begin

locale dp_consistency =
  fixes dp :: "'param \<Rightarrow> 'result"
begin
  
context
  includes lifting_syntax
begin
  
  (* Predicates *)
definition consistentM :: "('param \<rightharpoonup> 'result) \<Rightarrow> bool" where
  "consistentM M \<equiv> \<forall>param\<in>dom M. M param = Some (dp param)"
term 0 (**)
  
definition consistentS :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> ('param \<rightharpoonup> 'result, 'b) state \<Rightarrow> bool" where
  "consistentS R v s \<equiv> \<forall>M. consistentM M \<longrightarrow> (case runState s M of (v', M') \<Rightarrow> R v v' \<and> consistentM M')"
term 0 (**)
  
abbreviation rel_fun_lifted :: "('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('c ==_\<Longrightarrow> 'd) \<Rightarrow> bool" (infixr "===>\<^sub>T" 55) where
  "rel_fun_lifted R R' \<equiv> R ===> consistentS R'"
term 0 (**)
  
definition consistentDP :: "('param \<Rightarrow>\<^sub>T 'result) \<Rightarrow> bool" where
  "consistentDP \<equiv> (op = ===>\<^sub>T op =) dp"
term 0 (**)
  
  (* consistentM *)
lemma consistentM_intro:
  assumes "\<And>param v. M param = Some v \<Longrightarrow> v = dp param"
  shows "consistentM M"
  using assms unfolding consistentM_def by blast
term 0 (**)
  
lemma consistentM_elim:
  assumes "consistentM M" "M param = Some v"
  obtains "dp param = v"
  using assms unfolding consistentM_def dom_def by auto
term 0 (**)
  
  (* consistentS *)
lemma consistentS_intro:
  assumes "\<And>M v' M'. \<lbrakk>consistentM M; runState v\<^sub>T M = (v', M')\<rbrakk> \<Longrightarrow> R v v' \<and> consistentM M'"
  shows "consistentS R v v\<^sub>T"
  using assms unfolding consistentS_def by blast
term 0 (**)
  
lemma consistentS_elim:
  assumes "consistentS R v v\<^sub>T" "consistentM M"
  obtains v' M' where "runState v\<^sub>T M = (v', M')" "R v v'" "consistentM M'"
  using assms unfolding consistentS_def by blast
term 0 (**)
  
  (* consistentDP *)
lemma consistentDP_intro:
  assumes "\<And>param. consistentS (op =) (dp param) (dp\<^sub>T param)"
  shows "consistentDP dp\<^sub>T"
  using assms unfolding consistentDP_def by blast
term 0 (**)
  
lemma consistentS_return:
  "\<lbrakk>R x y\<rbrakk> \<Longrightarrow> consistentS R x (return y)"
  unfolding return_def by (fastforce intro: consistentS_intro)
term 0 (**)
  
  (* Low level operators *)
lemma consistentM_upd:
  "\<lbrakk>consistentM M; v = dp param\<rbrakk> \<Longrightarrow> consistentM (M(param\<mapsto>v))"
  unfolding consistentM_def by auto
term 0 (**)
  
lemma consistentS_get:
  "\<lbrakk>\<And>M. consistentM M \<Longrightarrow> consistentS R v (sf M)\<rbrakk> \<Longrightarrow> consistentS R v (get \<bind> sf)"
  unfolding get_def bind_def by (fastforce intro: consistentS_intro elim: consistentS_elim split: prod.split)
term 0 (**)
  
lemma consistentS_put:
  "\<lbrakk>consistentS R v sf; consistentM M\<rbrakk> \<Longrightarrow> consistentS R v (put M \<then> sf)"
  unfolding put_def bind_def by (fastforce intro: consistentS_intro elim: consistentS_elim split: prod.split)
term 0 (**)
  
lemma consistentS_bind_eq:
  "\<lbrakk>consistentS op = v s; consistentS R (f v) (sf v)\<rbrakk> \<Longrightarrow> consistentS R (f v) (s \<bind> sf)"
  unfolding bind_def rel_fun_def by (fastforce intro: consistentS_intro elim: consistentS_elim split: prod.split)
term 0 (**)
  
lemma consistentS_checkmem:
  "\<lbrakk>consistentS op = (dp param) s\<rbrakk> \<Longrightarrow> consistentS op = (dp param) (checkmem param s)"
  unfolding checkmem_def by (fastforce intro: consistentS_return consistentS_get consistentS_put
      consistentS_bind_eq consistentM_upd elim: consistentM_elim split: option.splits)
term 0 (**)
  
  (** Transfer rules **)
lemma return_transfer[transfer_rule]:
  "(R ===>\<^sub>T R) (\<lambda>x. x) return"
  unfolding id_def rel_fun_def by (metis consistentS_return)
    
lemma bind_transfer[transfer_rule]:
  "(consistentS R0 ===> (R0 ===>\<^sub>T R1) ===> consistentS R1) (\<lambda>v f. f v) (op \<bind>)"
  unfolding bind_def rel_fun_def by (fastforce intro: consistentS_intro elim: consistentS_elim split: prod.split)
    
lemma fun_app_lifted_transfer[transfer_rule]:
  "(consistentS (R0 ===>\<^sub>T R1) ===> consistentS R0 ===> consistentS R1) (\<lambda> f x. f x) (op .)"
  unfolding fun_app_def fun_app_lifted_def by transfer_prover

term 0 (**)

lemma unlift_'_transfer[transfer_rule]:
  "(R ===> consistentS R) (\<lambda> x. x) unlift_'"
  unfolding unlift_'_def by transfer_prover
term 0 (**)
  
lemma unlift_3_transfer[transfer_rule]:
  "((R0 ===>\<^sub>T R1) ===> (R0 ===> consistentS R1)) (\<lambda> f x. f x) unlift_3"
  unfolding unlift_3_def by transfer_prover
term 0 (**)
  
lemma unlift_33_transfer[transfer_rule]:
  "((R0 ===>\<^sub>T R1 ===>\<^sub>T R2) ===> (R0 ===> R1 ===> consistentS R2)) (\<lambda> f x0 x1. f x0 x1) unlift_33"
  unfolding unlift_33_def by transfer_prover

lemma lift_'_transfer[transfer_rule]:
  "(R ===> consistentS R) (\<lambda> x. x) lift_'"
  unfolding lift_'_def by transfer_prover

lemma lift_3_transfer[transfer_rule]:
  "((R0 ===> R1) ===> consistentS (R0 ===>\<^sub>T R1)) (\<lambda> f x. f x) lift_3"
  unfolding lift_3_def by transfer_prover
    
lemma lift_33_transfer[transfer_rule]:
  "((R0 ===> R1 ===> R2) ===> consistentS (R0 ===>\<^sub>T R1 ===>\<^sub>T R2)) (\<lambda> f x0 x1. f x0 x1) lift_33"
  unfolding lift_33_def by transfer_prover

lemma lift_333_transfer[transfer_rule]:
  "((R0 ===> R1 ===> R2 ===> R3) ===> consistentS (R0 ===>\<^sub>T R1 ===>\<^sub>T R2 ===>\<^sub>T R3)) (\<lambda> f x0 x1 x2. f x0 x1 x2) lift_333"
  unfolding lift_333_def by transfer_prover
term 0 (**)

lemma If_transfer[transfer_rule]:
  "consistentS (op = ===>\<^sub>T R ===>\<^sub>T R ===>\<^sub>T R) If If\<^sub>T"
  unfolding If\<^sub>T_def by transfer_prover
term 0 (**)
  
lemma case_option_transfer[transfer_rule]:
  "consistentS (R1 ===>\<^sub>T (R0 ===>\<^sub>T R1) ===>\<^sub>T rel_option R0 ===>\<^sub>T R1) case_option case_option\<^sub>T"
  unfolding case_option\<^sub>T_def by transfer_prover
    
term 0 (**)
  
lemma case_list_transfer[transfer_rule]:
  "consistentS (R1 ===>\<^sub>T (R0 ===>\<^sub>T list_all2 R0 ===>\<^sub>T R1) ===>\<^sub>T list_all2 R0 ===>\<^sub>T R1) case_list case_list\<^sub>T"
  unfolding case_list\<^sub>T_def by transfer_prover
term 0 (**)
  
lemma case_prod_transfer[transfer_rule]:
  "consistentS ((R0 ===>\<^sub>T R1 ===>\<^sub>T R2) ===>\<^sub>T rel_prod R0 R1 ===>\<^sub>T R2) case_prod case_prod\<^sub>T"
  unfolding case_prod\<^sub>T_def by transfer_prover
term 0 (**)
  
term 0 (**)
lemma id_transfer[transfer_rule]:
  "consistentS (R ===>\<^sub>T R) id id\<^sub>T"
  unfolding id_def id\<^sub>T_def by transfer_prover
term 0 (**)
  
lemma plus_transfer[transfer_rule]:
  "consistentS (op = ===>\<^sub>T op = ===>\<^sub>T op =) plus plus\<^sub>T"
  unfolding plus\<^sub>T_def by transfer_prover
term 0 (**)
  
lemma Cons_transfer[transfer_rule]:
  "consistentS (R ===>\<^sub>T list_all2 R ===>\<^sub>T list_all2 R) Cons Cons\<^sub>T"
  unfolding Cons\<^sub>T_def by transfer_prover
term 0 (**)
  
lemma Some_transfer[transfer_rule]:
  "consistentS (R ===>\<^sub>T rel_option R) Some Some\<^sub>T"
  unfolding Some\<^sub>T_def by transfer_prover
term 0 (**)
  
lemma Pair_transfer[transfer_rule]:
  "consistentS (R0 ===>\<^sub>T R1 ===>\<^sub>T rel_prod R0 R1) Pair Pair\<^sub>T"
  unfolding Pair\<^sub>T_def by transfer_prover
term 0 (**)
  
lemma min_transfer[transfer_rule]:
  "consistentS (op = ===>\<^sub>T op = ===>\<^sub>T op =) min min\<^sub>T"
  unfolding min\<^sub>T_def by transfer_prover
    
lemma max_transfer[transfer_rule]:
  "consistentS (op = ===>\<^sub>T op = ===>\<^sub>T op =) max max\<^sub>T"
  unfolding max\<^sub>T_def by transfer_prover
    
lemma upt_transfer[transfer_rule]:
  "consistentS (op = ===>\<^sub>T op = ===>\<^sub>T list_all2 op =) upt upt\<^sub>T"
  unfolding upt\<^sub>T_def by transfer_prover
    
lemma comp_transfer[transfer_rule]:
  "consistentS ((R1 ===>\<^sub>T R2) ===>\<^sub>T (R0 ===>\<^sub>T R1) ===>\<^sub>T (R0 ===>\<^sub>T R2)) comp comp\<^sub>T"
  unfolding comp_def comp\<^sub>T_def fun_app_lifted_def by transfer_prover
    
lemma map_transfer[transfer_rule]:
  "consistentS ((R0 ===>\<^sub>T R1) ===>\<^sub>T list_all2 R0 ===>\<^sub>T list_all2 R1) map map\<^sub>T"
proof -
  have [transfer_rule]: "((R0 ===>\<^sub>T R1) ===> (list_all2 R0 ===>\<^sub>T list_all2 R1)) map map\<^sub>T'"
    apply ((rule rel_funI)+, induct_tac rule: list_all2_induct, assumption; unfold list.map map\<^sub>T'.simps)
    subgoal premises [transfer_rule] by transfer_prover
    subgoal premises [transfer_rule] by transfer_prover
    done
  show ?thesis
    unfolding map\<^sub>T_def by transfer_prover
qed
  
lemma fold_transfer[transfer_rule]:
  "consistentS ((R0 ===>\<^sub>T R1 ===>\<^sub>T R1) ===>\<^sub>T list_all2 R0 ===>\<^sub>T R1 ===>\<^sub>T R1) fold fold\<^sub>T"
proof -
  have [transfer_rule]: "((R0 ===>\<^sub>T R1 ===>\<^sub>T R1) ===> list_all2 R0 ===>\<^sub>T R1 ===>\<^sub>T R1) fold fold\<^sub>T'"
    apply ((rule rel_funI)+, induct_tac rule: list_all2_induct, assumption; unfold fold.simps fold\<^sub>T'.simps)
    subgoal premises [transfer_rule] by transfer_prover
    subgoal premises [transfer_rule] by transfer_prover
    done
  show ?thesis
    unfolding fold\<^sub>T_def by transfer_prover
qed

end
end
end