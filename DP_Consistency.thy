theory DP_Consistency
  imports "DP_Lifting"
begin

context
  includes lifting_syntax
begin

(* Predicates *)
definition consistentM :: "('param \<Rightarrow> 'result) \<Rightarrow> ('param \<rightharpoonup> 'result) \<Rightarrow> bool" where
  "consistentM dp M \<equiv> \<forall>param\<in>dom M. M param = Some (dp param)"
term 0 (**)
  
definition consistentS :: "('param \<Rightarrow> 'result) \<Rightarrow> 'a \<Rightarrow> ('param \<rightharpoonup> 'result, 'a) state \<Rightarrow> bool" where
  "consistentS dp v s \<equiv> \<forall>M. consistentM dp M \<longrightarrow> (case runState s M of (v', M') \<Rightarrow> v = v' \<and> consistentM dp M')"
term 0 (**)

(* Consistency predicates for functions *)
definition consistentS_0arg :: "('param \<Rightarrow> 'result) \<Rightarrow> 'a \<Rightarrow> ('param \<rightharpoonup> 'result, 'a) state \<Rightarrow> bool" where
  "consistentS_0arg dp v v\<^sub>T \<equiv> consistentS dp v v\<^sub>T"
definition consistentS_1arg :: "('param \<Rightarrow> 'result) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('param \<rightharpoonup> 'result, 'a ==_\<Longrightarrow> 'b) state \<Rightarrow> bool" where
  "consistentS_1arg dp f f\<^sub>T \<equiv> \<forall>x. consistentS_0arg dp (f x) (f\<^sub>T . \<langle>x\<rangle>)"
definition consistentS_2arg :: "('param \<Rightarrow> 'result) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('param \<rightharpoonup> 'result, 'a ==_\<Longrightarrow> 'b ==_\<Longrightarrow> 'c) state \<Rightarrow> bool" where
  "consistentS_2arg dp f f\<^sub>T \<equiv> \<forall>x. consistentS_1arg dp (f x) (f\<^sub>T . \<langle>x\<rangle>)"
term 0 (**)

definition consistentDP :: "('param \<Rightarrow> 'result) \<Rightarrow> ('param \<Rightarrow>\<^sub>T 'result) \<Rightarrow> bool" where
  "consistentDP dp dp\<^sub>T \<equiv> \<forall>param. consistentS dp (dp param) (dp\<^sub>T param)"
term 0 (**)

(* consistentM *)
lemma consistentM_intro:
  assumes "\<And>param v. M param = Some v \<Longrightarrow> v = dp param"
  shows "consistentM dp M"
  using assms unfolding consistentM_def by blast
term 0 (**)

lemma consistentM_elim:
  assumes "consistentM dp M" "M param = Some v"
  obtains "dp param = v"
  using assms unfolding consistentM_def dom_def by auto
term 0 (**)

(* consistentS *)
lemma consistentS_intro:
  assumes "\<And>M v' M'. \<lbrakk>consistentM dp M; runState v\<^sub>T M = (v', M')\<rbrakk> \<Longrightarrow> v = v' \<and> consistentM dp M'"
  shows "consistentS dp v v\<^sub>T"
  using assms unfolding consistentS_def by blast
term 0 (**)

lemma consistentS_elim:
  assumes "consistentS dp v v\<^sub>T" "consistentM dp M"
  obtains v' M' where "runState v\<^sub>T M = (v', M')" "v = v'" "consistentM dp M'"
  using assms unfolding consistentS_def by blast
term 0 (**)

(* consistentS_0arg *)
lemma consistentS_0arg_intro:
  assumes "consistentS dp v v\<^sub>T"
  shows "consistentS_0arg dp v v\<^sub>T"
  using assms unfolding consistentS_0arg_def .
term 0 (**)

lemma consistentS_0arg_elim:
  assumes "consistentS_0arg dp v v\<^sub>T"
  obtains "consistentS dp v v\<^sub>T"
  using assms unfolding consistentS_0arg_def ..
term 0 (**)

(*consistentS_1arg *)
lemma consistentS_1arg_intro:
  assumes "\<And>x. consistentS_0arg dp (f x) (f\<^sub>T . \<langle>x\<rangle>)"
  shows "consistentS_1arg dp f f\<^sub>T"
  using assms unfolding consistentS_1arg_def ..

(* consistentDP *)
lemma consistentDP_intro:
  assumes "\<And>param. consistentS dp (dp param) (dp\<^sub>T param)"
  shows "consistentDP dp dp\<^sub>T"
  using assms unfolding consistentDP_def by blast
term 0 (**)

(** Transfer rules **)
lemma consistentS_return_transfer[transfer_rule]:
  "(op = ===> consistentS dp) (\<lambda>x. x) return"
  unfolding rel_fun_def return_def by (fastforce intro: consistentS_intro)
lemmas consistentS_return = consistentS_return_transfer[unfolded rel_fun_def, rule_format]
term 0 (**)

(* Low level operators *)
lemma consistentM_upd:
  assumes "consistentM dp M" "v = dp param"
  shows "consistentM dp (M(param\<mapsto>v))"
  using assms unfolding consistentM_def by auto
term 0 (**)

lemma consistentS_get:
  assumes "\<And>M. consistentM dp M \<Longrightarrow> consistentS dp v (sf M)"
  shows "consistentS dp v (get \<bind> sf)"
  using assms unfolding get_def bind_def by (fastforce intro: consistentS_intro elim: consistentS_elim split: prod.split)
  
term 0 (**)

lemma consistentS_put:
  assumes "consistentS dp v sf" "consistentM dp M"
  shows "consistentS dp v (put M \<then> sf)"
  using assms unfolding put_def bind_def by (fastforce intro: consistentS_intro elim: consistentS_elim split: prod.split)
term 0 (**)

lemma consistentS_app:
  assumes "consistentS dp v s" "consistentS dp v' (sf v)"
  shows "consistentS dp v' (s \<bind> sf)"
  using assms unfolding bind_def by (fastforce intro: consistentS_intro elim: consistentS_elim split: prod.split)
term 0 (**)

lemma consistentS_checkmem:
  assumes "consistentS dp (dp param) s"
  shows "consistentS dp (dp param) (checkmem param s)"
  using assms unfolding checkmem_def by (fastforce intro: consistentS_return consistentS_get
      consistentS_put consistentS_app consistentM_upd elim: consistentM_elim split: option.splits)
term 0 (**)

end

end