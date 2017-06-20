theory DP_Consistency
  imports "DP_Lifting"
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
  
  (* Consistency predicates for functions *)
abbreviation R_' :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "R_' \<equiv> op ="
abbreviation R_3 :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a ==_\<Longrightarrow> 'b) \<Rightarrow> bool" where
  "R_3  \<equiv> R_' ===> consistentS R_'"
abbreviation R_33 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a ==_\<Longrightarrow> 'b ==_\<Longrightarrow> 'c) \<Rightarrow> bool" where
  "R_33 \<equiv> R_' ===> consistentS R_3"
abbreviation R_333 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('a ==_\<Longrightarrow> 'b ==_\<Longrightarrow> 'c==_\<Longrightarrow> 'd) \<Rightarrow> bool" where
  "R_333 \<equiv> R_' ===> consistentS R_33"
abbreviation R_q3p33 :: "(('a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> (('a ==_\<Longrightarrow> 'b) ==_\<Longrightarrow> 'c ==_\<Longrightarrow> 'd) \<Rightarrow> bool" where
  "R_q3p33 \<equiv> R_3 ===> consistentS R_3"
abbreviation R_q33p333 :: "(('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f) \<Rightarrow> (('a ==_\<Longrightarrow> 'b ==_\<Longrightarrow> 'c) ==_\<Longrightarrow> 'd ==_\<Longrightarrow> 'e ==_\<Longrightarrow> 'f) \<Rightarrow> bool" where
  "R_q33p333 \<equiv> R_33 ===> consistentS R_33"
  
term 0 (**)
  
definition consistentDP :: "('param \<Rightarrow>\<^sub>T 'result) \<Rightarrow> bool" where
  "consistentDP \<equiv> R_3 dp"
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
  assumes "\<And>param. consistentS R_' (dp param) (dp\<^sub>T param)"
  shows "consistentDP dp\<^sub>T"
  using assms unfolding consistentDP_def by blast
term 0 (**)
  
  (** Transfer rules **)
lemma consistentS_return_transfer[transfer_rule]:
  "(R ===> consistentS R) (\<lambda>x. x) (\<lambda>x. \<langle>x\<rangle>)"
  unfolding rel_fun_def return_def by (fastforce intro: consistentS_intro)
lemmas consistentS_return = consistentS_return_transfer[unfolded rel_fun_def, rule_format]
term 0 (**)
  
  (* Low level operators *)
lemma consistentM_upd:
  assumes "consistentM M" "v = dp param"
  shows "consistentM (M(param\<mapsto>v))"
  using assms unfolding consistentM_def by auto
term 0 (**)
  
lemma consistentS_get:
  assumes "\<And>M. consistentM M \<Longrightarrow> consistentS R v (sf M)"
  shows "consistentS R v (get \<bind> sf)"
  using assms unfolding get_def bind_def by (fastforce intro: consistentS_intro elim: consistentS_elim split: prod.split)
    
term 0 (**)
  
lemma consistentS_put:
  assumes "consistentS R v sf" "consistentM M"
  shows "consistentS R v (put M \<then> sf)"
  using assms unfolding put_def bind_def by (fastforce intro: consistentS_intro elim: consistentS_elim split: prod.split)
term 0 (**)
  
lemma consistentS_bind:
  assumes "consistentS R_' v s" "consistentS R_' (f v) (sf v)"
  shows "consistentS R_' (f v) (s \<bind> sf)"
  using assms unfolding bind_def rel_fun_def by (fastforce intro: consistentS_intro elim: consistentS_elim split: prod.split)
term 0 (**)
  
lemma consistentS_checkmem:
  assumes "consistentS R_' (dp param) s"
  shows "consistentS R_' (dp param) (checkmem param s)"
  using assms unfolding checkmem_def
  by (fastforce intro: consistentS_return consistentS_get
      consistentS_put consistentS_bind consistentM_upd elim: consistentM_elim split: option.splits)
term 0 (**)
  
lemma fun_app_lifted_transfer[transfer_rule]:
  "(consistentS (R ===> consistentS R') ===> consistentS R ===> consistentS R') (\<lambda>f x. f x) (\<lambda>f\<^sub>T x\<^sub>T. f\<^sub>T . x\<^sub>T)"
proof -
  { fix f f\<^sub>T x x\<^sub>T assume sf: "consistentS (R ===> consistentS R') f f\<^sub>T" and sx: "consistentS R x x\<^sub>T"
    { fix M ov oM assume cm: "consistentM M" and os:"runState (f\<^sub>T . x\<^sub>T) M = (ov, oM)"
      obtain fv M' where bf: "runState f\<^sub>T M = (fv, M')" and rf: "(R ===> consistentS R') f fv" and cm':"consistentM M'"
        using sf cm by (auto elim: consistentS_elim)
      obtain xv M'' where bx: "runState x\<^sub>T M' = (xv, M'')" and rx: "R x xv" and cm'': "consistentM M''"
        using sx cm' by (auto elim: consistentS_elim)
      have srfx: "consistentS R' (f x) (fv xv)"
        using rf rx by (auto dest: rel_funD)
      obtain res M''' where bres: "runState (fv xv) M'' = (res, M''')" and rres: "R' (f x) (res)" and cm''': "consistentM M'''"
        using srfx cm'' by (auto elim: consistentS_elim)
      have bfx: "runState (f\<^sub>T . x\<^sub>T) M = (res, M''')"
        unfolding fun_app_lifted_def bind_def by (auto simp: bf bx bres)
      have "R' (f x) ov" "consistentM oM"
        using os bfx rres cm''' by auto
    } hence "consistentS R' (f x) (f\<^sub>T . x\<^sub>T)" by (blast intro: consistentS_intro)
  } thus ?thesis by blast
qed

lemma lift_'_transfer[transfer_rule]: "R_' x (lift_' x)"
  unfolding lift_'_def ..

lemma lift_3_transfer[transfer_rule]: "R_3 f (lift_3 f)"
  unfolding lift_3_def lift_'_def by transfer_prover

lemma lift_33_transfer[transfer_rule]: "R_33 f (lift_33 f)"
  unfolding lift_33_def lift_3_def lift_'_def by transfer_prover
term 0 (**)
  
lemma lift_Cons_transfer[transfer_rule]: "R_33 Cons Cons\<^sub>T"
  unfolding Cons\<^sub>T_def by transfer_prover

term 0 (**)
lemma "R_q3p33 map map\<^sub>T"
proof -
  fix f f\<^sub>T assume "R_3 f f\<^sub>T"
  have "consistentS R_' (map f xs) (map\<^sub>T' f\<^sub>T xs)" for xs
    apply (induction xs)
     apply (unfold list.map map\<^sub>T'.simps)
    subgoal by transfer_prover
    subgoal premises prems thm prems
      apply transfer_prover_start
                  prefer 8 apply transfer_step
                 prefer 5 apply transfer_step
                prefer 6 apply transfer_step
               prefer 7 apply transfer_step
              prefer 7 apply transfer_step
             prefer 7 apply transfer_step
            prefer 6 apply transfer_step
           apply transfer_step
          apply transfer_step
      term lfp
      oops
end
end
end