theory Scratch_relator_mono
  imports Main
begin

definition le_equality :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "le_equality R \<equiv> R \<le> op ="
  
definition ge_equality :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "ge_equality R \<equiv> R \<ge> op ="
  
lemma ge_equality_refl[transfer_rule]:
  fixes R x
  assumes "ge_equality R"
  shows "R x x"
  using assms unfolding ge_equality_def by auto

ML_val \<open>
Transfer.get_transfer_raw @{context} |> rev |> hd;
Transfer.get_transfer_raw @{context} |> hd;
\<close>

term 0 (**)
  
lemma is_equality_le_equality:
  fixes R
  shows "is_equality R \<Longrightarrow> le_equality R"
  unfolding is_equality_def le_equality_def by auto
    
lemma is_equality_ge_equality:
  fixes R
  shows "is_equality R \<Longrightarrow> ge_equality R"
  unfolding is_equality_def ge_equality_def by auto

lemma le_equality_eq_onp:
  fixes P
  shows "le_equality (eq_onp P)"
  unfolding le_equality_def by (fact eq_onp_le_eq)
    
lemma
  fixes R
  shows le_equality_rel_option: "le_equality R \<Longrightarrow> le_equality (rel_option R)"
    and ge_equality_rel_option: "ge_equality R \<Longrightarrow> ge_equality (rel_option R)"
  by (-; unfold le_equality_def ge_equality_def, fold option.rel_eq, rule option.rel_mono, assumption)+
    
lemma
  fixes R
  shows le_equality_list_all2: "le_equality R \<Longrightarrow> le_equality (list_all2 R)"
    and ge_equality_list_all2: "ge_equality R \<Longrightarrow> ge_equality (list_all2 R)"
  by (-; unfold le_equality_def ge_equality_def, fold list.rel_eq, rule list.rel_mono, assumption)+
    
lemma
  fixes R0 R1
  shows le_equality_rel_prod: "le_equality R0 \<Longrightarrow> le_equality R1 \<Longrightarrow> le_equality (rel_prod R0 R1)"
    and ge_equality_rel_prod: "ge_equality R0 \<Longrightarrow> ge_equality R1 \<Longrightarrow> ge_equality (rel_prod R0 R1)"
  by (-; unfold le_equality_def ge_equality_def, fold prod.rel_eq, rule prod.rel_mono; assumption)+

lemma
  fixes R0 R1
  shows le_equality_rel_fun: "ge_equality R0 \<Longrightarrow> le_equality R1 \<Longrightarrow> le_equality (rel_fun R0 R1)"
    and ge_equality_rel_fun: "le_equality R0 \<Longrightarrow> ge_equality R1 \<Longrightarrow> ge_equality (rel_fun R0 R1)"
  by (-; unfold le_equality_def ge_equality_def, fold fun.rel_eq, rule fun_mono; assumption)+

lemmas relator_mono =
  is_equality_le_equality is_equality_ge_equality
  le_equality_eq_onp
  le_equality_rel_option ge_equality_rel_option
  le_equality_list_all2 ge_equality_list_all2
  le_equality_rel_prod ge_equality_rel_prod
  le_equality_rel_fun ge_equality_rel_fun

end