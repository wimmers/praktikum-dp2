theory Tree_Diameter
  imports "../DP_CRelVS"
begin

datatype tree = Node "(int \<times> tree) list"
term 0 (**)


context dp_consistency begin
definition hd\<^sub>T :: "('M, 'a list =='M\<Longrightarrow> 'a) state" where
  "hd\<^sub>T \<equiv> lift_3 hd"
definition "cc \<equiv> case_list"
context
  includes lifting_syntax
begin
thm hd_def[folded cc_def]
    
  thm list.rel_intros list.rel_induct list.rel_transfer list.rel_inject
  thm list.rel_cases list.rel_cong
    thm list.rel_flip list.rel_sel
lemma "list_all2 P (x#xs) (y#ys) \<Longrightarrow> P x y \<and> list_all2 P xs ys"
  using [[simp_trace]]
  by simp
    


term 0 (**
lemma "crel_vs (list_all2 R ===>\<^sub>T R) hd hd\<^sub>T"
  thm lift_3_transfer
  unfolding hd\<^sub>T_def
  apply transfer_prover_start
    apply transfer_step
    
    