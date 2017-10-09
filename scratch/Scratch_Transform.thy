theory Scratch_Transform
  imports Main "../Monad" "../DP_Lifting"
begin
  
context (* Knapsack *)
  fixes w :: "nat \<Rightarrow> nat"
begin

fun su :: "nat\<times>nat \<Rightarrow> nat" where
  "su (0, W) = (if W < w 0 then 0 else w 0)" |
  "su (Suc i, W) = (if W < w (Suc i)
    then su (i, W)
    else max (su (i, W)) (w i + su (i, W - w i)))"

ML_val \<open>
val su_info = Function.get_info @{context} @{term su};
val su_simps = su_info |> #simps |> the;
val [su_simp0, su_simp1] = su_simps;
HOLogic.mk_eq;
Binding.name_of @{binding xx};

\<close>
term 0 (**)
ML_file \<open>Transform.ML\<close>
term 0 (*
ML \<open>
su_simp0;
transform_simp su_simp1;
suffix;
@{term a\<^sub>T};
\<close>
  
ML \<open>
val suT_fixes: (binding * typ option * mixfix) list =
  [(@{binding su\<^sub>T}, SOME @{typ "nat\<times>nat \<Rightarrow> (nat\<times>nat \<rightharpoonup> nat, nat) state"}, NoSyn)];
val suT_specs: Specification.multi_specs = 
  [(((Binding.empty, []),
   transform_simp su_simp0),
    [], []),
   (((Binding.empty, []),
    transform_simp su_simp1),
    [], [])];
\<close>
  *)
local_setup \<open>
lift_fun (SOME @{term su}) @{context}
\<close>
  
find_theorems su\<^sub>T
definition "a\<equiv>w"
ML_val \<open>
@{thms su\<^sub>T.simps};
Function.get_info @{context} @{term su};

\<close>
  thm refl[of x]
ML_val \<open>
op OF;
Thm.instantiate;
Thm.rule_attribute;
@{term xx} |> Thm.cterm_of @{context};
Sign.certify_term;
(*Thm.cterm_of @{context} (Bound 1)*)
@{thms transfer_forall_eq transfer_implies_eq};
rewrite_goal_tac;
Seq.DETERM;
\<close>
ML \<open>
val _ = Transfer.get_relator_eq_raw @{context};
@{thms is_equality_eq};
TRY;
fun nth' l i = nth i l;
Transfer.get_transfer_raw @{context} |> drop 240 |> take 10;
Item_Net.update;
Transfer.transfer_raw_add;
val _ = Transfer.get_relator_eq @{context};
\<close>
ML \<open>
val transfer_raw = Thm.intro_rules;
val known_frees = [];

val relator_eq_raw = Thm.full_rules;
val relator_domain = Thm.full_rules;
Thm.theory_of_thm @{lemma "P \<Longrightarrow> Q \<Longrightarrow> R \<Longrightarrow> P" by auto}
\<close>
  declare TrueI[transfer_rule]
  term 0 (*
  
ML \<open>
val su_term = Const ("Scratch_Transform.su", @{typ "(nat \<Rightarrow> nat) \<Rightarrow> nat \<times> nat \<Rightarrow> nat"});
val (lhs, rhs) = Thm.full_prop_of su_simp0 |> HOLogic.dest_Trueprop |> HOLogic.dest_eq;
(exists_subterm (fn x => x = su_term) rhs);
rhs
\<close>
end
end
  