theory Fibonacci
  imports "../DP_Lifting" "../DP_CRelVS" "../DP_Proof"
begin
  
  (*
fun fib :: "nat \<Rightarrow> int option" where
  "fib 0 = Some 0"
| "fib (Suc 0) = Some 1"
| "fib (Suc (Suc n)) = (case (fib (Suc n), fib n) of (Some f1, Some f0) \<Rightarrow> Some (f1 + f0) | _ \<Rightarrow> None)"
term 0 (**)
*)

fun fib :: "nat \<Rightarrow> int option" where
  "fib 0 = Some 0"
| "fib (Suc 0) = Some 1"
| "fib (Suc (Suc n)) = case_prod
      (\<lambda>of1 of0. case_option
        None
        (\<lambda>f1. case_option
          None
          (\<lambda>f0. Some (f1 + f0))
          of0)
        of1)
      (Pair (fib (Suc n)) (fib n))"


ML_file \<open>../scratch/Transform.ML\<close>
local_setup \<open>
lift_fun NONE;
\<close>

interpretation fib: dp_consistency fib .

lemma "fib.consistentDP fib\<^sub>T"
  by (dp_match induct: fib\<^sub>T.induct simp: fib.simps simp\<^sub>T: fib\<^sub>T.simps)
end