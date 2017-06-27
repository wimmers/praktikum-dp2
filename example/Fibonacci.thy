theory Fibonacci
  imports "../DP_Lifting" "../DP_Consistency" "../DP_Proof"
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
thm fib.simps
term 0 (**)

fun fib\<^sub>T :: "nat \<Rightarrow>\<^sub>T int option" where
  "fib\<^sub>T$ 0 =CHECKMEM= \<langle>Some 0\<rangle>"
| "fib\<^sub>T$ (Suc 0) =CHECKMEM= \<langle>Some 1\<rangle>"
| "fib\<^sub>T$ (Suc (Suc n)) =CHECKMEM= case_prod\<^sub>T
    . (\<lambda>\<^sub>T of1 of0. case_option\<^sub>T
        . \<langle>None\<rangle>
        . (\<lambda>\<^sub>T f1. case_option\<^sub>T
          . \<langle>None\<rangle>
          . (\<lambda>\<^sub>T f0. \<langle>Some (f1 + f0)\<rangle>)
          . \<langle>of0\<rangle>)
        . \<langle>of1\<rangle>)
    . (Pair\<^sub>T . (fib\<^sub>T (Suc n)) . (fib\<^sub>T n))"
term 0 (**)

interpretation fib: dp_consistency fib .

lemma "fib.consistentDP fib\<^sub>T"
  by (dp_match induct: fib\<^sub>T.induct simp: fib.simps simp\<^sub>T: fib\<^sub>T.simps)
end