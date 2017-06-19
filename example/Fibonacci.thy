theory Fibonacci
  imports "../DP_Lifting" "../DP_Consistency"
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
      (\<lambda>of1. (\<lambda>of0. case_option
        None
        (\<lambda>f1. case_option
          None
          (\<lambda>f0. Some (f1 + f0))
          of0))
        of1)
      (Pair (fib (Suc n)) (fib n))"
thm fib.simps
term 0 (**)

fun fib\<^sub>T :: "nat \<Rightarrow>\<^sub>T int option" where
  "fib\<^sub>T$ 0 =CHECKMEM= \<langle>Some 0\<rangle>"
| "fib\<^sub>T$ (Suc 0) =CHECKMEM= \<langle>Some 1\<rangle>"
| "fib\<^sub>T$ (Suc (Suc n)) =CHECKMEM= \<langle>case_prod\<^sub>T\<rangle>
    . \<langle>\<lambda>of1. \<langle>\<lambda>of0. \<langle>case_option\<^sub>T\<rangle>
        . \<langle>None\<rangle>
        . \<langle>\<lambda>f1. \<langle>case_option\<^sub>T\<rangle>
          . \<langle>None\<rangle>
          . \<langle>\<lambda>f0. \<langle>Some (f1 + f0)\<rangle>\<rangle>
          . \<langle>of0\<rangle>\<rangle>\<rangle>
        . \<langle>of1\<rangle>\<rangle>
    . (\<langle>Pair\<^sub>T\<rangle> . (fib\<^sub>T (Suc n)) . (fib\<^sub>T n))"
term 0 (**)

lemma "consistentDP fib fib\<^sub>T"
  apply (rule consistentDP_intro, induct_tac rule: fib\<^sub>T.induct; unfold fib\<^sub>T.simps, rule consistentS_checkmem, unfold fib.simps)
  subgoal
    apply (rule consistentS_return)
    subgoal by (rule refl)
    done
  subgoal
    apply (rule consistentS_return)
    subgoal by (rule refl)
    done
  subgoal
    
  done
term 0 (**)

end