theory Scratch_Tactic
  imports Main
begin
  
lemma "x@[] = x"
  (* apply (rule append_Nil2) done *)
  apply (tactic \<open>FIRSTGOAL (resolve0_tac [@{thm append_Nil2}])\<close>) done
    
  ML \<open>
resolve_tac;
op THEN_ALL_NEW;
\<close>
end