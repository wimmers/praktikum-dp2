theory Grid_Path
  imports "../DP_CRelVS" "../DP_Lifting" "../DP_Proof"
begin
(*
definition lift_option_choice :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "lift_option_choice \<equiv> \<lambda>f v0 v1.
    case v0 of
      None \<Rightarrow> (case v1 of
        None \<Rightarrow> None
      | Some y \<Rightarrow> Some y)
    | Some x \<Rightarrow> (case v1 of
      None \<Rightarrow> Some x
      | Some y \<Rightarrow> Some (f x y))"

definition lift_option_choice :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "lift_option_choice \<equiv> \<lambda>f. \<lambda>v0. \<lambda>v1.
    case_option
      (case_option
        None
        (\<lambda>y. Some y)
        v1)
      (\<lambda>x. (case_option
        (Some x)
        (\<lambda>y. Some (f x y))
        v1))
      v0"

abbreviation min_opt :: "'a::ord option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "min_opt \<equiv> lift_option_choice min"
term 0 (**)

definition lift_option_choice\<^sub>T :: "('M, ('a =='M\<Longrightarrow> 'a =='M\<Longrightarrow> 'a) =='M\<Longrightarrow> 'a option =='M\<Longrightarrow> 'a option =='M\<Longrightarrow> 'a option) state" where
  "lift_option_choice\<^sub>T \<equiv> \<lambda>\<^sub>Tf v0 v1.
    case_option\<^sub>T
    . (case_option\<^sub>T
      . \<langle>None\<rangle>
      . (\<lambda>\<^sub>T y. Some\<^sub>T . \<langle>y\<rangle>)
      . \<langle>v1\<rangle>)
    . (\<lambda>\<^sub>T x. case_option\<^sub>T
      . (Some\<^sub>T . \<langle>x\<rangle>)
      . (\<lambda>\<^sub>T y. Some\<^sub>T . (\<langle>f\<rangle> . \<langle>x\<rangle> . \<langle>y\<rangle>))
      . \<langle>v1\<rangle>)
    . \<langle>v0\<rangle>"
  
abbreviation min_opt\<^sub>T :: "('M, 'a::ord option =='M\<Longrightarrow> 'a option =='M\<Longrightarrow> 'a option) state" where
  "min_opt\<^sub>T \<equiv> lift_option_choice\<^sub>T . min\<^sub>T"

context dp_consistency begin
lemma [transfer_rule]: "crel_vs ((R ===>\<^sub>T R ===>\<^sub>T R) ===>\<^sub>T rel_option R ===>\<^sub>T rel_option R ===>\<^sub>T rel_option R) lift_option_choice lift_option_choice\<^sub>T"
  unfolding lift_option_choice_def lift_option_choice\<^sub>T_def by transfer_prover
end
*)

definition "min_opt a b \<equiv>
  case (a, b) of
    (None, None) \<Rightarrow> None
  | (Some a0, None) \<Rightarrow> Some a0
  | (None, Some b0) \<Rightarrow> Some b0
  | (Some a0, Some b0) \<Rightarrow> Some (min a0 b0)"
term 0 (**)

context
  fixes W :: "nat \<Rightarrow> nat \<Rightarrow> nat option"
begin

fun ed :: "nat\<times>nat \<Rightarrow> nat option" where
  "ed (0, 0) = W 0 0"
| "ed (0, Suc j) = case_option None (\<lambda>prev.
                     case_option None (\<lambda>here.
                       Some (plus prev here)
                     ) (W 0 (Suc j))
                   ) (ed (0, j))"
| "ed (Suc i, 0) = case_option None (\<lambda>prev.
                     case_option None (\<lambda>here.
                       Some (plus prev here)
                     ) (W (Suc i) 0)
                   ) (ed (i, 0))"
| "ed (Suc i, Suc j) = case_option None (\<lambda>prev.
                         case_option None (\<lambda>here.
                           Some (plus prev here)
                         ) (W (Suc i) (Suc j))
                       ) (min_opt (ed (i, j)) (min_opt (ed (Suc i, j)) (ed (i, Suc j))))"

ML_file \<open>../scratch/Transform.ML\<close>
local_setup \<open>
lift_fun NONE;
\<close>
print_theorems

interpretation ed: dp_consistency ed .

term 0 (**)
lemma "ed.consistentDP ed\<^sub>T"
  by (dp_match induct: ed\<^sub>T.induct simp: ed.simps simp\<^sub>T: ed\<^sub>T.simps)

end