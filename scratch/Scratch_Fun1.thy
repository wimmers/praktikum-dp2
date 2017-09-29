theory Scratch_Fun1
  imports Main
begin

context (* Longest path *)
  fixes v :: "nat \<Rightarrow> nat"
    and p :: "nat \<Rightarrow> nat"
  assumes p_lt: "p (Suc j) < Suc j"
begin


text \<open>Dimensionality given by i\<close>
function wis :: "nat \<Rightarrow> nat" where
  "wis 0 = 0" |
  "wis (Suc i) = max (wis (p (Suc i)) + v i) (wis i)"
  by pat_completeness auto
termination
  by (relation "(\<lambda>p. size p) <*mlex*> {}") (auto intro: wf_mlex mlex_less simp: p_lt)

ML \<open>
val wis_info = Function.get_info @{context} @{term wis};
\<close>

ML \<open>
val wis_totality = wis_info |> #totality |> the;
\<close>
find_theorems wis_dom
find_theorems wis_rel

end

end