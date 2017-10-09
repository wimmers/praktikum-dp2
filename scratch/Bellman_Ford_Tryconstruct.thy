theory Bellman_Ford_Tryconstruct
  imports "../DP_Lifting" "../DP_CRelVS" "../DP_Proof"
begin
  
consts n :: nat
consts W :: "nat \<Rightarrow> nat \<Rightarrow> int"
term 0 (**)
  
  (*
fun bf :: "nat\<times>nat \<Rightarrow> int" where
  "bf (0,j) = W 0 j"
| "bf (Suc k, j) = fold min [bf (k, i) + W i j. i \<leftarrow> [0..<n]] (bf (k, j))"
term 0 (**)
*)
  
fun bf :: "nat\<times>nat \<Rightarrow> int" where
  "bf (0, j) = W 0 j"
| "bf (Suc k, j) =
    fold
      (min)
      (map
          (\<lambda>i. plus (W i j) (bf (k, i)))
          (upt 0 n))
      (bf (k, j))"
thm bf.simps
thm bf.induct
term 0 (**)
  
lemma map\<^sub>T_return_return_cong[fundef_cong]:
  fixes f g xs
  assumes "\<And>x. x\<in>set xs \<Longrightarrow> f x = g x"
  shows "map\<^sub>T . \<langle>f\<rangle> . \<langle>xs\<rangle> = map\<^sub>T . \<langle>g\<rangle> . \<langle>xs\<rangle>"
  sorry
term 0 (**)
  
fun bf\<^sub>T :: "nat\<times>nat \<Rightarrow>\<^sub>T int" where
  "bf\<^sub>T$ (0, j) =CHECKMEM= \<langle>W 0 j\<rangle>"
| "bf\<^sub>T$ (Suc k, j) =CHECKMEM=
    fold\<^sub>T
    . min\<^sub>T
    . (map\<^sub>T
      . (\<lambda>\<^sub>Ti. plus\<^sub>T . \<langle>W i j\<rangle> . (bf\<^sub>T (k, i)))
      . \<langle>upt 0 n\<rangle>)
    . (bf\<^sub>T (k, j))"
thm bf\<^sub>T.simps
thm bf\<^sub>T.induct
term 0 (**)
                          
interpretation bf: dp_consistency bf .
    
notation bf.rel_fun_lifted (infixr "===>\<^sub>T" 55)

notepad
begin
  
  
  {
    fix j::nat
    have "W 0 j = W 0 j"
      by (fact refl)
    have "bf.crel_vs op = (W 0 j) \<langle>W 0 j\<rangle>"
      by (fact bf.crel_vs_return[where R="op =", OF \<open>W 0 j = W 0 j\<close>])
  }
next
  {
    fix k::nat and j::nat
    assume IH1: "bf.crel_vs op = (bf (k, j)) (bf\<^sub>T (k, j))"
    assume IH2: "x \<in> set [0..<n] \<Longrightarrow> bf.crel_vs op = (bf (k, x)) (bf\<^sub>T (k, x))" for x
    note bf.fold_transfer
    note bf.min_transfer
    have "bf.crel_vs (list_all2 op = ===>\<^sub>T op = ===>\<^sub>T op =) (fold min) (fold\<^sub>T . min\<^sub>T)"
      by (fact bf.crel_vs_fun_app[OF bf.fold_transfer, OF bf.min_transfer])
    {
      fix i::nat
      assume "i \<in> set [0..<n]"
      note bf.plus_transfer
      have "W i j = W i j"
        by (fact refl)
      have "bf.crel_vs op = (W i j) \<langle>W i j\<rangle>"
        by (fact bf.crel_vs_return[where R="op =", OF \<open>W i j = W i j\<close>])
      have "bf.crel_vs (op = ===>\<^sub>T op =) (op + (W i j)) (plus\<^sub>T . \<langle>W i j\<rangle>)"
        by (fact bf.crel_vs_fun_app[OF bf.plus_transfer, OF \<open>bf.crel_vs op = (W i j) \<langle>W i j\<rangle>\<close>])
      note IH2
      have "bf.crel_vs op = (bf (k, i)) (bf\<^sub>T (k, i))"
        by (fact IH2[OF \<open>i \<in> set [0..<n]\<close>])
      have "bf.crel_vs op = (W i j + bf (k, i)) (plus\<^sub>T . \<langle>W i j\<rangle> . (bf\<^sub>T (k, i)))"
        by (fact bf.crel_vs_fun_app[OF \<open>bf.crel_vs (op = ===>\<^sub>T op =) (op + (W i j)) (plus\<^sub>T . \<langle>W i j\<rangle>)\<close> \<open>bf.crel_vs op = (bf (k, i)) (bf\<^sub>T (k, i))\<close>])
          thm \<open>bf.crel_vs op = ((\<lambda>i. W i j + bf (k, i)) i) ((\<lambda>i. plus\<^sub>T . \<langle>W i j\<rangle> . (bf\<^sub>T (k, i))) i)\<close>
      have "bf.crel_vs op = ((\<lambda>i. W i j + bf (k, i)) i) ((\<lambda>i. plus\<^sub>T . \<langle>W i j\<rangle> . (bf\<^sub>T (k, i))) i)"
        by (fact \<open>bf.crel_vs op = (W i j + bf (k, i)) (plus\<^sub>T . \<langle>W i j\<rangle> . (bf\<^sub>T (k, i)))\<close>)
    }
    have "list_all2 op = [0..<n] [0..<n]"
      by (fact refl[of "[0..<n]", folded list.rel_eq])
    have "bf.crel_vs (list_all2 op =) [0..<n] \<langle>[0..<n]\<rangle>"
      by (insert \<open>list_all2 op = [0..<n] [0..<n]\<close>) (fact bf.crel_vs_return)
      term 0 (**
    have "bf.crel_vs op = [0..<n] \<langle>[0..<n]\<rangle>"
      by (fact bf.crel_vs_return[where R="op =", OF \<open>[0..<n] = [0..<n]\<close>])
    have "bf.crel_vs op = (map (\<lambda>i. W i j + bf (k, i)) [0..<n]) (map\<^sub>T . \<langle>\<lambda>i. plus\<^sub>T . \<langle>W i j\<rangle> . (bf\<^sub>T (k, i))\<rangle> . \<langle>[0..<n]\<rangle>)"
      by (insert \<open>\<And>i. i \<in> set [0..<n] \<Longrightarrow> bf.crel_vs op = (W i j + bf (k, i)) (plus\<^sub>T . \<langle>W i j\<rangle> . (bf\<^sub>T (k, i)))\<close> \<open>bf.crel_vs op = [0..<n] \<langle>[0..<n]\<rangle>\<close>) (fact bf.crel_vs_map_simple)
        have
term 0 (*
    ML_prf \<open>
val t0 = @{thm bf.crel_vs_map_simple};
val t1 = @{thm \<open>\<And>i. i \<in> set [0..<n] \<Longrightarrow> bf.crel_vs op = (W i j + bf (k, i)) (plus\<^sub>T . \<langle>W i j\<rangle> . (bf\<^sub>T (k, i)))\<close>};
val t2 = @{thm \<open>bf.crel_vs op = [0..<n] \<langle>[0..<n]\<rangle>\<close>};
t0 OF [t1, t2];
(*Drule.compose (t0, 1, t1);*)
\<close>
  }
end
  term 0 (*
lemma "list_all2 op = l l"
  thm list.rel_eq list_all2_eq
    thm bf.map_transfer_inset_unfolded'
    term option.rel_option
    term list.list_all2
    ML_prf \<open>
[@{type_name list}, @{type_name option}, @{type_name prod}, @{type_name fun}]
|> map (BNF_Def.rel_of_bnf o the o BNF_Def.bnf_of @{context});
\<close>
    have "cre(map (\<lambda>i. plus (W i j) (bf (k, i))) (upt 0 n))"
      thm map_cong
