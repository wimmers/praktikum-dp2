theory Bellman_Ford
  imports "../DP_Lifting" "../DP_CRelVS" "../DP_Proof" "../scratch/Scratch_relator_mono"
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
context
  includes lifting_syntax
begin

abbreviation K :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "K x \<equiv> eq_onp (op = x)"
term 0 (**)

lemma bf_induct:
  "\<lbrakk>\<And>j. P (0, j);
    \<And>k j. \<lbrakk>\<And>x. x \<in> set [0..<n] \<Longrightarrow> P (k, x);
           P (k, j)
           \<rbrakk> \<Longrightarrow> P (Suc k, j)
   \<rbrakk> \<Longrightarrow> P (x::nat\<times>nat)"
  by (fact bf\<^sub>T.induct)

lemma bf_inductS:
  "\<lbrakk>\<And>j. bf.crel_vs op = (bf (0, j)) (bf\<^sub>T (0, j));
    \<And>k j. \<lbrakk>\<And>x. x \<in> set [0..<n] \<Longrightarrow> bf.crel_vs op = (bf (k, x)) (bf\<^sub>T (k, x));
           bf.crel_vs op = (bf (k, j)) (bf\<^sub>T (k, j))
           \<rbrakk> \<Longrightarrow> bf.crel_vs op = (bf (Suc k, j)) (bf\<^sub>T (Suc k, j))
   \<rbrakk> \<Longrightarrow> bf.crel_vs op = (bf (x::nat\<times>nat)) (bf\<^sub>T x)"
  by (fact bf_induct)


lemma bf_inductS':
  "\<lbrakk>\<And>j. bf.crel_vs op = (bf (0, j)) (bf\<^sub>T (0, j));
    \<And>k j. \<lbrakk>(rel_prod (K k) (eq_onp (\<lambda>x. x\<in>set [0..<n])) ===> bf.crel_vs op =) bf bf\<^sub>T;
           (rel_prod (K k) (K j) ===> bf.crel_vs op =) bf bf\<^sub>T
           \<rbrakk> \<Longrightarrow> bf.crel_vs op = (bf (Suc k, j)) (bf\<^sub>T (Suc k, j))
   \<rbrakk> \<Longrightarrow> bf.crel_vs op = (bf (x::nat\<times>nat)) (bf\<^sub>T x)"
  unfolding eq_onp_def rel_prod.simps using bf_inductS by blast

thm eq_onp_to_eq
  
notation bf.rel_fun_lifted (infixr "===>\<^sub>T" 55)
  
lemma "bf.consistentDP bf\<^sub>T"
  apply (rule dp_consistency.consistentDP_intro)
    subgoal for param
      apply (rule bf.induct)
       apply (unfold bf\<^sub>T.simps)
      subgoal for j
        apply (rule dp_consistency.crel_vs_checkmem)
        apply (unfold bf.simps)
          
        apply (rule bf.crel_vs_return[where R="op =" and x="W 0 j" and y="W 0 j"])
        apply (rule refl[of "W 0 j"])
        done
      subgoal premises IH for k j
        apply (rule dp_consistency.crel_vs_checkmem)
        apply (unfold bf.simps)
        apply (rule bf.crel_vs_fun_app[
            where f="fold min (map (\<lambda>i. W i j + bf (k, i)) [0..<n])" and x="(bf (k, j))"
              and f\<^sub>T="fold\<^sub>T . min\<^sub>T . (map\<^sub>T . \<langle>\<lambda>i. plus\<^sub>T . \<langle>W i j\<rangle> . (bf\<^sub>T (k, i))\<rangle> .\<langle>[0..<n]\<rangle>)"
              and x\<^sub>T="(bf\<^sub>T (k, j))"
              and ?R0.0="op ="
              and ?R1.0="op ="
              ])
         apply (rule bf.crel_vs_fun_app[
              where f="fold min" and x="map (\<lambda>i. W i j + bf (k, i)) [0..<n]"
                and f\<^sub>T="fold\<^sub>T . min\<^sub>T"
                and x\<^sub>T="map\<^sub>T . \<langle>\<lambda>i. plus\<^sub>T . \<langle>W i j\<rangle> . (bf\<^sub>T (k, i))\<rangle> . \<langle>[0..<n]\<rangle>"
                and ?R0.0="list_all2 op ="
                and ?R1.0="op = ===>\<^sub>T op ="
                ])
          apply (rule bf.crel_vs_fun_app[
              where f=fold and x=min
                and f\<^sub>T=fold\<^sub>T and x\<^sub>T=min\<^sub>T
                and ?R0.0="op = ===>\<^sub>T op = ===>\<^sub>T op ="
                and ?R1.0="list_all2 op = ===>\<^sub>T op = ===>\<^sub>T op ="
                ])
           apply (fact bf.fold_transfer)
          apply (fact bf.min_transfer)
         apply (rule bf.map_transfer_inset_unfolded'[
              where f="\<lambda>i. W i j + bf (k, i)" and xs="[0..<n]"
                and f\<^sub>T'="\<lambda>i. plus\<^sub>T . \<langle>W i j\<rangle> . (bf\<^sub>T (k, i))" and xs\<^sub>T="\<langle>[0..<n]\<rangle>"
                and ?R0.0="op =" and ?R1.0="op ="
                ])
        subgoal premises prems for x x\<^sub>T'
          apply (rule bf.crel_vs_fun_app[
                where f="op + (W x j)" and x="bf (k, x)"
                  and f\<^sub>T="plus\<^sub>T . \<langle>W x\<^sub>T' j\<rangle>" and x\<^sub>T="bf\<^sub>T (k, x\<^sub>T')"
                  and ?R0.0="op =" and ?R1.0="op ="
                  ])
           apply (rule bf.crel_vs_fun_app[
                where f="op +" and x="(W x j)"
                  and f\<^sub>T="plus\<^sub>T" and x\<^sub>T="\<langle>W x\<^sub>T' j\<rangle>"
                  and ?R0.0="op =" and ?R1.0="op = ===>\<^sub>T op ="
                  ])
            apply (fact bf.plus_transfer)
           apply (rule bf.crel_vs_return[where x="W x j" and y="W x\<^sub>T' j" and R="op ="])
           apply (rule cong[where f="W x" and g="W x\<^sub>T'" and x=j and y=j])
            apply (rule cong[where f="W" and g="W" and x=x and y=x\<^sub>T'])
             apply (fact refl)
            apply (fact prems)
           apply (fact refl)
            using prems IH(2)[where x=x\<^sub>T']
              
            oops
lemma eq_onp_eq: "(eq_onp P0 ===> eq_onp P1 ===> op =) f f"
  unfolding eq_onp_def rel_fun_def by auto
ML  \<open>
fun tac0 ctx = REPEAT_ALL_NEW (resolve_tac ctx (Transfer.get_transfer_raw ctx));
fun tac1 ctx = DETERM o Transfer.eq_tac ctx;
fun transfer_step_tac ctx = tac0 ctx THEN_ALL_NEW tac1 ctx;

fun eq_tac' ctxt =
  TRY o REPEAT_ALL_NEW (resolve_tac ctxt @{thms relator_eq_raw relator_mono})
  THEN_ALL_NEW resolve_tac ctxt @{thms is_equality_eq};
fun tac1' ctx = DETERM o eq_tac' ctx;
fun transfer_step_tac' ctx = tac0 ctx THEN_ALL_NEW tac1' ctx;
\<close>

lemma K_self: "K x x x"  
  unfolding eq_onp_def by auto

lemma K_fun:
  fixes R f g x
  assumes "R (f x) (g x)"
  shows "(K x ===> R) f g"
  using assms unfolding eq_onp_def by auto

term 0 (**)
lemma "bf.consistentDP bf\<^sub>T"
  apply (rule bf.consistentDP_intro)
  subgoal for param
    apply (rule bf_inductS')
     apply (unfold bf\<^sub>T.simps)
    subgoal
      apply (rule bf.crel_vs_checkmem)
      apply (unfold bf.simps)
      apply transfer_prover
      done
    subgoal premises prems
      apply (rule bf.crel_vs_checkmem)
      apply (unfold bf.simps)
      supply [transfer_rule] = prems K_self K_fun
      apply transfer_prover_start
                          apply transfer_step
                          apply transfer_step
                          apply transfer_step back back back back back back back back
                          apply transfer_step
                          apply transfer_step
                          apply transfer_step
                          apply transfer_step
                         apply transfer_step back back back back
                        apply transfer_step
                       apply transfer_step back back back back back back back back back back back back
                      apply transfer_step back
                     apply transfer_step
                    apply (tactic \<open>HEADGOAL (transfer_step_tac' @{context})\<close>) 
                   apply transfer_step
                  apply transfer_step back
                 apply transfer_step
                apply transfer_step
               apply transfer_step
              supply [transfer_rule] = bf.map_transfer_inset0
              apply transfer_step
             apply transfer_step
            apply transfer_step
           apply transfer_step back
          supply [transfer_rule] = bf.fold_transfer
          apply transfer_step
         apply transfer_step
        apply transfer_step
       apply transfer_step
      apply transfer_prover_end
      done
    done
  done
