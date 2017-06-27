theory Bellman_Ford
  imports "../DP_Lifting" "../DP_Consistency"
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
    . (min)
    . (map
        . (\<lambda>i. plus . (W i j) . (bf (k, i)))
        . (upt . 0 . n))
    . (bf (k, j))"
thm bf.simps
term 0 (**)
  
fun bf\<^sub>T :: "nat\<times>nat \<Rightarrow>\<^sub>T int" where
  "bf\<^sub>T$ (0, j) =CHECKMEM= \<langle>W 0 j\<rangle>\<^sub>T"
| "bf\<^sub>T$ (Suc k, j) =CHECKMEM=
    \<langle>fold\<^sub>T\<rangle>\<^sub>T
    .\<^sub>T \<langle>min\<^sub>T\<rangle>\<^sub>T
    .\<^sub>T (\<langle>map\<^sub>T\<rangle>\<^sub>T
      .\<^sub>T \<langle>\<lambda>i. \<langle>plus\<^sub>T\<rangle>\<^sub>T .\<^sub>T \<langle>W i j\<rangle>\<^sub>T .\<^sub>T (bf\<^sub>T (k, i))\<rangle>\<^sub>T
      .\<^sub>T (\<langle>upt\<^sub>T\<rangle>\<^sub>T .\<^sub>T \<langle>0\<rangle>\<^sub>T .\<^sub>T \<langle>n\<rangle>\<^sub>T))
    .\<^sub>T (bf\<^sub>T (k, j))"
term 0 (**)
  
interpretation bf: dp_consistency bf .
context
  includes lifting_syntax
begin

definition K :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "K x \<equiv> \<lambda> a b. a=x \<and> b=x"
term 0 (**)

lemma bf_induct:
  "\<lbrakk>\<And>j. P (0, j);
    \<And>k j. \<lbrakk>\<And>x. P (k, x);
           P (k, j)
           \<rbrakk> \<Longrightarrow> P (Suc k, j)
   \<rbrakk> \<Longrightarrow> P (x::nat\<times>nat)"
  by (fact bf\<^sub>T.induct)

lemma bf_inductS:
  "\<lbrakk>\<And>j. bf.consistentS op = (bf (0, j)) (bf\<^sub>T (0, j));
    \<And>k j. \<lbrakk>\<And>x. bf.consistentS op = (bf (k, x)) (bf\<^sub>T (k, x));
           bf.consistentS op = (bf (k, j)) (bf\<^sub>T (k, j))
           \<rbrakk> \<Longrightarrow> bf.consistentS op = (bf (Suc k, j)) (bf\<^sub>T (Suc k, j))
   \<rbrakk> \<Longrightarrow> bf.consistentS op = (bf (x::nat\<times>nat)) (bf\<^sub>T x)"
  by (fact bf_induct)


lemma bf_inductS':
  "\<lbrakk>\<And>j. bf.consistentS op = (bf (0, j)) (bf\<^sub>T (0, j));
    \<And>k j. \<lbrakk>K k k k;
           K j j j;
           (rel_prod (K k) op = ===> bf.consistentS op =) bf bf\<^sub>T;
           (rel_prod (K k) (K j) ===> bf.consistentS op =) bf bf\<^sub>T
           \<rbrakk> \<Longrightarrow> bf.consistentS op = (bf (Suc k, j)) (bf\<^sub>T (Suc k, j))
   \<rbrakk> \<Longrightarrow> bf.consistentS op = (bf (x::nat\<times>nat)) (bf\<^sub>T x)"
  unfolding rel_prod.simps rel_fun_def K_def by (simp add: bf_inductS)
term 0 (**)

lemma "bf.consistentDP bf\<^sub>T"
  apply (rule bf.consistentDP_intro, induct_tac rule: bf_inductS', unfold bf\<^sub>T.simps; rule bf.consistentS_checkmem, unfold bf.simps)
  subgoal premises prems[transfer_rule] by transfer_prover
  subgoal premises prems[transfer_rule] by transfer_prover
  done

end