theory Bellman_Ford
  imports "../DP_Lifting" "../DP_Consistency" "../DP_Proof"
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

definition K :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "K x \<equiv> \<lambda> a b. a=x \<and> b=x"
term 0 (**)

lemma bf_induct:
  "\<lbrakk>\<And>j. P (0, j);
    \<And>k j. \<lbrakk>\<And>x. x \<in> set [0..<n] \<Longrightarrow> P (k, x);
           P (k, j)
           \<rbrakk> \<Longrightarrow> P (Suc k, j)
   \<rbrakk> \<Longrightarrow> P (x::nat\<times>nat)"
  by (fact bf\<^sub>T.induct)

lemma bf_inductS:
  "\<lbrakk>\<And>j. bf.consistentS op = (bf (0, j)) (bf\<^sub>T (0, j));
    \<And>k j. \<lbrakk>\<And>x. x \<in> set [0..<n] \<Longrightarrow> bf.consistentS op = (bf (k, x)) (bf\<^sub>T (k, x));
           bf.consistentS op = (bf (k, j)) (bf\<^sub>T (k, j))
           \<rbrakk> \<Longrightarrow> bf.consistentS op = (bf (Suc k, j)) (bf\<^sub>T (Suc k, j))
   \<rbrakk> \<Longrightarrow> bf.consistentS op = (bf (x::nat\<times>nat)) (bf\<^sub>T x)"
  by (fact bf_induct)


lemma bf_inductS':
  "\<lbrakk>\<And>j. bf.consistentS op = (bf (0, j)) (bf\<^sub>T (0, j));
    \<And>k j. \<lbrakk>K k k k;
           K j j j;
           (rel_prod (K k) (eq_onp (\<lambda>x. x\<in>set [0..<n])) ===> bf.consistentS op =) bf bf\<^sub>T;
           (rel_prod (K k) (K j) ===> bf.consistentS op =) bf bf\<^sub>T
           \<rbrakk> \<Longrightarrow> bf.consistentS op = (bf (Suc k, j)) (bf\<^sub>T (Suc k, j))
   \<rbrakk> \<Longrightarrow> bf.consistentS op = (bf (x::nat\<times>nat)) (bf\<^sub>T x)"
  unfolding K_def eq_onp_def rel_prod.simps using bf_inductS by blast

lemma "bf.consistentDP bf\<^sub>T"
  by (dp_match induct: bf_inductS' simp: bf.simps simp\<^sub>T: bf\<^sub>T.simps)
term 0 (**)

thm bf.induct bf\<^sub>T.induct

end