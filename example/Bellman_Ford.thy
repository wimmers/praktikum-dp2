theory Bellman_Ford
  imports "../DP_Lifting"
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
      min
      (map
        (\<lambda>i. plus (bf (k, i)) (W i j))
        (upt 0 n))
      (bf (k, j))"
thm bf.simps
term 0 (**)

fun bf\<^sub>T :: "nat\<times>nat \<Rightarrow> (nat\<times>nat \<rightharpoonup> int, int) state" where
  "bf\<^sub>T$ (0, j) =CHECKMEM= \<langle>W 0 j\<rangle>"
| "bf\<^sub>T$ (Suc k, j) =CHECKMEM=
    \<langle>fold\<^sub>T\<rangle>
    . \<langle>min\<^sub>T\<rangle>
    . (\<langle>map\<^sub>T\<rangle>
      . \<langle>\<lambda>i. \<langle>plus\<^sub>T\<rangle> . (bf\<^sub>T (k, i)) . \<langle>W i j\<rangle>\<rangle>
      . \<langle>upt 0 n\<rangle>)
    . (bf\<^sub>T (k, j))"
term 0 (**)
end