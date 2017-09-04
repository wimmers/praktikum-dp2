theory Scratch
  imports Main
begin
term int
term fold
  
fun f :: "nat \<Rightarrow> nat" where
  "f 0 = 0"
| "f (Suc x) = fold op + (map (\<lambda>x. f) [0..<x]) 0"
end