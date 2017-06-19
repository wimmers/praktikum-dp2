theory DP_Lifting
  imports Main "./Monad"
begin

(* Types *)
type_synonym ('a,'M,'b) fun_lifted = "'a \<Rightarrow> ('M,'b) state" ("_ ==_\<Longrightarrow> _" [3,1000,2] 2)
type_synonym ('a,'b) dpfun = "'a ==('a\<rightharpoonup>'b)\<Longrightarrow> 'b" (infixr "\<Rightarrow>\<^sub>T" 2)
term 0 (**)

(* Basics *)
definition fun_app_lifted :: "('M,'a =='M\<Longrightarrow> 'b) state \<Rightarrow> ('M,'a) state \<Rightarrow> ('M,'b) state" (infixl "." 999) where
  "f\<^sub>T . x\<^sub>T \<equiv> do { f \<leftarrow> f\<^sub>T; x \<leftarrow> x\<^sub>T; f x }"

definition fcomp_lifted :: "('b =='M\<Longrightarrow> 'c) =='M\<Longrightarrow> ('a =='M\<Longrightarrow> 'b) =='M\<Longrightarrow> ('a =='M\<Longrightarrow> 'c)" where
  "fcomp_lifted \<equiv> \<lambda>g. \<langle>\<lambda>f. \<langle>\<lambda>x. \<langle>g\<rangle> . (\<langle>f\<rangle>.\<langle>x\<rangle>) \<rangle>\<rangle>"

definition checkmem :: "'param \<Rightarrow> ('param \<rightharpoonup> 'result, 'result) state \<Rightarrow> ('param \<rightharpoonup> 'result, 'result) state" where
  "checkmem param calc \<equiv> do {
    M \<leftarrow> get;
    case M param of
      Some x \<Rightarrow> \<langle>x\<rangle>
    | None \<Rightarrow> do {
        x \<leftarrow> calc;
        M' \<leftarrow> get;
        put (M'(param\<mapsto>x));
        \<langle>x\<rangle>
      }
  }"

abbreviation checkmem_eq :: "('param \<Rightarrow>\<^sub>T 'result) \<Rightarrow> 'param \<Rightarrow> ('param \<rightharpoonup> 'result, 'result) state \<Rightarrow> bool" ("_$ _ =CHECKMEM= _" [1000,51] 51) where
  "(dp\<^sub>T$ param =CHECKMEM= calc) \<equiv> (dp\<^sub>T param = checkmem param calc)"
term 0 (**)

(* Auxiliary *)
definition lift_0arg :: "'a \<Rightarrow> 'a" where
  "lift_0arg x \<equiv> x"
definition lift_1arg :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a =='M\<Longrightarrow> 'b)" where
  "lift_1arg f \<equiv> \<lambda>v. \<langle>lift_0arg (f v)\<rangle>"
definition lift_2arg :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a =='M\<Longrightarrow> 'b =='M\<Longrightarrow> 'c)" where
  "lift_2arg f \<equiv> \<lambda>v. \<langle>lift_1arg (f v)\<rangle>"
definition lift_3arg :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('a =='M\<Longrightarrow> 'b =='M\<Longrightarrow> 'c =='M\<Longrightarrow> 'd)" where
  "lift_3arg f \<equiv> \<lambda>v. \<langle>lift_2arg (f v)\<rangle>"

definition unlift_0arg :: "('M, 'a) state \<Rightarrow> ('M, 'a) state" where
  "unlift_0arg x\<^sub>T \<equiv> x\<^sub>T"
definition unlift_1arg :: "('M, 'a =='M\<Longrightarrow> 'b) state \<Rightarrow> ('a \<Rightarrow> ('M, 'b) state)" where
  "unlift_1arg f\<^sub>T \<equiv> \<lambda>v. unlift_0arg (f\<^sub>T . \<langle>v\<rangle>)"
definition unlift_2arg :: "('M, 'a =='M\<Longrightarrow> 'b =='M\<Longrightarrow> 'c) state \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> ('M, 'c) state)" where
  "unlift_2arg f\<^sub>T \<equiv> \<lambda>v. unlift_1arg (f\<^sub>T . \<langle>v\<rangle>)"

term 0 (**)

(* HOL *)
definition If\<^sub>T :: "bool =='M\<Longrightarrow> 'a =='M\<Longrightarrow> 'a =='M\<Longrightarrow> 'a" where
  "If\<^sub>T \<equiv> lift_3arg If"
term 0 (**)

(* List *)
definition Cons\<^sub>T :: "'a =='M\<Longrightarrow> 'a list =='M\<Longrightarrow> 'a list" where
  "Cons\<^sub>T \<equiv> lift_2arg Cons"

definition case_list\<^sub>T :: "'b =='M\<Longrightarrow> ('a =='M\<Longrightarrow> 'a list =='M\<Longrightarrow> 'b) =='M\<Longrightarrow> 'a list =='M\<Longrightarrow> 'b" where
  "case_list\<^sub>T \<equiv> \<lambda>ifNil. \<langle>\<lambda>ifCons. \<langle>\<lambda>val. case_list (unlift_0arg \<langle>ifNil\<rangle>) (unlift_2arg \<langle>ifCons\<rangle>) val\<rangle>\<rangle>"

primrec map\<^sub>T' :: "('a =='M\<Longrightarrow>'b) \<Rightarrow> ('a list =='M\<Longrightarrow> 'b list)" where
  "map\<^sub>T' f [] = \<langle>[]\<rangle>"
| "map\<^sub>T' f (x#xs) = \<langle>Cons\<^sub>T\<rangle> . (f x) . (map\<^sub>T' f xs)"
definition map\<^sub>T :: "('a =='M\<Longrightarrow> 'b) =='M\<Longrightarrow> 'a list =='M\<Longrightarrow> 'b list" where
  "map\<^sub>T \<equiv> lift_1arg map\<^sub>T'"

primrec fold\<^sub>T' :: "('a =='M\<Longrightarrow> 'b =='M\<Longrightarrow> 'b) \<Rightarrow> ('a list =='M\<Longrightarrow> 'b =='M\<Longrightarrow> 'b)" where
  "fold\<^sub>T' f [] = \<langle>return\<rangle>"
| "fold\<^sub>T' f (x#xs) = \<langle>fcomp_lifted\<rangle> . (f x) . (fold\<^sub>T' f xs)"
definition fold\<^sub>T :: "('a =='M\<Longrightarrow> 'b =='M\<Longrightarrow> 'b) =='M\<Longrightarrow> 'a list =='M\<Longrightarrow> 'b =='M\<Longrightarrow> 'b" where
  "fold\<^sub>T \<equiv> lift_1arg fold\<^sub>T'"
term 0 (**)

(* Option *)
definition Some\<^sub>T :: "'a =='M\<Longrightarrow> 'a option" where
  "Some\<^sub>T \<equiv> lift_1arg Some"

definition case_option\<^sub>T :: "'b =='M\<Longrightarrow> ('a =='M\<Longrightarrow> 'b) =='M\<Longrightarrow> 'a option =='M\<Longrightarrow> 'b" where
  "case_option\<^sub>T \<equiv> \<lambda>ifNone. \<langle>\<lambda>ifSome. \<langle>\<lambda>val. case_option (unlift_0arg \<langle>ifNone\<rangle>) (unlift_1arg \<langle>ifSome\<rangle>) val\<rangle>\<rangle>"
term 0 (**)

(* Prod *)
definition Pair\<^sub>T :: "'a0 =='M\<Longrightarrow> 'a1 =='M\<Longrightarrow> 'a0\<times>'a1" where
  "Pair\<^sub>T \<equiv> lift_2arg Pair"

definition case_prod\<^sub>T :: "('a0 =='M\<Longrightarrow> 'a1 =='M\<Longrightarrow> 'b) =='M\<Longrightarrow> ('a0\<times>'a1) =='M\<Longrightarrow> 'b" where
  "case_prod\<^sub>T \<equiv> \<lambda>ifProd. \<langle>\<lambda>val. case_prod (unlift_2arg \<langle>ifProd\<rangle>) val\<rangle>"

term "\<langle>case_prod\<^sub>T\<rangle> . \<langle>\<lambda>v0. \<langle>\<lambda>v1. \<langle>v0+v1\<rangle>\<rangle>\<rangle> . (\<langle>Pair\<^sub>T\<rangle> . \<langle>0\<rangle> . \<langle>0::int\<rangle>)"
term 0 (**)

(* Arithmetic *)
definition min\<^sub>T :: "'a::ord =='M\<Longrightarrow> 'a =='M\<Longrightarrow> 'a" where
  "min\<^sub>T \<equiv> lift_2arg min"

definition max\<^sub>T :: "'a::ord =='M\<Longrightarrow> 'a =='M\<Longrightarrow> 'a" where
  "max\<^sub>T \<equiv> lift_2arg max"

definition plus\<^sub>T :: "'a::plus =='M\<Longrightarrow> 'a =='M\<Longrightarrow> 'a" where
  "plus\<^sub>T \<equiv> lift_2arg plus"
term 0 (**)
end