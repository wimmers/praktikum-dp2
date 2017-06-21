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
  
lemma fun_app_lifted_elim:
  assumes "runState (f\<^sub>T . x\<^sub>T) M = (v, Mv)" "runState f\<^sub>T M = (f, Mf)"
  obtains x Mx where "runState x\<^sub>T Mf = (x, Mx)" and "runState (f x) Mx = (v, Mv)"
  using assms unfolding fun_app_lifted_def bind_def by (auto split: prod.splits)
term 0 (**)
  
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
syntax
  "_lambda\<^sub>T" :: "[pttrns, 'a] \<Rightarrow> logic" ("(3\<lambda>\<^sub>T_./ _)" [0, 3] 3)
translations
  "\<lambda>\<^sub>T v vs. e" \<rightharpoonup> "\<lambda>\<^sub>T v. \<lambda>\<^sub>T vs. e"
  "\<lambda>\<^sub>T v. e" \<rightharpoonup> "\<lambda> v. \<langle>e\<rangle>"

definition unlift_' :: "'a \<Rightarrow> ('M, 'a) state" where
  "unlift_' x \<equiv> \<langle>x\<rangle>"
definition unlift_3 :: "('a =='M\<Longrightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> ('M, 'b) state)" where
  "unlift_3 f \<equiv> \<lambda>v0. \<langle>f\<rangle>.\<langle>v0\<rangle>"
definition unlift_33 :: "('a =='M\<Longrightarrow> 'b =='M\<Longrightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> ('M, 'c) state)" where
  "unlift_33 f \<equiv> \<lambda>v0 v1. \<langle>f\<rangle>.\<langle>v0\<rangle>.\<langle>v1\<rangle>"
  
term 0 (**)
  
  (* HOL *)
definition If\<^sub>T :: "bool =='M\<Longrightarrow> 'a =='M\<Longrightarrow> 'a =='M\<Longrightarrow> 'a" where
  "If\<^sub>T \<equiv> \<lambda>\<^sub>T P x y. If P x y"

thm comp_def
definition comp\<^sub>T :: "('b =='M\<Longrightarrow> 'c) =='M\<Longrightarrow> ('a =='M\<Longrightarrow> 'b) =='M\<Longrightarrow> ('a =='M\<Longrightarrow> 'c)" where
  "comp\<^sub>T \<equiv> \<lambda>\<^sub>T f g. (\<lambda>x. \<langle>f\<rangle> . (\<langle>g\<rangle> . \<langle>x\<rangle>))"
  
thm id_def
definition id\<^sub>T :: "'a =='M\<Longrightarrow> 'a" where
  "id\<^sub>T \<equiv> \<lambda>\<^sub>T x. x"
term 0 (**)
  
  (* List *)
definition Cons\<^sub>T :: "'a =='M\<Longrightarrow> 'a list =='M\<Longrightarrow> 'a list" where
  "Cons\<^sub>T \<equiv> \<lambda>\<^sub>T x xs. Cons x xs"
  
definition case_list\<^sub>T :: "'b =='M\<Longrightarrow> ('a =='M\<Longrightarrow> 'a list =='M\<Longrightarrow> 'b) =='M\<Longrightarrow> 'a list =='M\<Longrightarrow> 'b" where
  "case_list\<^sub>T \<equiv> \<lambda>\<^sub>T ifNil ifCons. (\<lambda>val. case_list (unlift_' ifNil) (unlift_33 ifCons) val)"
  
primrec map\<^sub>T' :: "('a =='M\<Longrightarrow>'b) \<Rightarrow> 'a list =='M\<Longrightarrow> 'b list" where
  "(map\<^sub>T' f) [] = \<langle>[]\<rangle>"
| "(map\<^sub>T' f) (x#xs) = \<langle>Cons\<^sub>T\<rangle> . (\<langle>f\<rangle> . \<langle>x\<rangle>) . ((map\<^sub>T' f) xs)"
lemma
  "(map\<^sub>T' f) (x#xs) = \<langle>Cons\<^sub>T\<rangle> . (\<langle>f\<rangle> . \<langle>x\<rangle>) . (\<langle>map\<^sub>T' f\<rangle> . \<langle>xs\<rangle>)" unfolding map\<^sub>T'.simps(2) fun_app_lifted_def left_identity ..
    
definition map\<^sub>T :: "('a =='M\<Longrightarrow> 'b) =='M\<Longrightarrow> 'a list =='M\<Longrightarrow> 'b list" where
  "map\<^sub>T \<equiv> \<lambda>\<^sub>T f\<^sub>T. map\<^sub>T' f\<^sub>T"
  
primrec fold\<^sub>T' :: "('a =='M\<Longrightarrow> 'b =='M\<Longrightarrow> 'b) \<Rightarrow> 'a list =='M\<Longrightarrow> 'b =='M\<Longrightarrow> 'b" where
  "(fold\<^sub>T' f) [] = \<langle>id\<^sub>T\<rangle>"
| "(fold\<^sub>T' f) (x#xs) = \<langle>comp\<^sub>T\<rangle> . ((fold\<^sub>T' f) xs) . (\<langle>f\<rangle> . \<langle>x\<rangle>)"
lemma
  "(fold\<^sub>T' f) (x#xs) = \<langle>comp\<^sub>T\<rangle> . (\<langle>fold\<^sub>T' f\<rangle> . \<langle>xs\<rangle>) . (\<langle>f\<rangle> . \<langle>x\<rangle>)" unfolding fold\<^sub>T'.simps(2) fun_app_lifted_def left_identity ..
    
definition fold\<^sub>T :: "('a =='M\<Longrightarrow> 'b =='M\<Longrightarrow> 'b) =='M\<Longrightarrow> 'a list =='M\<Longrightarrow> 'b =='M\<Longrightarrow> 'b" where
  "fold\<^sub>T \<equiv> \<lambda>\<^sub>T f\<^sub>T. fold\<^sub>T' f\<^sub>T"

definition upt\<^sub>T :: "nat =='M\<Longrightarrow> nat =='M\<Longrightarrow> nat list" where
  "upt\<^sub>T \<equiv> \<lambda>\<^sub>T i j. upt i j"
term 0 (**)
  
  (* Option *)
definition Some\<^sub>T :: "'a =='M\<Longrightarrow> 'a option" where
  "Some\<^sub>T \<equiv> \<lambda>\<^sub>T x. Some x"
  
definition case_option\<^sub>T :: "'b =='M\<Longrightarrow> ('a =='M\<Longrightarrow> 'b) =='M\<Longrightarrow> 'a option =='M\<Longrightarrow> 'b" where
  "case_option\<^sub>T \<equiv> \<lambda>\<^sub>T ifNone ifSome. (\<lambda>val. case_option (unlift_' ifNone) (unlift_3 ifSome) val)"
term 0 (**)
  
  (* Prod *)
definition Pair\<^sub>T :: "'a0 =='M\<Longrightarrow> 'a1 =='M\<Longrightarrow> 'a0\<times>'a1" where
  "Pair\<^sub>T \<equiv> \<lambda>\<^sub>T x y. Pair x y"
  
definition case_prod\<^sub>T :: "('a0 =='M\<Longrightarrow> 'a1 =='M\<Longrightarrow> 'b) =='M\<Longrightarrow> ('a0\<times>'a1) =='M\<Longrightarrow> 'b" where
  "case_prod\<^sub>T \<equiv> \<lambda>\<^sub>T ifProd. (\<lambda>val. case_prod (unlift_33 ifProd) val)"
  
term "\<langle>case_prod\<^sub>T\<rangle> . \<langle>\<lambda>\<^sub>T v0 v1. v0+v1\<rangle> . (\<langle>Pair\<^sub>T\<rangle> . \<langle>0\<rangle> . \<langle>0::int\<rangle>)"
term 0 (**)
  
  (* Arithmetic *)
definition min\<^sub>T :: "'a::ord =='M\<Longrightarrow> 'a =='M\<Longrightarrow> 'a" where
  "min\<^sub>T \<equiv> \<lambda>\<^sub>T x y. min x y"
  
definition max\<^sub>T :: "'a::ord =='M\<Longrightarrow> 'a =='M\<Longrightarrow> 'a" where
  "max\<^sub>T \<equiv> \<lambda>\<^sub>T x y. max x y"
  
definition plus\<^sub>T :: "'a::plus =='M\<Longrightarrow> 'a =='M\<Longrightarrow> 'a" where
  "plus\<^sub>T \<equiv> \<lambda>\<^sub>T x y. plus x y"
term 0 (**)
end