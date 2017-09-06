theory DP_Lifting
  imports Main "./Monad"
begin

  (* Types *)
type_synonym ('a,'M,'b) fun_lifted = "'a \<Rightarrow> ('M,'b) state" ("_ ==_\<Longrightarrow> _" [3,1000,2] 2)
type_synonym ('a,'b) dpfun = "'a ==('a\<rightharpoonup>'b)\<Longrightarrow> 'b" (infixr "\<Rightarrow>\<^sub>T" 2)
term 0 (**)
  
  (* Basics *)
notation Monad.return ("\<langle>_\<rangle>")

syntax
  "_lambda\<^sub>T" :: "[pttrns, 'a] \<Rightarrow> logic" ("(3\<lambda>\<^sub>T_./ _)" [0, 3] 3)
translations
  "\<lambda>\<^sub>T v vs. e" \<rightharpoonup> "\<lambda>\<^sub>T v. \<lambda>\<^sub>T vs. e"
  "\<lambda>\<^sub>T v. e" \<rightharpoonup> "\<langle>\<lambda> v. e\<rangle>"

definition fun_app_lifted :: "('M,'a =='M\<Longrightarrow> 'b) state \<Rightarrow> ('M,'a) state \<Rightarrow> ('M,'b) state" (infixl "." 999) where
  "f\<^sub>T . x\<^sub>T \<equiv> do { f \<leftarrow> f\<^sub>T; x \<leftarrow> x\<^sub>T; f x }"
term 0 (**)
  
lemma fun_app_lifted_elim1:
  assumes "runState (f\<^sub>T . x\<^sub>T) M = (v, Mv)"
  obtains f Mf x Mx where "runState f\<^sub>T M = (f, Mf)" "runState x\<^sub>T Mf = (x, Mx)" and "runState (f x) Mx = (v, Mv)"
  using assms unfolding fun_app_lifted_def bind_def by (auto split: prod.splits)

lemma fun_app_lifted_elim:
  assumes "runState (f\<^sub>T . x\<^sub>T) M = (v, Mv)" "runState f\<^sub>T M = (f, Mf)"
  obtains x Mx where "runState x\<^sub>T Mf = (x, Mx)" and "runState (f x) Mx = (v, Mv)"
  using assms by (auto intro: fun_app_lifted_elim1)

lemma fun_app_lifted_dest:
  assumes "runState f\<^sub>T M = (f, Mf)" "runState x\<^sub>T Mf = (x, Mx)" "runState (f x) Mx = (v, Mv)"
  shows "runState (f\<^sub>T . x\<^sub>T) M = (v, Mv)"
    using assms unfolding fun_app_lifted_def bind_def by auto
term 0 (**)
  
lemma return_app_return:
  "\<langle>f\<rangle> . \<langle>x\<rangle> = f x"
  unfolding fun_app_lifted_def left_identity ..
term 0 (**)
  
definition checkmem :: "'param \<Rightarrow> ('param \<rightharpoonup> 'result, 'result) state \<Rightarrow> ('param \<rightharpoonup> 'result, 'result) state" where
  "checkmem param calc \<equiv> do {
    M \<leftarrow> get;
    case M param of
      Some x \<Rightarrow> return x
    | None \<Rightarrow> do {
        x \<leftarrow> calc;
        M' \<leftarrow> get;
        put (M'(param\<mapsto>x));
        return x
      }
  }"
  
abbreviation checkmem_eq :: "('param \<Rightarrow>\<^sub>T 'result) \<Rightarrow> 'param \<Rightarrow> ('param \<rightharpoonup> 'result, 'result) state \<Rightarrow> bool" ("_$ _ =CHECKMEM= _" [1000,51] 51) where
  "(dp\<^sub>T$ param =CHECKMEM= calc) \<equiv> (dp\<^sub>T param = checkmem param calc)"
term 0 (**)
  
context
  includes lifting_syntax
begin
  
  (* Auxiliary *)
definition unlift_' :: "'a \<Rightarrow> ('M, 'a) state" where
  "unlift_' x \<equiv> \<langle>x\<rangle>"
definition unlift_3 :: "('a =='M\<Longrightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> ('M, 'b) state)" where
  "unlift_3 f \<equiv> \<lambda>v0. \<langle>f\<rangle> . \<langle>v0\<rangle>"
definition unlift_33 :: "('a =='M\<Longrightarrow> 'b =='M\<Longrightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> ('M, 'c) state)" where
  "unlift_33 f \<equiv> \<lambda>v0 v1. \<langle>f\<rangle> . \<langle>v0\<rangle> . \<langle>v1\<rangle>"
  
definition lift_' :: "'a \<Rightarrow> ('M, 'a) state" where
  "lift_' x \<equiv> \<langle>x\<rangle>"
definition lift_3 :: "('a \<Rightarrow> 'b) \<Rightarrow> ('M, 'a =='M\<Longrightarrow> 'b) state" where
  "lift_3 f \<equiv> \<lambda>\<^sub>T x. \<langle>f x\<rangle>"
definition lift_33 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('M, 'a =='M\<Longrightarrow> 'b =='M\<Longrightarrow> 'c) state" where
  "lift_33 f \<equiv> \<lambda>\<^sub>T x0 x1. \<langle>f x0 x1\<rangle>"
definition lift_333 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('M, 'a =='M\<Longrightarrow> 'b =='M\<Longrightarrow> 'c =='M\<Longrightarrow> 'd) state" where
  "lift_333 f \<equiv> \<lambda>\<^sub>T x0 x1 x2. \<langle>f x0 x1 x2\<rangle>"
term 0 (**)
  
  (* HOL *)
definition If\<^sub>T :: "('M, bool =='M\<Longrightarrow> 'a =='M\<Longrightarrow> 'a =='M\<Longrightarrow> 'a) state" where
  "If\<^sub>T \<equiv> lift_333 If"

thm comp_def
definition comp\<^sub>T :: "('M, ('b =='M\<Longrightarrow> 'c) =='M\<Longrightarrow> ('a =='M\<Longrightarrow> 'b) =='M\<Longrightarrow> ('a =='M\<Longrightarrow> 'c)) state" where
  "comp\<^sub>T \<equiv> \<lambda>\<^sub>T f g x. \<langle>f\<rangle> . (\<langle>g\<rangle> . \<langle>x\<rangle>)"
  
thm id_def
definition id\<^sub>T :: "('M, 'a =='M\<Longrightarrow> 'a) state" where
  "id\<^sub>T \<equiv> lift_3 id"
term 0 (**)
  
  (* List *)
definition Nil\<^sub>T :: "('M, 'a list) state" where
  "Nil\<^sub>T \<equiv> lift_' Nil"
  
definition Cons\<^sub>T :: "('M, 'a =='M\<Longrightarrow> 'a list =='M\<Longrightarrow> 'a list) state" where
  "Cons\<^sub>T \<equiv> lift_33 Cons"

definition case_list\<^sub>T :: "('M, 'b =='M\<Longrightarrow> ('a =='M\<Longrightarrow> 'a list =='M\<Longrightarrow> 'b) =='M\<Longrightarrow> 'a list =='M\<Longrightarrow> 'b) state" where
  "case_list\<^sub>T \<equiv> \<lambda>\<^sub>T ifNil ifCons val. case_list (unlift_' ifNil) (unlift_33 ifCons) val"
  
fun map\<^sub>T' :: "('a =='M\<Longrightarrow>'b) \<Rightarrow> 'a list =='M\<Longrightarrow> 'b list" where
  "(map\<^sub>T' f) [] = \<langle>[]\<rangle>"
| "(map\<^sub>T' f) (x#xs) = Cons\<^sub>T . (f x) . ((map\<^sub>T' f) xs)"
lemma
  "(map\<^sub>T' f) (x#xs) = Cons\<^sub>T . (f x) . (\<langle>map\<^sub>T' f\<rangle> . \<langle>xs\<rangle>)" unfolding map\<^sub>T'.simps(2) fun_app_lifted_def left_identity ..
    
definition map\<^sub>T :: "('M, ('a =='M\<Longrightarrow> 'b) =='M\<Longrightarrow> 'a list =='M\<Longrightarrow> 'b list) state" where
  "map\<^sub>T \<equiv> lift_3 map\<^sub>T'"

lemma map\<^sub>T_map\<^sub>T': "map\<^sub>T . f\<^sub>T . xs\<^sub>T = do {f \<leftarrow> f\<^sub>T; xs \<leftarrow> xs\<^sub>T; map\<^sub>T' f xs}"
  unfolding map\<^sub>T_def lift_3_def fun_app_lifted_def left_identity bind_assoc ..
term 0 (**)
  
primrec fold\<^sub>T' :: "('a =='M\<Longrightarrow> 'b =='M\<Longrightarrow> 'b) \<Rightarrow> 'a list =='M\<Longrightarrow> 'b =='M\<Longrightarrow> 'b" where
  "(fold\<^sub>T' f) [] = id\<^sub>T"
| "(fold\<^sub>T' f) (x#xs) = comp\<^sub>T . ((fold\<^sub>T' f) xs) . (\<langle>f\<rangle> . \<langle>x\<rangle>)"
lemma
  "(fold\<^sub>T' f) (x#xs) = comp\<^sub>T . (\<langle>fold\<^sub>T' f\<rangle> . \<langle>xs\<rangle>) . (\<langle>f\<rangle> . \<langle>x\<rangle>)" unfolding fold\<^sub>T'.simps(2) fun_app_lifted_def left_identity ..
    
definition fold\<^sub>T :: "('M, ('a =='M\<Longrightarrow> 'b =='M\<Longrightarrow> 'b) =='M\<Longrightarrow> 'a list =='M\<Longrightarrow> 'b =='M\<Longrightarrow> 'b) state" where
  "fold\<^sub>T \<equiv> \<lambda>\<^sub>T f\<^sub>T. \<langle>fold\<^sub>T' f\<^sub>T\<rangle>"

definition upt\<^sub>T :: "('M, nat =='M\<Longrightarrow> nat =='M\<Longrightarrow> nat list) state" where
  "upt\<^sub>T \<equiv> lift_33 upt"
term 0 (**)
  
  (* Option *)
definition None\<^sub>T :: "('M, 'a option) state" where
  "None\<^sub>T \<equiv> lift_' None"

definition Some\<^sub>T :: "('M, 'a =='M\<Longrightarrow> 'a option) state" where
  "Some\<^sub>T \<equiv> lift_3 Some"
  
definition case_option\<^sub>T :: "('M, 'b =='M\<Longrightarrow> ('a =='M\<Longrightarrow> 'b) =='M\<Longrightarrow> 'a option =='M\<Longrightarrow> 'b) state" where
  "case_option\<^sub>T \<equiv> \<lambda>\<^sub>T ifNone ifSome val. case_option (unlift_' ifNone) (unlift_3 ifSome) val"
term 0 (**)
  
  (* Prod *)
definition Pair\<^sub>T :: "('M, 'a0 =='M\<Longrightarrow> 'a1 =='M\<Longrightarrow> 'a0\<times>'a1) state" where
  "Pair\<^sub>T \<equiv> lift_33 Pair"
  
definition case_prod\<^sub>T :: "('M, ('a0 =='M\<Longrightarrow> 'a1 =='M\<Longrightarrow> 'b) =='M\<Longrightarrow> ('a0\<times>'a1) =='M\<Longrightarrow> 'b) state" where
  "case_prod\<^sub>T \<equiv> \<lambda>\<^sub>T ifProd val. case_prod (unlift_33 ifProd) val"
  
term "case_prod\<^sub>T . (\<lambda>\<^sub>T v0 v1. \<langle>v0+v1\<rangle>) . (Pair\<^sub>T . \<langle>0\<rangle> . \<langle>0::int\<rangle>)"
term 0 (**)
  
  (* Arithmetic *)
definition min\<^sub>T :: "('M, 'a::ord =='M\<Longrightarrow> 'a =='M\<Longrightarrow> 'a) state" where
  "min\<^sub>T \<equiv> lift_33 min"
  
definition max\<^sub>T :: "('M, 'a::ord =='M\<Longrightarrow> 'a =='M\<Longrightarrow> 'a) state" where
  "max\<^sub>T \<equiv> lift_33 max"
  
definition plus\<^sub>T :: "('M, 'a::plus =='M\<Longrightarrow> 'a =='M\<Longrightarrow> 'a) state" where
  "plus\<^sub>T \<equiv> lift_33 plus"
term 0 (**)
end
end