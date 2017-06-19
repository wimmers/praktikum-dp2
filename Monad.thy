theory Monad
  imports Main
begin

datatype ('M, 'a) state = State (runState: "'M \<Rightarrow> 'a \<times> 'M")
term 0 (**)

definition return :: "'a \<Rightarrow> ('M, 'a) state" where
  "return a \<equiv> State (\<lambda>M. (a, M))"
term 0 (**)

definition bind :: "('M, 'a) state \<Rightarrow> ('a \<Rightarrow> ('M, 'b) state) \<Rightarrow> ('M, 'b) state" (infixl "\<bind>" 54) where
  "s \<bind> k \<equiv> State (\<lambda>M. let (a, M') = runState s M in runState (k a) M')"
term 0 (**)
  
abbreviation then_monad :: "('M, 'a) state \<Rightarrow> ('M, 'b) state \<Rightarrow> ('M, 'b) state" (infixl "\<then>" 54) where
  "s \<then> s' \<equiv> s \<bind> (\<lambda>_. s')"
term 0 (**)

nonterminal do_binds and do_bind
syntax
  "_do_block" :: "do_binds \<Rightarrow> 'a" ("do {//(2  _)//}" [12] 62)
  "_do_bind"  :: "[pttrn, 'a] \<Rightarrow> do_bind" ("(2_ \<leftarrow>/ _)" 13)
  "_do_let" :: "[pttrn, 'a] \<Rightarrow> do_bind" ("(2let _ =/ _)" [1000, 13] 13)
  "_do_then" :: "'a \<Rightarrow> do_bind" ("_" [14] 13)
  "_do_final" :: "'a \<Rightarrow> do_binds" ("_")
  "_do_cons" :: "[do_bind, do_binds] \<Rightarrow> do_binds" ("_;//_" [13, 12] 12)

translations
  "_do_block (_do_cons (_do_then t) (_do_final e))"
    \<rightleftharpoons> "CONST then_monad t e"
  "_do_block (_do_cons (_do_bind p t) (_do_final e))"
    \<rightleftharpoons> "CONST bind t (\<lambda>p. e)"
  "_do_block (_do_cons (_do_let p t) bs)"
    \<rightleftharpoons> "let p = t in _do_block bs"
  "_do_block (_do_cons b (_do_cons c cs))"
    \<rightleftharpoons> "_do_block (_do_cons b (_do_final (_do_block (_do_cons c cs))))"
  "_do_cons (_do_let p t) (_do_final s)"
    \<rightleftharpoons> "_do_final (let p = t in s)"
  "_do_block (_do_final e)" \<rightharpoonup> "e"

term 0 (**)
lemma bind_assoc[simp]:
  "(s \<bind> k0) \<bind> k1 = s \<bind> (\<lambda>a. k0 a \<bind> k1)"
  unfolding bind_def by (auto split: prod.split)

end