theory Scratch_ML
  imports Main
begin
  
fun f :: "nat \<Rightarrow> nat" where
  "f 0 = 0"
| "f (Suc n) = n + f n"
  
  
ML \<open>
open Function
\<close>

ML_val \<open>
val t = Function.get_info @{context} @{term f};
0;
\<close>
  
ML \<open>
Binding.map_name;
Binding.reset_pos;
Local_Theory.abbrev;
Syntax.mode_default;
Local_Theory.abbrev Syntax.mode_default;
Const ("a", @{typ nat});
Goal.init;
fn (s, t, b) => Const (s, t) $ b;
fn x => x;
\<close>  
  
ML \<open>
val f : int -> int = (fn x => x);
val idlt : local_theory -> local_theory = (fn x => x);
val idt : theory -> theory = (fn x => x);
\<close>

setup \<open>
idt
\<close>

ML {*
Sign.add_type;
val x: mixfix -> mixfix = fn x => x;
@{binding x};
Sign.add_type @{context} (@{binding x}, 0, NoSyn);
*}
  
setup \<open>
Sign.add_type @{context} (@{binding x}, 0, NoSyn);
\<close>
typ x
  
ML \<open>
Sign.add_abbrev "asdf" (@{binding xab}, @{term "3+4"}) #> snd;
@{term "3+4"};
fn (a, b) => a |> b;
\<close>
  
setup \<open>
Sign.add_abbrev "asdf" (@{binding xab}, @{term "3+4::nat"}) #> snd;
\<close>

function fc :: "nat \<Rightarrow> nat" where
  "fc x = Suc x"
  term fc
ML_val \<open>
@{term fc}
\<close>
  by pat_completeness auto
term fc
ML_val \<open>
@{term fc};
Parse_Spec.specification;
val _ : Specification.multi_specs_cmd -> Specification.multi_specs_cmd = fn x => x;
val _ = fn (a, b) => a -- b;
\<close>
  
notepad
begin
  fix a
  assume *:"a = (3::nat)"
  have True ..
end
  
ML \<open>
Function_Fun.add_fun;
\<close>
  
end