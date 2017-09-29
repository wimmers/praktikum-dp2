theory Scratch_Transform
  imports Main "../Monad" "../DP_Lifting"
begin
  
context (* Knapsack *)
  fixes w :: "nat \<Rightarrow> nat"
begin

fun su :: "nat\<times>nat \<Rightarrow> nat" where
  "su (0, W) = (if W < w 0 then 0 else w 0)" |
  "su (Suc i, W) = (if W < w (Suc i)
    then su (i, W)
    else max (su (i, W)) (w i + su (i, W - w i)))"

ML \<open>
val su_info = Function.get_info @{context} @{term su};
\<close>
  
ML \<open>
val su_simps = su_info |> #simps |> the;
val [su_simp0, su_simp1] = su_simps;
val su_def0 = su_simp0 |> Thm.full_prop_of;
@{term "HOL.Trueprop"};
refl;
HOLogic.dest_eq;
\<close>
  
ML \<open>
val su_eq0 = su_def0 |> HOLogic.dest_Trueprop |> HOLogic.dest_eq;
fst su_eq0 |> strip_comb;
hd;
0:: [1, 2, 3];
strip_comb @{term plus};
type_of @{term plus} |> binder_types;
val (su0_lhs, su0_rhs) = su_eq0;
type_of su0_lhs;
\<close>
  
ML \<open>
lambda @{term "y"} @{term y};
@{term "\<lambda>x. (\<lambda>y. x)"};
val tt = absfree ("x", @{typ nat}) @{term "x"};
Thm.cterm_of @{context} tt;
exists_subterm;
Name.aT;
Name.bound 1000003;
Name.invent (Variable.names_of @{context}) "Scratch_Transform.st" 5;
su_eq0;
\<close>
  
ML \<open>
strip_all_vars @{term "0"};
@{term "\<lambda>x x. x"};
binder_types (type_of @{term fold});
length [1,2,3];
op |>;
op o;
Term.abs;
op abs;
K;
val _: int = 0;
0 upto 10;
fold;
fold_rev;
curry op = 0;
exists_subterm (curry op = @{term "0::nat"}) @{term "Suc 0"};
curry op = @{term 1} @{term 1};
@{term "Suc 0"};
@{typ "('a, 'b) DP_Lifting.dpfun"};
@{typ "'a =='M\<Longrightarrow> 'b"} |> dest_Type;
Type ("Monad.state", [@{typ nat}, @{typ int}])=
@{typ "(nat, int) state"};
HOLogic.natT;
Type ("DP_Lifting.fun_lifted", [HOLogic.natT, HOLogic.natT, HOLogic.natT]) = @{typ "nat ==nat\<Longrightarrow> nat"};
HOLogic.natT;
@{typ "nat Option.option"};
@{typ "'a \<rightharpoonup> 'b"};
@{const_name return};
betapply;
\<close>
  
ML \<open>
Thm.cterm_of @{context} su0_rhs;

Args.term;
Syntax.read_term @{context} "plus (0::nat)";
(*Syntax.check_terms @{context} [@{term plus} $ @{term "0::nat"}];*)
Type_Infer.object_logic;
Proof_Context.prepare_sorts;
\<close>
ML \<open>
type_of1 ([@{typ nat}], (Bound 0))
\<close>

  
ML \<open>
(* FIXME: placeholder for debugging*)
(*
val dom_type = @{typ "nat \<times> nat"};
val ran_type = @{typ "int"};
val mem_type = dom_type --> Type (@{type_name "Option.option"}, [ran_type]);
*)
(*val (lhs, rhs) = (su0_lhs, su0_rhs);*)
Library.foldl;
HOLogic.zero;
@{term If};
SOME 0;
(case [1,2,3,4] of
  (x::y::(t as z)::u) => t);
@{term HOL.If};
Proof_Context.prepare_sorts @{context} [@{term plus}];
@{term plus};
infix 9 <$>;
let
fun x <$> y = x + y;
in
3 <$> 4
end;
let
fun x <$> y = x * y;
in
3 <$> 4
end;
infix 9 <APP>;
@{type_name fun};
let val a=0; val b=1 in writeln "x"; 4 end;
fun f x = case x of NONE => 3 | SOME t => t;

@{term case_prod};
[] = [];
hd;
not true;
NONE;
get_first;
\<close>
  
term 0 (**)
ML_file \<open>Transform.ML\<close>
term 0 (**)
ML \<open>
su_simp0;

\<close>
  
ML \<open>

\<close>
end
end
  