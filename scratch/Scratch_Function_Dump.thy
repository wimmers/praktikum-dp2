theory Scratch_Function_Dump
  imports Main
  keywords
    "gunction" "uermination" :: thy_goal and
    "gun" :: thy_decl
begin
term 0
(* Function.ML *)
ML \<open>
(*  Title:      HOL/Tools/Function/function.ML
    Author:     Alexander Krauss, TU Muenchen

Main entry points to the function package.
*)

open Function_Lib
open Function_Common

val simp_attribs =
  @{attributes [simp, nitpick_simp]} @ [Code.add_default_eqn_attrib Code.Equation]

val psimp_attribs =
  @{attributes [nitpick_psimp]}

fun note_derived (a, atts) (fname, thms) =
  Local_Theory.note ((derived_name fname a, atts), thms) #> apfst snd

fun add_simps fnames post sort extra_qualify label mod_binding moreatts simps lthy =
  let
    val _ = writeln ("fnames: " ^ @{make_string} fnames);
    val _ = writeln ("post: " ^ @{make_string} post);
    val _ = writeln ("sort: " ^ @{make_string} sort);
    val _ = writeln ("extra_qualify: " ^ @{make_string} extra_qualify);
    val _ = writeln ("label: " ^ @{make_string} label);
    val _ = writeln ("mod_binding: " ^ @{make_string} mod_binding);
    val spec = post simps
      |> map (apfst (apsnd (fn ats => moreatts @ ats)))
      |> map (apfst (apfst extra_qualify));
    
    val _ = writeln ("spec: " ^ @{make_string} spec);

    val (saved_spec_simps, lthy) =
      fold_map Local_Theory.note spec lthy

    val saved_simps = maps snd saved_spec_simps
    val simps_by_f = sort saved_simps

    fun note fname simps =
      Local_Theory.note ((mod_binding (derived_name fname label), []), simps) #> snd
  in (saved_simps, fold2 note fnames simps_by_f lthy) end

fun prepare_function do_print prep fixspec eqns config lthy =
  let
    val ((fixes0, spec0), ctxt') = prep fixspec eqns lthy
    val fixes = map (apfst (apfst Binding.name_of)) fixes0
    val spec = map (fn (bnd, prop) => (bnd, [prop])) spec0
    val (eqs, post, sort_cont, cnames) = get_preproc lthy config ctxt' fixes spec

    val fnames = map (fst o fst) fixes0
    val defname = Binding.conglomerate fnames;

    val _ = writeln ("Eqs: " ^ (@{make_string} eqs));
    val _ = writeln ("fixes: " ^ (@{make_string} fixes));
    val _ = writeln ("fnames: " ^ (@{make_string} fnames));
    val _ = writeln ("defname: " ^ (@{make_string} defname));

    val FunctionConfig {partials, default, ...} = config
    val _ =
      if is_some default
      then legacy_feature "\"function (default)\" -- use 'partial_function' instead"
      else ()

    val ((goal_state, cont), lthy') =
      Function_Mutual.prepare_function_mutual config defname fixes0 eqs lthy

    fun afterqed [[proof]] lthy =
      let
        val result = cont lthy (Thm.close_derivation proof)
        val FunctionResult {fs, R, dom, psimps, simple_pinducts,
                termination, domintros, cases, ...} = result

        val pelims = Function_Elims.mk_partial_elim_rules lthy result

        val concealed_partial = if partials then I else Binding.concealed

        val addsmps = add_simps fnames post sort_cont

        val (((((psimps', [pinducts']), [termination']), cases'), pelims'), lthy) =
          lthy
          |> addsmps (concealed_partial o Binding.qualify false "partial")
               "psimps" concealed_partial psimp_attribs psimps
          ||>> Local_Theory.notes [((concealed_partial (derived_name defname "pinduct"), []),
                simple_pinducts |> map (fn th => ([th],
                 [Attrib.case_names cnames, Attrib.consumes (1 - Thm.nprems_of th)] @
                 @{attributes [induct pred]})))]
          ||>> (apfst snd o
            Local_Theory.note
              ((Binding.concealed (derived_name defname "termination"), []), [termination]))
          ||>> fold_map (note_derived ("cases", [Attrib.case_names cnames]))
            (fnames ~~ map single cases)
          ||>> fold_map (note_derived ("pelims", [Attrib.consumes 1, Attrib.constraints 1]))
            (fnames ~~ pelims)
          ||> (case domintros of NONE => I | SOME thms =>
                Local_Theory.note ((derived_name defname "domintros", []), thms) #> snd)

        val info =
          { add_simps=addsmps, fnames=fnames, case_names=cnames, psimps=psimps',
          pinducts=snd pinducts', simps=NONE, inducts=NONE, termination=termination',
          fs=fs, R=R, dom=dom, defname=defname, is_partial=true, cases=flat cases',
          pelims=pelims',elims=NONE}

        val _ =
          Proof_Display.print_consts do_print (Position.thread_data ()) lthy
            (K false) (map fst fixes)
      in
        (info,
         lthy |> Local_Theory.declaration {syntax = false, pervasive = false}
          (fn phi => add_function_data (transform_function_data phi info)))
      end
  in
    ((goal_state, afterqed), lthy')
  end

fun gen_add_function do_print prep fixspec eqns config tac lthy =
  let
    val ((goal_state, afterqed), lthy') =
      prepare_function do_print prep fixspec eqns config lthy
    val pattern_thm =
      case SINGLE (tac lthy') goal_state of
        NONE => error "pattern completeness and compatibility proof failed"
      | SOME st => Goal.finish lthy' st
  in
    lthy'
    |> afterqed [[pattern_thm]]
  end

val add_function = gen_add_function false Specification.check_multi_specs
fun add_function_cmd a b c d int = gen_add_function int Specification.read_multi_specs a b c d

fun gen_function do_print prep fixspec eqns config lthy =
  let
    val ((goal_state, afterqed), lthy') =
      prepare_function do_print prep fixspec eqns config lthy
  in
    lthy'
    |> Proof.theorem NONE (snd oo afterqed) [[(Logic.unprotect (Thm.concl_of goal_state), [])]]
    |> Proof.refine_singleton (Method.primitive_text (K (K goal_state)))
  end

val function = gen_function false Specification.check_multi_specs
fun function_cmd a b c int = gen_function int Specification.read_multi_specs a b c

fun prepare_termination_proof prep_term raw_term_opt lthy =
  let
    val term_opt = Option.map (prep_term lthy) raw_term_opt
    val info =
      (case term_opt of
        SOME t =>
          (case import_function_data t lthy of
            SOME info => info
          | NONE => error ("Not a function: " ^ quote (Syntax.string_of_term lthy t)))
      | NONE =>
          (case import_last_function lthy of
            SOME info => info
          | NONE => error "Not a function"))

    val { termination, fs, R, add_simps, case_names, psimps,
      pinducts, defname, fnames, cases, dom, pelims, ...} = info
    val domT = domain_type (fastype_of R)
    val goal = HOLogic.mk_Trueprop (HOLogic.mk_all ("x", domT, mk_acc domT R $ Free ("x", domT)))
    fun afterqed [[totality]] lthy =
      let
        val _ = Output.writeln (@{make_string} ("###totality:", totality))
        val totality = Thm.close_derivation totality
        val remove_domain_condition =
          full_simplify (put_simpset HOL_basic_ss lthy
            addsimps [totality, @{thm True_implies_equals}])
        val tsimps = map remove_domain_condition psimps
        val tinduct = map remove_domain_condition pinducts
        val telims = map (map remove_domain_condition) pelims
      in
        lthy
        |> add_simps I "simps" I simp_attribs tsimps
        ||>> Local_Theory.note
          ((derived_name defname "induct", [Attrib.case_names case_names]), tinduct)
        ||>> fold_map (note_derived ("elims", [Attrib.consumes 1, Attrib.constraints 1]))
          (fnames ~~ telims)
        |-> (fn ((simps,(_,inducts)), elims) => fn lthy =>
          let val info' = { is_partial=false, defname=defname, fnames=fnames, add_simps=add_simps,
            case_names=case_names, fs=fs, R=R, dom=dom, psimps=psimps, pinducts=pinducts,
            simps=SOME simps, inducts=SOME inducts, termination=termination, cases=cases, pelims=pelims, elims=SOME elims}
          in
            (info',
             lthy
             |> Local_Theory.declaration {syntax = false, pervasive = false}
               (fn phi => add_function_data (transform_function_data phi info'))
             |> Spec_Rules.add Spec_Rules.Equational (fs, tsimps))
          end)
      end
  in
    (goal, afterqed, termination)
  end

fun gen_prove_termination prep_term raw_term_opt tac lthy =
  let
    val (goal, afterqed, termination) =
      prepare_termination_proof prep_term raw_term_opt lthy

    val totality = Goal.prove lthy [] [] goal (K tac)
  in
    afterqed [[totality]] lthy
end

val prove_termination = gen_prove_termination Syntax.check_term
val prove_termination_cmd = gen_prove_termination Syntax.read_term

fun gen_termination prep_term raw_term_opt lthy =
  let
    val (goal, afterqed, termination) = prepare_termination_proof prep_term raw_term_opt lthy
  in
    lthy
    |> Proof_Context.note_thmss ""
       [((Binding.empty, [Context_Rules.rule_del]), [([allI], [])])] |> snd
    |> Proof_Context.note_thmss ""
       [((Binding.empty, [Context_Rules.intro_bang (SOME 1)]), [([allI], [])])] |> snd
    |> Proof_Context.note_thmss ""
       [((Binding.name "termination", [Context_Rules.intro_bang (SOME 0)]),
         [([Goal.norm_result lthy termination], [])])] |> snd
    |> Proof.theorem NONE (snd oo afterqed) [[(goal, [])]]
  end

val termination = gen_termination Syntax.check_term
val termination_cmd = gen_termination Syntax.read_term


(* Datatype hook to declare datatype congs as "function_congs" *)

fun add_case_cong n thy =
  let
    val cong = #case_cong (Old_Datatype_Data.the_info thy n)
      |> safe_mk_meta_eq
  in
    Context.theory_map (Function_Context_Tree.add_function_cong cong) thy
  end

val _ = Theory.setup (Old_Datatype_Data.interpretation (K (fold add_case_cong)))


(* get info *)

val get_congs = Function_Context_Tree.get_function_congs

fun get_info ctxt t = Item_Net.retrieve (get_functions ctxt) t
  |> the_single |> snd


(* outer syntax *)
val _ =
  Outer_Syntax.local_theory_to_proof' @{command_keyword gunction}
    "define general recursive functions"
    (function_parser default_config
      >> (fn (config, (fixes, specs)) => function_cmd fixes specs config))

val _ =
  Outer_Syntax.local_theory_to_proof @{command_keyword uermination}
    "prove termination of a recursive function"
    (Scan.option Parse.term >> termination_cmd)


\<close>
  (* Fun.ML *)
ML \<open>

fun check_pats ctxt geq =
  let
    fun err str = error (cat_lines ["Malformed definition:",
      str ^ " not allowed in sequential mode.",
      Syntax.string_of_term ctxt geq])

    fun check_constr_pattern (Bound _) = ()
      | check_constr_pattern t =
      let
        val (hd, args) = strip_comb t
      in
        (case hd of
          Const (hd_s, hd_T) =>
          (case body_type hd_T of
            Type (Tname, _) =>
            (case Ctr_Sugar.ctr_sugar_of ctxt Tname of
              SOME {ctrs, ...} => exists (fn Const (s, _) => s = hd_s) ctrs
            | NONE => false)
          | _ => false)
        | _ => false) orelse err "Non-constructor pattern";
        map check_constr_pattern args;
        ()
      end

    val (_, qs, gs, args, _) = split_def ctxt (K true) geq

    val _ = if not (null gs) then err "Conditional equations" else ()
    val _ = map check_constr_pattern args

    (* just count occurrences to check linearity *)
    val _ = if fold (fold_aterms (fn Bound _ => Integer.add 1 | _ => I)) args 0 > length qs
      then err "Nonlinear patterns" else ()
  in
    ()
  end

fun mk_catchall fixes arity_of =
  let
    fun mk_eqn ((fname, fT), _) =
      let
        val n = arity_of fname
        val (argTs, rT) = chop n (binder_types fT)
          |> apsnd (fn Ts => Ts ---> body_type fT)

        val qs = map Free (Name.invent Name.context "a" n ~~ argTs)
      in
        HOLogic.mk_eq(list_comb (Free (fname, fT), qs),
          Const (@{const_name undefined}, rT))
        |> HOLogic.mk_Trueprop
        |> fold_rev Logic.all qs
      end
  in
    map mk_eqn fixes
  end

fun add_catchall ctxt fixes spec =
  let val fqgars = map (split_def ctxt (K true)) spec
      val arity_of = map (fn (fname,_,_,args,_) => (fname, length args)) fqgars
                     |> AList.lookup (op =) #> the
  in
    spec @ mk_catchall fixes arity_of
  end

fun further_checks ctxt origs tss =
  let
    fun fail_redundant t =
      error (cat_lines ["Equation is redundant (covered by preceding clauses):", Syntax.string_of_term ctxt t])
    fun warn_missing strs =
      warning (cat_lines ("Missing patterns in function definition:" :: strs))

    val (tss', added) = chop (length origs) tss

    val _ = case chop 3 (flat added) of
       ([], []) => ()
     | (eqs, []) => warn_missing (map (Syntax.string_of_term ctxt) eqs)
     | (eqs, rest) => warn_missing (map (Syntax.string_of_term ctxt) eqs
         @ ["(" ^ string_of_int (length rest) ^ " more)"])

    val _ = (origs ~~ tss')
      |> map (fn (t, ts) => if null ts then fail_redundant t else ())
  in
    ()
  end

fun sequential_preproc (config as FunctionConfig {sequential, ...}) ctxt fixes spec =
  if sequential then
    let
      val (bnds, eqss) = split_list spec

      val eqs = map the_single eqss

      val feqs = eqs
        |> tap (check_defs ctxt fixes) (* Standard checks *)
        |> tap (map (check_pats ctxt)) (* More checks for sequential mode *)

      val compleqs = add_catchall ctxt fixes feqs (* Completion *)

      val spliteqs = Function_Split.split_all_equations ctxt compleqs
        |> tap (further_checks ctxt feqs)

      fun restore_spec thms =
        bnds ~~ take (length bnds) (unflat spliteqs thms)

      val spliteqs' = flat (take (length bnds) spliteqs)
      val fnames = map (fst o fst) fixes
      val indices = map (fn eq => find_index (curry op = (fname_of eq)) fnames) spliteqs'

      fun sort xs = partition_list (fn i => fn (j,_) => i = j) 0 (length fnames - 1) (indices ~~ xs)
        |> map (map snd)


      val bnds' = bnds @ replicate (length spliteqs - length bnds) Binding.empty_atts

      (* using theorem names for case name currently disabled *)
      val case_names = map_index (fn (i, (_, es)) => mk_case_names i "" (length es)) 
        (bnds' ~~ spliteqs) |> flat
    in
      (flat spliteqs, restore_spec, sort, case_names)
    end
  else
    Function_Common.empty_preproc check_defs config ctxt fixes spec

val _ = Theory.setup (Context.theory_map (Function_Common.set_preproc sequential_preproc))



val fun_config = FunctionConfig { sequential=true, default=NONE,
  domintros=false, partials=false }

fun gen_add_fun add lthy =
  let
    fun pat_completeness_auto ctxt =
      Pat_Completeness.pat_completeness_tac ctxt 1
      THEN auto_tac ctxt
    fun prove_termination lthy =
      Function.prove_termination NONE (Function_Common.termination_prover_tac false lthy) lthy
  in
    lthy
    |> add pat_completeness_auto |> snd
    |> prove_termination |> snd
  end

fun add_fun a b c = gen_add_fun (Function.add_function a b c)
fun add_fun_cmd a b c int = gen_add_fun (fn tac => Function.add_function_cmd a b c tac int)

\<close>

ML \<open>
val _ =
  Outer_Syntax.local_theory' @{command_keyword gun}
    "define general recursive functions (short version)"
    (function_parser fun_config
      >> (fn (config, (fixes, specs)) => (
          let
             val ((((a0,a1), b), c, d)::e) = specs
             val haha = length c
             val _ = Output.writeln (@{make_string} ("##config: ", config))
             val _ = Output.writeln (@{make_string} ("##fixes: ", fixes))
             val _ = Output.writeln (@{make_string} ("##specs: ", specs))
             val _ = Output.writeln (@{make_string} ("##haha: ", haha))
          in 
          add_fun_cmd fixes specs config
          end)))
\<close>
  
ML \<open>
PROFILE;
Pretty.writeln (Pretty.str "adsf");
default_config;
@{make_string} 0
\<close>
  
context
  fixes w :: "nat \<Rightarrow> nat"
begin
  
term 0 (**)
gun f :: "nat \<Rightarrow> nat" where
  "f 0 = 0"
| "f (Suc x) = Suc (f x)"
  
  
ML \<open>
val (x::y) = [3, 4];
x;
y;
"#" ^ "$" ^ "%" = "#$%";
substring ("asdf", 0, 1);
hd;
\<close>
  (*,
  type multi_specs_cmd =
    ((Attrib.binding * string) * string list * (binding * string option * mixfix) list) list
  type multi_specs =
    ((Attrib.binding * term) * term list * (binding * typ option * mixfix) list) list

*)
  
ML \<open>
val ff_cmd_fixes: (binding * string option * mixfix) list = [(@{binding ff}, SOME "nat \<Rightarrow> nat", NoSyn)];
val ff_cmd_specs: Specification.multi_specs_cmd =
  [(((Binding.empty, []), "ff 0 = 0"), [], []),
   (((Binding.empty, []), "ff (Suc x) = Suc (f x)"), [], [])];
\<close>
term 0 (**)
local_setup \<open>
add_fun_cmd ff_cmd_fixes ff_cmd_specs default_config false
\<close>
term ff
thm ff.simps
  
ML \<open>
val gg_fixes: (binding * typ option * mixfix) list =
  [(@{binding gg}, SOME @{typ "nat \<Rightarrow> nat"}, NoSyn)];
val gg_specs: Specification.multi_specs = 
  [(((Binding.empty, []),
   @{term "Trueprop (gg (0::nat) = (0::nat))"}),
    [], []),
   (((Binding.empty, []),
    @{term "Trueprop (gg (Suc x) = Suc (gg x))"}),
    [], [])];
val gg_specs_alt: Specification.multi_specs = 
  [(((Binding.empty, []),
   Const ("HOL.Trueprop", @{typ "bool \<Rightarrow> prop"}) $
      (Const ("HOL.eq", @{typ "nat \<Rightarrow> nat \<Rightarrow> bool"}) $
        (Free ("gg", @{typ "nat \<Rightarrow> nat"}) $
          Const ("Groups.zero_class.zero",
                 @{typ "nat"})) $
        Const ("Groups.zero_class.zero", @{typ "nat"}))),
    [], []),
   (((Binding.empty, []),
    Const ("HOL.Trueprop", @{typ "bool \<Rightarrow> prop"}) $
      (Const ("HOL.eq", @{typ "nat \<Rightarrow> nat \<Rightarrow> bool"}) $
        (Free ("gg",
                @{typ "nat \<Rightarrow> nat"}) $
          (Const ("Nat.Suc", @{typ "nat \<Rightarrow> nat"}) $
            Free ("x", @{typ "nat"}))) $
        (Const ("Nat.Suc", @{typ "nat \<Rightarrow> nat"}) $
          (Free ("gg",
                  @{typ "nat \<Rightarrow> nat"}) $
            Free ("x", @{typ "nat"}))))),
    [], [])];
\<close>
term 0 (**)
  
local_setup \<open>
add_fun gg_fixes gg_specs default_config
\<close>
  
thm gg.simps
  
ML \<open>
@{typ "nat \<Rightarrow> nat"};
@{prop "3 \<equiv> 4"} = @{term "3 \<equiv> 4"};
Const;
Args.term;
Args.prop;
Syntax.read_prop;
(*
open Syntax_Phases;
      parse_term = parse_term false,
      parse_prop = parse_term true,
*)
Function.get_info @{context} @{term gg} |> #simps |> the |> map Thm.prop_of;
Const ("HOL.Trueprop", @{typ "bool \<Rightarrow> prop"});

val it =
   [Const ("HOL.Trueprop", @{typ "bool \<Rightarrow> prop"}) $
      (Const ("HOL.eq", @{typ "nat \<Rightarrow> nat \<Rightarrow> bool"}) $
        (Const ("Scratch_Function_Dump.gg",
                @{typ "nat \<Rightarrow> nat"}) $
          Const ("Groups.zero_class.zero",
                 @{typ "nat"})) $
        Const ("Groups.zero_class.zero", @{typ "nat"})),
    Const ("HOL.Trueprop", @{typ "bool \<Rightarrow> prop"}) $
      (Const ("HOL.eq", @{typ "nat \<Rightarrow> nat \<Rightarrow> bool"}) $
        (Const ("Scratch_Function_Dump.gg",
                @{typ "nat \<Rightarrow> nat"}) $
          (Const ("Nat.Suc", @{typ "nat \<Rightarrow> nat"}) $
            Var (("x", 0), @{typ "nat"}))) $
        (Const ("Nat.Suc", @{typ "nat \<Rightarrow> nat"}) $
          (Const ("Scratch_Function_Dump.gg",
                  @{typ "nat \<Rightarrow> nat"}) $
            Var (("x", 0), @{typ "nat"}))))];
\<close>
ML \<open>
@{prop "3 \<equiv> 4"};
@{term "3 \<equiv> 4"};
@{prop "3 = 4"};
@{term "(3::nat) = 4"};
\<close>
  
ML \<open>
@{term "0::nat"};
@{typ "nat \<Rightarrow> nat"} = Type ("fun", [Type ("Nat.nat", []), Type ("Nat.nat", [])]);

val x = @{typ "nat option \<Rightarrow> int \<Rightarrow> nat list"};
x |> range_type;
x |> domain_type;
x |> dest_funT;
x |> binder_types;
x |> body_type;
x |> strip_type;
x |> size_of_typ;

\<close>
term HOL.Trueprop
term "Trueprop (a=a)"
term Pure.eq
ML \<open>
val eq0 = @{term "Trueprop (gg (0::nat) = (0::nat))"};
val eq1 = @{term "Trueprop (gg (Suc x) = Suc (gg x))"};
eq0 |> dest_comb ||>> dest_comb;
eq1 |> (strip_comb ##> map strip_comb);
\<close>
ML \<open>
@{term "\<lambda>x y. Suc(x+y)"};
@{term "\<And>x. x=[]"};
@{term "ttt=5"};
@{term "gg=gg"}
\<close>
  
ML \<open>
val gginfo = Function.get_info @{context} @{term gg};
\<close>
  
ML \<open>
gginfo |> #simps |> the |> hd |> Thm.proof_of;
gginfo |> #psimps |> tl |> hd |> Thm.proof_of;
nth;
val _ = @{thm append1_eq_conv} |> Thm.proof_of;
val _ = @{thm refl} |> Thm.proof_of;
fun f (z_smaller: cterm) lhs_acc acc_downward = (Thm.assume z_smaller) RS ((Thm.assume lhs_acc) RS acc_downward);
Type.constraint (type_of @{term ff}) @{term "[]"};
Local_Theory.abbrev;
@{map 7};
refl;
spec;
HOLogic.mk_not @{term "~x"};
HOLogic.mk_Trueprop;
Goal.init @{cterm "HOL.Trueprop (x=y)"};
Goal.init @{cterm "HOL.Trueprop (x=y)"} |> Goal.conclude;
SINGLE;
fold_rev;
@{thm acc.accI};
@{thm accp.accI};
forall_intr_rename;
@{make_string};
ML_Pretty.make_string_fn;
\<close>
ML \<open>
put_simpset;
HOL_basic_ss;
op addsimps;
\<close>
thm True_implies_equals
term ff_graph
term ff_dom
context (* Longest path *)
  fixes v :: "nat \<Rightarrow> nat"
    and p :: "nat \<Rightarrow> nat"
  assumes p_lt: "p (Suc j) < Suc j"
begin


text \<open>Dimensionality given by i\<close>
gunction wis :: "nat \<Rightarrow> nat" where
  "wis 0 = 0" |
  "wis (Suc i) = max (wis (p (Suc i)) + v i) (wis i)"
  by pat_completeness auto
uermination
  by (relation "(\<lambda>p. size p) <*mlex*> {}") (auto intro: wf_mlex mlex_less simp: p_lt)

end
  
ML \<open>
Thm.close_derivation;
Thm.derivation_name @{thm spec};
\<close>  
end
end