theory Bellman_Ford
  imports "../DP_Lifting" "../DP_CRelVS" "../DP_Proof"
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

lemma bf_induct:
  "\<lbrakk>\<And>j. P (0, j);
    \<And>k j. \<lbrakk>\<And>x. P (k, x);
           P (k, j)
           \<rbrakk> \<Longrightarrow> P (Suc k, j)
   \<rbrakk> \<Longrightarrow> P (x::nat\<times>nat)"
  by (fact bf\<^sub>T.induct)

lemma bf_induct':
  "\<lbrakk>\<And>j. pred_fun (pred_prod (op = 0) (op = j)) id P;
    \<And>k j. \<lbrakk>pred_fun (pred_prod (op = k) top) id P;
           pred_fun (pred_prod (op = k) (op = j)) id P\<rbrakk> \<Longrightarrow> P (Suc k, j)
   \<rbrakk> \<Longrightarrow> P (x::nat\<times>nat)"
  subgoal premises IH
    apply (rule bf_induct)
    subgoal premises prems for j
      apply (rule IH(1)[of j, unfolded pred_fun_def id_def, THEN spec, THEN mp])
      apply (rule pred_prod.intros)
       apply (rule refl)
      apply (rule refl)
      done
    subgoal premises prems for k j
      apply (rule IH(2)[of k j])
      subgoal
        unfolding pred_fun_def id_def
        apply (rule allI, rule impI)
        apply (erule pred_prod.induct)
        apply (clarify)
        apply (rule prems(1))
        done
      subgoal
        unfolding pred_fun_def id_def
        apply (rule allI, rule impI)
        apply (erule pred_prod.induct)
        apply clarify
        apply (rule prems(2))
        done
      done
    done
  done
    
    
term 0 (**)

lemma bf_inductS:
  "\<lbrakk>\<And>j. bf.crel_vs op = (bf (0, j)) (bf\<^sub>T (0, j));
    \<And>k j. \<lbrakk>\<And>x. bf.crel_vs op = (bf (k, x)) (bf\<^sub>T (k, x));
           bf.crel_vs op = (bf (k, j)) (bf\<^sub>T (k, j))
           \<rbrakk> \<Longrightarrow> bf.crel_vs op = (bf (Suc k, j)) (bf\<^sub>T (Suc k, j))
   \<rbrakk> \<Longrightarrow> bf.crel_vs op = (bf (x::nat\<times>nat)) (bf\<^sub>T x)"
  by (fact bf_induct)

definition "K x \<equiv> eq_onp (op = x)"
lemma K_self: "K x x x"
  unfolding K_def eq_onp_def by auto
    
ML \<open>
fun debug_tac th = let val _ = @{print} th in all_tac th end;
SOLVE;
\<close>
  
lemma bf_inductS':
  "\<And>param.
  \<lbrakk>\<And>j. K j j j \<Longrightarrow> bf.crel_vs op = (bf (0, j)) (bf\<^sub>T (0, j));
    \<And>k j. \<lbrakk>K k k k; K j j j;
           (rel_prod (K k) (op =) ===> bf.crel_vs op =) bf bf\<^sub>T;
           (rel_prod (K k) (K j) ===> bf.crel_vs op =) bf bf\<^sub>T
           \<rbrakk> \<Longrightarrow> bf.crel_vs op = (bf (Suc k, j)) (bf\<^sub>T (Suc k, j))
   \<rbrakk> \<Longrightarrow> (\<lambda>param. bf.crel_vs op = (bf param) (bf\<^sub>T param)) (param::nat\<times>nat)"
term 0 *)
  ML_val \<open>Goal.init; print_tac;
op oo;
op THEN_ALL_NEW;
TRY;
solve_tac;
unfold_tac;
clarify_tac;
Proof_Context.fact_tac;
clarsimp_tac;
SUBGOAL;
Subgoal.subgoal_cmd;
full_simp_tac;
op addsimps;
clear_simpset;
rewrite_goals_tac;
simp_tac;
\<close>
ML_prf \<open>
fun tac0 ctxt prems = (
        K all_tac
THEN' (K debug_tac)
        THEN' (resolve_tac ctxt @{thms rel_funI}

        THEN' eresolve_tac ctxt @{thms rel_prod.induct}
        THEN' (K (unfold_tac ctxt @{thms K_def eq_onp_def}))
        THEN' clarify_tac ctxt

        THEN' Proof_Context.fact_tac ctxt prems) ORELSE' (resolve_tac ctxt @{thms K_self}));
SIMPLE_METHOD;
TRY;
SOLVE;
resolve_tac;
assume_tac;
\<close>

  ML_prf \<open>
fun pretty_cterm ctxt ctrm =
Syntax.pretty_term ctxt (Thm.term_of ctrm)

fun pretty_terms ctxt trms =
Pretty.block (Pretty.commas (map (Syntax.pretty_term ctxt) trms));

fun pretty_thm_no_vars ctxt thm =
let
val ctxt' = Config.put show_question_marks false ctxt
in
Syntax.pretty_term ctxt' (Thm.prop_of thm)
end

fun pretty_thms_no_vars ctxt thms =
  Pretty.block (Pretty.commas (map (pretty_thm_no_vars ctxt) thms));

fun pretty_cterms ctxt ctrms =
  Pretty.block (Pretty.commas (map (pretty_cterm ctxt) ctrms));

fun foc_tac focus =
    let
      val {prems, params, asms, concl, context, schematics}: Subgoal.focus = focus;
      fun assgn1 f1 f2 xs =
        let
        val out = map (fn (x, y) => Pretty.enum ":=" "" "" [f1 x, f2 y]) xs
        in
        Pretty.list "" "" out
        end

      fun assgn2 f xs = assgn1 f f xs

      val pps = map (fn (s, pp) => Pretty.block [Pretty.str s, pp])
        [("params: ", assgn1 Pretty.str (pretty_cterm context) params),
        ("assumptions: ", pretty_cterms context asms),
        ("conclusion: ", pretty_cterm context concl),
        ("premises: ", pretty_thms_no_vars context prems),
        ("schematics: ", Pretty.str (@{make_string} schematics))
        ]
    in
      tracing (Pretty.string_of (Pretty.chunks pps)); all_tac
    end
\<close>
(*    apply(tactic {* Subgoal.FOCUS foc_tac @{context} 1 *})*)
  ML_prf \<open>
val tactac =       resolve_tac @{context} @{thms K_self}
      ORELSE' (resolve_tac @{context} @{thms rel_funI}
        THEN' eresolve_tac @{context} @{thms rel_prod.induct}
        THEN' (SELECT_GOAL (unfold_tac @{context} @{thms K_def eq_onp_def}))
        THEN' clarsimp_tac @{context})
;
Proof.apply;
Method.evaluate;
Proof_Context.note_thmss;
Transfer.transfer_raw_add;
fold;

\<close>

  ML_val \<open>#goal @{Isar.goal}\<close>
    term 0 (**)
  apply (tactic \<open>HEADGOAL (
    resolve_tac @{context} @{thms bf\<^sub>T.induct}
    THEN_ALL_NEW (fn i => Subgoal.FOCUS (fn {context=ctx, prems=IH, ...} =>
      HEADGOAL (resolve_tac ctx [nth IH (i-1)])) @{context} i)
    THEN_ALL_NEW tactac)\<close>)
  done
interpretation bf: dp_consistency bf .
lemma "bf.consistentDP bf\<^sub>T"
  
  (*by (dp_match induct: bf_inductS' simp: bf.simps simp\<^sub>T: bf\<^sub>T.simps)*)
  (*
  ( rule dp_consistency.consistentDP_intro,
    rule induct,
    unfold simp\<^sub>T;
    rule dp_consistency.crel_vs_checkmem,
    unfold simp,
    ((match premises in _[transfer_rule]: _ (multi) \<Rightarrow> transfer_prover)
      | (match conclusion in _ \<Rightarrow> transfer_prover)))
*)
  apply (tactic \<open>resolve_tac @{context} @{thms "dp_consistency.consistentDP_intro"} 1\<close>)
  apply (tactic \<open>resolve_tac @{context} @{thms "bf_inductS'"} 1\<close>)
   apply (tactic \<open>unfold_tac @{context} @{thms bf\<^sub>T.simps}\<close>)
   apply (tactic \<open>ALLGOALS (resolve_tac @{context} @{thms "dp_consistency.crel_vs_checkmem"})\<close>)
   apply (tactic \<open>unfold_tac @{context} @{thms bf.simps}\<close>)
   apply (tactic \<open>Subgoal.FOCUS (fn {context=ctxt, prems, ...} => Transfer.transfer_prover_tac ctxt 1) @{context} 1\<close>)
  apply (tactic \<open>Subgoal.FOCUS (fn {context=ctxt, prems, ...} =>
  let
    val ctxt' = fold Transfer.transfer_raw_add prems (Context.Proof ctxt) |> Context.proof_of;
  in
    Transfer.transfer_prover_start_tac ctxt' 1
  end) @{context} 1\<close>)
    oops
      ML_val  \<open>
Toplevel.proofs;
Subgoal.subgoal
\<close>
  term 0 (*
  apply (tactic \<open>HEADGOAL (
    resolve_tac @{context} @{thms bf\<^sub>T.induct}
    THEN_ALL_NEW (fn i => Subgoal.FOCUS (fn {context=ctx, prems=IH, ...} =>
      HEADGOAL (resolve_tac ctx [nth IH (i-1)])) @{context} i)
THEN_ALL_NEW tactac)\<close>)
      term 0 (*
    THEN_ALL_NEW (
      resolve_tac @{context} @{thms K_self}
      ORELSE' (resolve_tac @{context} @{thms rel_funI}
        THEN' eresolve_tac @{context} @{thms rel_prod.induct}
        THEN' (K (unfold_tac @{context} @{thms K_def eq_onp_def}))
        THEN' clarsimp_tac @{context}
      )
      ORELSE' (K (print_tac @{context} "wtf"))
    )
)
\<close>)
    term 0 (*
  apply (tactic \<open>Subgoal.FOCUS (fn {context=ctx, prems=IH, ...} =>
    resolve_tac ctx IH 1) @{context} 1\<close>)
   apply (tactic \<open>resolve_tac @{context} @{thms K_self} 1\<close>)
    apply (tactic \<open>Subgoal.FOCUS (fn {context=ctx, prems=IH, ...} =>
    resolve_tac ctx IH 1) @{context} 1\<close>)
     apply (tactic \<open>resolve_tac @{context} @{thms K_self} 1\<close>)
    apply (tactic \<open>resolve_tac @{context} @{thms K_self} 1\<close>)
    apply (tactic \<open>(resolve_tac @{context} @{thms rel_funI}

        THEN' eresolve_tac @{context} @{thms rel_prod.induct}
        THEN' (K (unfold_tac @{context} @{thms K_def eq_onp_def}))
        THEN' clarsimp_tac @{context}

) 1\<close>)+
      
term 0 (*
  apply(tactic \<open>
    HEADGOAL (Subgoal.FOCUS (fn {context=ctxt, prems=IH, ...} => HEADGOAL (
      let
        val _ = @{print} IH;
      in
        resolve_tac ctxt @{thms bf\<^sub>T.induct}
        THEN_ALL_NEW (fn i =>
          let
            val _ = @{print} i;
          in
            Subgoal.FOCUS (fn {context=ctxt, params, prems, schematics, ...} => HEADGOAL (
              let
                val _ = @{print} ("prems", prems, "params", params, "schematics", schematics)
              in
                resolve_tac ctxt [nth IH (i-1)]
                THEN_ALL_NEW (fn i =>
                  let
                    val _ = @{print} ("inner", i)
                  in
                    Subgoal.FOCUS (fn {context=ctxt, ...} => HEADGOAL (
                      resolve_tac ctxt @{thms K_self}
                    )) ctxt i
                    ORELSE
                    Subgoal.FOCUS (fn {context=ctxt, ...} =>
                      HEADGOAL (resolve_tac ctxt @{thms rel_funI})
                      THEN HEADGOAL (eresolve_tac ctxt @{thms rel_prod.induct})
                      THEN (unfold_tac ctxt @{thms K_def eq_onp_def})
                      THEN HEADGOAL (clarify_tac ctxt)
THEN print_tac ctxt "blah"
                    ) ctxt i
                    ORELSE (debug_tac)
                  end)
              end
            )) ctxt i
          end
        )
      end
    )) @{context})
\<close>)
term 0 *)
*)
  subgoal premises IH
    apply (rule bf\<^sub>T.induct)
    subgoal premises prems
      apply (rule IH(1))
      subgoal by (rule K_self)
      done
      term 0 (**)
    subgoal premises prems
      apply (rule IH(2))
      subgoal by (rule K_self)
      subgoal by (rule K_self)
      subgoal
        apply (rule rel_funI)
        apply (erule rel_prod.induct)
        unfolding K_def eq_onp_def
        apply clarify
        apply (fact prems)
        done
      subgoal
        apply (rule rel_funI)
        apply (erule rel_prod.induct)
        unfolding K_def eq_onp_def
        apply clarify
        apply (fact prems)
        done
      done
    done
  done
thm eq_onp_to_eq
  
interpretation bf: dp_consistency bf .
lemma "bf.consistentDP bf\<^sub>T"
  by (dp_match induct: bf_inductS' simp: bf.simps simp\<^sub>T: bf\<^sub>T.simps)
    
term 0 (**)
  thm bf.induct[split_format(complete)] bf.induct
ML_command \<open>
val prop = @{thm bf.induct} |> Thm.prop_of;
val horn = prop |> Logic.strip_horn;
val horn0 = horn |> fst |> hd;
val horn00 = horn0 |> Logic.strip_assums_concl;
@{print} horn0
\<close>
ML_command \<open>
val prop = @{thm bf.consistentDP_intro} |> Thm.prop_of;
val concl = prop |> Logic.strip_assums_concl;
val cterm = prop |> Thm.cterm_of @{context};
cterm |> Goal.init |> Goal.conclude;
\<close>
ML_val \<open>
@{term "True = True"} |> HOLogic.mk_Trueprop |> Thm.cterm_of @{context} |> Goal.init;
Clasimp.auto_tac;
op RS;
@{cterm P};
resolve_tac;
Proof.apply;
\<close>
ML \<open>
val pth: tactic = fn th =>
  let
    val _ = @{print} th;
  in
    all_tac th
  end
\<close>
  
ML \<open>
val prop = @{thm bf.induct} |> Thm.prop_of;
val (IH, thesis) = prop |> Logic.strip_horn;
val prop' = Logic.list_implies (IH, thesis);
val cterm' = Thm.cterm_of @{context} prop';
val tac = HEADGOAL (resolve_tac @{context} @{thms bf.induct});
fun factac ctxt = Proof_Context.fact_tac ctxt @{thms bf.induct};
val thm' = Goal.init cterm'
|> tac |> Seq.hd
;
Goal.prove @{context} [] [] prop' (K (HEADGOAL (factac @{context})));
@{print} it;
@{print} prop';
@{print} @{thms bf.induct};
Variable.variant_frees;
Term.close_schematic_term prop;
@{print} it;
@{print} prop;
Term.abs;
Name.is_skolem;
\<close>
  
ML \<open>
val pp = @{thm bf.induct} |> Thm.prop_of;
Term.add_vars pp [];
pp |> Term.close_schematic_term;

fun
  all_abs (Abs (x, tp, body)) = Logic.all_const tp $ Abs(x, tp, all_abs body)
| all_abs tm = tm;                          

val ppa = pp |> Term.close_schematic_term |> all_abs;
val cterm = Thm.cterm_of @{context} ppa;

Goal.prove @{context} [] [] ppa (K (HEADGOAL (factac @{context})));
\<close>
  
ML \<open>
ppa |> Logic.strip_params;
ppa |> Logic.strip_assums_hyp;
ppa |> Logic.strip_assums_concl;
not true;
length;
HOLogic.mk_eq;
HOLogic.eq_const;
nth;
@{const_name K};
@{const_name Pair};
Term.type_of;
HOLogic.boolT;
@{type_name prod};
@{term "bf.crel_vs"};
@{const_name "DP_CRelVS.dp_consistency.crel_vs"};
op @;
(Term.strip_type @{typ "'a => 'a => bool"} |> snd) = HOLogic.boolT;
val s = "s";
BNF_Util.mk_pred2T;
op `;
HOLogic.dest_Trueprop @{prop "None=None"};
HOLogic.mk_prodT;
single;
\<close>
  
ML \<open>
@{method auto};
Method.check_name;
Method_Closure.apply_method;
Proof.apply;
Method.evaluate;
Thm.instantiate;
Rule_Insts.where_rule;
Term.abs;
\<close>
term rel_fun
thm bf\<^sub>T.induct[of x]
term 0 (**)
ML_file \<open>../scratch/Transform_Induct.ML\<close>
  
ML_val \<open>
val prop = transform_induct @{context} @{thm bf\<^sub>T.induct};
Goal.prove;
Subgoal.subgoal;
\<close>    