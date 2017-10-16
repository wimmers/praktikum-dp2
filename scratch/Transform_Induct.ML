val f_head = @{term "bf"};
val fT_head = @{term "bf\<^sub>T"};

val dom_type = @{typ "nat \<times> nat"};
val ran_type = @{typ "int"};
val mem_type = dom_type --> Type (@{type_name "Option.option"}, [ran_type]);
fun state_type M a = Type (@{type_name Monad.state}, [M, a]);
val ran_type_lifted = state_type mem_type ran_type;

val eq_rel_tp = (ran_type --> ran_type --> HOLogic.boolT);
val eq_rel_lifted_tp = (ran_type --> ran_type_lifted --> HOLogic.boolT);

val crel_vs_name = @{const_name "DP_CRelVS.dp_consistency.crel_vs"};
val crel_vs_eq = Const (crel_vs_name, (dom_type --> ran_type) --> eq_rel_tp --> eq_rel_lifted_tp) $ f_head $ HOLogic.eq_const ran_type;

fun mk_rel_fun_tp ((tp_a, tp_b), (tp_c, tp_d)) =
  (tp_a --> tp_b --> HOLogic.boolT) --> (tp_c --> tp_d --> HOLogic.boolT) -->
  (tp_a --> tp_c) --> (tp_b --> tp_d) --> HOLogic.boolT;

fun mk_rel_fun_tm tps = Const (@{const_name rel_fun}, mk_rel_fun_tp tps)

fun mk_rel_prod_tp ((tp_a, tp_b), (tp_c, tp_d)) =
  (tp_a --> tp_b --> HOLogic.boolT) --> (tp_c --> tp_d --> HOLogic.boolT) -->
  HOLogic.mk_prodT (tp_a, tp_c) --> HOLogic.mk_prodT (tp_b, tp_d) --> HOLogic.boolT;

fun mk_rel_prod_tm tps = Const (@{const_name rel_prod}, mk_rel_prod_tp tps);



fun mk_K1 tp tm =
  Const (@{const_name K}, tp --> tp --> tp --> HOLogic.boolT) $ tm

fun mk_K tm = mk_K1 (Term.type_of tm) tm;

fun
  all_abs (Abs (x, tp, body)) = Logic.all_const tp $ Abs(x, tp, all_abs body)
| all_abs tm = tm;

fun strip_prop prop =
  (Logic.strip_params prop, Logic.strip_assums_hyp prop, Logic.strip_assums_concl prop);

fun strip_arg prop =
  let
    val (_, [arg]) = HOLogic.dest_Trueprop prop |> Term.strip_comb;
  in
    arg
  end

fun replace_P prop =
  let
    val arg = strip_arg prop;
  in
    (Term.abs ("param", dom_type) (crel_vs_eq $ (f_head $ Bound 0) $ (fT_head $ Bound 0))) $ arg |> HOLogic.mk_Trueprop
  end;

fun transform_IH IH =
  let
    val (params, IH2s, IH_concl) = strip_prop IH;
  
    fun transform_IH2 IH2 =
      let
        val (params2, IH3s, IH2_concl) = strip_prop IH2;
        val n_param2 = length params2;
        val _ = @{print} n_param2;
        val _ = if null IH3s then () else raise TERM("non empty IH3", IH3s);
    
        val bound_types = (params2 @ params) |> map snd;
        val arg = strip_arg IH2_concl;
        
        fun
          arg_to_rel (tm as (Const _)) = mk_K tm
        | arg_to_rel (tm as (Bound b)) =
          let
            val tm' = Bound (b - n_param2)
          in
            if b < n_param2
              then HOLogic.eq_const (Term.type_of1 (bound_types, tm))
              else mk_K1 (Term.type_of1 (bound_types, tm)) tm'
          end
        | arg_to_rel (tm as (Const (@{const_name Pair}, _)) $ p0 $ p1) =
          let
            val tp = Term.type_of1 (bound_types, tm);
            val Type (@{type_name prod}, [tp0, tp1]) = tp;
          in
            mk_rel_prod_tm ((tp0, tp0), (tp1, tp1)) $ (arg_to_rel p0) $ (arg_to_rel p1)
          end
        | arg_to_rel tm = raise TERM("unsupported", tm |> Term.strip_comb |> snd);
val _ = @{print} arg;
        val arg_rel = arg_to_rel arg;
        val arg_tp = Term.type_of1 (bound_types, arg);
        val rel_fun = mk_rel_fun_tm ((arg_tp, arg_tp), (ran_type, ran_type_lifted)) $ arg_rel $ crel_vs_eq;

        val IH2' = rel_fun $ f_head $ fT_head;
      in
        IH2' |> HOLogic.mk_Trueprop
      end;
    
    val IH2s' = map transform_IH2 IH2s;
    val IH' = Logic.list_all (params, Logic.list_implies (IH2s', replace_P IH_concl));
  in
    IH'
  end;

fun transform_induct ctxt induct_thm =
  let
    val quantified = induct_thm |> Thm.prop_of |> Term.close_schematic_term |> all_abs;    
    val (params, IHs, concl) = strip_prop quantified;

    val IHs' = map transform_IH IHs;
    val induct_prop' = Logic.list_all (params, Logic.list_implies (IHs', replace_P concl));
  in
(*    Goal.prove ctxt [] [] induct_prop' (K (HEADGOAL (Proof_Context.fact_tac ctxt [induct_thm])))*)
Goal.init (Thm.cterm_of ctxt induct_prop')
  end;