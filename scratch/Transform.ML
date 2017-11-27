fun get_rest prefix l =
  let
    val (l_prefix, l_postfix) = chop (length prefix) l
  in
    if length prefix <= length l andalso l_prefix = prefix then SOME l_postfix else NONE
  end;

fun subst_var_free tm =
  map_aterms (fn x =>
    case x of
      Var ((vn, 0), tp) => Free (vn, tp)
    | Var _ => raise TERM("nonzero indexname", [x])
    | _ => x) tm;

infix 9 <$>;

fun state_type M a = Type (@{type_name Monad.state}, [M, a]);

fun extract_lhs (lhs: term) =
  let
    val (func_head, all_param) = strip_comb lhs;
    val (context, param) = split_last all_param;
  in
    (func_head, context, param)
  end;

fun lift_fun term_checkmem term_crel_vs term_opt = fn ctxt =>
  let
    val func_info =
      case term_opt of
        SOME tm => Function.get_info ctxt tm
      | NONE => Function_Common.import_last_function ctxt |> the;

    val funcT_binding = #fnames func_info |> the_single |> Binding.suffix_name "\<^sub>T";
    val funcT_name = Binding.name_of funcT_binding;

    val local_func_head = #fs func_info |> the_single;
    val func_type = local_func_head |> type_of;
    val (dom_type, ran_type) = dest_funT func_type;
    val mem_type = dom_type --> Type (@{type_name "Option.option"}, [ran_type]);
    val ran_type_lifted = state_type mem_type ran_type;

    val _ = Pretty.writeln (Pretty.block [
      Pretty.str "Transform", Pretty.brk 1,
      Pretty.quote (Syntax.pretty_term ctxt local_func_head), Pretty.brk 1,
      Pretty.str "into", Pretty.brk 1,
      Pretty.str funcT_name])
    
    val _ =
      case ran_type of
        Type (@{type_name fun}, _) => raise TYPE("ran_type cannot be function", [ran_type], [])
      | _ => ();

    (* TODO: quadratic -> linear *)
    fun return1 bound_types tm =
      let
        val tp = type_of1 (bound_types, tm);
      in
        Const (@{const_name Monad.return}, tp --> state_type mem_type tp) $ tm
      end;
    
    fun app_lifted1 bound_types (fT, xT) =
      let
        val fT_tp as Type (@{type_name Monad.state}, [_, Type (@{type_name fun}, [dom, fx_tp])])
               = type_of1 (bound_types, fT);
        val xT_tp as Type (@{type_name Monad.state}, [_, dom']) = type_of1 (bound_types, xT);
      in
        if dom = dom'
          then Const (@{const_name DP_Lifting.fun_app_lifted}, fT_tp --> xT_tp --> fx_tp) $ fT $ xT
          else raise TYPE("inconsistent state dom type", [dom,dom'], [fT,xT])
      end;
    
    fun
      lift_type tp = state_type mem_type (lift_type' tp)
    and
      lift_type' (Type (@{type_name fun}, [dom, ran])) = (lift_type' dom) --> (lift_type ran)
    | lift_type' tp = tp;
    
    fun
      lift_pure_term bound_types tm = return1 bound_types (lift_pure_term' bound_types tm)
    and
      lift_pure_term' bound_types tm =
        (case type_of1 (bound_types, tm) of
          Type (@{type_name fun}, [dom, _]) =>
            (case dom of
              Type (@{type_name fun}, _) => raise TYPE("High order domain type", [dom], [tm])
            | _ => Term.absdummy dom (lift_pure_term (dom::bound_types) (incr_boundvars 1 tm $ Bound 0)))
         | _ => tm);

    val funcT_head = Free (funcT_name, dom_type --> ran_type_lifted);

    fun transform_simp simp_thm =
      let
        val (lhs, rhs0) = Thm.full_prop_of simp_thm |> HOLogic.dest_Trueprop |> HOLogic.dest_eq;
        val rhs = subst_var_free rhs0;
    
        val (func_head, _, param0) = extract_lhs lhs;
        val param = subst_var_free param0;
    
        fun lift_term bound_types tm =
          let
            val return = return1 bound_types;
            val op <$> = app_lifted1 bound_types;
    
            fun check_map tm =
              case tm of
                map_term $ f $ ls =>
                  if Term.aconv_untyped (map_term, @{term map})
                    then SOME (
                      Const (@{const_name DP_Lifting.map\<^sub>T}, lift_type (type_of map_term))
                      <$> lift_term bound_types f
                      <$> lift_term bound_types ls
                    )
                    else NONE
              | map_term =>
                  if Term.aconv_untyped (map_term, @{term map})
                    then raise TERM("outstanding map", [])
                    else NONE;
            
            fun check_fold tm =
              case tm of
                fold_term $ f $ ls $ init =>
                  if Term.aconv_untyped (fold_term, @{term fold})
                    then SOME (
                      Const (@{const_name DP_Lifting.fold\<^sub>T}, lift_type (type_of fold_term))
                      <$> lift_term bound_types f
                      <$> lift_term bound_types ls
                      <$> lift_term bound_types init
                    )
                    else NONE
              | fold_term =>
                  if Term.aconv_untyped (fold_term, @{term fold})
                    then raise TERM("outstanding map", [])
                    else NONE;
            
            fun check_pure tm =
              if exists_subterm (fn x => x aconv func_head) tm
                then NONE
                else SOME (lift_pure_term bound_types tm);

            fun check_If tm =
              case tm of
                If_term $ cond $ true_clause $ false_clause =>
                  if Term.aconv_untyped (If_term, @{term If})
                    then SOME (
                      Const (@{const_name DP_Lifting.If\<^sub>T}, lift_type (type_of If_term))
                      <$> lift_term bound_types cond
                      <$> lift_term bound_types true_clause
                      <$> lift_term bound_types false_clause
                    )
                    else NONE
              | If_term =>
                  if Term.aconv_untyped (If_term, @{term If})
                    then raise TERM("outstanding If", [])
                    else NONE;
    
            fun check_case_prod tm =
              case tm of
                case_prod_term $ if_prod $ prod_term =>
                  if Term.aconv_untyped (case_prod_term, @{term case_prod})
                    then SOME (
                      Const (@{const_name DP_Lifting.case_prod\<^sub>T}, lift_type (type_of case_prod_term))
                      <$> lift_term bound_types if_prod
                      <$> lift_term bound_types prod_term
                    )
                    else NONE
              | case_prod_term =>
                  if Term.aconv_untyped (case_prod_term, @{term case_prod})
                    then raise TERM("outstanding case_prod", [case_prod_term])
                    else NONE;

            fun check_case_option tm =
              case tm of
                case_option_term $ if_none $ if_some =>
                  if Term.aconv_untyped (case_option_term, @{term case_option})
                    then SOME (
                      Const (@{const_name DP_Lifting.case_option\<^sub>T}, lift_type (type_of case_option_term))
                      <$> lift_term bound_types if_none
                      <$> lift_term bound_types if_some
                    )
                    else NONE
              | case_option_term =>
                if Term.aconv_untyped (case_option_term, @{term case_option})
                  then raise TERM("outstanding case_option", [case_option_term])
                  else NONE;
    
            fun check_func tm =
              case tm of
                f $ x => if f aconv local_func_head then SOME (funcT_head $ x) else NONE
              | _ => if tm aconv local_func_head then SOME (return tm) else
                      if tm aconv func_head then raise TERM("incomplete function context", [tm]) else NONE;
    
            fun check_fallback tm =
              case tm of
                Abs (abs_name, abs_tp, abs_body) =>
                  let
                    val abs_tp_lifted = lift_type' abs_tp
                  in
                    SOME (return (Term.abs (abs_name, abs_tp_lifted)
                      (lift_term (abs_tp_lifted::bound_types) abs_body)))
                  end
              | f $ x =>
                SOME (lift_term bound_types f <$> lift_term bound_types x)
              | _ => NONE;
    
            val checks = [
              check_map,
              check_fold,
              check_pure,
              check_If,
              check_case_prod,
              check_case_option,
              check_func,
              check_fallback
            ];
          in
            get_first (fn check => check tm) checks |> the
          end;
        fun add_checkmem tm = term_checkmem $ param $ tm;
      in
        HOLogic.mk_eq (funcT_head $ param, lift_term [] rhs |> add_checkmem) |> HOLogic.mk_Trueprop
      end;

    val func_fixes = [(funcT_binding, SOME (type_of funcT_head), NoSyn)];
    val func_specs = map (fn simp => (((Binding.empty, []), transform_simp simp), [], [])) (#simps func_info |> the);

    fun transform_totality ctxt (info0: Function.info) (info1: Function.info) =
      let
        val def0 = Inductive.the_inductive ctxt (#R info0) |> snd |> #eqs;
        val def1 = Inductive.the_inductive ctxt (#R info1) |> snd |> #eqs;
        val totality0 = info0 |> #totality |> the;
        val totality1 = totality0
          |> Local_Defs.unfold ctxt def0
          |> Local_Defs.fold ctxt def1
      in
(*        HEADGOAL (resolve_tac ctxt [totality1])*)
        totality1
      end;

    fun transform_totality_tac info0 info1 ctxt = HEADGOAL (resolve_tac ctxt [transform_totality ctxt info0 info1]);

    val default_termination_prover_tac = Function_Common.termination_prover_tac false;

    fun termination_prover_tac info0 info1 ctxt =
      transform_totality_tac info0 info1 ctxt ORELSE default_termination_prover_tac ctxt;

    fun pat_completeness_auto ctxt =
      Pat_Completeness.pat_completeness_tac ctxt 1
      THEN auto_tac ctxt

  in
    let
      val (info1, ctxt1) = Function.add_function func_fixes func_specs Function_Fun.fun_config pat_completeness_auto ctxt;
      val totality1 = transform_totality ctxt1 func_info info1;
      val (info1, ctxt2) = Function.prove_termination NONE (termination_prover_tac func_info info1 ctxt1) ctxt1;
      

      val induct_for_transfer = let
        val eq_rel_tp = (ran_type --> ran_type --> HOLogic.boolT);
        val eq_rel_lifted_tp = (ran_type --> ran_type_lifted --> HOLogic.boolT);
        
        val crel_vs_eq = term_crel_vs $ HOLogic.eq_const ran_type;
        
        fun mk_rel_fun_tp ((tp_a, tp_b), (tp_c, tp_d)) =
          (tp_a --> tp_b --> HOLogic.boolT) --> (tp_c --> tp_d --> HOLogic.boolT) -->
          (tp_a --> tp_c) --> (tp_b --> tp_d) --> HOLogic.boolT;
        
        fun mk_rel_fun_tm tps = Const (@{const_name rel_fun}, mk_rel_fun_tp tps)
        
        fun mk_rel_prod_tp ((tp_a, tp_b), (tp_c, tp_d)) =
          (tp_a --> tp_b --> HOLogic.boolT) --> (tp_c --> tp_d --> HOLogic.boolT) -->
          HOLogic.mk_prodT (tp_a, tp_c) --> HOLogic.mk_prodT (tp_b, tp_d) --> HOLogic.boolT;
        
        fun mk_rel_prod_tm tps = Const (@{const_name rel_prod}, mk_rel_prod_tp tps);

        fun mk_optionT tp = Type (@{type_name option}, [tp]);

        fun mk_rel_option_tp (tp_a, tp_b) =
          (tp_a --> tp_b --> HOLogic.boolT) -->
          mk_optionT tp_a --> mk_optionT tp_b --> HOLogic.boolT; 
        
        fun mk_rel_option_tm tps = Const (@{const_name rel_option}, mk_rel_option_tp tps);
        
        fun mk_K1 tp tm =
          Const (@{const_name K}, tp --> tp --> tp --> HOLogic.boolT)
          $ tm;
        
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
            (Term.abs ("param", dom_type) (crel_vs_eq $ (local_func_head $ Bound 0) $ (funcT_head $ Bound 0))) $ arg |> HOLogic.mk_Trueprop
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
                  arg_to_rel (tm as (Bound b)) =
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
                 | arg_to_rel (tm as (Const (@{const_name Some}, _)) $ s) =
                  let
                    val tp = Term.type_of1 (bound_types, tm)
                    val Type (@{type_name option}, [tp0]) = tp;
                  in
                    mk_rel_option_tm (tp0, tp0) $ (arg_to_rel s)
                  end
                | arg_to_rel tm = mk_K1 (Term.type_of1 (bound_types, tm)) tm
(*                | arg_to_rel tm = raise TERM("unsupported", tm |> Term.strip_comb |> snd);*)
        val _ = @{print} arg;
                val arg_rel = arg_to_rel arg;
                val arg_tp = Term.type_of1 (bound_types, arg);
                val rel_fun = mk_rel_fun_tm ((arg_tp, arg_tp), (ran_type, ran_type_lifted)) $ arg_rel $ crel_vs_eq;
        
                val IH2' = rel_fun $ local_func_head $ funcT_head;
              in
                IH2' |> HOLogic.mk_Trueprop
              end;
            
            val IH2s' = map transform_IH2 IH2s;
            val param_Ks = map_index (fn (i, (_, tp)) => mk_K1 tp (Bound i) $ (Bound i) $ (Bound i) |> HOLogic.mk_Trueprop) params;
            val IH' = Logic.list_all (params, Logic.list_implies (param_Ks @ IH2s', replace_P IH_concl));
          in
            IH'
          end;
        
        fun transform_induct_tac induct0 ctxt =
          HEADGOAL (
            resolve_tac ctxt [induct0]
            THEN_ALL_NEW (fn i => Subgoal.FOCUS (fn {context=ctx, prems=IH, ...} =>
              HEADGOAL (resolve_tac ctx [nth IH (i-1)])) ctxt i)
            THEN_ALL_NEW (
              resolve_tac ctxt @{thms K_self}
              ORELSE' (resolve_tac ctxt @{thms rel_funI}
                THEN' (eresolve_tac ctxt @{thms rel_prod.induct} ORELSE' (K all_tac))
                THEN' (SELECT_GOAL (unfold_tac ctxt @{thms K_def eq_onp_def}))
                THEN' clarsimp_tac ctxt)));
        
        fun transform_induct ctxt =
          let
            val induct_thm = (info1 |> #inducts |> the |> hd);
            val quantified = induct_thm |> Thm.prop_of |> Term.close_schematic_term |> all_abs;    
            val (params, IHs, concl) = strip_prop quantified;
        
            val IHs' = map transform_IH IHs;
            val induct_prop' = Logic.list_all (params, Logic.list_implies (IHs', replace_P concl));
          in
            Goal.prove ctxt [] [] induct_prop' (fn {context=ctxt, ...} => transform_induct_tac induct_thm ctxt)
          end;
      in
        transform_induct ctxt2
      end;
      
      val (_, ctxt3) = Local_Theory.note ((Binding.qualify_name true (#defname info1) "crel_vs_induct", []), [induct_for_transfer]) ctxt2;
      
    in
      @{print} induct_for_transfer; ctxt3
    end
  end;