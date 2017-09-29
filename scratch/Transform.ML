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

fun lift_fun term_opt ctxt =
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
            | _ => Term.abs (Name.uu, dom) (lift_pure_term (dom::bound_types) (incr_boundvars 1 tm $ Bound 0)))
         | _ => tm);

    val funcT_head = Free (funcT_name, dom_type --> lift_type ran_type);

    fun transform_simp simp_thm =
      let
        val (lhs, rhs0) = Thm.full_prop_of simp_thm |> HOLogic.dest_Trueprop |> HOLogic.dest_eq;
        val rhs = subst_var_free rhs0;
    
        val (func_head, func_context, param0) = extract_lhs lhs;
        val param = subst_var_free param0;
    
        fun lift_term bound_types tm =
          let
            val return = return1 bound_types;
            val op <$> = app_lifted1 bound_types;
            
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
                    then raise TERM("outstanding case_prod", [])
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
                    val abs_tp_lifted = lift_type abs_tp
                  in
                    SOME (return (Term.abs (abs_name, abs_tp_lifted)
                      (lift_term (abs_tp_lifted::bound_types) abs_body)))
                  end
              | f $ x =>
                SOME (lift_term bound_types f <$> lift_term bound_types x)
              | _ => NONE;
    
            val checks = [
              check_pure,
              check_If,
              check_case_prod,
              check_func,
              check_fallback
            ];
          in
            get_first (fn check => check tm) checks |> the
          end;
      in
        HOLogic.mk_eq (funcT_head $ param, lift_term [] rhs) |> HOLogic.mk_Trueprop
      end;

    val func_fixes = [(funcT_binding, SOME (type_of funcT_head), NoSyn)];
    val func_specs = map (fn simp => (((Binding.empty, []), transform_simp simp), [], [])) (#simps func_info |> the);
  in
    Function_Fun.add_fun func_fixes func_specs Function_Common.default_config
  end;