fun get_rest prefix l =
  let
    val (l_prefix, l_postfix) = chop (length prefix) l
  in
    if length prefix <= length l andalso l_prefix = prefix then SOME l_postfix else NONE
  end;

infix 9 <$>;

fun state_type M a = Type (@{type_name Monad.state}, [M, a]);

fun extract_lhs (lhs: term) =
  let
    val (func, all_param) = strip_comb lhs;
    val (context, param) = split_last all_param;
  in
    (func, context, param)
  end;

fun transform simp_thm =
  let
    val (lhs, rhs) = Thm.full_prop_of simp_thm |> HOLogic.dest_Trueprop |> HOLogic.dest_eq;
    val (func, func_context, param) = extract_lhs lhs;

    val dom_type = type_of param;
    val ran_type = type_of rhs;
    val mem_type = dom_type --> Type (@{type_name "Option.option"}, [ran_type]);

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
    

    fun lift_term bound_types tm =
      let
        val return = return1 bound_types;
        val op <$> = app_lifted1 bound_types;
        
        fun check_pure tm =
          if exists_subterm (fn x => x aconv func) tm
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
          let
            val (func_term, func_args) = strip_comb tm;
          in
            if func aconv func_term
              then
                case get_rest func_context func_args of
                  SOME [] => SOME (return tm)
                | SOME [_] => SOME tm
                | SOME _ => raise TERM("internal error, multiple param", [tm])
                | NONE => raise TERM("incomplete function context", [tm])
              else NONE
          end

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
    lift_term [] rhs
  end;
