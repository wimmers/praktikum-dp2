fun state_type M a = Type (@{type_name "Monad.state"}, [M, a]);

(* TODO: quadratic -> linear *)
fun return bound_types tm =
  let
    val tp = type_of1 (bound_types, tm);
  in
    Const (@{const_name "Monad.return"}, tp --> state_type mem_type tp) $ tm
  end;

fun
  lift_type tp = state_type mem_type (lift_type' tp)
and
  lift_type' (Type ("fun", [dom, ran])) = (lift_type' dom) --> (lift_type ran)
| lift_type' tp = tp

fun
  lift_pure_term bound_types tm = return bound_types (lift_pure_term' bound_types tm)
and
  lift_pure_term' bound_types tm =
    (case (type_of1 (bound_types, tm)) of
      (Type ("fun", [dom, ran])) =>
        (case dom of
          (Type ("fun", _)) => raise TYPE("High order domain type", [dom], [tm])
        | _ => Term.abs (Name.uu, dom) (lift_pure_term (dom::bound_types) (incr_boundvars 1 tm $ Bound 0)))
     | _ => tm);

fun extract_lhs (lhs: term) =
  let
    val (func, all_param) = strip_comb lhs;
    val param :: rev_context = rev all_param;
    val context = rev rev_context;
  in
    (func, context, param)
  end;

fun transform simp_thm =
  let
    val (lhs, rhs) = Thm.full_prop_of simp_thm |> HOLogic.dest_Trueprop |> HOLogic.dest_eq;
    val (func, func_context, param) = extract_lhs lhs;

    val dom_type = type_of param;
    val ran_type = type_of rhs;

    fun lift_term bound_types tm =
      let
        fun check_pure bound_types tm =
          if exists_subterm (curry aconv func)
            then NONE
            else SOME lift_pure_term bound_types tm;

        fun check_If bound_types tm =
          (case tm of
            (If_term $ cond $ true_clause $ false_clause) =>
              if If_term aconv_untyped @{term HOL.If}
                then (Const @{const_name DP_Lifting.If\<^sub>T}
  in
    lift_term rhs
  end;
