theory Scratch_Tactic_Antiquotation
  imports Main
begin
ML \<open>
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

fun foc_tac {prems, params, asms, concl, context, schematics} =
    let
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
        ("schematics: ", assgn2 (pretty_cterm context) (snd schematics))]
    in
      tracing (Pretty.string_of (Pretty.chunks pps)); all_tac
    end
\<close>
  schematic_goal shows "\<And>x y. A x y \<Longrightarrow> B y x \<Longrightarrow> C (?z y) x"
apply(tactic {* Subgoal.FOCUS foc_tac @{context} 1 *})
end