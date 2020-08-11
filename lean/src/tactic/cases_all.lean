import tactic.basic
import tactic.induction
import .base

open tactic.interactive

setup_tactic_parser

/--
`cases_all h : e` is equivalent to `cases h : e; rewrite h at *`. 
That is, it performs a case analysis on an expression and use the result 
uniformly throughout the context and goal.
-/
@[interactive] meta def cases_all 
  (h : parse ident)
  (_x : parse (parser.tk ":"))
  (e : parse types.texpr)
  (with_ids : parse with_ident_list) := 
tactic.seq' 
  (cases (h, e) with_ids)
  (do 
    e_h ← tactic.get_local h,
    tactic.interactive.rewrite 
      (tactic.interactive.rw_rules_t.mk 
        [(tactic.interactive.rw_rule.mk 
          dummy_loc ff (pexpr.of_expr e_h))]
        none) 
        interactive.loc.wildcard)
