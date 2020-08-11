import tactic.basic

open tactic.interactive

setup_tactic_parser

/-
 - `case_c`, `case_f`, and `case_b` act like `case`
 - even when goals are not tagged.
 - `case_c` (c for current) focuses the current subgoal
 - `case_f` (f for forward) focuses the next subgoal
 - `case_b` (b for backward) focuses the previous (last) subgoal
 -/

-- current case
@[interactive] meta def case_c (_ : parse ident?) := focus ∘ solve1

-- forward case
@[interactive] meta def case_f
  (_ : parse ident?)
  (tac : itactic) : tactic unit :=
do swap 2,
   focus $ solve1 tac

-- backward case
@[interactive] meta def case_b
  (_ : parse ident?)
  (tac : itactic) : tactic unit :=
do gs ← tactic.get_goals,
   swap gs.length,
   focus $ solve1 tac
