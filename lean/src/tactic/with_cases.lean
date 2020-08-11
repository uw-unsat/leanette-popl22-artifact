import tactic.basic

open tactic.interactive

@[interactive] meta def constructor_c := `[with_cases { constructor }]
@[interactive] meta def split_c := `[with_cases { repeat { split } }]
@[interactive] meta def apply_c := with_cases ∘ apply
@[interactive] meta def by_cases_c := with_cases ∘ by_cases
