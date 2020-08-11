import tactic.basic

open tactic.interactive

setup_tactic_parser

/-
 `contra` is like `contradiction`, but it will `simp` a specified 
 hypothesis first (potentially with helping lemmas)
 -/

@[interactive] meta def contra
  (hs : parse tactic.simp_arg_list) (attr_names : parse with_ident_list) (locat : parse location) : tactic unit :=
do simp none none ff hs attr_names locat,
   `[contradiction]