import ..tactic.all
open tactic.interactive

setup_tactic_parser

@[interactive] meta def cases_on_interp 
  (h : parse ident)
  (_x : parse (parser.tk ":"))
  (e : parse types.texpr)
  (ids : parse $ (tk ":" *> ident_*)?) : tactic unit := 
do
  tactic.interactive.cases_all h _x e [],
  case [([`none], none)] `[contradiction],
  tactic.interactive.focus_case [([`some], ids)] skip,
  return ()