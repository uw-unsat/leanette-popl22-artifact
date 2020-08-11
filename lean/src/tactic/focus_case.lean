import tactic.basic

open tactic.interactive
open tactic.interactive.case_tag.match_result

setup_tactic_parser

-- The case tactic is taken from https://github.com/leanprover-community/lean/pull/508

private meta def goals_with_matching_tag (ns : list name) :
  tactic (list (expr × case_tag) × list (expr × case_tag)) :=
do gs ← tactic.get_goals,
   (gs : list (expr × tactic.tag)) ←
     gs.mmap (λ g, do t ← tactic.get_tag g, pure (g, t)),
   pure $ gs.foldr
     (λ ⟨g, t⟩ ⟨exact_matches, suffix_matches⟩,
       match case_tag.parse t with
       | none := ⟨exact_matches, suffix_matches⟩
       | some t :=
         match case_tag.match_tag ns t with
         | exact_match := ⟨⟨g, t⟩ :: exact_matches, suffix_matches⟩
         | fuzzy_match := ⟨exact_matches, ⟨g, t⟩ :: suffix_matches⟩
         | no_match := ⟨exact_matches, suffix_matches⟩
         end
       end)
     ([], [])

private meta def goal_with_matching_tag (ns : list name) :
  tactic (expr × case_tag) :=
do ⟨exact_matches, suffix_matches⟩ ← goals_with_matching_tag ns,
   match exact_matches, suffix_matches with
   | [] , []  := tactic.fail format!
     "Invalid `case`: there is no goal tagged with suffix {ns}."
   | [] , [g] := pure g
   | [] , _   :=
     let tags : list (list name) :=
       suffix_matches.map (λ ⟨_, t⟩, t.case_names.reverse) in
     tactic.fail format!
     "Invalid `case`: there is more than one goal tagged with suffix {ns}.\nMatching tags: {tags}"
   | [g], _   := pure g
   | _  , _   := tactic.fail format!
     "Invalid `case`: there is more than one goal tagged with tag {ns}."
   end

meta def case_core (args : parse case_parser) (tac : itactic) : 
tactic (list expr × list expr) :=
do
  original_goals ← tactic.get_goals,
  target_goals ← args.mmap (λ ⟨ns, ids⟩, do
    ⟨goal, tag⟩ ← goal_with_matching_tag ns,
    let ids := ids.get_or_else [],
    let num_ids := ids.length,
    goals ← tactic.get_goals,
    let other_goals := goals.filter (≠ goal),
    tactic.set_goals [goal],
    match tag with
    | (case_tag.pi _ num_args) := do
      tactic.intro_lst ids,
      when (num_ids < num_args) $ tactic.intron (num_args - num_ids)
    | (case_tag.hyps _ new_hyp_names) := do
        let num_new_hyps := new_hyp_names.length,
        when (num_ids > num_new_hyps) $ tactic.fail format!
          ("Invalid `case`: You gave {num_ids} names, but the case introduces " ++
          "{num_new_hyps} new hypotheses."),
        let renamings := native.rb_map.of_list (new_hyp_names.zip ids),
        propagate_tags $ tactic.rename_many renamings tt tt
    end,
    goals ← tactic.get_goals,
    tactic.set_goals other_goals,
    match goals with
    | [g] := return g
    | _ := tactic.fail "Unexpected goals introduced by renaming"
    end),
  remaining_goals ← tactic.get_goals,
  tactic.set_goals target_goals,
  tac,
  unsolved_goals ← tactic.get_goals,
  tactic.set_goals original_goals,
  return (unsolved_goals, remaining_goals)

@[interactive] 
meta def focus_case (args : parse case_parser) (tac : itactic) : tactic unit :=
do (unsolved_goals, remaining_goals) ← case_core args tac,
   tactic.set_goals (unsolved_goals ++ remaining_goals)
