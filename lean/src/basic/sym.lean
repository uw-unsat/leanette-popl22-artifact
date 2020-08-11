import ..cs.sym
import ..tactic.all
import ..cs.lib
import .basic

open sym

section choices

variables 
  {Model SymB SymV D : Type}
  {ev : has_eval Model SymB SymV D}

lemma choices.lone_implies_one_or_none {gvs : choices SymB SymV} {m : Model} 
  (h : choices.lone ev m gvs) : (choices.none ev m gvs ∨ choices.one ev m gvs) := 
begin 
  simp only [choices.none, choices.one],
  simp only [choices.lone] at h,
  omega,
end 

lemma choices.none_iff_none_true {gvs : choices SymB SymV} {m : Model} :
  gvs.none ev m ↔ ∀ (i : ℕ) (hi : i < gvs.length), ¬ ev.evalB m (gvs.nth_le i hi).guard :=
begin 
  split_c,
  case mp {
    intros h_none i hi,
    simp only [choices.none, choices.true, list.length_eq_zero, list.filter_eq_nil] at h_none, 
    apply h_none (list.nth_le gvs i hi).guard,
    simp only [list.mem_map],
    use (list.nth_le gvs i hi),
    simp [list.mem_iff_nth_le, choice.guard],
    use [i, hi],
  },
  case mpr {
    intro h_none,
    simp only [choices.none, choices.true, list.length_eq_zero, list.filter_eq_nil], 
    intros g h_mem,
    simp [list.mem_iff_nth_le] at h_mem,
    rcases h_mem with ⟨i, hi, h_mem⟩,
    subst_vars,
    apply h_none,
  },
end

lemma choices.none_implies_none_true {gvs : choices SymB SymV} {m : Model} 
   (h : gvs.none ev m) (i : ℕ) (hi : i < gvs.length) :
   ¬ ev.evalB m (gvs.nth_le i hi).guard :=
begin 
  revert i,
  simpa only [← choices.none_iff_none_true],
end

lemma choices.none_implies_lone {gvs : choices SymB SymV} {m : Model} 
  (h : gvs.none ev m) : gvs.lone ev m := 
begin 
  simp only [choices.lone, choices.true], 
  simp only [choices.none, choices.true] at h, 
  linarith,
end 

lemma choices.one_implies_lone {gvs : choices SymB SymV} {m : Model} 
  (h : gvs.one ev m) : gvs.lone ev m := 
begin 
  simp only [choices.lone, choices.true], 
  simp only [choices.one, choices.true] at h, 
  linarith,
end 

lemma choices.eval_skips_false {gvs gvs' : choices SymB SymV} {m : Model} {default : D}
  (h : gvs.none ev m) : (gvs ++ gvs').eval ev m default = gvs'.eval ev m default :=
begin
  simp only [choices.none_iff_none_true] at h,
  induction gvs with hd tl ih,
  case nil { simp },
  case cons {
    cases hd with g v,
    simp only [choices.eval, list.cons_append],
    split_ifs with h_if,
    case_c {
      specialize h 0 (by simp),
      simp only [list.nth_le] at h,
      contra [h] at h_if,
    },
    case_c {
      apply ih,
      intros i hi,
      exact h (i + 1) (by simpa),
    },
  },
end

lemma choices.none_append {gvs gvs' : choices SymB SymV} {m : Model} : 
  (gvs.none ev m ∧ gvs'.none ev m) ↔ (gvs ++ gvs').none ev m := 
begin 
  split_c,
  case mp {
    rintro ⟨h_gvs, h_gvs'⟩,
    simp only [choices.none_iff_none_true] at ⊢ h_gvs h_gvs',
    intros i hi,
    by_cases_c h : i < gvs.length,
    case pos {
      rw list.nth_le_append _ h,
      apply h_gvs,
    },
    case neg {
      rw list.nth_le_append_right,
      case_b { linarith },
      case_c { apply h_gvs' },
    },
  },
  case mpr {
    intro h,
    simp only [choices.none_iff_none_true] at h ⊢,
    split_c,
    case left {
      intros i hi,
      specialize h i (by {
        simp only [list.length_append], 
        linarith,
      }),
      rw list.nth_le_append _ hi at h,
      assumption,
    },
    case right {
      intros i hi,
      specialize h (gvs.length + i) (by simpa),
      rw list.nth_le_append_right at h,
      case_b { linarith },
      case_c { simp only [nat.add_sub_cancel_left] at h, assumption },
    },
  },
end 

lemma choices.none_evals_none {gvs : choices SymB SymV} {m : Model} {default : D}
  (h : gvs.none ev m) : gvs.eval ev m default = default := 
begin 
  rewrite (by simp : gvs = gvs ++ []),
  rw choices.eval_skips_false,
  case_c { simp [choices.eval] },
  case_c { assumption },
end 

lemma choices.not_none_implies_not_none {gvs : choices SymB SymV} {m : Model} {default : D}
  (h : gvs.eval ev m default ≠ default) : ¬gvs.none ev m := 
begin 
  intro h',
  rw choices.none_evals_none h' at h,
  contradiction,
end 

-- we can use choices.filter_one_rest here, but well, I already got a proof
lemma choices.one_implies_one_true {gvs : choices SymB SymV} {m : Model} 
  (h : gvs.one ev m) : 
  ∃ (pre post : choices SymB SymV) (g : SymB) (v : SymV), 
    gvs = pre ++ ([⟨g, v⟩] ++ post) ∧ pre.none ev m ∧ post.none ev m ∧ ev.evalB m g :=
begin 
  simp only [choices.one_iff_filter] at h,
  rcases h with ⟨i, hi, h_one⟩, 
  have h_part := list.take_append_drop i gvs,
  simp [list.drop_eq_nth_le_cons hi] at h_part,
  cases list.nth_le gvs i hi with g v,
  use [gvs.take i, gvs.drop (i + 1), g, v],
  have h_true : ev.evalB m (choice.mk g v).guard = tt := by {
    apply choices.filter_one_guard,
    assumption,
  },
  rw ← h_part at h_one,
  simp only [list.filter, h_true, list.filter_append, if_true, coe_sort_tt] at h_one,
  replace h_one := list.append_eq_singleton_implies_other_eq_nil h_one,
  cases h_one with h_one_left h_one_right,
  split_c,
  case left { simp [h_part] },
  case right left { 
    apply_fun list.length at h_one_left,
    simpa [choices.none, choices.true, list.map_filter],
  },
  case right right left {
    apply_fun list.length at h_one_right,
    simpa [choices.none, choices.true, list.map_filter],
  },
  case right right right { simpa },
end

end choices