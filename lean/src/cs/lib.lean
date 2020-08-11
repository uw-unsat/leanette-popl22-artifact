import tactic.basic
import tactic.omega
import tactic.apply_fun
import data.option.basic
import .util
import .lang
import .sym
import .svm

namespace sym

--- The following lemmas depend on (has_eval Model SymB SymV SymR). -- 

section eval_generic

  variables 
    {Model SymB SymV SymR : Type} 
    (ev : has_eval Model SymB SymV SymR)
    {m : Model}

  lemma choices.one_of_ite {α} {b b' : SymB} {a1 a2 : α} : 
  ev.evalB m b' = ¬ ev.evalB m b → choices.one ev m [⟨b, a1⟩, ⟨b', a2⟩] := 
  begin 
    simp only [choices.one, choices.true, list.filter, list.map], 
    intro hb,
    split_ifs,
    any_goals { simp only [list.length_singleton], },
    { simp only [h, to_bool_false_eq_ff, not_true] at hb,  
      rewrite ←bool_iff_false at hb,
      contradiction, },   
    { simp only [h, to_bool_true_eq_tt, not_false_iff] at hb,
      rewrite bool.tt_eq_true at hb, 
      contradiction, },
  end

  lemma choices.eq_one {α β} {gvs : choices SymB α} {gws : choices SymB β} : 
  gvs.map choice.guard = gws.map choice.guard → gvs.one ev m → gws.one ev m := 
  begin
    intros heq,
    simp only [choices.one, choices.true, heq, imp_self], 
  end

  lemma choices.not_some_is_none {α} {gvs : choices SymB α} :
  ¬ (gvs.any (λ gv, ev.evalB m gv.guard)) → gvs.none ev m := 
  begin
    intro h,
    simp only [choices.none, choices.true, list.length_eq_zero, list.filter_eq_nil],
    intros g hg, 
    simp only [list.any_iff_exists, not_exists, exists_prop, eq_ff_eq_not_eq_tt, not_and] at h,
    simp only [list.mem_map] at hg,
    rcases hg with ⟨gv, hgv, hgg⟩,
    specialize h gv hgv, 
    simp only [hgg] at h,
    simp only [h, not_false_iff, coe_sort_ff], 
  end 

  lemma choices.some_ge_one {α} {gvs : choices SymB α} : 
  (gvs.any (λ gv, ev.evalB m gv.guard)) → 
  (gvs.true ev m).length ≥ 1 := 
  begin 
    simp only [choices.true, ge_iff_le],
    intro hsm,
    induction gvs,
    { simp only [list.any_nil, coe_sort_ff] at hsm, 
      contradiction, },
    { simp only [list.map, list.filter],
      split_ifs,
      { simp only [list.length, zero_le, le_add_iff_nonneg_left], },
      { apply gvs_ih, 
        simp only [h, bor_coe_iff, false_or, list.any_cons] at hsm,
        exact hsm, } } 
  end 

  lemma choices.lone_some_one {α} {gvs : choices SymB α} : 
  gvs.lone ev m → (gvs.any (λ gv, ev.evalB m gv.guard)) → 
  gvs.one ev m := 
  begin 
    simp only [choices.lone, choices.one],
    intros hln hsm,
    rcases (choices.some_ge_one ev hsm) with hge,
    omega, 
  end 

  lemma choices.one_implies_filter {gvs : choices SymB SymV} : 
  gvs.one ev m → 
  ∃ (i : ℕ) (hi : i < gvs.length), gvs.filter (λ gv, ev.evalB m gv.guard) = [gvs.nth_le i hi] := 
  begin 
    simp only [choices.one, choices.true], 
    intro h,
    induction gvs, 
    { simp only [list.filter_nil, list.length, nat.zero_ne_one, list.map] at h, contradiction,  }, 
    { simp only [list.filter, list.map] at h,
      split_ifs at h,
      { apply exists.intro 0,
        have hi :  0 < (gvs_hd :: gvs_tl).length := by { simp only [nat.succ_pos', list.length], },
        apply exists.intro hi,
        simp only [list.filter, h_1, true_and, if_true, list.nth_le, eq_self_iff_true],
        simp only [add_left_eq_self, list.length] at h, 
        rewrite ←list.length_eq_zero,
        rcases (@list.filter_map_length_eq (choice SymB SymV) SymB gvs_tl choice.guard (λ (g : SymB), ↥(ev.evalB m g)) _) with heq,
        rewrite heq at h, simp only at h, exact h, }, 
      { simp only [h, eq_self_iff_true, forall_true_left] at gvs_ih, 
        rcases gvs_ih with ⟨i, hi, ih⟩,
        apply exists.intro (i+1),
        have hi' : i + 1 < (gvs_hd :: gvs_tl).length := by { simp only [hi, list.length, add_lt_add_iff_right], },
        apply exists.intro hi',
        simp only [list.nth_le, list.filter, h_1, if_false],
        apply ih, } } 
  end

  lemma choices.filter_implies_one {gvs : choices SymB SymV} : 
  (∃ (i : ℕ) (hi : i < gvs.length), gvs.filter (λ gv, ev.evalB m gv.guard) = [gvs.nth_le i hi]) → 
  gvs.one ev m := 
  begin 
    simp only [choices.one, choices.true], 
    intro h,
    rcases (@list.map_filter SymB (choice SymB SymV) (λ b, ev.evalB m b) _ choice.guard gvs) with hmf,
    rcases h with ⟨i, hi, h⟩, 
    apply_fun (list.map choice.guard) at h,
    simp only [list.map] at h,
    rewrite hmf,
    simp only [h, list.length_singleton], 
  end 

  lemma choices.one_iff_filter {gvs : choices SymB SymV} : 
  gvs.one ev m ↔  
  ∃ (i : ℕ) (hi : i < gvs.length), 
    gvs.filter (λ gv, ev.evalB m gv.guard) = [gvs.nth_le i hi] := 
  begin 
    constructor, apply choices.one_implies_filter, apply choices.filter_implies_one,
  end 

  lemma choices.eval_filter {gvs : choices SymB SymV} {default : SymR} : 
  choices.eval ev m default gvs  = choices.eval ev m default (list.filter (λ (gv : choice SymB SymV), ev.evalB m gv.guard) gvs)  := 
  begin
    induction gvs,
    { simp only [list.filter_nil], },
    { cases gvs_hd, 
      simp only [choices.eval],
      split_ifs,
      { simp only [list.filter, h, choices.eval, if_true], },
      { simp only [list.filter, h, gvs_ih, if_false], } } 
  end 

  lemma choices.filter_one_guard {gvs : choices SymB SymV} {gv : choice SymB SymV} : 
  gvs.filter (λ gv, ev.evalB m gv.guard) = [gv] → ev.evalB m gv.guard := 
  begin 
    intro h,
    have hgv : gv ∈ [gv] := by { simp only [list.mem_singleton], },
    rewrite ←h at hgv,
    simp only [list.mem_filter] at hgv,
    simp only [hgv], 
  end 

  lemma choices.filter_one_eval {gvs : choices SymB SymV} {gv : choice SymB SymV} (default : SymR) : 
  gvs.filter (λ gv, ev.evalB m gv.guard) = [gv] → 
  choices.eval ev m default gvs = ev.evalV m gv.value := 
  begin 
    intro h,
    rcases (choices.filter_one_guard ev h) with hg,
    rewrite [choices.eval_filter, h],
    cases gv,
    simp only [choices.eval, hg, if_true],
  end 

  lemma choices.filter_one_rest {gvs : choices SymB SymV} {i j : ℕ} 
  (hi : i < gvs.length) (hj : j < gvs.length) :
  gvs.filter (λ gv, ev.evalB m gv.guard) = [gvs.nth_le i hi] → i ≠ j → 
  ¬ ev.evalB m (gvs.nth_le j hj).guard := 
  begin
    intros hu hij,
    by_contradiction,
    rcases (choices.filter_one_guard ev hu) with hg,
    rcases (@list.filter_length_gt_one (choice SymB SymV) gvs i j ((λ (g : choice SymB SymV), ↥(ev.evalB m g.guard))) _ hi hj hij ) with hlen,
    simp only [h, hu, hg, lt_self_iff_false, gt_iff_lt, list.length_singleton, forall_true_left] at hlen,
    contradiction, 
  end 

  lemma state.eqv_legal {σ σ' : state SymB} : 
  σ.legal ev m → σ.eqv ev m σ' → σ'.legal ev m := 
  begin
    simp only [state.legal, state.eqv, and_imp, bor_coe_iff, bool.to_bool_coe, bool.to_bool_or],
    finish, 
  end 

  lemma state.eqv_normal {σ σ' : state SymB} : 
  σ.normal ev m → state.eqv ev m σ σ' → σ'.normal ev m := 
  begin 
    simp only [state.eqv, state.normal, and_imp, eq_ff_eq_not_eq_tt, not_and, bool.to_bool_and, bool.to_bool_coe, band_coe_iff],
    intros h1 h2 h3 h4,
    simp only [h3, h4] at h1 h2,
    simp only [h1, h2, and_self],
  end 

  lemma state.eqv_abnormal {σ σ' : state SymB} : 
  ¬ σ.normal ev m → state.eqv ev m σ σ' → ¬ σ'.normal ev m := 
  begin 
    simp only [state.eqv, state.normal, and_imp, eq_ff_eq_not_eq_tt, not_and, bool.to_bool_and, bool.to_bool_coe, band_coe_iff],
    intros h1 h2 h3 h4,
    rewrite ←h3, apply h1, rewrite h2, exact h4, 
  end 

  lemma state.eqv_aborted {σ σ' : state SymB} : 
  state.eqv ev m σ σ' → σ.aborted ev m = σ'.aborted ev m := 
  begin
    simp only [state.eqv, state.aborted],
    rintro ⟨h1, h2⟩,
    simp [h1, h2]
  end 

  lemma state.errored_not_aborted {σ : state SymB} : 
  σ.errored ev m → (σ.aborted ev m) = ff := 
  begin 
    simp only [state.errored, state.aborted, and_imp, eq_ff_eq_not_eq_tt, not_and, bool.of_to_bool_iff, to_bool_ff_iff],
    intros, assumption, 
  end 

  lemma state.errored_not_normal {σ : state SymB} : 
  σ.errored ev m → (σ.normal ev m) = ff := 
  begin 
    simp only [state.errored, state.normal, and_imp, eq_ff_eq_not_eq_tt, bool.of_to_bool_iff, to_bool_ff_iff, bool.to_bool_and, band_eq_false_eq_eq_ff_or_eq_ff],
    intros h1 h2, simp only [h2, eq_self_iff_true, or_true],  
  end 

  lemma state.normal_is_legal {σ : state SymB} :
  σ.normal ev m → σ.legal ev m := 
  begin
    simp only [state.normal, state.legal, and_imp, bor_coe_iff, bool.to_bool_and, bool.to_bool_coe, band_coe_iff, bool.to_bool_or], 
    cases (ev.evalB m σ.assumes),
    { simp only [forall_false_left, coe_sort_ff],  },
    { simp only [implies_true_iff, true_or, coe_sort_tt], } 
  end 

end eval_generic

-- The following lemmas depend on (has_eval Model SymB SymV (lang.val D O))). -- 

section eval_lang 
  variables 
    {Model SymB SymV D O : Type} 
    (ev : has_eval Model SymB SymV (lang.val D O))
    {m : Model}

  lemma env.eval_length {ε : env SymV} {e : lang.env D O}  : 
  env.eval ev m ε = e → ε.length = e.length  := 
  begin 
    intro hε,
    rewrite ←hε, 
    simp only [env.eval, list.length_map], 
  end  

  lemma env.eval_nth_le {ε : env SymV} {e : lang.env D O} {y : ℕ} (hy : y < ε.length) : 
  env.eval ev m ε = e →  
  ∃ (hy' : y < e.length), ev.evalV m (ε.nth_le y hy) = (e.nth_le y hy') := 
  begin
    intro hε,
    rcases (env.eval_length ev hε) with hln,
    have hy' : y < e.length := by { linarith, },
    apply exists.intro hy',
    simp only [env.eval] at hε,
    rcases (list.nth_le_of_eq (eq.symm hε) hy') with h,
    simp only [list.nth_le_map'] at h,  
    simp only [h],
  end 

  lemma env.eval_update {ε : env SymV} {e : lang.env D O} (y : ℕ) {v : SymV} {w : lang.val D O} : 
  env.eval ev m ε = e → ev.evalV m v = w → 
  env.eval ev m (ε.update_nth y v) = (e.update_nth y w) := 
  begin 
    intros hε hv,
    simp only [env.eval],
    simp only [env.eval] at hε,
    rewrite ←hε, 
    apply list.ext_le, 
    { simp only [list.length_map, list.update_nth_length], },
    { intros i h1 h2, 
      simp only [list.nth_le_map'],
      cases classical.em (y = i),
      { have hy : y < list.length ε := by { simp only [list.length_map, list.update_nth_length] at h1, simp only [h1, h], },
        have h3 : y < (list.update_nth ε y v).length := by { simp only [hy, list.update_nth_length], }, 
        have h4 : y < ((list.map (ev.evalV m) ε).update_nth y w).length := by { simp only [hy, list.length_map, list.update_nth_length], },
        rewrite ←list.nth_le_eq_idx (list.update_nth ε y v) h h3,
        rewrite ←list.nth_le_eq_idx ((list.map (ev.evalV m) ε).update_nth y w) h h4,
        simp only [hv, list.nth_le_update_nth_eq], },
      { rewrite [←ne.def] at h, 
        rewrite list.nth_le_update_nth_of_ne h v,
        rewrite list.nth_le_update_nth_of_ne h w,
        simp only [list.nth_le_map'], } }
  end 

  
  lemma clos.evals_to_clos {c : clos D O SymV} {w : lang.val D O} :
  clos.eval ev m c = w → w.is_clos := 
  begin 
    intro h,
    simp only [clos.eval] at h,
    rewrite ←h,
    simp only [lang.val.is_clos, coe_sort_tt], 
  end 

  lemma result.eval_ans {σ : state SymB} {v : SymV} {w : lang.val D O} :
  σ.normal ev m → ev.evalV m v = w → (result.ans σ v).eval ev m = lang.result.ans w := 
  begin 
    intros hn hw,
    simp only [result.eval, hw, hn, if_true], 
  end 

  lemma result.eval_halt {ρ : result SymB SymV}  : 
  ¬ ρ.state.normal ev m → ρ.eval ev m = lang.result.halt (ρ.state.aborted ev m) := 
  begin
    intro hn,
    cases ρ with σ v σ,
    { simp only [result.state, eq_ff_eq_not_eq_tt] at hn, 
      simp only [result.eval, result.state, hn, if_false, coe_sort_ff], },
    { simp only [result.eval, result.state, state.aborted, eq_ff_eq_not_eq_tt, bool.to_bool_eq], }
  end  

end eval_lang 

-- The following lemmas depend on the factory interface. --

section factory 

  variables 
    {Model SymB SymV D O : Type} 
    [inhabited Model] [inhabited SymV]
    (f : factory Model SymB SymV D O)
    {m : Model}

  lemma factory.tt_neq_ff : f.mk_tt ≠ f.mk_ff := 
  begin 
    have h : ∀ m, f.evalB m f.mk_ff ≠ f.evalB m f.mk_tt,
    { simp [f.mk_ff_sound, f.mk_tt_sound] },
    specialize h (default Model),
    tauto, 
  end 

  lemma factory.all_eq_all {α} {fn : α → SymB} {xs : list α} : 
  f.evalB m (f.all fn xs) = xs.all (λ x, f.evalB m (fn x)) := 
  begin 
    simp only [factory.all, list.all],
    induction xs,
    { simp only [list.foldr_nil],
      apply f.mk_tt_sound, },
    { simp only [list.foldr],
      rewrite [←xs_ih, f.and_sound],
      simp only [bool.to_bool_and, bool.to_bool_coe], } 
  end 

  lemma factory.all_iff_forall {α} {fn : α → SymB} {xs : list α} : 
  f.evalB m (f.all fn xs) ↔ 
  ∀ (i : ℕ) (hi : i < xs.length), f.evalB m (fn (xs.nth_le i hi)) := 
  begin
    rewrite [f.all_eq_all, list.all_iff_forall],
    apply list.forall_mem_iff_forall_nth_le, 
  end

  lemma factory.some_eq_any {α} {fn : α → SymB} {xs : list α} : 
  f.evalB m (f.some fn xs) = xs.any (λ x, f.evalB m (fn x)) := 
  begin 
    simp only [factory.some, list.any],
    induction xs, 
    { simp only [f.mk_ff_sound, list.foldr_nil],  }, 
    { simp only [list.foldr], 
      rewrite [←xs_ih, f.or_sound], 
      simp only [bool.to_bool_coe, bool.to_bool_or], } 
  end 
  
  lemma factory.assume_normal_true {σ : state SymB} {b : SymB} : 
  σ.normal f.to_has_eval m → f.evalB m b → 
  (f.assume σ b).normal f.to_has_eval m := 
  begin 
    simp only [state.normal, factory.assume, f.and_sound, f.imp_sound, and_imp, eq_ff_eq_not_eq_tt, not_and, bool.of_to_bool_iff],
    intros h1 h2 h3,
    cases f.to_has_eval.evalB m σ.asserts,
    { simp only [coe_sort_ff] at h2, contradiction, }, 
    { simp only [h1, h3, coe_sort_tt, forall_true_left, and_self], }  
  end 

  lemma factory.assume_normal_false {σ : state SymB} {b : SymB} : 
  σ.normal f.to_has_eval m → ¬ f.evalB m b → 
  ¬ (f.assume σ b).normal f.to_has_eval m := 
  begin 
    simp only [state.normal, factory.assume, f.and_sound, f.imp_sound, and_imp, eq_ff_eq_not_eq_tt, not_and, bool.of_to_bool_iff],
    intros h1 h2 h3 h4,
    cases f.to_has_eval.evalB m σ.asserts,
    { simp only [forall_false_left, forall_true_left, coe_sort_ff], }, 
    { simp only [h3, forall_false_left, coe_sort_tt, forall_true_left, coe_sort_ff], }  
  end 

  lemma factory.assert_normal_true {σ : state SymB} {b : SymB} : 
  σ.normal f.to_has_eval m → f.evalB m b → 
  (f.assert σ b).normal f.to_has_eval m := 
  begin 
    simp only [state.normal, factory.assert, f.and_sound, f.imp_sound, and_imp, eq_ff_eq_not_eq_tt, not_and, bool.of_to_bool_iff],
    intros h1 h2 h3,
    cases f.to_has_eval.evalB m σ.asserts,
    { simp only [coe_sort_ff] at h2, contradiction, }, 
    { simp only [h1, h3, coe_sort_tt, forall_true_left, and_self], }  
  end 

  lemma factory.assert_normal_guard {σ : state SymB} {b : SymB} : 
  (f.assert σ b).normal f.to_has_eval m → f.evalB m b := 
  begin 
    simp only [factory.assert, state.normal, f.and_sound, f.imp_sound, and_imp, bool.of_to_bool_iff],
    intros h1,
    simp only [h1, imp_self, implies_true_iff, forall_true_left],
  end 

  lemma factory.cast_lone {c : SymV} : 
  (f.cast c).lone f.to_has_eval m := 
  begin 
    simp only [choices.lone, choices.true],
    rcases (f.cast_sound m c) with h,
    cases (f.to_has_eval.evalV m c).is_clos,
    { simp only [true_and, forall_false_left, forall_true_left, not_false_iff, coe_sort_ff] at h, 
      simp only [choices.none, choices.true, has_eval_clos] at h,
      linarith, }, 
    { simp only [forall_false_left, and_true, not_true, coe_sort_tt, forall_true_left] at h,
      cases h with h _,
      simp only [choices.one, choices.true, has_eval_clos] at h,
      linarith, } 
  end 

  lemma factory.assert_some_cast_one {c : SymV} {σ σ' : state SymB} :
  σ.normal f.to_has_eval m → σ'.normal f.to_has_eval m → 
  σ' = f.assert σ (f.some choice.guard (f.cast c)) →   
  (f.cast c).one f.to_has_eval m := 
  begin 
    intros hn hn' heq,
    apply choices.lone_some_one f.to_has_eval,
    { apply f.cast_lone, },  
    { rewrite ←f.some_eq_any, 
      rewrite heq at hn', 
      apply f.assert_normal_guard hn', }
  end 

  lemma top_normal : state.normal f.to_has_eval m ⟨f.mk_tt, f.mk_tt⟩ := 
  by { simp only [state.normal, f.mk_tt_sound, to_bool_true_eq_tt, coe_sort_tt, and_self], }

  lemma top_legal : state.legal f.to_has_eval m ⟨f.mk_tt, f.mk_tt⟩ := 
  by { apply state.normal_is_legal f.to_has_eval, apply top_normal, }


end factory 

end sym
