import tactic.basic
import tactic.split_ifs
import tactic.linarith
import tactic.apply_fun
import .svm
import .lib

namespace sym 

  variables 
    {Model SymB SymV D O : Type}
    [inhabited Model] [inhabited SymV]
    (f : factory Model SymB SymV D O) {m : Model}

  lemma factory.merge_φ_eqp {σ : state SymB} {grs : choices SymB (result SymB SymV)} {field : state SymB → SymB} : 
  (field = state.assumes ∨ field = state.asserts) → 
  (∀ (i : ℕ) (hi : i < grs.length), state.eqv f.to_has_eval m (grs.nth_le i hi).value.state σ) → 
  f.to_has_eval.evalB m (f.merge_φ σ grs field) = f.to_has_eval.evalB m (field σ) := 
  begin 
    intros hf hg,
    simp only [factory.merge_φ, f.and_sound, bool.to_bool_and, bool.to_bool_coe],
    rewrite [←bool.coe_bool_iff], 
    simp only [and_iff_left_iff_imp, band_coe_iff],
    intro ha,
    rewrite f.all_iff_forall,
    intros i hi,
    specialize hg i hi,
    simp only [state.eqv] at hg,
    cases hf; 
    simp only [hf] at ha; 
    simp only [hf, f.imp_sound, bool.of_to_bool_iff, hg]; 
    intro h; 
    exact ha, 
  end 
  
  lemma factory.merge_σ_eqp {σ : state SymB} {grs : choices SymB (result SymB SymV)} : 
  (∀ (i : ℕ) (hi : i < grs.length), state.eqv f.to_has_eval m (grs.nth_le i hi).value.state σ) → 
  state.eqv f.to_has_eval m (f.merge_σ σ grs) σ := 
  begin
    intros hg,
    simp only [factory.merge_σ, state.eqv],
    constructor; 
    apply f.merge_φ_eqp _ hg; 
    simp only [true_or, eq_self_iff_true, or_true],  
  end 

  lemma factory.merge_ρ_eqp {σ : state SymB} {grs : choices SymB (result SymB SymV)} :  
  (∀ (i : ℕ) (hi : i < grs.length), state.eqv f.to_has_eval m (grs.nth_le i hi).value.state σ) → 
  state.eqv f.to_has_eval m (f.merge_ρ σ grs).state σ := 
  begin 
    intros hg,
    simp only [factory.merge_ρ],
    cases (list.all grs (λ (gr : choice SymB (result SymB SymV)), gr.value.is_halt)),
    { simp only [factory.halt_or_ans, bool.coe_sort_ff, if_false], 
      cases (f.halted (f.merge_σ σ grs)),
      { simp only [result.state, bool.coe_sort_ff, if_false], 
        apply f.merge_σ_eqp hg, },
      { simp only [result.state, if_true, bool.coe_sort_tt], 
        apply f.merge_σ_eqp hg, } },
    { simp only [result.state, if_true, bool.coe_sort_tt], 
      apply f.merge_σ_eqp hg, } 
  end 
  
  lemma factory.merge_υ_map_filter_results {grs : choices SymB (result SymB SymV)} :  
  (list.map 
    (λ (gv : choice SymB (result SymB SymV)), choice.mk gv.guard (result.value (default SymV) gv.value)) 
    (list.filter (λ (gv : choice SymB (result SymB SymV)), ↥(f.to_has_eval.evalB m gv.guard)) grs)) = 
  (list.filter (λ (gv : choice SymB SymV), ↥(f.to_has_eval.evalB m gv.guard))
    (list.map (λ (gv : choice SymB (result SymB SymV)), choice.mk gv.guard (result.value (default SymV) gv.value)) grs)) := 
  begin 
    induction grs,
    { simp only [list.filter_nil, list.map], },
    { simp only [list.map, list.filter], 
      split_ifs,
      { simp only [true_and, eq_self_iff_true, list.map], 
        apply grs_ih, },
      { apply grs_ih, } } 
  end 

  lemma factory.merge_υ_normal {grs : choices SymB (result SymB SymV)} 
  {gv : choice SymB (result SymB SymV)} :  
  grs.filter (λ gv, f.evalB m gv.guard) = [gv] → 
  f.evalV m (f.merge_υ grs) = f.evalV m ((gv).value.value (default SymV)) := 
  begin 
    intros hu,
    have hlen : grs.filter (λ gv, f.evalB m gv.guard) = [gv] := hu,
    rcases (choices.filter_one_guard (has_eval_result f.to_has_eval) hu) with hg,
    simp only [has_eval_result] at hg,
    apply_fun (list.map (λ (gv : choice SymB (result SymB SymV)), choice.mk gv.guard (result.value (default SymV) gv.value))) at hu,
    simp only [list.map] at hu,
    apply_fun (choices.eval f.to_has_eval m (f.evalV m (default SymV))) at hu,
    simp only [choices.eval, hg, if_true] at hu,
    simp only [factory.merge_υ],
    rewrite f.merge_sound,
    { rewrite ←hu,
      rewrite factory.merge_υ_map_filter_results,
      apply choices.eval_filter, },
    { simp only [choices.one, choices.true, list.map_map],
      rewrite list.map_filter,
      simp only [list.length_map],
      apply_fun list.length at hlen,
      simp only [list.length_singleton] at hlen,
      have hf : ((λ (g : SymB), ↥(f.to_has_eval.evalB m g)) ∘ choice.guard ∘ λ (gr : choice SymB (result SymB SymV)), {guard := gr.guard, value := result.value (default SymV) gr.value}) = 
                (λ (gv : choice SymB (result SymB SymV)), ↥(f.to_has_eval.evalB m gv.guard)) := 
      by { apply funext, intro x, simp only [eq_iff_iff], },
      simp only [hf],
      exact hlen, }
  end 

  lemma factory.merge_φ_all_filter_results {grs : choices SymB (result SymB SymV)} {field : state SymB → SymB} : 
  list.all grs (λ (x : choice SymB (result SymB SymV)), f.evalB m (f.imp x.guard (field x.value.state))) = 
  list.all (list.filter (λ (gv : choice SymB (result SymB SymV)), (f.evalB m gv.guard)) grs) (λ (x : choice SymB (result SymB SymV)), f.evalB m (f.imp x.guard (field x.value.state))) :=
  begin 
    induction grs,
    { simp only [list.filter_nil], }, 
    { simp only [list.filter, list.all_cons], 
      split_ifs,
      { simp only [list.all_cons], 
        congr, exact grs_ih, },
      { rewrite f.imp_sound,
        simp only [h, grs_ih, forall_false_left, to_bool_true_eq_tt, band],  } } 
  end 


  lemma factory.merge_φ_normal {σ : state SymB} {grs : choices SymB (result SymB SymV)} 
  {gv : choice SymB (result SymB SymV)} {field : state SymB → SymB} : 
  (field = state.assumes ∨ field = state.asserts) → 
  σ.normal f.to_has_eval m → 
  grs.filter (λ gv, f.evalB m gv.guard) = [gv] → 
  f.to_has_eval.evalB m (f.merge_φ σ grs field) = f.to_has_eval.evalB m (field gv.value.state) := 
  begin 
    intros hf hn hu,
    simp only [state.normal, bool.to_bool_and, bool.to_bool_coe, band_coe_iff] at hn,
    simp only [factory.merge_φ, f.and_sound, bool.to_bool_and, bool.to_bool_coe],
    have ht : (f.to_has_eval.evalB m (field σ)) = tt := by { rewrite bool.tt_eq_true, cases hf; simp only [hf, hn], },
    simp only [ht, band],
    rewrite f.all_eq_all,  
    rewrite [factory.merge_φ_all_filter_results, hu],
    rcases (choices.filter_one_guard (has_eval_result f.to_has_eval) hu) with hg,
    simp only [has_eval_result] at hg,
    simp only [f.imp_sound, hg, bool.to_bool_coe, forall_true_left, list.all_nil, list.all_cons, band_tt], 
  end 

  lemma factory.merge_σ_normal  {σ : state SymB} {grs : choices SymB (result SymB SymV)} {gv : choice SymB (result SymB SymV)} : 
  σ.normal f.to_has_eval m → 
  grs.filter (λ gv, f.evalB m gv.guard) = [gv] → 
  (f.merge_σ σ grs).eqv f.to_has_eval m gv.value.state := 
  begin 
    intros hn hu, 
    simp only [factory.merge_σ, state.eqv],
    constructor;
    apply f.merge_φ_normal _ hn hu;
    simp only [true_or, or_true, eq_self_iff_true],  
  end 

  lemma factory.merge_ρ_normal_eqv {σ : state SymB} {grs : choices SymB (result SymB SymV)} {gv : choice SymB (result SymB SymV)} : 
  σ.normal f.to_has_eval m → 
  grs.filter (λ gv, f.evalB m gv.guard) = [gv] → 
  (f.merge_ρ σ grs).state.eqv f.to_has_eval m gv.value.state   := 
  begin
    intros hn hu,
    generalize hr : (f.merge_ρ σ grs) = r,
    simp only [factory.merge_ρ] at hr,
    rcases (f.merge_σ_normal hn hu) with hσ,
    split_ifs at hr,
    { rewrite list.all_iff_forall at h,
      specialize h gv,
      have hgv : gv ∈ [gv] := by { simp only [list.mem_singleton], },
      rewrite [←hu, list.mem_filter] at hgv,
      simp only [hgv, forall_true_left] at h,
      repeat { rewrite ←hr, },
      simp only [result.state, hσ, result.value, true_and],  },
    { simp only [factory.halt_or_ans] at hr,
      split_ifs at hr; 
      repeat { rewrite ←hr, }; 
      simp only [result.state, hσ, true_and], } 
  end 

  lemma factory.merge_ρ_normal_eval {σ : state SymB} {grs : choices SymB (result SymB SymV)} {gr : choice SymB (result SymB SymV)} : 
  σ.normal f.to_has_eval m → 
  grs.filter (λ gv, f.evalB m gv.guard) = [gr] → 
  (gr.value.legal f.to_has_eval m) → 
  (f.merge_ρ σ grs).eval f.to_has_eval m = gr.value.eval f.to_has_eval m := 
  begin 
    intros hn hu hl, 
    generalize hr : (f.merge_ρ σ grs) = r,
    simp only [factory.merge_ρ] at hr,
    rcases (f.merge_σ_normal hn hu) with hσ,
    split_ifs at hr,
    { rewrite list.all_iff_forall at h,
      specialize h gr, 
      have hgr : gr ∈ [gr] := by { simp only [list.mem_singleton], },
      rewrite [←hu, list.mem_filter] at hgr,
      simp only [hgr, forall_true_left] at h,
      repeat { rewrite ←hr, },
      cases gr.value with σ' v' σ',
      { simp only [result.is_halt, to_bool_false_eq_ff, coe_sort_ff] at h, 
        contradiction, }, 
      { simp only [result.eval],
        simp only [result.state] at hσ,
        apply state.eqv_aborted f.to_has_eval hσ, } }, 
    { simp only [factory.halt_or_ans] at hr,
      split_ifs at hr; 
      repeat { rewrite ←hr, }, 
      { cases gr.value with σ' v' σ',
        { simp only [result.state] at hσ, 
          simp only [factory.halted, bor_coe_iff] at h_1,
          cases h_1, 
          all_goals { 
            simp only [f.is_ff_sound] at h_1,
            apply_fun (f.evalB m) at h_1,
            simp only [f.mk_ff_sound] at h_1,
            have hnσ : ¬ ((f.merge_σ σ grs).normal f.to_has_eval m) := by { simp only [state.normal, h_1, to_bool_false_eq_ff, not_false_iff, coe_sort_ff, false_and, and_false],  },
            rcases (state.eqv_abnormal f.to_has_eval hnσ hσ) with hnσ', 
            simp only [result.eval, hnσ', if_false],
            apply state.eqv_aborted f.to_has_eval hσ, }  },
        { simp only [result.eval], 
          apply state.eqv_aborted f.to_has_eval hσ, } },
      { rcases (f.merge_υ_normal hu) with hv,
        cases gr.value with σ' v' σ',
        { simp only [result.eval], 
          cases hnσ : (state.normal f.to_has_eval m (f.merge_σ σ grs)), 
          { rewrite ←bool_iff_false at hnσ, 
            rcases (state.eqv_abnormal f.to_has_eval hnσ hσ) with hnσ',
            simp only [result.state] at hnσ', 
            simp only [hnσ', if_false, coe_sort_ff],
            apply state.eqv_aborted f.to_has_eval hσ, },
          { rewrite bool.tt_eq_true at hnσ,
            rcases (state.eqv_normal f.to_has_eval hnσ hσ) with hnσ',
            simp only [result.state] at hnσ', 
            simp only [hnσ', if_true, coe_sort_tt],
            simp only [result.value] at hv,
            exact hv, }  },
        { simp only [result.legal, eq_ff_eq_not_eq_tt, bool.of_to_bool_iff] at hl,
          cases hl with hl hnσ',
          rewrite ←bool_iff_false at hnσ',
          simp only [result.state] at hσ,
          rcases (state.eqv_abnormal f.to_has_eval hnσ' (state.eqv.symm f.to_has_eval m hσ)) with hnσ,
          simp only [result.eval, hnσ, if_false],
          apply state.eqv_aborted f.to_has_eval hσ,  }  } }
  end 

end sym