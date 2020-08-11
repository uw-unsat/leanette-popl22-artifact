import tactic.basic
import tactic.split_ifs
import tactic.linarith
import tactic.apply_fun
import .svm
import .lib
import .hp 
import .mrg

namespace sym 

open lang 

section lgl

  variables 
    {Model SymB SymV D O : Type}
    [inhabited Model] [inhabited SymV]
    (f : factory Model SymB SymV D O) {m : Model}

  lemma factory.hlgl_eqv_lgl {σ : state SymB} {ρ : result SymB SymV} : 
  σ.legal f.to_has_eval m → ¬ σ.normal f.to_has_eval m → ρ.state.eqv f.to_has_eval m σ → 
  ρ.legal f.to_has_eval m :=
  begin 
    intros hl_σ hnn heq,
    simp only [state.normal, eq_ff_eq_not_eq_tt, not_and, bool.to_bool_and, bool.to_bool_coe, band_coe_iff] at hnn,
    simp only [state.legal, bor_coe_iff, bool.to_bool_coe, bool.to_bool_or] at hl_σ,
    cases ρ with σ' v σ'; simp only [state.eqv, result.state] at heq,
    { simp only [result.legal, state.legal, state.normal, heq, and_imp, bool.of_to_bool_iff],
      simp only [hl_σ, true_and], },
    { simp only [result.legal, state.legal, state.normal, heq, hl_σ, true_and, eq_ff_eq_not_eq_tt, not_and, bool.of_to_bool_iff],
      exact hnn, } 
  end 

  theorem svm_hlgl {x : exp D O} {ε : env SymV} {σ : state SymB} {ρ : result SymB SymV} : 
  σ.legal f.to_has_eval m → ¬ σ.normal f.to_has_eval m → evalS f x ε σ ρ → 
  ρ.legal f.to_has_eval m := 
  by { intros hl_σ hnn hs, apply f.hlgl_eqv_lgl hl_σ hnn (svm_hp f hnn hs), }

  lemma factory.compose_lgl {σ σ' : state SymB}  
  (hl_σ : (state.legal f.to_has_eval m σ))
  (hl_σ' : (state.legal f.to_has_eval m σ')) : 
  (state.legal f.to_has_eval m (f.compose σ σ')) := 
  begin
    simp only [factory.compose, state.legal, f.and_sound, f.imp_sound, bool.of_to_bool_iff], 
    simp only [state.legal, bor_coe_iff, bool.to_bool_coe, bool.to_bool_or] at hl_σ hl_σ',
    cases (f.to_has_eval.evalB m σ.assumes),
    { simp only [false_or, coe_sort_ff] at hl_σ, 
      simp only [hl_σ, forall_false_left, false_or, and_self, coe_sort_ff, false_and],  },
    { simp only [true_and, coe_sort_tt, forall_true_left], 
      cases (f.to_has_eval.evalB m σ'.assumes),
      { simp only [false_or, coe_sort_ff] at hl_σ', 
        simp only [hl_σ', and_true, coe_sort_ff], finish, }, 
      { finish, } } 
  end 

  lemma factory.compose_normal {σ σ' : state SymB} :
  ((state.normal f.to_has_eval m σ) ∧ (state.normal f.to_has_eval m σ')) ↔ 
  state.normal f.to_has_eval m (f.compose σ σ') := 
  begin 
    simp only [factory.compose, state.normal, f.and_sound, f.imp_sound, bool.of_to_bool_iff],
    constructor; intro h,
    { simp only [h, forall_true_left, and_self], }, 
    { simp only [h, and_self], } 
  end 

  lemma factory.merge_ρ_lgl {σ : state SymB} {grs : choices SymB (result SymB SymV)} : 
  σ.normal f.to_has_eval m → grs.one f.to_has_eval m → 
  (∀ (i : ℕ) (hi : i < grs.length), (grs.nth_le i hi).value.legal f.to_has_eval m) → 
  (result.legal f.to_has_eval m (f.merge_ρ σ grs)) := 
  begin 
    intros hn hu hl_grs,
    replace hu : grs.one (has_eval_result f.to_has_eval) m := 
    by { simp only [has_eval_result, choices.one, choices.true],
         simp only [choices.one, choices.true] at hu, exact hu, },
    rewrite (choices.one_iff_filter (has_eval_result f.to_has_eval)) at hu,
    rcases hu with ⟨i, hi, hf⟩,
    simp only [has_eval_result] at hf,
    rcases (f.merge_ρ_normal_eqv hn hf) with hm_σ,
    rcases (f.merge_ρ_normal_eval hn hf (hl_grs i hi)) with h_eval,
    specialize hl_grs i hi,
    cases (f.merge_ρ σ grs) with σ' v' σ'; 
    cases (list.nth_le grs i hi).value with σ'' v'' σ'';
    simp only [result.legal, eq_ff_eq_not_eq_tt, bool.of_to_bool_iff]; 
    simp only [result.legal, eq_ff_eq_not_eq_tt, bool.of_to_bool_iff] at hl_grs;
    simp only [result.state] at hm_σ,
    { apply state.eqv_legal f.to_has_eval hl_grs (state.eqv.symm f.to_has_eval m hm_σ),  },
    { apply state.eqv_legal f.to_has_eval hl_grs.left (state.eqv.symm f.to_has_eval m hm_σ), },
    { constructor,
      { apply state.eqv_legal f.to_has_eval hl_grs (state.eqv.symm f.to_has_eval m hm_σ), },
      { simp only [result.eval] at h_eval,
        cases hn'' : (state.normal f.to_has_eval m σ''); 
        simp only [hn'', if_true, if_false, coe_sort_ff, coe_sort_tt] at h_eval,
        { rewrite ←bool_iff_false at hn'',
          rewrite ←bool_iff_false,
          apply state.eqv_abnormal f.to_has_eval hn'', 
          symmetry, exact hm_σ,  }, 
        { contradiction, }  } },
    { cases hl_grs with hl_grs hn'', 
      constructor,
      { apply state.eqv_legal f.to_has_eval hl_grs (state.eqv.symm f.to_has_eval m hm_σ), }, 
      { rewrite ←bool_iff_false at hn'', 
        rewrite ←bool_iff_false, 
        apply state.eqv_abnormal f.to_has_eval hn'',
        symmetry, exact hm_σ,  } },
  end 

  lemma factory.assert_lgl {σ : state SymB} (b : SymB) :
  σ.legal f.to_has_eval m → (f.assert σ b).legal f.to_has_eval m := 
  begin
    simp only [state.legal, factory.assert, bor_coe_iff, bool.to_bool_coe, bool.to_bool_or],
    intro hl_σ, 
    cases ha : (f.to_has_eval.evalB m σ.assumes),
    { simp only [false_or, coe_sort_ff],
      simp only [ha, false_or, coe_sort_ff] at hl_σ, 
      simp only [f.and_sound, f.imp_sound, hl_σ, ha, forall_false_left, to_bool_true_eq_tt, coe_sort_tt, and_self, coe_sort_ff], }, 
    { simp only [true_or, coe_sort_tt], }  
  end 

  lemma factory.assume_lgl {σ : state SymB} (b : SymB) :
  σ.legal f.to_has_eval m → (f.assume σ b).legal f.to_has_eval m := 
  begin
    simp only [state.legal, factory.assume, bor_coe_iff, bool.to_bool_coe, bool.to_bool_or],
    intro hl_σ, 
    cases ha : (f.to_has_eval.evalB m σ.asserts),
    { simp only [ha, or_false, coe_sort_ff] at hl_σ,
      simp only [or_false, coe_sort_ff], 
      simp only [f.and_sound, f.imp_sound, ha, hl_σ, forall_false_left, to_bool_true_eq_tt, coe_sort_tt, and_self, coe_sort_ff], },
    { simp only [coe_sort_tt, or_true], }
  end 

  lemma factory.app_lgl {ε : env SymV} {σ : state SymB} {o : O} {xs : list ℕ} {vs : list SymV} 
  (h1: xs.length = vs.length) 
  (h2: ∀ (i : ℕ) (hx : i < xs.length) (hv : i < vs.length), 
        evalS f (exp.var (xs.nth_le i hx)) ε σ (result.ans σ (vs.nth_le i hv)))
  (ih : ∀ (i : ℕ) (hx : i < xs.length) (hv : i < vs.length), (λ {x : exp D O} {ε : env SymV} {σ : state SymB} {ρ : result SymB SymV} (hs : evalS f x ε σ ρ), (state.legal f.to_has_eval m σ) → (result.legal f.to_has_eval m ρ)) (h2 i hx hv))
  (hl_σ : (state.legal f.to_has_eval m σ)) : 
  (result.legal f.to_has_eval m (f.strengthen σ (f.opS o vs))) := 
  begin
    rcases (f.opS_sound m o vs) with ⟨_, hl_σ'⟩,
    cases (f.opS o vs) with σ' v σ'; 
    simp only [factory.strengthen]; 
    simp only [result.legal, bool.of_to_bool_iff] at hl_σ';
    try { cases hl_σ' with hl_σ' hl_nσ' }; 
    rcases (f.compose_lgl hl_σ hl_σ') with hlc,
    { simp only [factory.halt_or_ans],
      cases hh : (f.halted (f.compose σ σ')), 
      { simp only [result.legal, hlc, if_false, coe_sort_ff], },
      { simp only [result.legal, hlc, true_and, eq_ff_eq_not_eq_tt, if_true, bool.of_to_bool_iff, coe_sort_tt],
        by_contradiction,
        simp only [eq_tt_eq_not_eq_ff] at h,
        rewrite bool.tt_eq_true at h,
        simp only [state.normal, bool.to_bool_and, bool.to_bool_coe, band_coe_iff] at h,
        simp only [factory.halted, bor_eq_true_eq_eq_tt_or_eq_tt] at hh,
        cases hh,
        all_goals
        { rewrite bool.tt_eq_true at hh,
          simp only [f.is_ff_sound] at hh, 
          apply_fun (f.to_has_eval.evalB m) at hh,
          simp only [f.mk_ff_sound] at hh,
          simp only [hh, coe_sort_ff, false_and, and_false, coe_sort_ff] at h,
          contradiction, },} },
    { simp only [result.legal, true_and, eq_ff_eq_not_eq_tt, bool.of_to_bool_iff],   
      by_contradiction,
      simp only [hlc, true_and, eq_tt_eq_not_eq_ff] at h,
      rewrite bool.tt_eq_true at h,
      rewrite ←f.compose_normal at h,
      cases h,
      contradiction, }
  end 

  lemma factory.call_sym_lgl {ε : env SymV} {σ σ' : state SymB}
  {x1 x2 : ℕ} {c v : SymV} {grs : choices SymB (result SymB SymV)}
  (h1  : evalS f (exp.var x1) ε σ (result.ans σ c))
  (h2  : evalS f (exp.var x2) ε σ (result.ans σ v))
  (h3  : σ' = f.assert σ (f.some choice.guard (f.cast c)))
  (h4  : ¬(f.is_ff (f.some choice.guard (f.cast c))) ∧ ¬(f.halted σ')) 
  (h5  : list.map choice.guard (f.cast c) = list.map choice.guard grs)
  (h6  : ∀ (i : ℕ) (hc : i < list.length (f.cast c)) (hr : i < list.length grs), evalS f (list.nth_le (f.cast c) i hc).value.exp (list.update_nth (list.nth_le (f.cast c) i hc).value.env (list.nth_le (f.cast c) i hc).value.var v) (f.assume σ' (list.nth_le (f.cast c) i hc).guard) (list.nth_le grs i hr).value)
  (ih1 : (state.legal f.to_has_eval m σ) → (result.legal f.to_has_eval m (result.ans σ c)))
  (ih2 : (state.legal f.to_has_eval m σ) → (result.legal f.to_has_eval m (result.ans σ v)))
  (ih6 : ∀ (i : ℕ) (hc : i < list.length (f.cast c)) (hr : i < list.length grs), 
          (λ {x : exp D O} {ε : env SymV} {σ : state SymB} {ρ : result SymB SymV} (hs : evalS f x ε σ ρ), 
            (state.legal f.to_has_eval m σ) → 
            (result.legal f.to_has_eval m ρ)) (h6 i hc hr))
  (hl_σ: (state.legal f.to_has_eval m σ)) : 
  (result.legal f.to_has_eval m (f.merge_ρ σ' grs)) := 
  begin
    cases hn : σ.normal f.to_has_eval m,
    { rewrite ←bool_iff_false at hn, 
      apply svm_hlgl f hl_σ hn (evalS.call_sym h1 h2 h3 h4 h5 h6), },
    { rewrite bool.tt_eq_true at hn, 
      have hl_σ' : ↥(σ'.legal f.to_has_eval m) := by { simp only [h3], apply f.assert_lgl _ hl_σ, },
      cases hn' : σ'.normal f.to_has_eval m,
      { rewrite ←bool_iff_false at hn', 
        apply f.hlgl_eqv_lgl hl_σ' hn',
        apply f.merge_ρ_eqp,
        intros i hr,
        rcases (list.map_bound (eq.symm h5) hr) with hc,
        specialize h6 i hc hr,
        transitivity (f.assume σ' (list.nth_le (f.cast c) i hc).guard),
        { apply svm_hp f _ h6, apply state.eqv_abnormal f.to_has_eval hn', symmetry, apply f.assume_hp hn', },
        { apply f.assume_hp hn', } },
      { rewrite bool.tt_eq_true at hn', 
        rcases (f.assert_some_cast_one hn hn' h3) with h_one,
        apply f.merge_ρ_lgl hn' (choices.eq_one f.to_has_eval h5 h_one), 
        intros i hr,
        rcases (list.map_bound (eq.symm h5) hr) with hc,
        rcases (choices.one_implies_filter (has_eval_clos f.to_has_eval) h_one) with ⟨w, hw, hwp⟩,
        cases classical.em (i = w),
        { apply ih6 i hc hr,
          apply f.assume_lgl _ hl_σ', }, 
        { rewrite [←ne.def] at h,
          apply svm_hlgl f _ _ (h6 i hc hr),
          apply f.assume_lgl _ hl_σ', 
          apply f.assume_normal_false hn', 
          apply choices.filter_one_rest (has_eval_clos f.to_has_eval) hw hc hwp,
          symmetry, exact h, } } } 
  end 

  lemma factory.call_halt_lgl {σ σ' : state SymB} {c : SymV} 
  (hσ' : σ' = f.assert σ (f.some choice.guard (f.cast c)))
  (hh  : ↥(f.is_ff (f.some choice.guard (f.cast c))) ∨ ↥(f.halted σ'))
  (hl_σ : (state.legal f.to_has_eval m σ)) :
  (result.legal f.to_has_eval m (result.halt σ')) := 
  begin 
    rcases (f.assert_lgl (f.some choice.guard (f.cast c)) hl_σ) with h,
    rewrite ←hσ' at h,
    simp only [result.legal, h, state.normal, true_and, eq_ff_eq_not_eq_tt, bool.of_to_bool_iff, not_and],
    intro ha,
    cases hh,
    { simp only [hσ', factory.assert] at ha,
      simp only [hσ', factory.assert, f.and_sound, f.imp_sound, ha, eq_ff_eq_not_eq_tt, not_and, to_bool_ff_iff, forall_true_left],
      intro ha',
      simp only [f.is_ff_sound] at hh,
      simp only [hh, f.mk_ff_sound], },
    { simp only [factory.halted, bor_coe_iff] at hh,
      cases hh; simp only [f.is_ff_sound] at hh,
      { rewrite hh at ha,
        simp only [f.mk_ff_sound, coe_sort_ff] at ha,
        contradiction, }, 
      { rewrite hh,
        apply f.mk_ff_sound,  } } 
  end 

  lemma factory.let0_lgl {ε : env SymV} {σ σ' : state SymB}
  {y : ℕ} {x2: exp D O} {v : SymV} {r: result SymB SymV}
  (h2  : evalS f x2 (list.update_nth ε y v) σ' r)
  (ih1 : (state.legal f.to_has_eval m σ) → (result.legal f.to_has_eval m (result.ans σ' v)))
  (ih2 : (state.legal f.to_has_eval m σ') → (result.legal f.to_has_eval m r))
  (hl_σ : (state.legal f.to_has_eval m σ)) : 
  (result.legal f.to_has_eval m r) := 
  begin 
    specialize ih1 hl_σ,
    simp only [result.legal, bool.of_to_bool_iff] at ih1,
    cases hn : (state.normal f.to_has_eval m σ'),
    { rewrite ←bool_iff_false at hn,
      apply svm_hlgl f ih1 hn h2, }, 
    { apply ih2 ih1, } 
  end 

  lemma factory.if0_sym_lgl {ε : env SymV} {σ : state SymB}
  {xc : ℕ} {xt xf : exp D O} {v : SymV} {rt rf: result SymB SymV}
  (hc : evalS f (exp.var xc) ε σ (result.ans σ v))
  (hv : ¬↥(f.is_tt (f.truth v)) ∧ ¬↥(f.is_ff (f.truth v)))
  (ht : evalS f xt ε (f.assume σ (f.truth v)) rt)
  (hf : evalS f xf ε (f.assume σ (f.not (f.truth v))) rf)
  (iht: (state.legal f.to_has_eval m (f.assume σ (f.truth v))) → (result.legal f.to_has_eval m rt))
  (ihf: (state.legal f.to_has_eval m (f.assume σ (f.not (f.truth v)))) → (result.legal f.to_has_eval m rf))
  (hl_σ: (state.legal f.to_has_eval m σ)) :
  (result.legal f.to_has_eval m (f.merge_ρ σ [{guard := f.truth v, value := rt}, {guard := f.not (f.truth v), value := rf}])) := 
  begin
    cases hn : σ.normal f.to_has_eval m,
    { rewrite ←bool_iff_false at hn, 
      apply svm_hlgl f hl_σ hn (evalS.if0_sym hc hv ht hf), }, 
    { rewrite bool.tt_eq_true at hn,
      apply f.merge_ρ_lgl hn,
      { apply choices.one_of_ite, apply f.not_sound, },
      { intros i hi,
        simp only [list.length, zero_add] at hi,
        rcases (nat.lt2_implies_01 hi) with hi01,
        cases hi01; simp only [hi01, list.nth_le],
        { apply iht, apply f.assume_lgl _ hl_σ, },
        { apply ihf, apply f.assume_lgl _ hl_σ, } } } 
  end 

  lemma factory.error_lgl {σ : state SymB} 
  (hl_σ : (state.legal f.to_has_eval m σ)) : 
  (result.legal f.to_has_eval m (result.halt (f.assert σ f.mk_ff))) := 
  begin 
    rcases (f.assert_lgl f.mk_ff hl_σ) with h,
    simp only [result.legal, eq_ff_eq_not_eq_tt, bool.of_to_bool_iff, h, true_and],
    cases hn : (σ.normal f.to_has_eval m),
    { rewrite ←bool_iff_false at hn, 
      rcases (@factory.assert_hp Model SymB SymV D O _ _ f m σ f.mk_ff hn) with heqv,
      rcases (state.eqv_abnormal f.to_has_eval hn (state.eqv.symm f.to_has_eval m heqv)) with hh,
      rewrite bool_iff_false at hh,
      exact hh, }, 
    { simp only [state.normal, band_eq_true_eq_eq_tt_and_eq_tt, bool.to_bool_and, bool.to_bool_coe] at hn,
      simp only [state.normal, factory.assert, hn, f.and_sound, f.imp_sound, f.mk_ff_sound, 
                 to_bool_false_eq_ff, coe_sort_tt, forall_true_left, and_false, coe_sort_ff], } 
  end 

  lemma factory.abort_lgl {σ : state SymB} 
  (hl_σ : (state.legal f.to_has_eval m σ)) : 
  (result.legal f.to_has_eval m (result.halt (f.assume σ f.mk_ff))) := 
  begin 
    rcases (f.assume_lgl f.mk_ff hl_σ) with h,
    simp only [result.legal, eq_ff_eq_not_eq_tt, bool.of_to_bool_iff, h, true_and],
    cases hn : (σ.normal f.to_has_eval m),
    { rewrite ←bool_iff_false at hn, 
      rcases (@factory.assume_hp Model SymB SymV D O _ _ f m σ f.mk_ff hn) with heqv,
      rcases (state.eqv_abnormal f.to_has_eval hn (state.eqv.symm f.to_has_eval m heqv)) with hh,
      rewrite bool_iff_false at hh,
      exact hh, },
    { simp only [state.normal, band_eq_true_eq_eq_tt_and_eq_tt, bool.to_bool_and, bool.to_bool_coe] at hn,
      simp only [state.normal, factory.assume, hn, f.and_sound, f.imp_sound, f.mk_ff_sound, 
                to_bool_false_eq_ff, coe_sort_tt, forall_true_left, and_false, coe_sort_ff, false_and], }
  end

  -- The SVM rules preserve the legality of states across steps: 
  -- legal input state leads to a legal result. 
  -- A state is legal with respect to a model if its assumptions or 
  -- assertions (or both) are true under that model. A result is 
  -- legal if its state is legal.
  theorem svm_lgl {x : exp D O} {ε : env SymV} {σ : state SymB} {ρ : result SymB SymV} :
  σ.legal f.to_has_eval m → 
  evalS f x ε σ ρ → 
  ρ.legal f.to_has_eval m :=
  begin 
    intros hl_σ hs,
    induction hs,
    case sym.evalS.app       { apply f.app_lgl hs_h1 hs_h2 hs_ih hl_σ, },
    case sym.evalS.call_sym  { apply f.call_sym_lgl hs_h1 hs_h2 hs_h3 hs_h4 hs_h5 hs_h6 hs_ih_h1 hs_ih_h2 hs_ih_h6 hl_σ, },
    case sym.evalS.call_halt { apply f.call_halt_lgl hs_h3 hs_h4 hl_σ, },
    case sym.evalS.let0      { apply f.let0_lgl hs_h2 hs_ih_h1 hs_ih_h2 hl_σ, },
    case sym.evalS.let0_halt { apply hs_ih hl_σ, },
    case sym.evalS.if0_true  { apply hs_ih_hr hl_σ, },
    case sym.evalS.if0_false { apply hs_ih_hr hl_σ, },
    case sym.evalS.if0_sym   { apply f.if0_sym_lgl hs_hc hs_hv hs_ht hs_hf hs_ih_ht hs_ih_hf hl_σ, },
    case sym.evalS.error     { apply f.error_lgl hl_σ, },
    case sym.evalS.abort     { apply f.abort_lgl hl_σ, },
    all_goals                { -- bool, datum, lam, var
      simp only [result.legal, hl_σ, f.bval_sound, f.dval_sound, f.cval_sound, 
                to_bool_true_eq_tt, implies_true_iff, coe_sort_tt, and_self], },
  end 

end lgl 

end sym 
