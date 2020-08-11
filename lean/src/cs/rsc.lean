import tactic.basic
import tactic.split_ifs
import tactic.linarith
import tactic.apply_fun
import .svm
import .lib
import .hp 
import .mrg
import .lgl
import .detc

namespace sym 

open lang 

section rsc
  variables 
    {Model SymB SymV D O : Type}
    [inhabited Model] [inhabited SymV]
    (f : factory Model SymB SymV D O) {m : Model}

  lemma factory.normal_ans_rc {σ' : state SymB} (v : SymV)
  (hn' : (state.normal f.to_has_eval m σ')) : 
  ∃ w, f.evalV m v = w ∧ (result.ans σ' v).eval f.to_has_eval m = (lang.result.ans w) := 
  begin 
    apply exists.intro (f.to_has_eval.evalV m v), 
    simp only [result.eval, true_and, eq_ff_eq_not_eq_tt, eq_self_iff_true, ite_eq_left_iff],
    intro hnn,
    simp only [hnn, coe_sort_ff] at hn',
    contradiction, 
  end 
  
  lemma factory.var_rc {ε : env SymV} {σ : state SymB} {y : ℕ} {e : lang.env D O} {r : lang.result D O}
  (hy : y < ε.length)
  (hn : (state.normal f.to_has_eval m σ))
  (hε : env.eval f.to_has_eval m ε = e)
  (hr : result.eval f.to_has_eval m (result.ans σ (ε.nth_le y hy)) = r) :
  evalC f.opC (exp.var y) e r := 
  begin 
    rcases (env.eval_nth_le f.to_has_eval hy hε) with ⟨hy', he⟩,
    simp only [result.eval, he, hn, if_true] at hr, 
    rewrite ←hr,
    apply evalC.var, 
  end 

  lemma factory.compose_normal_any (σ σ' : state SymB) :
  σ.normal f.to_has_eval m → (f.compose σ σ').eqv f.to_has_eval m σ' := 
  begin 
    simp only [state.normal, factory.compose, state.eqv, and_imp, bool.to_bool_and, bool.to_bool_coe, band_coe_iff],
    intros h1 h2,
    simp only [f.and_sound, f.imp_sound, h1, h2, true_and, eq_self_iff_true, bool.to_bool_coe, forall_true_left], 
  end 

  lemma factory.halted_is_abnormal {σ : state SymB} : 
  f.halted σ → ¬ σ.normal f.to_has_eval m := 
  begin 
    simp only [factory.halted, state.normal, eq_ff_eq_not_eq_tt, bor_coe_iff, not_and, bool.to_bool_and, bool.to_bool_coe, band_coe_iff],
    intros h1 h2,
    cases h1;
    rewrite f.is_ff_sound at h1; 
    apply_fun (f.evalB m) at h1; 
    simp only [f.mk_ff_sound] at h1,
    { simp only [h1, coe_sort_ff] at h2,
      contradiction,},
    { exact h1, } 
  end 

  lemma factory.eval_strengthen_normal {σ : state SymB} {ρ : result SymB SymV} 
  (hn : (state.normal f.to_has_eval m σ)) :
  result.eval f.to_has_eval m (f.strengthen σ ρ) = result.eval f.to_has_eval m ρ := 
  begin 
    cases ρ with σ' v' σ',
    { rcases (f.compose_normal_any σ σ' hn) with hc,
      simp only [factory.strengthen, factory.halt_or_ans],
      split_ifs,
      { simp only [result.eval],
        rcases (@factory.halted_is_abnormal Model SymB SymV D O _ _ f m (f.compose σ σ') h) with hnc,
        rcases (state.eqv_abnormal f.to_has_eval hnc hc) with hn',
        simp only [hn', if_false],
        apply state.eqv_aborted f.to_has_eval hc, },
      { simp only [result.eval],
        cases hnc : (state.normal f.to_has_eval m (f.compose σ σ')),
        { rewrite ←bool_iff_false at hnc,
          rcases (state.eqv_abnormal f.to_has_eval hnc hc) with hn',
          simp only [hn', if_false, coe_sort_ff],  
          apply state.eqv_aborted f.to_has_eval hc, }, 
        { rcases (state.eqv_normal f.to_has_eval hnc hc) with hn',
          simp only [hn', if_true, coe_sort_tt], } } },
    { rcases (f.compose_normal_any σ σ' hn) with hc,
      simp only [factory.strengthen, result.eval, state.aborted, eq_ff_eq_not_eq_tt, bool.to_bool_eq],
      simp only [state.eqv] at hc,
      simp only [hc, iff_self], } 
  end 

  lemma factory.app_rc {ε : env SymV} {σ : state SymB} {o : O} {xs : list ℕ} {vs : list SymV}
  {e : lang.env D O} {r : lang.result D O} 
  (h1 : xs.length = vs.length)
  (h2 : ∀ (i : ℕ) (hx : i < xs.length) (hv : i < vs.length), evalS f (exp.var (xs.nth_le i hx)) ε σ (result.ans σ (vs.nth_le i hv)))
  (ih: ∀ (i : ℕ) (hx : i < xs.length) (hv : i < vs.length), (λ {x : exp D O} {ε : env SymV} {σ : state SymB} {ρ : result SymB SymV} (hs : evalS f x ε σ ρ), (state.normal f.to_has_eval m σ) → ∀ {e : lang.env D O} {r : lang.result D O}, env.eval f.to_has_eval m ε = e → result.eval f.to_has_eval m ρ = r → evalC f.opC x e r) (h2 i hx hv))
  (hn : (state.normal f.to_has_eval m σ))
  (hε : env.eval f.to_has_eval m ε = e)
  (hr : result.eval f.to_has_eval m (f.strengthen σ (f.opS o vs)) = r) : 
  evalC f.opC (exp.app o xs) e r := 
  begin 
    rewrite f.eval_strengthen_normal hn at hr,
    rcases (f.opS_sound m o vs) with ⟨hos, _⟩,
    rewrite [←hr, hos],
    apply evalC.app,
    { simp only [h1, list.length_map], },
    { intros i hx hw,
      specialize @ih i hx (by { rewrite ←h1, exact hx, }) hn e (lang.result.ans ((list.map (f.to_has_eval.evalV m) vs).nth_le i hw)) hε,
      apply ih, 
      apply result.eval_ans f.to_has_eval hn, 
      simp only [list.nth_le_map'], } 
  end 

  lemma factory.not_some_cast_not_clos {c : SymV} {w : lang.val D O} 
  (hf : f.to_has_eval.evalB m (f.some choice.guard (f.cast c)) = ff) 
  (hw : f.to_has_eval.evalV m c = w): 
  ¬(w.is_clos) := 
  begin 
    rcases (f.cast_sound m c) with ⟨hcs1, _⟩,
    rewrite hw at hcs1,
    by_contradiction,
    specialize hcs1 h,
    cases hcs1 with hcs1 _,
    simp only [f.some_eq_any] at hf,
    rewrite ← bool_iff_false at hf,
    rcases (choices.not_some_is_none (has_eval_clos f.to_has_eval) hf) with hf',
    simp only [choices.one, choices.none] at hf' hcs1,
    simp only [hcs1, nat.one_ne_zero] at hf',
    contradiction
  end 

  lemma factory.call_sym_cast {c : SymV} {w : lang.val D O} {i : ℕ} (hi : i < (f.cast c).length) :
  f.evalV m c = w → 
  (f.cast c).filter (λ (gv : choice SymB (clos D O SymV)), f.evalB m gv.guard) = [(f.cast c).nth_le i hi] → 
  ∃ e,  ((f.cast c).nth_le i hi).value.env.eval f.to_has_eval m = e ∧ 
        w = lang.val.clos ((f.cast c).nth_le i hi).value.var ((f.cast c).nth_le i hi).value.exp e := 
  begin 
    intros hw hf,
    have h1 : ((f.cast c).one f.to_has_eval m) := by 
    { apply choices.filter_implies_one (has_eval_clos f.to_has_eval), 
      apply exists.intro i, apply exists.intro hi, exact hf, },
    rcases (f.cast_sound m c) with ⟨hsc1, hsc2⟩,
    rewrite ←hw,
    apply exists.intro (env.eval f.to_has_eval m (list.nth_le (f.cast c) i hi).value.env),
    simp only [true_and, eq_self_iff_true],
    cases (f.to_has_eval.evalV m c).is_clos,
    { simp only [choices.none, choices.true, has_eval_clos, forall_true_left, not_false_iff, coe_sort_ff] at hsc2,
      simp only [choices.one, choices.true, hsc2, nat.zero_ne_one] at h1,
      contradiction, },
    { simp only [coe_sort_tt, forall_true_left] at hsc1,
      rcases hsc1 with ⟨_, hsc1⟩,
      rewrite ←hsc1,
      rcases (choices.filter_one_eval (has_eval_clos f.to_has_eval) (f.to_has_eval.evalV m c) hf) with hfc,
      rewrite hfc,
      simp only [has_eval_clos, clos.eval, eq_self_iff_true, and_self], } 
  end

  lemma factory.call_sym_same_idx 
  {gvs : choices SymB (clos D O SymV)} {grs : choices SymB (result SymB SymV)} 
  {i : ℕ} (hv : i < gvs.length) (hr : i < grs.length) : 
  gvs.map choice.guard = grs.map choice.guard →
  gvs.filter (λ gv, f.evalB m gv.guard) = [gvs.nth_le i hv] → 
  grs.filter (λ gv, f.evalB m gv.guard) = [grs.nth_le i hr] := 
  begin
    intros heq hfv,
    have hv1 : (gvs.one f.to_has_eval m) := by 
    { apply choices.filter_implies_one (has_eval_clos f.to_has_eval), 
      apply exists.intro i, apply exists.intro hv, exact hfv, },
    rcases (choices.eq_one (has_eval_result f.to_has_eval) heq hv1) with hfr,
    rewrite choices.one_iff_filter at hfr,
    rcases hfr with ⟨j, hj, hfr⟩,
    simp only [has_eval_result] at hfr,
    rewrite hfr,
    congr,
    by_contradiction,
    rewrite ←ne.def at h,
    rcases (choices.filter_one_guard (has_eval_clos f.to_has_eval) hfv) with hi,
    simp only [has_eval_clos] at hi,
    rcases (choices.filter_one_rest (has_eval_result f.to_has_eval) hj hr hfr h) with hi',
    simp only [has_eval_result, eq_ff_eq_not_eq_tt] at hi',
    have hh : i < (list.map choice.guard gvs).length := by { simp only [hv, list.length_map], },
    rcases (list.nth_le_of_eq heq hh) with heq_i,
    simp only [list.nth_le_map'] at heq_i,
    simp only [heq_i, hi', coe_sort_ff] at hi,
    contradiction, 
  end

  lemma factory.call_sym_rc {ε : env SymV} {σ σ' : state SymB} {x1 x2 : ℕ} {c v: SymV} 
  {grs : choices SymB (result SymB SymV)} {e : lang.env D O} {r : lang.result D O}   
  (h1 : evalS f (exp.var x1) ε σ (result.ans σ c))
  (h2 : evalS f (exp.var x2) ε σ (result.ans σ v))
  (h3 : σ' = f.assert σ (f.some choice.guard (f.cast c)))
  (h4 : ¬↥(f.is_ff (f.some choice.guard (f.cast c))) ∧ ¬↥(f.halted σ'))
  (h5 : list.map choice.guard (f.cast c) = list.map choice.guard grs)
  (h6 : ∀ (i : ℕ) (hc : i < list.length (f.cast c)) (hr : i < list.length grs), evalS f (list.nth_le (f.cast c) i hc).value.exp (list.update_nth (list.nth_le (f.cast c) i hc).value.env (list.nth_le (f.cast c) i hc).value.var v) (f.assume σ' (list.nth_le (f.cast c) i hc).guard) (list.nth_le grs i hr).value)
  (ih1: (state.normal f.to_has_eval m σ) → ∀ {e : lang.env D O} {r : lang.result D O}, env.eval f.to_has_eval m ε = e → result.eval f.to_has_eval m (result.ans σ c) = r → evalC f.opC (exp.var x1) e r)
  (ih2: (state.normal f.to_has_eval m σ) → ∀ {e : lang.env D O} {r : lang.result D O}, env.eval f.to_has_eval m ε = e → result.eval f.to_has_eval m (result.ans σ v) = r → evalC f.opC (exp.var x2) e r)
  (ih6: ∀ (i : ℕ) (hc : i < list.length (f.cast c)) (hr : i < list.length grs), (λ {x : exp D O} {ε : env SymV} {σ : state SymB} {ρ : result SymB SymV} (hs : evalS f x ε σ ρ), (state.normal f.to_has_eval m σ) → ∀ {e : lang.env D O} {r : lang.result D O}, env.eval f.to_has_eval m ε = e → result.eval f.to_has_eval m ρ = r → evalC f.opC x e r) (h6 i hc hr))
  (hn : (state.normal f.to_has_eval m σ))
  (hε : env.eval f.to_has_eval m ε = e)
  (hr : result.eval f.to_has_eval m (f.merge_ρ σ' grs) = r) :
  evalC f.opC (exp.call x1 x2) e r := 
  begin 
    rcases (f.normal_ans_rc c hn) with ⟨w1, hw1, h1e⟩,
    rcases (f.normal_ans_rc v hn) with ⟨w2, hw2, h2e⟩,
    specialize ih1 hn hε h1e,
    specialize ih2 hn hε h2e,
    have hlen : (f.cast c).length = grs.length := by { apply_fun list.length at h5, simp only [list.length_map] at h5, exact h5, },
    cases hgc : (f.evalB m (f.some choice.guard (f.cast c))),
    { have hf : ↥(state.errored f.to_has_eval m σ') := by 
      { simp only [state.normal, bool.to_bool_and, bool.to_bool_coe, band_coe_iff] at hn,
        simp only [h3, factory.assert, state.errored, hn, f.and_sound, f.imp_sound, hgc, true_and, eq_ff_eq_not_eq_tt, bool.of_to_bool_iff, forall_true_left, not_false_iff], },
      rcases (state.errored_not_normal f.to_has_eval hf) with hn',
      rewrite ←bool_iff_false at hn',
      have hh : state.eqv f.to_has_eval m (f.merge_ρ σ' grs).state σ' := by 
      { apply f.merge_ρ_eqp,
        intros i hi, 
        have hic : i < (f.cast c).length := by { simp only [hlen, hi], },
        specialize h6 i hic hi, 
        have heq : state.eqv f.to_has_eval m (f.assume σ' (list.nth_le (f.cast c) i hic).guard) σ' := by {apply f.assume_hp hn',},
        transitivity (f.assume σ' (list.nth_le (f.cast c) i hic).guard),
        { apply svm_hp f _ h6, apply state.eqv_abnormal f.to_has_eval hn', symmetry, exact heq, },
        { exact heq, } },
      rcases (state.eqv_abnormal f.to_has_eval hn' (state.eqv.symm f.to_has_eval m hh)) with hnm,
      rewrite ←hr, rewrite result.eval_halt f.to_has_eval hnm, 
      rewrite state.eqv_aborted f.to_has_eval hh,
      rewrite state.errored_not_aborted f.to_has_eval hf,
      rewrite ←lang.err,
      apply evalC.call_halt ih1 ih2,
      apply f.not_some_cast_not_clos hgc hw1, },
    { rewrite bool.tt_eq_true at hgc,
      rcases (f.assert_normal_true hn hgc) with hn', rewrite ←h3 at hn',
      rcases (f.assert_some_cast_one hn hn' h3) with h_one,
      rcases (choices.one_implies_filter (has_eval_clos f.to_has_eval) h_one) with ⟨i, hic, hfc⟩,
      simp only [has_eval_clos] at hfc,
      have hig : i < list.length grs :=  by { rewrite ←hlen, exact hic, },
      rcases (f.call_sym_same_idx hic hig h5 hfc) with hfg,
      have hl : ↥(result.legal f.to_has_eval m (list.nth_le grs i hig).value) := by
      { specialize h6 i hic hig,
        apply svm_lgl f _ h6,
        apply f.assume_lgl,
        apply state.normal_is_legal f.to_has_eval hn', },
      rcases (f.merge_ρ_normal_eval hn' hfg hl) with hm,
      rewrite [←hr, hm],
      rcases (f.call_sym_cast hic hw1 hfc) with ⟨ce, hce, hcw1⟩,
      simp only [hcw1] at ih1,
      apply evalC.call ih1 ih2,
      apply ih6 i hic hig _ _ rfl,
      { apply f.assume_normal_true hn', apply choices.filter_one_guard (has_eval_clos f.to_has_eval) hfc, },
      { apply env.eval_update f.to_has_eval, exact hce, exact hw2, }, }
  end 

  lemma factory.call_halt_rc {ε : env SymV} {σ σ' : state SymB} {x1 x2 : ℕ} {c v: SymV} 
  {e : lang.env D O} {r : lang.result D O}   
  (h1 : evalS f (exp.var x1) ε σ (result.ans σ c))
  (h2 : evalS f (exp.var x2) ε σ (result.ans σ v))
  (h3 : σ' = f.assert σ (f.some choice.guard (f.cast c)))
  (h4 : ↥(f.is_ff (f.some choice.guard (f.cast c))) ∨ ↥(f.halted σ'))
  (ih1: (state.normal f.to_has_eval m σ) → ∀ {e : lang.env D O} {r : lang.result D O}, env.eval f.to_has_eval m ε = e → result.eval f.to_has_eval m (result.ans σ c) = r → evalC f.opC (exp.var x1) e r)
  (ih2: (state.normal f.to_has_eval m σ) → ∀ {e : lang.env D O} {r : lang.result D O}, env.eval f.to_has_eval m ε = e → result.eval f.to_has_eval m (result.ans σ v) = r → evalC f.opC (exp.var x2) e r)
  (hn : (state.normal f.to_has_eval m σ))
  (hε : env.eval f.to_has_eval m ε = e)
  (hr : result.eval f.to_has_eval m (result.halt σ') = r) :
  evalC f.opC (exp.call x1 x2) e r := 
  begin 
    rcases (f.normal_ans_rc c hn) with ⟨w1, hw1, h1e⟩,
    rcases (f.normal_ans_rc v hn) with ⟨w2, hw2, h2e⟩,
    specialize ih1 hn hε h1e,
    specialize ih2 hn hε h2e,
    rewrite ←hr, 
    simp only [result.eval], 
    simp only [state.normal, bool.to_bool_and, bool.to_bool_coe, band_coe_iff] at hn,
    have hf : f.to_has_eval.evalB m (f.some choice.guard (f.cast c)) = ff := by 
    { cases h4,
      { simp only [f.is_ff_sound] at h4, 
        simp only [h4, f.mk_ff_sound],  },
      { simp only [factory.halted, h3, factory.assert, bor_coe_iff] at h4,
        cases h4; simp only [f.is_ff_sound] at h4; apply_fun (f.evalB m) at h4,
        { simp only [f.mk_ff_sound] at h4,
          simp only [h4, coe_sort_ff, false_and] at hn,
          contradiction, },
        { simp only [f.and_sound, hn, f.imp_sound, f.mk_ff_sound, true_and, bool.to_bool_coe, forall_true_left] at h4, 
          exact h4, } } },
    have hh : ↥(state.errored f.to_has_eval m σ') := by { simp only [h3, factory.assert, state.errored, hn, f.and_sound, f.imp_sound, hf, true_and, eq_ff_eq_not_eq_tt, bool.of_to_bool_iff, forall_true_left], },
    rcases (state.errored_not_aborted f.to_has_eval hh) with hh',
    simp only [hh'], rewrite ←lang.err,
    apply evalC.call_halt ih1 ih2,
    apply f.not_some_cast_not_clos hf hw1, 
  end 

  lemma factory.let0_rc {ε : env SymV} {σ σ' : state SymB} {y : ℕ} {x1 x2 : exp D O} 
  {v : SymV} {ρ : result SymB SymV} {e : lang.env D O} {r : lang.result D O} 
  (h1 : evalS f x1 ε σ (result.ans σ' v))
  (h2 : evalS f x2 (list.update_nth ε y v) σ' ρ)
  (ih1: (state.normal f.to_has_eval m σ) → ∀ {e : lang.env D O} {r : lang.result D O}, env.eval f.to_has_eval m ε = e → result.eval f.to_has_eval m (result.ans σ' v) = r → evalC f.opC x1 e r)
  (ih2: (state.normal f.to_has_eval m σ') → ∀ {e : lang.env D O} {r : lang.result D O}, env.eval f.to_has_eval m (list.update_nth ε y v) = e → result.eval f.to_has_eval m ρ = r → evalC f.opC x2 e r)
  (hn : (state.normal f.to_has_eval m σ))
  (hε : env.eval f.to_has_eval m ε = e) 
  (hr : result.eval f.to_has_eval m ρ = r) :
  evalC f.opC (exp.let0 y x1 x2) e r := 
  begin 
    cases hn' : (σ'.normal f.to_has_eval m), 
    { rewrite ←bool_iff_false at hn',
      have hnv : ¬ (result.ans σ' v).state.normal f.to_has_eval m := by { simp only [result.state, hn', not_false_iff], },
      rcases (result.eval_halt f.to_has_eval hnv) with hrv,
      rcases (svm_hp f hn' h2) with hρ,
      have hnρ : ¬ ρ.state.normal f.to_has_eval m := by { apply state.eqv_abnormal f.to_has_eval hn', symmetry, exact hρ, },
      rcases (result.eval_halt f.to_has_eval hnρ) with hρv,
      rcases (state.eqv_aborted f.to_has_eval hρ) with heq,
      specialize ih1 hn hε hrv, 
      simp only [result.state] at ih1,
      rewrite ←hr, 
      simp only [hρv, heq],
      apply evalC.let0_halt ih1, }, 
    { rewrite bool.tt_eq_true at hn',
      rcases (f.normal_ans_rc v hn') with ⟨w, hw, h1r⟩,
      rcases (env.eval_update f.to_has_eval y hε hw) with hup,
      specialize @ih1 hn e (lang.result.ans w) hε h1r,
      specialize @ih2 hn' (list.update_nth e y w) r hup hr,
      apply evalC.let0 ih1 ih2, } 
  end 

  lemma factory.let0_halt_rc {ε : env SymV} {σ σ' : state SymB} {y : ℕ} {x1 x2 : exp D O} {e : lang.env D O} {r : lang.result D O} 
  (h1 : evalS f x1 ε σ (result.halt σ')) 
  (ih : (state.normal f.to_has_eval m σ) → ∀ {e : lang.env D O} {r : lang.result D O}, env.eval f.to_has_eval m ε = e → result.eval f.to_has_eval m (result.halt σ') = r → evalC f.opC x1 e r)
  (hn : (state.normal f.to_has_eval m σ))
  (hε : env.eval f.to_has_eval m ε = e)  
  (hr : result.eval f.to_has_eval m (result.halt σ') = r) :
  evalC f.opC (exp.let0 y x1 x2) e r := 
  begin 
    specialize @ih hn e r hε hr,
    simp only [result.eval] at hr,
    rewrite ←hr, rewrite ←hr at ih,
    apply evalC.let0_halt ih, 
  end 

  lemma factory.if0_sym_rc {ε : env SymV} {σ : state SymB} {xc : ℕ} {xt xf : exp D O} {v : SymV} 
  {rt rf : result SymB SymV} {e : lang.env D O} {r : lang.result D O}
  (hc : evalS f (exp.var xc) ε σ (result.ans σ v))
  (hv : ¬↥(f.is_tt (f.truth v)) ∧ ¬↥(f.is_ff (f.truth v)))
  (ht : evalS f xt ε (f.assume σ (f.truth v)) rt)
  (hf : evalS f xf ε (f.assume σ (f.not (f.truth v))) rf)
  (ihc: (state.normal f.to_has_eval m σ) → ∀ {e : lang.env D O} {r : lang.result D O}, env.eval f.to_has_eval m ε = e → result.eval f.to_has_eval m (result.ans σ v) = r → evalC f.opC (exp.var xc) e r)
  (iht: (state.normal f.to_has_eval m (f.assume σ (f.truth v))) → ∀ {e : lang.env D O} {r : lang.result D O}, env.eval f.to_has_eval m ε = e → result.eval f.to_has_eval m rt = r → evalC f.opC xt e r)
  (ihf: (state.normal f.to_has_eval m (f.assume σ (f.not (f.truth v)))) → ∀ {e : lang.env D O} {r : lang.result D O}, env.eval f.to_has_eval m ε = e → result.eval f.to_has_eval m rf = r → evalC f.opC xf e r)
  (hn : (state.normal f.to_has_eval m σ))
  (hε : env.eval f.to_has_eval m ε = e)
  (hr : result.eval f.to_has_eval m (f.merge_ρ σ [{guard := f.truth v, value := rt}, {guard := f.not (f.truth v), value := rf}]) = r) :
  evalC f.opC (exp.if0 xc xt xf) e r := 
  begin
    rcases (f.normal_ans_rc v hn) with ⟨w, hw, hce⟩,
    specialize (@ihc hn e (lang.result.ans w) hε hce),  
    rcases (f.truth_sound m v) with hbv,
    rewrite ←hr,
    cases hb : (f.evalB m (f.truth v)),
    { rewrite ←bool_iff_false at hb,
      rcases (f.not_sound m (f.truth v)) with hb',
      simp only [hb, to_bool_true_eq_tt, coe_sort_tt, iff_true, not_false_iff] at hb',
      rcases (f.assume_normal_true hn hb') with hn',
      have h : list.filter (λ (gv : choice SymB (result SymB SymV)), f.evalB m gv.guard) [choice.mk (f.truth v) rt, choice.mk (f.not (f.truth v)) rf] = [⟨f.not (f.truth v), rf⟩] := 
      by { simp only [list.filter, hb, hb', if_true, eq_self_iff_true, if_false, and_self, coe_sort_tt], },
      have hl : ↥((choice.mk (f.not (f.truth v)) rf).value.legal f.to_has_eval m) := 
      by { simp only, apply svm_lgl f (state.normal_is_legal f.to_has_eval hn') hf, },
      rcases (f.merge_ρ_normal_eval hn h hl) with hrf,
      simp only at hrf,
      specialize ihf hn' hε (eq.symm hrf),
      apply evalC.if0_false ihc _ ihf,
      simp only [hbv, hw, not_not] at hb, 
      exact hb, },
    { rewrite bool.tt_eq_true at hb,
      rcases (f.assume_normal_true hn hb) with hn',
      have h : list.filter (λ (gv : choice SymB (result SymB SymV)), f.evalB m gv.guard) [choice.mk (f.truth v) rt, choice.mk (f.not (f.truth v)) rf] = [⟨f.truth v, rt⟩] := 
      by { simp only [list.filter, hb, f.not_sound, to_bool_false_eq_ff, if_true, eq_self_iff_true, not_true, if_false, and_self, coe_sort_ff], },
      have hl : ↥((choice.mk (f.truth v) rt).value.legal f.to_has_eval m) := 
      by { simp only, apply svm_lgl f (state.normal_is_legal f.to_has_eval hn') ht, },
      rcases (f.merge_ρ_normal_eval hn h hl) with hrt,
      simp only at hrt,
      specialize iht hn' hε (eq.symm hrt),
      apply evalC.if0_true ihc _ iht,
      rewrite [hbv, hw] at hb,
      exact hb, }
  end 

  lemma factory.if0_true_rc {ε : env SymV} {σ : state SymB} {xc : ℕ} {xt xf : exp D O} {v : SymV} {ρ : result SymB SymV}
  {e : lang.env D O} {r : lang.result D O}
  (hc : evalS f (exp.var xc) ε σ (result.ans σ v))
  (hv : (f.is_tt (f.truth v)))
  (hr : evalS f xt ε σ ρ)
  (ihc: (state.normal f.to_has_eval m σ) → ∀ {e : lang.env D O} {r : lang.result D O}, env.eval f.to_has_eval m ε = e → result.eval f.to_has_eval m (result.ans σ v) = r → evalC f.opC (exp.var xc) e r)
  (ihr: (state.normal f.to_has_eval m σ) → ∀ {e : lang.env D O} {r : lang.result D O}, env.eval f.to_has_eval m ε = e → result.eval f.to_has_eval m ρ = r → evalC f.opC xt e r)
  (hn : (state.normal f.to_has_eval m σ))
  (hε : env.eval f.to_has_eval m ε = e)
  (hr : result.eval f.to_has_eval m ρ = r) : 
  evalC f.opC (exp.if0 xc xt xf) e r :=
  begin
    rcases (f.normal_ans_rc v hn) with ⟨w, hw, hce⟩,
    specialize (@ihc hn e (lang.result.ans w) hε hce),  
    specialize (@ihr hn e r hε hr),
    apply evalC.if0_true ihc _ ihr,
    rcases (f.truth_sound m v) with ht,
    rewrite [←hw, ←ht],
    rewrite [f.is_tt_sound] at hv,
    apply_fun (f.evalB m) at hv,
    simp only [f.mk_tt_sound] at hv,
    simp only [hv, coe_sort_tt],  
  end 

  lemma factory.if0_false_rc {ε : env SymV} {σ : state SymB} {xc : ℕ} {xt xf : exp D O} {v : SymV} {ρ : result SymB SymV}
  {e : lang.env D O} {r : lang.result D O}
  (hc : evalS f (exp.var xc) ε σ (result.ans σ v))
  (hv : (f.is_ff (f.truth v)))
  (hr : evalS f xf ε σ ρ)
  (ihc: (state.normal f.to_has_eval m σ) → ∀ {e : lang.env D O} {r : lang.result D O}, env.eval f.to_has_eval m ε = e → result.eval f.to_has_eval m (result.ans σ v) = r → evalC f.opC (exp.var xc) e r)
  (ihr: (state.normal f.to_has_eval m σ) → ∀ {e : lang.env D O} {r : lang.result D O}, env.eval f.to_has_eval m ε = e → result.eval f.to_has_eval m ρ = r → evalC f.opC xf e r)
  (hn : (state.normal f.to_has_eval m σ))
  (hε : env.eval f.to_has_eval m ε = e)
  (hr : result.eval f.to_has_eval m ρ = r) : 
  evalC f.opC (exp.if0 xc xt xf) e r :=
  begin
    rcases (f.normal_ans_rc v hn) with ⟨w, hw, hce⟩,
    specialize (@ihc hn e (lang.result.ans w) hε hce),  
    specialize (@ihr hn e r hε hr),
    apply evalC.if0_false ihc _ ihr,
    rcases (f.truth_sound m v) with ht,
    rewrite [f.is_ff_sound] at hv,
    apply_fun (f.evalB m) at hv,
    simp only [f.mk_ff_sound] at hv,
    simp only [hw, hv, false_iff, not_not, coe_sort_ff] at ht,
    exact ht, 
  end 
 

  lemma factory.error_rc {ε : env SymV} {σ : state SymB} {e : lang.env D O} {r : lang.result D O}
  (hn : (state.normal f.to_has_eval m σ))
  (hε : env.eval f.to_has_eval m ε = e)
  (hr : result.eval f.to_has_eval m (result.halt (f.assert σ f.mk_ff)) = r) :
  evalC f.opC exp.error e r := 
  begin 
    simp only [state.normal, bool.to_bool_and, bool.to_bool_coe, band_coe_iff] at hn,
    simp only [result.eval, state.aborted, factory.assert, hn, to_bool_false_eq_ff, not_true, false_and] at hr,
    rewrite ←hr, 
    apply evalC.error, 
  end 

  lemma factory.abort_rc {ε : env SymV} {σ : state SymB} {e : lang.env D O} {r : lang.result D O}
  (hn : (state.normal f.to_has_eval m σ))
  (hε : env.eval f.to_has_eval m ε = e)
  (hr : result.eval f.to_has_eval m (result.halt (f.assume σ f.mk_ff)) = r) :
  evalC f.opC exp.abort e r := 
  begin 
    simp only [state.normal, bool.to_bool_and, bool.to_bool_coe, band_coe_iff] at hn,
    simp only [result.eval, state.aborted, factory.assume, hn, f.and_sound, f.imp_sound, f.mk_ff_sound, to_bool_false_eq_ff,
               to_bool_true_eq_tt, forall_true_left, not_false_iff, and_self, and_false, coe_sort_ff] at hr,
    rewrite ←hr, 
    apply evalC.abort, 
  end 

  -- The SVM rules are relatively complete with respect to the concrete 
  -- semantics: if the SVM terminates on a well-formed input state σ 
  -- and well-formed symbolic environment ε to produce a result ρ, 
  -- then for any model m under which σ is normal and ε evaluates to 
  -- the concrete environment e = ε.eval m, executing the concrete semantics on 
  -- e terminates and leads to a result r if r = ρ.eval m.
  theorem svm_rc {x : exp D O} {ε : env SymV} {e : lang.env D O} 
  {σ : state SymB} {ρ : result SymB SymV} {r : lang.result D O} :
  σ.normal f.to_has_eval m → ε.eval f.to_has_eval m = e → evalS f x ε σ ρ → 
  ρ.eval f.to_has_eval m = r → evalC f.opC x e r :=
  begin 
    intros hn hε hs hr,
    induction hs generalizing e r,
    case sym.evalS.bool {
      simp only [result.eval, f.bval_sound, hn, if_true] at hr,
      rewrite ←hr, apply evalC.bool, },
    case sym.evalS.datum {
      simp only [result.eval, f.dval_sound, hn, if_true] at hr,
      rewrite ←hr, apply evalC.datum, }, 
    case sym.evalS.lam {
      simp only [result.eval, f.cval_sound, hn, clos.eval, hε, coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe, if_true] at hr,
      rewrite ←hr, apply evalC.lam, },
    case sym.evalS.var       { apply f.var_rc hs_hy hn hε hr, },
    case sym.evalS.app       { apply f.app_rc hs_h1 hs_h2 hs_ih hn hε hr, },
    case sym.evalS.call_sym  { apply f.call_sym_rc hs_h1 hs_h2 hs_h3 hs_h4 hs_h5 hs_h6 hs_ih_h1 hs_ih_h2 hs_ih_h6 hn hε hr,  },
    case sym.evalS.call_halt { apply f.call_halt_rc hs_h1 hs_h2 hs_h3 hs_h4 hs_ih_h1 hs_ih_h2 hn hε hr, },
    case sym.evalS.let0      { apply f.let0_rc hs_h1 hs_h2 hs_ih_h1 hs_ih_h2 hn hε hr, },
    case sym.evalS.let0_halt { apply f.let0_halt_rc hs_h1 hs_ih hn hε hr, },
    case sym.evalS.if0_true  { apply f.if0_true_rc hs_hc hs_hv hs_hr hs_ih_hc hs_ih_hr hn hε hr, },
    case sym.evalS.if0_false { apply f.if0_false_rc hs_hc hs_hv hs_hr hs_ih_hc hs_ih_hr hn hε hr, },
    case sym.evalS.if0_sym   { apply f.if0_sym_rc hs_hc hs_hv hs_ht hs_hf hs_ih_hc hs_ih_ht hs_ih_hf hn hε hr,  },
    case sym.evalS.error     { apply f.error_rc hn hε hr },
    case sym.evalS.abort     { apply f.abort_rc hn hε hr }, 
  end 

  -- The SVM rules are relatively sound and complete with respect to the concrete 
  -- semantics: if the SVM terminates on a well-formed input state σ 
  -- and symbolic environment ε to produce a result ρ, 
  -- then for any model m under which σ is normal and ε evaluates to 
  -- the concrete environment e = ε.eval m, executing the concrete semantics on 
  -- e terminates and leads to a result r if and only if r = ρ.eval m.
  theorem svm_rsc {x : exp D O} {ε : env SymV} {e : lang.env D O} 
  {σ : state SymB} {ρ : result SymB SymV} {r : lang.result D O} :
  σ.normal f.to_has_eval m → ε.eval f.to_has_eval m = e → evalS f x ε σ ρ → 
  (evalC f.opC x e r ↔ ρ.eval f.to_has_eval m = r) :=
  begin 
    intros hn hε hs,
    constructor,
    { intro hrc,
      rcases (svm_rc f hn hε hs rfl) with hr,
      apply evalC_det hr hrc, }, 
    { apply svm_rc f hn hε hs, }
  end 

end rsc

end sym