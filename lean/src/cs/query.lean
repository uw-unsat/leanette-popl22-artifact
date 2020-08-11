import tactic.basic
import tactic.split_ifs
import tactic.linarith
import tactic.apply_fun
import .lang
import .sym
import .svm
import .lib
import .lgl
import .rsc

namespace lang 

  def result.normal {D O : Type} : result D O → bool 
  | (result.ans _) := tt 
  | _              := ff

  def result.errors {D O : Type} : result D O → bool 
  | (result.halt ff) := tt 
  | _                := ff

  def result.aborts {D O : Type} : result D O → bool 
  | (result.halt tt) := tt 
  | _                := ff

end lang 

namespace sym 

  inductive decision (μ : Type) : Type
  | sat     : μ → decision 
  | unsat   : decision 
  | diverge : decision 


section queries 

  open decision
  open lang

  variables {Model SymB SymV D O : Type}
  [inhabited Model] [inhabited SymV]
  (f : factory Model SymB SymV D O)

  -- We model the solver as a function from SymB to a decision. The 
  -- solver may not able to decide if a given b is sat or unsat, in 
  -- which case, the solver returns diverge. But if it returns sat or 
  -- unsat, then the result must represent real models or lack thereof.
  structure solver := 
  (decide      : SymB → decision Model)
  (sat_sound   : ∀ (b : SymB) (m : Model), decide b = sat m → f.evalB m b = tt)
  (unsat_sound : ∀ (b : SymB), decide b = unsat → ∀ (m : Model), f.evalB m b = ff)

  -- We model the symbolic evaluator as a function from programs and symbolic environments 
  -- maybe Results. The evaluator is assumed to implement evalS.
  structure evaluator := 
  (eval  : (lang.exp D O) → env SymV → option (result SymB SymV))
  (impl  : ∀ (x : lang.exp D O) (ε : env SymV) (ρ : result SymB SymV),  
             (eval x ε) = ρ → evalS f x ε ⟨f.mk_tt, f.mk_tt⟩ ρ)
  
  def lower (ε : env SymV) : decision Model → decision (lang.env D O)
  | (sat m) := sat (ε.eval f.to_has_eval m)
  | unsat   := unsat 
  | diverge := diverge 

  def guess (se : evaluator f) (slv : solver f) (x : lang.exp D O) (ε : env SymV) : 
  decision (lang.env D O) := 
  match (se.eval x ε) with 
  | none   := diverge 
  | some ρ := lower f ε (slv.decide (f.and ρ.state.assumes ρ.state.asserts)) 
  end  

  def verify (se : evaluator f) (slv : solver f) (x : lang.exp D O) (ε : env SymV) : 
  decision (lang.env D O) := 
  match (se.eval x ε) with 
  | none   := diverge 
  | some ρ := lower f ε (slv.decide (f.and ρ.state.assumes (f.not ρ.state.asserts))) 
  end  
  
  lemma guess_sat_domain {se : evaluator f} {slv : solver f} 
  {x : lang.exp D O} {ε : env SymV} {e : lang.env D O}:
  guess f se slv x ε = sat e → ∃ m, ε.eval f.to_has_eval m = e := 
  begin 
    intro h,
    simp only [guess] at h,
    cases (se.eval x ε) with ρ;
    simp only [guess] at h,
    contradiction,
    cases (slv.decide (f.and ρ.state.assumes ρ.state.asserts)) with m;
    simp only [lower] at h,
    any_goals { contradiction },
    apply exists.intro m,
    exact h, 
  end 

  lemma guess_sat_correct {se : evaluator f} {slv : solver f} 
  {x : lang.exp D O} {ε : env SymV} {e : lang.env D O}:
  guess f se slv x ε = sat e → 
  ∃ (r : lang.result D O), evalC f.opC x e r ∧ r.normal := 
  begin 
    intro h,
    simp only [guess] at h,
    cases hse : (se.eval x ε) with ρ;
    rewrite hse at h; 
    simp only [guess] at h,
    contradiction,
    cases hslv : (slv.decide (f.and ρ.state.assumes ρ.state.asserts)) with m; 
    rewrite hslv at h; 
    simp only [lower] at h,
    any_goals { contradiction },
    rcases (slv.sat_sound (f.and ρ.state.assumes ρ.state.asserts) m hslv) with hsat,
    simp only [f.and_sound, band_eq_true_eq_eq_tt_and_eq_tt, bool.to_bool_and, bool.to_bool_coe] at hsat,
    rcases (se.impl x ε ρ hse) with hs,
    rcases (svm_lgl f (@top_legal Model SymB SymV D O _ _ f m) hs) with hlgl,
    apply exists.intro (ρ.eval f.to_has_eval m),
    constructor,
    { rewrite svm_rsc f (@top_normal Model SymB SymV D O _ _  f m) h hs, },
    { have hn : ↥(ρ.state.normal f.to_has_eval m) := by { simp only [state.normal, hsat, to_bool_true_eq_tt, coe_sort_tt, and_self], },
      cases ρ with σ v σ,
      { simp only [result.state] at hn, 
        simp only [result.eval, hn, result.normal, if_true, coe_sort_tt], },
      { simp only [result.legal, eq_ff_eq_not_eq_tt, bool.of_to_bool_iff] at hlgl,
        cases hlgl with _ hlgl,
        simp only [result.state, hlgl, coe_sort_ff] at hn,
        contradiction,  } } 
  end 

  lemma guess_unsat_correct {se : evaluator f} {slv : solver f} 
  {x : lang.exp D O} {ε : env SymV} :
  guess f se slv x ε = unsat → 
  ∀ (m : Model) (r : lang.result D O), evalC f.opC x (ε.eval f.to_has_eval m) r → ¬ r.normal := 
  begin 
    intros h m r hc,
    simp only [guess] at h,
    cases hse : (se.eval x ε) with ρ;
    rewrite hse at h; 
    simp only [guess] at h,
    contradiction,
    cases hslv : (slv.decide (f.and ρ.state.assumes ρ.state.asserts)) with m; 
    rewrite hslv at h; 
    simp only [lower] at h,
    any_goals { contradiction },
    clear h,
    rcases (slv.unsat_sound (f.and ρ.state.assumes ρ.state.asserts) hslv m) with hsat,
    simp only [f.and_sound, bool.to_bool_and, bool.to_bool_coe, band_eq_false_eq_eq_ff_or_eq_ff] at hsat,
    rcases (se.impl x ε ρ hse) with hs,
    rcases (svm_lgl f (@top_legal Model SymB SymV D O _ _ f m) hs) with hlgl,
    rewrite svm_rsc f (@top_normal Model SymB SymV D O _ _ f m) rfl hs at hc,
    rewrite ←hc,
    have hn : ¬ ρ.state.normal f.to_has_eval m := by 
    { simp only [state.normal, eq_ff_eq_not_eq_tt, not_and, bool.to_bool_and, bool.to_bool_coe, band_coe_iff],
      intro ha, 
      cases hsat,
      { simp only [hsat, coe_sort_ff] at ha, contradiction, },
      { exact hsat, } },
    rcases (result.eval_halt f.to_has_eval hn) with hh,
    rewrite hh,
    simp only [result.normal, not_false_iff, coe_sort_ff], 
  end 

  lemma verify_sat_domain {se : evaluator f} {slv : solver f} 
  {x : lang.exp D O} {ε : env SymV} {e : lang.env D O}:
  verify f se slv x ε = sat e → ∃ m, ε.eval f.to_has_eval m = e := 
  begin 
    intro h,
    simp only [verify] at h,
    cases (se.eval x ε) with ρ;
    simp only [verify] at h,
    contradiction,
    cases (slv.decide (f.and ρ.state.assumes (f.not ρ.state.asserts))) with m;
    simp only [lower] at h,
    any_goals { contradiction },
    apply exists.intro m,
    exact h, 
  end

  lemma verify_sat_correct {se : evaluator f} {slv : solver f} 
  {x : lang.exp D O} {ε : env SymV} {e : lang.env D O}:
  verify f se slv x ε = sat e → 
  ∃ (r : lang.result D O), evalC f.opC x e r ∧ r.errors := 
  begin 
    intro h,
    simp only [verify] at h,
    cases hse : (se.eval x ε) with ρ;
    rewrite hse at h; 
    simp only [verify] at h,
    contradiction,
    cases hslv : (slv.decide (f.and ρ.state.assumes (f.not ρ.state.asserts))) with m; 
    rewrite hslv at h; 
    simp only [lower] at h,
    any_goals { contradiction },
    rcases (slv.sat_sound (f.and ρ.state.assumes (f.not ρ.state.asserts)) m hslv) with hsat,
    simp only [f.and_sound, f.not_sound, eq_ff_eq_not_eq_tt, bool.of_to_bool_iff, to_bool_iff] at hsat,
    rcases (se.impl x ε ρ hse) with hs,
    apply exists.intro (ρ.eval f.to_has_eval m),
    constructor,
    { rewrite svm_rsc f (@top_normal Model SymB SymV D O _ _  f m) h hs, },
    { have hn : ¬ (ρ.state.normal f.to_has_eval m) := by { simp only [state.normal, hsat, to_bool_false_eq_ff, not_false_iff, and_false, coe_sort_ff], },
      rcases (result.eval_halt f.to_has_eval hn) with hh,
      rewrite hh,
      have ha : (state.aborted f.to_has_eval m ρ.state) = ff := by 
      { apply state.errored_not_aborted f.to_has_eval, 
        simp only [state.errored, hsat, to_bool_true_eq_tt, coe_sort_tt, not_false_iff, and_self, coe_sort_ff], },
      rewrite ha,
      simp only [result.errors, coe_sort_tt], }
  end 

  lemma verify_unsat_correct {se : evaluator f} {slv : solver f} 
  {x : lang.exp D O} {ε : env SymV} :
  verify f se slv x ε = unsat → 
  ∀ (m : Model) (r : lang.result D O), evalC f.opC x (ε.eval f.to_has_eval m) r → ¬ r.errors := 
  begin 
    intros h m r hc,
    simp only [verify] at h,
    cases hse : (se.eval x ε) with ρ;
    rewrite hse at h; 
    simp only [verify] at h,
    contradiction,
    cases hslv : (slv.decide (f.and ρ.state.assumes (f.not ρ.state.asserts))) with m; 
    rewrite hslv at h; 
    simp only [lower] at h,
    any_goals { contradiction },
    clear h,
    rcases (slv.unsat_sound (f.and ρ.state.assumes (f.not ρ.state.asserts)) hslv m) with hsat,
    simp only [f.and_sound, f.not_sound, eq_ff_eq_not_eq_tt, not_and, eq_tt_eq_not_eq_ff, to_bool_ff_iff] at hsat,
    rcases (se.impl x ε ρ hse) with hs,
    rcases (svm_lgl f (@top_legal Model SymB SymV D O _ _ f m) hs) with hlgl,
    rewrite svm_rsc f (@top_normal Model SymB SymV D O _ _ f m) rfl hs at hc,
    rewrite ←hc,
    cases ρ with σ v σ,
    { cases hn : (state.normal f.to_has_eval m σ),
      { rewrite ←bool_iff_false at hn,
        simp only [result.eval, hn, eq_ff_eq_not_eq_tt, if_false],
        simp only [state.aborted, eq_ff_eq_not_eq_tt],
        simp only [state.normal, eq_ff_eq_not_eq_tt, not_and, bool.to_bool_and, bool.to_bool_coe, band_coe_iff] at hn,
        simp only [result.legal, state.legal, bor_coe_iff, bool.to_bool_coe, bool.to_bool_or] at hlgl,
        cases f.to_has_eval.evalB m σ.assumes,
        { simp only [false_or, coe_sort_ff] at hlgl,
          simp only [hlgl, result.errors, to_bool_true_eq_tt, eq_self_iff_true, and_self], },
        { simp only [coe_sort_tt, forall_true_left] at hsat hn,
          simp only [result.state, hn] at hsat,
          contradiction, } },
      { rewrite bool.tt_eq_true at hn, 
        simp only [result.eval, hn, result.errors, if_true, not_false_iff, coe_sort_ff],  }},
    { simp only [result.eval, state.aborted, eq_ff_eq_not_eq_tt],
      simp only [result.legal, state.legal, eq_ff_eq_not_eq_tt, bor_coe_iff, bool.of_to_bool_iff] at hlgl,
      cases hlgl with hlgl hn,
      simp only [state.normal, bool.to_bool_and, bool.to_bool_coe, band_eq_false_eq_eq_ff_or_eq_ff] at hn,
      cases f.to_has_eval.evalB m σ.assumes,
      { simp only [false_or, coe_sort_ff] at hlgl,
        simp only [hlgl, result.errors, to_bool_true_eq_tt, eq_self_iff_true, and_self], },
      { simp only [result.state, coe_sort_tt, forall_true_left] at hsat,
        simp only [hsat, or_self] at hn,
        contradiction, }  }
 end 

end queries

end sym