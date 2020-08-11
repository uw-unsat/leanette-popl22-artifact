import tactic.basic
import tactic.split_ifs
import tactic.linarith
import tactic.apply_fun
import .sym
import .svm
import .lib
import .fin
import .rsc
import .detc
import .dets
import .red
import .query


namespace sym 

open lang 

class has_contains (φ α β : Type) :=
(contains : φ → α → β → Prop)

notation a ` ∈[` f `] ` b := has_contains.contains f a b

section
variables {Model SymB SymV D O : Type}
[inhabited Model] [inhabited SymV]

instance env.has_contains :
  has_contains (factory Model SymB SymV D O) (lang.env D O) (env SymV) :=
⟨λ f e ε, ∃ (m : Model), ε.eval f.to_has_eval m = e⟩

instance result.has_contains :
  has_contains (factory Model SymB SymV D O) (lang.result D O) (result SymB SymV) :=
⟨λ f r ρ, ∃ (m : Model), ρ.eval f.to_has_eval m = r⟩

end

-- The following top-level theorems are proven with respect to the top-level state 
-- that is normal under every model.
section thm 
  parameters {Model SymB SymV D O : Type}
  [inhabited Model] [inhabited SymV]
  (f : factory Model SymB SymV D O)

  @[simp] def σₜₜ : state SymB := ⟨f.mk_tt, f.mk_tt⟩

  lemma σₜₜ_normal (m : Model) : σₜₜ.normal f.to_has_eval m := 
  by { simp only [σₜₜ, top_normal], }
  
  lemma σₜₜ_legal (m : Model) : σₜₜ.legal f.to_has_eval m := 
  by { simp only [σₜₜ, top_legal], }

  -- The symbolic semantics evalS preserves the legality of states across steps: 
  -- legal input state leads to a legal result. 
  theorem legality {x : exp D O} {ε : env SymV} {σ : state SymB} {ρ : result SymB SymV} {m : Model} :
  σ.legal f.to_has_eval m → 
  evalS f x ε σ ρ → 
  ρ.legal f.to_has_eval m :=
  begin 
    apply svm_lgl
  end 

  -- The symbolic semantics evalS is deterministic: given the same environment and 
  -- state, it produces the same result.
  theorem determinism {x : exp D O} {ε : env SymV} {σ : state SymB} {ρ1 ρ2 : result SymB SymV} :
  evalS f x ε σ ρ1 → 
  evalS f x ε σ ρ2 → 
  ρ1 = ρ2 :=
  begin 
    apply svm_det 
  end 

  -- The symbolic semantics evalS is composable: 
  -- if evalS terminates on a program x, equivalent environments ε1 and ε2, and states σₜₜ and σ to produce 
  -- the results ρ1 and ρ2, respectively, then ρ2 can be obtained by strengthening ρ1 
  -- with σ under all models.
  theorem composability {x : exp D O} {ε1 ε2 : env SymV} {σ : state SymB} {ρ1 ρ2 : result SymB SymV} : 
  evalS f x ε1 σₜₜ ρ1 → 
  evalS f x ε2 σ ρ2 → 
  (∀ (m : Model), ε1.eval f.to_has_eval m = ε2.eval f.to_has_eval m) → 
  ∀ (m : Model), 
    ρ2.eval f.to_has_eval m = (f.strengthen σ ρ1).eval f.to_has_eval m := 
  begin 
    intros h1 h2 heq m,
    cases hn : (σ.normal f.to_has_eval m),
    { rewrite ←bool_iff_false at hn,
      have hq1 : state.eqv f.to_has_eval m (f.strengthen σ ρ1).state σ := by { apply f.strengthen_hp hn, },
      have hh1 : (f.strengthen σ ρ1).eval f.to_has_eval m = lang.result.halt ((f.strengthen σ ρ1).state.aborted f.to_has_eval m) := 
      by {  apply result.eval_halt,
            apply state.eqv_abnormal f.to_has_eval hn,
            symmetry, exact hq1, },
      rcases (svm_hp f hn h2) with hq2,
      have hh2 : ρ2.eval f.to_has_eval m = lang.result.halt (ρ2.state.aborted f.to_has_eval m) := 
      by {  apply result.eval_halt, 
            apply state.eqv_abnormal f.to_has_eval hn,
            symmetry, exact hq2,  },
      rewrite [hh1, hh2],
      simp only,
      apply state.eqv_aborted,
      transitivity σ,
      { exact hq2, },
      { symmetry, exact hq1, }}, 
    { rewrite bool.tt_eq_true at hn,
      have h1c : evalC f.opC x (ε1.eval f.to_has_eval m) (ρ1.eval f.to_has_eval m) := 
      by { rewrite svm_rsc f (σₜₜ_normal f m) rfl h1, },
      have h2c :  evalC f.opC x (ε1.eval f.to_has_eval m) (ρ2.eval f.to_has_eval m) := 
      by { rewrite heq, rewrite svm_rsc f hn rfl h2, },
      rcases (evalC_det h2c h1c) with hq,
      rewrite hq,
      symmetry,
      apply f.eval_strengthen_normal hn, }
  end 

  -- The symbolic semantics evalS behaves equivalently to the concrete semantics evalC 
  -- when evaluating an expression x in a concrete environment and normal concrete state. 
  theorem reducibility {x : exp D O} {e : lang.env D O} {r : lang.result D O} 
  {pe : reducer Model SymB SymV D O} (hr : f = pe.to_factory) : 
  evalS f x (e.lift pe.lift) σₜₜ (r.lift f pe.lift) ↔ 
  evalC f.opC x e r := 
  begin 
    simp only [hr, σₜₜ],
    rewrite ←σₙ,
    apply svm_reduce pe,
  end 

  -- The symbolic semantics evalS faithfully lifts the concrete semantics evalC: 
  -- if evalS produces a result ρ on a program x, top symbolic state σₜₜ, and 
  -- a symbolic environment ε, then for any model m and concrete environment 
  -- e = ε.eval f m, evalC produces a result r on x and e if and only if r = ρ.eval f m.
  theorem faithful_lifting 
  {x : exp D O} {ε : env SymV} {ρ : result SymB SymV} :
  evalS f x ε σₜₜ ρ → 
  ∀ (m : Model) {e : lang.env D O} {r : lang.result D O}, 
    ε.eval f.to_has_eval m = e → 
    (evalC f.opC x e r ↔ ρ.eval f.to_has_eval m = r) := 
  begin 
    intros hs m e r he,
    apply svm_rsc f (σₜₜ_normal f m) he hs, 
  end 

  -- The symbolic semantics evalS is sound with respect to the concrete semantics evalC: 
  -- if evalS produces a result ρ on a program x, symbolic environment ε, and the top 
  -- state σₜₜ, then for all environments e ∈ ε, if evalC produces a result r on x and e,   
  -- then r is covered by ρ, i.e., r ∈ ρ.
  theorem soundness
  {x : exp D O} {ε : env SymV} {ρ : result SymB SymV} :
  evalS f x ε σₜₜ ρ →
  ∀ (e : lang.env D O), 
    (e ∈[f] ε) → 
    ∀ (r : lang.result D O), 
      (evalC f.opC x e r) → (r ∈[f] ρ) :=
  begin 
    intros hs e he r hc,
    rcases he with ⟨m, he⟩,
    apply exists.intro m,
    rewrite ←faithful_lifting f hs m he,
    exact hc,
  end 

  -- The symbolic semantics evalS is sound with respect to the concrete semantics evalC: 
  -- if evalC produces a result r on a program x and environment e, then for all 
  -- environments ε such that e ∈ ε, if evalS produces a result ρ on x, ε, and σₜₜ,  
  -- then r is covered by ρ, i.e., r ∈ ρ.
  theorem soundness'
  {x : exp D O} {e : lang.env D O} {r : lang.result D O} :
  (evalC f.opC x e r) → 
  ∀ (ε : env SymV), 
    (e ∈[f] ε) → 
    ∀ (ρ : result SymB SymV), 
      evalS f x ε σₜₜ ρ → (r ∈[f] ρ) :=
  begin 
    intros hc ε he ρ hs,
    rcases he with ⟨m, he⟩,
    apply exists.intro m,
    rewrite ←faithful_lifting f hs m he,
    exact hc,
  end 

  -- The symbolic semantics evalS is complete with respect to the concrete semantics evalC: 
  -- if evalS produces a result ρ on a program x, top symbolic state σₜₜ, and 
  -- a symbolic environment ε, then for every concrete result r ∈ ρ, there 
  -- exists a concrete environment e ∈ ε such that evalC produces r on x and e.
  theorem completeness 
  {x : exp D O} {ε : env SymV} {ρ : result SymB SymV} :
  evalS f x ε σₜₜ ρ → 
  ∀ (r : lang.result D O),  
    (r ∈[f] ρ) →
    ∃ (e : lang.env D O), 
      (evalC f.opC x e r) ∧ (e ∈[f] ε) :=
  begin 
    intros hs r hr,
    rcases hr with ⟨m, hr⟩, 
    apply exists.intro (ε.eval f.to_has_eval m),
    constructor,
    { rewrite faithful_lifting f hs m rfl, exact hr, }, 
    { simp only [has_contains.contains, exists_apply_eq_apply], },
  end 

  -- The symbolic semantics evalS terminates on every expression x 
  -- that is finite with respect to the environment ε, i.e., free of calls and 
  -- with all variable references bound to valid indices in ε.
  theorem termination {x : exp D O} {ε : env SymV} (σ : state SymB) :
  x.finite ε.length →  ∃ (ρ : result SymB SymV), evalS f x ε σ ρ := 
  by { apply svm_ft f, } 

  open decision 

  def normal (x : lang.exp D O) (e : lang.env D O) : Prop := 
  ∃ (r : lang.result D O), evalC f.opC x e r ∧ r.normal

  def errors (x : lang.exp D O) (e : lang.env D O) : Prop := 
  ∃ (r : lang.result D O), evalC f.opC x e r ∧ r.errors

  -- The guess(x, ε) query is correct:
  -- if it returns an environment e, then  e ∈ ε and there is a normal concrete execution of x in e;  
  -- if it returns unsat, then there is no normal concrete execution of x in any e ∈ ε. 
  theorem guess_correct {se : evaluator f} {slv : solver f} 
  {x : lang.exp D O} {ε : env SymV} :
  (∀ (e : lang.env D O), 
    guess f se slv x ε = sat e →
    ((e ∈[f] ε) ∧ normal x e)) ∧ 
  (guess f se slv x ε = unsat → 
    ∀ (e : lang.env D O),
      (e ∈[f] ε) → ¬ normal x e) := 
  begin 
    constructor,
    { intros e h,
      constructor,
      { simp only [has_contains.contains],
        apply guess_sat_domain f h, },
      { apply guess_sat_correct f h, } },
    { simp only [normal, not_exists, eq_ff_eq_not_eq_tt, not_and],
      intros h e he r hc, 
      rewrite ←bool_iff_false, 
      simp only [has_contains.contains] at he,
      cases he with m he,
      rewrite ←he at hc,
      apply guess_unsat_correct f h m,
      exact hc, } 
  end 
  
  -- The verify(x, ε) query is correct:
  -- if it returns an environment e, then  e ∈ ε and there is an erroneous concrete execution of x in e;  
  -- if it returns unsat, then there is no erroneous concrete execution of x in any e ∈ ε. 
  theorem verify_correct {se : evaluator f} {slv : solver f} 
  {x : lang.exp D O} {ε : env SymV} :
  (∀ (e : lang.env D O), 
    verify f se slv x ε = sat e →
    ((e ∈[f] ε) ∧ errors x e)) ∧ 
  (verify f se slv x ε = unsat → 
    ∀ (e : lang.env D O),
      (e ∈[f] ε) → ¬ errors x e) := 
  begin 
    constructor,
    { intros e h,
      constructor,
      { simp only [has_contains.contains],
        apply verify_sat_domain f h, },
      { apply verify_sat_correct f h, } },
    { simp only [errors, not_exists, eq_ff_eq_not_eq_tt, not_and],
      intros h e he r hc, 
      rewrite ←bool_iff_false, 
      simp only [has_contains.contains] at he,
      cases he with m he,
      rewrite ←he at hc,
      apply verify_unsat_correct f h m,
      exact hc, } 
  end 


end thm


end sym