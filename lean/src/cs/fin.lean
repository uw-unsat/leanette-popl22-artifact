import tactic.basic
import tactic.split_ifs
import tactic.linarith
import tactic.apply_fun
import .svm
import .lib

namespace lang 

  -- A program is call free if it contains no calls.
  def exp.call_free {D O : Type} : exp D O → bool 
  | (exp.call _ _) := ff 
  | (exp.let0 y x1 x2) := exp.call_free x1 ∧ exp.call_free x2
  | (exp.if0 y x1 x2)  := exp.call_free x1 ∧ exp.call_free x2
  | _ := tt 

  -- A program is bound if every variable reference is within 
  -- the given bound on environment length.
  def exp.bound {D O : Type} (bnd : ℕ) : exp D O → bool 
  | (exp.var y)        := y < bnd
  | (exp.call y1 y2)   := y1 < bnd ∧ y2 < bnd 
  | (exp.let0 y x1 x2) := y < bnd ∧ exp.bound x1 ∧ exp.bound x2
  | (exp.if0 y x1 x2)  := y < bnd ∧ exp.bound x1 ∧ exp.bound x2
  | (exp.app _ ys)     := ys.all (λ y, y < bnd) 
  | _                  := tt

  -- A program is finite if it is free of calls and every variable 
  -- reference is within the given bound on environment length.
  def exp.finite {D O : Type} (bnd : ℕ) (x : exp D O) : bool := 
  x.call_free ∧ x.bound bnd 

end lang 

namespace sym 

open lang 

section thms
  variables 
    {Model SymB SymV D O : Type}
    [inhabited Model] [inhabited SymV]
    (f : factory Model SymB SymV D O) 
    
  lemma app_args_fbt {xs : list ℕ} {ε : env SymV}
  (h : ∀ x, x ∈ xs → x < ε.length)  :
  ∃ (vs : list SymV), xs.map ε.nth = vs.map some := 
  begin 
    induction xs,
    { apply exists.intro [], simp only [list.map], },
    { simp only [forall_eq_or_imp, list.mem_cons_iff] at h,
      specialize xs_ih h.right,
      rcases xs_ih with ⟨vs_tl, hvs_tl⟩,
      simp only [list.map], 
      apply exists.intro ((list.nth_le ε xs_hd h.left)::vs_tl),
      simp only [hvs_tl, and_true, eq_self_iff_true, list.map],
      apply list.nth_le_nth, } 
  end 

  -- The symbolic semantics evalS terminates on every expression x 
  -- that is finite with respect to the environment ε, i.e., free of calls and 
  -- with all variable references bound to valid indices in ε.
  theorem svm_ft {x : exp D O} {ε : env SymV} (σ : state SymB) :
  x.finite ε.length → 
  ∃ (ρ : result SymB SymV), evalS f x ε σ ρ  :=
  begin 
    intros hf,
    simp only [exp.finite, bool.to_bool_and, bool.to_bool_coe, band_coe_iff] at hf,
    rcases hf with ⟨hf, hb⟩,
    induction x generalizing ε σ,
    case lang.exp.bool  : { apply exists.intro (result.ans σ (f.bval x)), apply evalS.bool, },
    case lang.exp.datum : { apply exists.intro (result.ans σ (f.dval x)), apply evalS.datum, },
    case lang.exp.lam   : y x { apply exists.intro (result.ans σ (f.cval (clos.mk y x ε))), apply evalS.lam, },
    case lang.exp.app   : o xs {
      simp only [exp.bound] at hb,
      rewrite list.all_iff_forall at hb,
      simp only [bool.of_to_bool_iff] at hb,
      rcases (app_args_fbt hb) with ⟨vs, hvs⟩,
      apply exists.intro (f.strengthen σ (f.opS o vs)),
      apply evalS.app,
      { apply_fun list.length at hvs, 
        simp only [list.length_map] at hvs, 
        exact hvs, }, 
      { intros i hx hv,
        have hi : i < (list.map (list.nth ε) xs).length := by { simp only [hx, list.length_map], },
        rcases (list.nth_le_of_eq hvs hi) with hm,
        simp only [list.nth_eq_some, list.nth_le_map'] at hm,
        rcases hm with ⟨hmx, hm⟩,
        rewrite ←hm,
        apply evalS.var hmx, } },
    case lang.exp.var   : { 
      simp only [exp.bound, bool.of_to_bool_iff] at hb, 
      apply exists.intro (result.ans σ (ε.nth_le x hb)),
      apply evalS.var hb, },
    case lang.exp.call  : { simp only [exp.call_free, coe_sort_ff] at hf, contradiction, },
    case lang.exp.let0  : y x1 x2 ih1 ih2 {
      simp only [exp.call_free, bool.to_bool_and, bool.to_bool_coe, band_coe_iff] at hf,
      simp only [exp.bound, bool.of_to_bool_iff] at hb,
      specialize @ih1 hf.left ε σ hb.right.left,
      rcases ih1 with ⟨ρ1, ih1⟩, 
      cases ρ1 with σ' v σ',
      { specialize @ih2 hf.right (ε.update_nth y v) σ',
        simp only [list.update_nth_length, hb, forall_true_left] at ih2,
        rcases ih2 with ⟨ρ2, ih2⟩, 
        apply exists.intro ρ2,
        apply evalS.let0 ih1 ih2, },
      { apply exists.intro (result.halt σ'), 
        apply evalS.let0_halt ih1, } },
    case lang.exp.if0   : xc xt xf iht ihf { 
      simp only [exp.bound, bool.of_to_bool_iff] at hb,
      simp only [exp.call_free, bool.to_bool_and, bool.to_bool_coe, band_coe_iff] at hf,
      have hc : evalS f (exp.var xc) ε σ (result.ans σ (ε.nth_le xc hb.left)) := by { apply evalS.var hb.left, },
      cases hv : f.is_tt (f.truth (ε.nth_le xc hb.left)),
      { rewrite ←bool_iff_false at hv,
        cases hv' : f.is_ff (f.truth (ε.nth_le xc hb.left)),
        { rewrite ←bool_iff_false at hv', 
          specialize @iht hf.left ε (f.assume σ (f.truth (ε.nth_le xc hb.left))) hb.right.left,
          rcases iht with ⟨rt, iht⟩, 
          specialize @ihf hf.right ε (f.assume σ (f.not (f.truth (ε.nth_le xc hb.left)))) hb.right.right,
          rcases ihf with ⟨rf, ihf⟩, 
          apply exists.intro (f.merge_ρ σ [⟨f.truth (ε.nth_le xc hb.left), rt⟩, ⟨f.not (f.truth (ε.nth_le xc hb.left)), rf⟩]),
          apply evalS.if0_sym hc _ iht ihf, 
          simp only [hv, hv', not_false_iff, and_self], },
        { rewrite bool.tt_eq_true at hv', 
          specialize @ihf hf.right ε σ hb.right.right,
          rcases ihf with ⟨rf, ihf⟩, 
          apply exists.intro rf,
          apply evalS.if0_false hc hv' ihf, } },
      { rewrite bool.tt_eq_true at hv,
        specialize @iht hf.left ε σ hb.right.left,
        rcases iht with ⟨rt, iht⟩, 
        apply exists.intro rt, 
        apply evalS.if0_true hc hv iht, } },
    case lang.exp.error : { apply exists.intro (result.halt (f.assert σ f.mk_ff)), apply evalS.error, },
    case lang.exp.abort : { apply exists.intro (result.halt (f.assume σ f.mk_ff)), apply evalS.abort, },
  end 



end thms

end sym 

