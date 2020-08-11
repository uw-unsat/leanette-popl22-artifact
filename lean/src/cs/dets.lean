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

section det

  variables 
    {Model SymB SymV D O : Type}
    [inhabited Model] [inhabited SymV]
    (f : factory Model SymB SymV D O) {m : Model}

  -- The SVM rules are deterministic: given the same environment and 
  -- state, they produce the same result .
  theorem svm_det {x : exp D O} {ε : env SymV} {σ : state SymB} {ρ1 ρ2 : result SymB SymV} :
  evalS f x ε σ ρ1 → 
  evalS f x ε σ ρ2 → 
  ρ1 = ρ2 :=
  begin 
    intros h1 h2,
    induction h1 generalizing ρ2,
    case sym.evalS.app { 
      cases h2,
      congr,
      apply list.ext_le,
      { rewrite [←h1_h1, ←h2_h1], },
      { intros i h1 h2, 
        have hx : i < h1_xs.length := by { simp only [h1_h1, h1], },
        specialize h2_h2 i hx h2,
        specialize h1_ih i hx h1 h2_h2,
        simp only [true_and, eq_self_iff_true] at h1_ih,
        exact h1_ih, } },
    case sym.evalS.call_sym {  
      cases h2,
      { clear h2,
        specialize h1_ih_h1 h2_h1,
        simp only at h1_ih_h1,
        specialize h1_ih_h2 h2_h2,
        simp only at h1_ih_h2,
        congr,
        { simp only [h1_h3, h2_h3, h1_ih_h1],  }, 
        { apply list.ext_le,
          { apply_fun list.length at h1_h5 h2_h5,
            simp only [list.length_map] at h1_h5 h2_h5, 
            rewrite [←h1_h5, ←h2_h5], 
            simp only [h1_ih_h1],  },
          { intros i h1 h2,
            cases h1_ih_h1 with h1_ih_h1_σ h1_ih_h1_c,
            cases h1_ih_h2 with h1_ih_h2_σ h1_ih_h2_v,
            specialize h2_h6 i (list.map_bound (eq.symm h2_h5) h2) h2, 
            have hc1 : i < list.length (f.cast h1_c) := (list.map_bound (eq.symm h1_h5) h1),
            have hc2 : i < list.length (f.cast h2_c) := (list.map_bound (eq.symm h2_h5) h2),
            have h : (list.nth_le (f.cast h2_c) i hc2) = (list.nth_le (f.cast h1_c) i hc1) := by { congr, simp only [h1_ih_h1_c], },
            have h' : h2_σ' = h1_σ' := by { simp only [h1_h3, h2_h3, h1_ih_h1_c], },
            simp only [h, h'] at h2_h6,
            rewrite ←h1_ih_h2_v at h2_h6,
            specialize h1_ih_h6 i hc1 h1 h2_h6,
            cases h1' : list.nth_le h1_grs i h1,
            cases h2' : list.nth_le h2_grs i h2,
            congr,
            { apply_fun choice.guard at h1' h2',
              rewrite [←h1', ←h2'],
              rcases (list.nth_le_of_eq h1_h5 (by {simp only [list.length_map], exact hc1,})) with hq1,
              simp only [list.nth_le_map'] at hq1,
              rcases (list.nth_le_of_eq h2_h5 (by {simp only [list.length_map], exact hc2,})) with hq2,
              simp only [list.nth_le_map'] at hq2,
              rewrite [←hq1, ←hq2],
              simp only [h1_ih_h1_c], },
            { simp only [h1', h2'] at h1_ih_h6,
              exact h1_ih_h6, } } } }, 
      { specialize h1_ih_h1 h2_h1,
        simp only at h1_ih_h1,
        simp only [h1_ih_h1, h1_h3] at h1_h4,
        simp only [h1_h4, h2_h3, or_self] at h2_h4,
        contradiction, } },
    case sym.evalS.call_halt { 
      cases h2,
      { specialize h1_ih_h1 h2_h1,
        simp only at h1_ih_h1,
        simp only [h1_ih_h1, h1_h3] at h1_h4,
        simp only [h2_h3, eq_ff_eq_not_eq_tt] at h2_h4,
        simp only [h2_h4, coe_sort_ff, or_self] at h1_h4, 
        contradiction, },
      { specialize h1_ih_h1 h2_h1,
        simp only at h1_ih_h1,
        simp only [h1_h3, h2_h3], 
        congr,
        simp only [h1_ih_h1], } },
    case sym.evalS.let0 {
      cases h2,
      { specialize h1_ih_h1 h2_h1,
        simp only at h1_ih_h1,
        apply h1_ih_h2, 
        simp only [h1_ih_h1, h2_h2], },
      { specialize h1_ih_h1 h2_h1,
        simp only at h1_ih_h1,
        contradiction, } },
    case sym.evalS.let0_halt {
      cases h2,
      { specialize h1_ih h2_h1,
        simp only at h1_ih,
        contradiction},
      { apply h1_ih h2_h1, } },
    case sym.evalS.if0_true { 
      cases h2; 
      specialize h1_ih_hc h2_hc;
      simp only [true_and, eq_self_iff_true] at h1_ih_hc; 
      simp only [h1_ih_hc] at h1_hv,
      { apply h1_ih_hr h2_hr, },
      { rewrite [f.is_tt_sound] at h1_hv,
        rewrite [f.is_ff_sound] at h2_hv,
        rewrite h1_hv at h2_hv,
        rcases (f.tt_neq_ff) with hn,
        contradiction, },
      { clear h2, elide 0, 
        simp only [h1_hv, not_true, false_and] at h2_hv,
        contradiction, }, },
    case sym.evalS.if0_false { 
      cases h2; 
      specialize h1_ih_hc h2_hc;
      simp only [true_and, eq_self_iff_true] at h1_ih_hc; 
      simp only [h1_ih_hc] at h1_hv,
      { rewrite [f.is_tt_sound] at h2_hv,
        rewrite [f.is_ff_sound] at h1_hv,
        rewrite h2_hv at h1_hv,
        rcases (f.tt_neq_ff) with hn,
        contradiction, },
      { apply h1_ih_hr h2_hr, },
      { clear h2, elide 0,
        simp only [h1_hv, not_true, and_false] at h2_hv,
        contradiction, }, },
    case sym.evalS.if0_sym { 
      cases h2; 
      specialize h1_ih_hc h2_hc; 
      simp only [true_and, eq_self_iff_true] at h1_ih_hc; 
      simp only [h1_ih_hc] at h1_hv,
      { simp only [h1_hv, not_true, false_and] at h2_hv,
        contradiction, },
      { simp only [h1_hv, not_true, and_false] at h2_hv,
        contradiction, },
      { clear h2, congr, 
        any_goals { exact h1_ih_hc, },
        { apply h1_ih_ht, 
          simp only [h1_ih_hc, h2_ht], },
        { apply h1_ih_hf, 
          simp only [h1_ih_hc, h2_hf], },  }, },
    all_goals { cases h2, refl, },
  end 

end det 

end sym