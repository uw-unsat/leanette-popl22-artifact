import tactic.basic
import tactic.split_ifs
import tactic.linarith
import tactic.apply_fun
import .svm
import .lib
import .mrg

namespace sym

open lang 

section hp

  variables 
    {Model SymB SymV D O : Type}
    [inhabited Model] [inhabited SymV]
    (f : factory Model SymB SymV D O) {m : Model}

  lemma factory.compose_hp {σ σ' : state SymB} : 
  ¬ σ.normal f.to_has_eval m → state.eqv f.to_has_eval m (f.compose σ σ') σ := 
  begin 
    intro hnn, 
    simp only [state.eqv, factory.compose],
    simp only [state.normal, eq_ff_eq_not_eq_tt, not_and, bool.to_bool_and, bool.to_bool_coe, band_coe_iff] at hnn,
    rewrite [f.and_sound, f.imp_sound],
    rewrite [f.and_sound, f.imp_sound],
    cases (f.to_has_eval.evalB m σ.assumes),
    { simp only [and_true, bool.to_bool_false, forall_prop_of_false, 
                  bool.of_to_bool_iff, bool.coe_sort_ff, eq_self_iff_true,
                  bool.to_bool_coe, not_false_iff, false_and], },
    { simp only [forall_prop_of_true, bool.coe_sort_tt] at hnn, 
      simp only [hnn, bool.to_bool_false, forall_prop_of_false, bool.to_bool_true, bool.coe_sort_ff, eq_self_iff_true,
                  bool.to_bool_coe, not_false_iff, and_self, false_and], } 
  end 

  lemma factory.strengthen_hp {σ : state SymB} {ρ : result SymB SymV} : 
  ¬ σ.normal f.to_has_eval m → state.eqv f.to_has_eval m (f.strengthen σ ρ).state σ := 
  begin
    intro hn,
    cases ρ with σ' v σ', 
    { simp only [factory.strengthen, factory.halt_or_ans],
      cases (f.halted (f.compose σ σ')),
      all_goals { 
        simp only [result.state, bool.coe_sort_ff, if_false, if_true, bool.coe_sort_tt], 
        apply f.compose_hp hn, }, },
    { simp only [factory.strengthen, result.state],
      apply f.compose_hp hn, } 
  end 

  lemma factory.assert_hp {σ : state SymB} {b : SymB} : 
  ¬ σ.normal f.to_has_eval m → state.eqv f.to_has_eval m (f.assert σ b) σ  := 
  begin
    intro hnn,
    simp only [state.normal, eq_ff_eq_not_eq_tt, not_and, bool.to_bool_and, bool.to_bool_coe, band_coe_iff] at hnn,
    simp only [state.eqv, factory.assert, true_and, eq_self_iff_true],
    rewrite [f.and_sound, f.imp_sound],
    cases (f.to_has_eval.evalB m σ.assumes),
    { simp only [and_true, forall_prop_of_false, bool.to_bool_true, 
                bool.coe_sort_ff, bool.coe_sort_tt, bool.to_bool_coe,
                not_false_iff], },
    { simp only [hnn, bool.to_bool_false, bool.coe_sort_ff, bool.coe_sort_tt, 
                false_and], } 
  end  

  lemma factory.assume_hp {σ : state SymB} {b : SymB} : 
  ¬ σ.normal f.to_has_eval m → state.eqv f.to_has_eval m (f.assume σ b) σ  := 
  begin
    intro hnn,
    simp only [state.normal, eq_ff_eq_not_eq_tt, not_and, bool.to_bool_and, bool.to_bool_coe, band_coe_iff] at hnn,
    simp only [state.eqv, factory.assume, true_and, eq_self_iff_true],
    rewrite [f.and_sound, f.imp_sound],
    cases (f.to_has_eval.evalB m σ.assumes),
    { simp only [bool.to_bool_false, bool.coe_sort_ff, eq_self_iff_true, and_self, false_and], }, 
    { simp only [hnn, forall_prop_of_false, bool.to_bool_true, 
                bool.coe_sort_ff, bool.coe_sort_tt, eq_self_iff_true, 
                not_false_iff, and_self], } 
  end 



  -- The SVM rules preserve the semantics of halted states across steps: 
  -- if the asserts or assumes evaluate to false under a model in the start 
  -- state, then the value of both the assumes and the asserts under that model 
  -- remains the same in the end state.
  theorem svm_hp {x : exp D O} {ε : env SymV} {σ : state SymB} {ρ : result SymB SymV} :
  ¬ σ.normal f.to_has_eval m → evalS f x ε σ ρ → ρ.state.eqv f.to_has_eval m σ := 
  begin 
    intros hnn hs,
    induction hs, 
    case sym.evalS.app { apply f.strengthen_hp hnn, },
    case sym.evalS.call_sym { 
      have hnn' : ¬↥(state.normal f.to_has_eval m hs_σ') := 
      by { rewrite hs_h3, apply state.eqv_abnormal f.to_has_eval hnn, symmetry, apply f.assert_hp hnn, },
      transitivity hs_σ',
      { apply f.merge_ρ_eqp,
        intros i hr,
        rcases (list.map_bound (eq.symm hs_h5) hr) with hc,
        specialize hs_ih_h6 i hc hr,
        transitivity (f.assume hs_σ' (list.nth_le (f.cast hs_c) i hc).guard),
        { apply hs_ih_h6, 
          apply state.eqv_abnormal f.to_has_eval hnn,
          transitivity hs_σ',
          { rewrite hs_h3, symmetry, apply f.assert_hp hnn, },
          { symmetry, 
            apply f.assume_hp,
            apply state.eqv_abnormal f.to_has_eval hnn,
            symmetry, 
            rewrite hs_h3,
            apply f.assert_hp hnn, } },
        { apply f.assume_hp hnn', } },
      { rewrite hs_h3, 
        apply f.assert_hp hnn, } },
    case sym.evalS.call_halt { 
      rewrite hs_h3,
      simp only [result.state],
      apply f.assert_hp hnn, },
    case sym.evalS.let0 { 
      specialize hs_ih_h1 hnn,
      simp only [result.state] at hs_ih_h1,
      transitivity hs_σ',
      { apply hs_ih_h2, 
        apply state.eqv_abnormal f.to_has_eval hnn (state.eqv.symm f.to_has_eval m hs_ih_h1), }, 
      { exact hs_ih_h1, } },
    case sym.evalS.let0_halt { apply hs_ih hnn, },
    case sym.evalS.if0_true  { apply hs_ih_hr hnn, },
    case sym.evalS.if0_false { apply hs_ih_hr hnn, },
    case sym.evalS.if0_sym { 
      apply f.merge_ρ_eqp,
      intros i hi,
      simp only [list.length, zero_add] at hi,
      rcases (nat.lt2_implies_01 hi) with hi01,
      cases hi01; simp only [hi01, list.nth_le],
      { transitivity (f.assume hs_σ (f.truth hs_v)),
        { apply hs_ih_ht, 
          apply state.eqv_abnormal f.to_has_eval hnn,
          symmetry,
          apply f.assume_hp hnn, },
        { apply f.assume_hp hnn, } },
      { transitivity (f.assume hs_σ (f.not (f.truth hs_v))),
        { apply hs_ih_hf, 
          apply state.eqv_abnormal f.to_has_eval hnn,
          symmetry,
          apply f.assume_hp hnn, },
        { apply f.assume_hp hnn, } } },
    case sym.evalS.error { 
      simp only [result.state],
      apply f.assert_hp hnn, },
    case sym.evalS.abort {
      simp only [result.state],
      apply f.assume_hp hnn, },
    all_goals { -- bool, datum, lam, var
      solve1 { simp only [result.state, eq_self_iff_true, and_self], } },
  end 

end hp

end sym