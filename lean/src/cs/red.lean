import tactic.basic
import tactic.split_ifs
import tactic.linarith
import tactic.apply_fun
import .svm
import .lib
import .hp 
import .lgl
import .detc
import .conc
import .rsc

namespace sym 

open lang 

section reducibility
  variables 
    {Model SymB SymV D O : Type}
    [inhabited Model] [inhabited SymV]
    (f : reducer Model SymB SymV D O) 

  @[simp] def σₙ : state SymB := ⟨f.mk_tt, f.mk_tt⟩

  lemma σₙ_normal (m : Model) : (σₙ f).normal f.to_has_eval m := 
  by { simp only [σₙ, top_normal], }

  lemma reducer.tt_is_tt : (f.is_tt f.mk_tt) = tt := 
  begin 
    rewrite bool.tt_eq_true,
    simp only [factory.is_tt_sound], 
  end 

  lemma reducer.ff_is_ff : (f.is_ff f.mk_ff) = tt := 
  begin
    rewrite bool.tt_eq_true,
    simp only [factory.is_ff_sound],  
  end 
  
  lemma reducer.tt_is_nf : (f.is_ff f.mk_tt) = ff := 
  begin 
    rewrite ←bool_iff_false,
    simp only [factory.is_ff_sound],
    intro h,
    rcases (factory.tt_neq_ff f.to_factory) with h',
    contradiction, 
  end 


  lemma reducer.ff_is_nt : (f.is_tt f.mk_ff) = ff := 
  begin
    rewrite ←bool_iff_false,
    simp only [factory.is_tt_sound],
    intro h,
    rewrite eq_comm at h,
    rcases (factory.tt_neq_ff f.to_factory) with h',
    contradiction, 
  end  

  lemma reducer.and_tt : f.and f.mk_tt f.mk_tt = f.mk_tt := 
  begin 
    rcases (f.and_red f.mk_tt f.mk_tt) with h,  
    simp only [factory.is_tf, factory.is_tt_sound, bool.of_to_bool_iff, true_or, eq_self_iff_true, forall_true_left] at h,
    cases h,
    { exact h },
    { simp only [f.to_factory.is_ff_sound] at h,
      apply_fun (f.evalB (default Model)) at h,
      simp only [f.to_factory.and_sound, f.to_factory.mk_tt_sound, f.to_factory.mk_ff_sound, to_bool_true_eq_tt, coe_sort_tt, and_self] at h,
      contradiction, } 
  end 

  lemma reducer.and_tf : f.and f.mk_tt f.mk_ff = f.mk_ff := 
  begin 
    rcases (f.and_red f.mk_tt f.mk_ff) with h,
    simp only [factory.is_tf, factory.is_tt_sound, factory.is_ff_sound, bool.of_to_bool_iff, true_or, eq_self_iff_true, forall_true_left, or_true] at h,
    cases h,
    { apply_fun (f.evalB (default Model)) at h,
      simp only [f.to_factory.and_sound, f.to_factory.mk_tt_sound, f.to_factory.mk_ff_sound, to_bool_false_eq_ff, and_false, coe_sort_ff] at h,
      contradiction},
    { exact h } 
  end 

  lemma reducer.and_ft : f.and f.mk_ff f.mk_tt = f.mk_ff := 
  begin 
    rcases (f.and_red f.mk_ff f.mk_tt) with h,
    simp only [factory.is_tf, factory.is_tt_sound, factory.is_ff_sound, bool.of_to_bool_iff, true_or, eq_self_iff_true, forall_true_left, or_true] at h,
    cases h,
    { apply_fun (f.evalB (default Model)) at h,
      simp only [f.to_factory.and_sound, f.to_factory.mk_tt_sound, f.to_factory.mk_ff_sound, to_bool_false_eq_ff, coe_sort_ff, false_and] at h,
      contradiction},
    { exact h }  
  end 

  lemma reducer.or_tf : f.or f.mk_tt f.mk_ff = f.mk_tt := 
  begin 
    rcases (f.or_red f.mk_tt f.mk_ff) with h,
    simp only [factory.is_tf, factory.is_tt_sound, factory.is_ff_sound, bool.of_to_bool_iff, true_or, eq_self_iff_true, forall_true_left, or_true] at h,
    cases h,
    { exact h },
    { apply_fun (f.evalB (default Model)) at h,
      simp only [f.to_factory.or_sound, f.to_factory.mk_tt_sound, f.to_factory.mk_ff_sound, to_bool_true_eq_tt, coe_sort_tt, or_false, coe_sort_ff] at h,
      contradiction, } 
  end 

  lemma reducer.imp_tt : f.imp f.mk_tt f.mk_tt = f.mk_tt := 
  begin 
    rcases (f.imp_red f.mk_tt f.mk_tt) with h, 
    simp only [factory.is_tf, reducer.tt_is_tt, factory.is_tt_sound, true_or, coe_sort_tt, forall_true_left, bool.of_to_bool_iff] at h,
    cases h, 
    { exact h, },
    { simp only [f.to_factory.is_ff_sound] at h,
      apply_fun (f.evalB (default Model)) at h,
      simp only [f.to_factory.imp_sound, f.to_factory.mk_ff_sound, imp_self, to_bool_true_eq_tt] at h,
      contradiction, }
  end 

  lemma reducer.imp_tf : f.imp f.mk_tt f.mk_ff = f.mk_ff := 
  begin 
    rcases (f.imp_red f.mk_tt f.mk_ff) with h, 
    simp only [factory.is_tf, reducer.tt_is_tt, reducer.ff_is_ff, bor_coe_iff, to_bool_true_eq_tt, true_or, coe_sort_tt, bool.to_bool_coe, forall_true_left, or_true, bool.to_bool_or] at h,
    cases h, 
    { simp only [factory.is_tt_sound] at h,  
      apply_fun (f.evalB (default Model)) at h,
      simp only [f.to_factory.imp_sound, f.to_factory.mk_ff_sound, factory.mk_tt_sound, to_bool_false_eq_ff, coe_sort_tt, forall_true_left, coe_sort_ff] at h,
      contradiction, },
    { simp only [f.to_factory.is_ff_sound] at h,
      exact h, }
  end 

  lemma reducer.red_merge_ρ (r : lang.result D O) : 
  (f.to_factory.merge_ρ (σₙ f) [⟨f.mk_tt, r.lift f.to_factory f.lift⟩]) = 
  r.lift f.to_factory f.lift := 
  begin 
    simp only [factory.merge_ρ, σₙ, band, list.all_nil, list.all_cons, band_tt],
    cases r with v b,
    { simp only [result.lift, result.is_halt, to_bool_false_eq_ff, if_false, coe_sort_ff], 
      simp only [factory.merge_υ, result.value, reducer.merge_red, list.map], 
      simp only [factory.merge_σ, factory.merge_φ, factory.all, result.state, list.foldr],
      simp only [reducer.imp_tt, reducer.and_tt, factory.halt_or_ans, factory.halted, reducer.tt_is_nf, eq_self_iff_true, if_false, bor, and_self, coe_sort_ff],},
    { cases b;
      simp only [result.lift, result.is_halt, to_bool_true_eq_tt, if_true, coe_sort_tt];
      simp only [factory.merge_σ, factory.merge_φ, factory.all, result.state, list.foldr];
      simp only [reducer.imp_tf, reducer.imp_tt, reducer.and_tt, reducer.and_ft, reducer.and_tf, eq_self_iff_true, and_self], } 
  end 

  lemma reducer.assert_ff : (f.to_factory.assert ⟨f.mk_tt, f.mk_tt⟩ f.mk_ff) = ⟨f.mk_tt, f.mk_ff⟩ := 
  begin 
    simp only [factory.assert, reducer.imp_tf, reducer.and_tf, eq_self_iff_true, and_self],
  end 

  lemma reducer.assume_ff : (f.to_factory.assume ⟨f.mk_tt, f.mk_tt⟩ f.mk_ff) = ⟨f.mk_ff, f.mk_tt⟩ :=
  begin 
    simp only [factory.assume, reducer.imp_tf, reducer.and_tf, eq_self_iff_true, and_self],
  end  

  lemma reducer.truth_nf {v : lang.val D O } :
  v ≠ lang.val.bool ff → 
  (f.to_factory.is_tt (f.to_factory.truth (f.lift v))) := 
  begin 
    intro h,
    simp only [f.to_factory.is_tt_sound],
    rcases (f.truth_red v) with ht,
    simp only [factory.is_tf, bor_coe_iff, bool.to_bool_coe, bool.to_bool_or] at ht,
    cases ht,
    { simp only [f.to_factory.is_tt_sound] at ht,
      exact ht, },
    { simp only [f.to_factory.is_ff_sound] at ht,
      apply_fun (f.evalB (default Model)) at ht,
      simp only [f.to_factory.mk_ff_sound] at ht,
      rewrite ←bool_iff_false at ht,
      rcases (f.truth_sound (default Model) (f.lift v)) with hs,
      rewrite hs at ht,
      simp only [f.lift_sound, not_not] at ht,
      contradiction, } 
  end 

  lemma reducer.truth_ff {v : lang.val D O } :
  v = lang.val.bool ff → 
  (f.to_factory.is_ff (f.to_factory.truth (f.lift v))) := 
  begin 
    intro h,
    simp only [f.to_factory.is_ff_sound],
    rcases (f.truth_red v) with ht,
    simp only [factory.is_tf, bor_coe_iff, bool.to_bool_coe, bool.to_bool_or] at ht,
    cases ht,
    { simp only [f.to_factory.is_tt_sound] at ht,
      apply_fun (f.evalB (default Model)) at ht,
      simp only [f.to_factory.mk_tt_sound] at ht,
      rewrite bool.tt_eq_true at ht,
      rcases (f.truth_sound (default Model) (f.lift v)) with hs,
      rewrite hs at ht,
      simp only [f.lift_sound, ne.def] at ht,
      contradiction, },
    { simp only [f.to_factory.is_ff_sound] at ht,
      exact ht, } 
  end 

  lemma reducer.not_clos {v : lang.val D O} :
  ¬ v.is_clos → val.to_clos f.lift v = none := 
  begin
    intro h,
    cases v,
    case lang.val.clos { 
      simp only [val.is_clos, not_true, coe_sort_tt] at h, 
      contradiction, },
    all_goals { simp only [val.to_clos], }, 
  end 

  lemma reducer.red_strengthen {o : O} {vs : list (lang.val D O)} :
  (f.opS o (vs.map f.lift)) = f.to_factory.strengthen ⟨f.mk_tt, f.mk_tt⟩ (f.opS o (vs.map f.lift)) := 
  begin
    simp only [f.opS_red],
    cases (f.to_factory.opC o vs) with v b,
    { simp only [result.lift, factory.strengthen, factory.compose],
      simp only [reducer.imp_tt, reducer.and_tt, factory.halt_or_ans, factory.halted, reducer.tt_is_nf, eq_self_iff_true, if_false, bor, and_self, coe_sort_ff], },
    { cases b; 
      simp only [result.lift, factory.strengthen, factory.compose];
      simp only [reducer.imp_tt, reducer.imp_tf, reducer.and_tf, reducer.and_tt, eq_self_iff_true, and_self],}
  end 

  lemma env.red_update {e : lang.env D O} (y : ℕ) {v : lang.val D O} : 
  (env.lift f.lift (e.update_nth y v)) = 
  (list.update_nth (env.lift f.lift e) y (f.lift v))  := 
  begin 
    simp only [env.lift],
    apply list.ext_le, 
    { simp only [list.length_map, list.update_nth_length],  },
    { intros i h1 h2,
      simp only [list.nth_le_map'],
      cases classical.em (y = i),
      { have hy : y < list.length e := by { simp only [list.length_map, list.update_nth_length] at h1,  simp only [h1, h], },
        have h3 : y < (list.update_nth e y v).length := by { simp only [hy, list.update_nth_length], },
        have h4 : y < ((list.map f.lift e).update_nth y (f.lift v)).length := by { simp only [hy, list.length_map, list.update_nth_length], },
        rewrite ←list.nth_le_eq_idx (list.update_nth e y v) h h3,
        rewrite ←list.nth_le_eq_idx ((list.map f.lift e).update_nth y (f.lift v)) h h4,
        simp only [list.nth_le_update_nth_eq], },
      { rewrite [←ne.def] at h,
        rewrite list.nth_le_update_nth_of_ne h v,
        rewrite list.nth_le_update_nth_of_ne h (f.lift v),
        simp only [list.nth_le_map'], } }  
  end 

  lemma env.red_nth_le {e : lang.env D O} {y : ℕ} 
  (h1 : y < e.length) (h2 : y < (e.lift f.lift).length) : 
  (f.lift (e.nth_le y h1)) = (e.lift f.lift).nth_le y h2 := 
  begin 
    simp only [env.lift, list.nth_le_map'], 
  end 

  -- The symbolic semantics evalS behaves equivalently to the concrete semantics evalC 
  -- when evaluating an expression x in a concrete environment and normal concrete state. 
  theorem svm_red {x : exp D O} {e : lang.env D O} {r : lang.result D O} : 
  evalC f.opC x e r → 
  evalS f.to_factory x (e.lift f.lift) (σₙ f) (r.lift f.to_factory f.lift) := 
  begin
    intro h,
    induction h,
    case lang.evalC.bool : e b { 
      simp only [result.lift, reducer.bval_red, σₙ],
      apply evalS.bool, },
    case lang.evalC.datum : e d { 
      simp only [result.lift, reducer.dval_red, σₙ],
      apply evalS.datum, },
    case lang.evalC.lam : e y x { 
      simp only [result.lift, σₙ],
      have h : (val.clos y x e).to_clos f.lift = some (clos.mk y x (e.lift f.lift)) := by { simp only [val.to_clos, eq_self_iff_true, and_self], },
      rcases (f.cval_red (val.clos y x e) (clos.mk y x (e.lift f.lift))) with hc,
      simp only [h, true_iff, eq_self_iff_true, and_self] at hc,
      simp only [hc],
      apply evalS.lam, },
    case lang.evalC.var : e y hy { 
      simp only [result.lift, σₙ],
      have hy' : y < list.length (env.lift f.lift e) := by { simp only [env.lift, hy, list.length_map], },
      rewrite env.red_nth_le f hy hy',
      apply evalS.var, },
    case lang.evalC.app : e o xs vs h1 h2 ih { 
      rewrite ←f.opS_red,
      rewrite f.red_strengthen,
      apply evalS.app,
      { simp only [h1, list.length_map], },
      { intros i hx hv,
        have hv' : i < vs.length := by { simp only [list.length_map] at hv, exact hv, },
        specialize ih i hx hv',
        simp only [result.lift, σₙ] at ih,
        simp only [σₙ, list.nth_le_map'],
        exact ih, }  },
    case lang.evalC.call : e x1 x2 py px pe v r h1 h2 h3 ih1 ih2 ih3 {
      rcases (f.cast_red (val.clos py px pe)) with ⟨_, hc⟩,
      simp only [val.to_clos, forall_eq'] at hc, 
      have ht : (f.to_factory.some choice.guard (f.to_factory.cast (f.lift (val.clos py px pe)))) = f.mk_tt := by 
      { simp only [hc, factory.some, list.foldr, reducer.or_tf], },
      rewrite ←reducer.red_merge_ρ,
      apply evalS.call_sym ih1 ih2,
      { simp only [factory.assert, true_and, σₙ, eq_self_iff_true, ht],
        simp only [reducer.imp_tt, reducer.and_tt], },
      { simp only [ht, factory.halted, reducer.tt_is_nf, σₙ, bor, not_false_iff, and_self, coe_sort_ff], },
      { simp only [hc, eq_self_iff_true, and_self, list.map], },
      { intros i hi hi', 
        simp only [hc, factory.assume, σₙ, list.nth_le_singleton],
        simp only [reducer.imp_tt, reducer.and_tt],
        rewrite [←σₙ, ←env.red_update],
        exact ih3, }, },
    case lang.evalC.call_halt : e x1 x2 v1 v2 h1 h2 h3 ih1 ih2 { 
      simp only [result.lift, σₙ, err],
      apply evalS.call_halt ih1 ih2,
      { rcases (f.cast_red v1) with ⟨hf, _⟩,
        rcases (f.not_clos h3) with hc, 
        simp only [hc, eq_self_iff_true, forall_true_left] at hf,
        simp only [hf, factory.some, reducer.assert_ff, σₙ, eq_self_iff_true, and_self, list.foldr_nil], },
      { apply or.inr, 
        simp only [factory.halted, bor_coe_iff], 
        apply or.inr, 
        apply reducer.ff_is_ff, } },
    case lang.evalC.let0 : e y x1 x2 v r h1 h2 ih1 ih2 { 
      apply evalS.let0 ih1,
      rewrite ←env.red_update,
      apply ih2, },
    case lang.evalC.let0_halt : e y x1 x2 b h1 ih1 { 
      cases b; simp only [result.lift, σₙ]; apply evalS.let0_halt ih1, },
    case lang.evalC.if0_true  : e xc xt xf v r hc hv hr ihc ihr { 
      apply evalS.if0_true ihc (f.truth_nf hv) ihr, },
    case lang.evalC.if0_false : e xc xt xf v r hc hv hr ihc ihr { 
      apply evalS.if0_false ihc (f.truth_ff hv) ihr, },
    case lang.evalC.error { 
      simp only [result.lift, err, σₙ],
      rewrite ←reducer.assert_ff,  
      apply evalS.error, },
    case lang.evalC.abort { 
      simp only [result.lift, abt, σₙ],
      rewrite ←reducer.assume_ff, 
      apply evalS.abort, },
  end 


  -- The symbolic semantics evalS behaves equivalently to the concrete semantics evalC 
  -- when evaluating an expression x in a concrete environment and normal concrete state. 
  theorem svm_reduce {x : exp D O} {e : lang.env D O} {r : lang.result D O} : 
  evalS f.to_factory x (e.lift f.lift) (σₙ f) (r.lift f.to_factory f.lift) ↔ 
  evalC f.opC x e r := 
  begin
    constructor,
    { intro hr,
      let m := (default Model),
      have he : env.eval f.to_has_eval m (env.lift f.lift e) = e := by 
      { simp only [env.lift, env.eval, list.map_map], 
        apply list.ext_le,
        { simp only [list.length_map],  },
        { intros i h1 h2, 
          simp only [reducer.lift_sound, function.comp_app, list.nth_le_map'], } },
      rewrite svm_rsc f.to_factory (σₙ_normal f m) he hr,
      cases r with v b,
      { simp only [ result.lift, result.eval, state.normal, factory.mk_tt_sound, 
                    reducer.lift_sound, to_bool_true_eq_tt, if_true, coe_sort_tt, and_self],  },
      { cases b, 
        { simp only [ result.lift, result.eval, state.aborted, factory.mk_ff_sound, to_bool_false_eq_ff, and_false, coe_sort_ff], },
        { simp only [ result.lift, result.eval, state.aborted, factory.mk_ff_sound, factory.mk_tt_sound, to_bool_true_eq_tt, coe_sort_tt,
                      not_false_iff, and_self, coe_sort_ff], } } },
    { apply svm_red, } 
  end 
 
end reducibility 


end sym