import ...cs.svm
import ...cs.sym
import ...cs.lang
import .defs
import ..tactic
import ...basic.basic

namespace interp

section interp

variables 
  {Model SymB SymV D O : Type}
  [inhabited Model] [inhabited SymV]
  {f : sym.factory Model SymB SymV D O}

open sym
open lang

lemma mk_tt_ne_mk_ff : f.mk_tt ≠ f.mk_ff :=
begin 
  intro h,
  have t_sound := f.mk_tt_sound (default Model),
  have f_sound := f.mk_ff_sound (default Model),
  contra [h, f_sound] at t_sound,
end

lemma interpVar_evalS 
  {a : ℕ} {ε : sym.env SymV} {v : SymV} {σ : sym.state SymB}
  (h : ε.nth a = some v) : evalS f (exp.var a) ε σ (sym.result.ans σ v) :=
begin
  simp only [list.nth_eq_some] at h,
  cases h with _ h',
  subst_vars,
  constructor,
end

-- The symbolic interpreter is sound:
-- if running `interpS` with `fuel` produces a symbolic result `r`
-- on a program `e` and a symbolic environment `ε`, then 
-- `evalS` also produces `r` on `e` and `ε`.
lemma interpS_soundness {fuel : ℕ}
  {e : exp D O} {ε : sym.env SymV} {r : sym.result SymB SymV} {σ : sym.state SymB}
  (h : interpS f fuel e ε σ = some r) : evalS f e ε σ r :=
begin
  induction fuel with fuel ih generalizing e ε σ r,
  case zero { contradiction },
  case succ {
    cases e,
    all_goals { simp only [interpS] at h },
    case [error, abort, bool, datum, lam] {
      all_goals { subst_vars, constructor },
    },
    case var : a {
      cases_on_interp h_a : ε.nth a : v,
      simp only [interpS] at h,
      subst_vars,
      apply interpVar_evalS,
      assumption,
    },
    case call : a_f a_a {
      cases_on_interp h_f : ε.nth a_f  : v_f,
      simp only [interpS] at h,
      cases_on_interp h_f : ε.nth a_a : v_a,
      simp only [interpS] at h,
      split_ifs at h with h_if,
      case_c {
        subst_vars,
        apply_c evalS.call_halt,
        case h1 { apply interpVar_evalS, assumption },
        case h2 { apply interpVar_evalS, assumption },
        case h3 { simp },
        case h4 {
          simp only [bor_coe_iff] at h_if,
          simp [h_if],
        },
      },
      case_c {
        generalize_hyp h_map : list.mmap _ _ = r_map at h,
        cases_on_interp h_r : r_map : grs,
        subst r_map,
        simp only [interpS] at h,
        subst_vars,
        apply_c evalS.call_sym,
        case h1 { apply interpVar_evalS, assumption },
        case h2 { apply interpVar_evalS, assumption },
        case h3 { simp },
        case h4 {
          simp at h_if,
          simp only [← not_or_distrib, h_if, not_false_iff],
        },
        case h5 {
          apply_c list.ext_le,
          case hl { simp [mmap.length h_map] },
          case h {
            intros i hi hj,
            have hi' := hi,
            have hj' := hj,
            simp only [list.length_map] at hi' hj',
            replace h_map := mmap.eq_some h_map i hi' hj',
            cases h_nth : list.nth_le (f.cast v_f) i hi' with g cl,
            cases cl with x e_b ε_static,
            simp only [h_nth, interpS] at h_map,
            cases_on_interp h_body : 
              interpS f fuel e_b 
                (list.update_nth ε_static x v_a) 
                (f.assume (f.assert σ (f.some choice.guard (f.cast v_f))) g) : 
              r_body,
            simp only [interpS] at h_map,
            simp [← h_map, h_nth],
          },
        },
        case h6 {
          intros i hi hj,
          replace h_map := mmap.eq_some h_map i hi hj,
          apply ih,
          cases list.nth_le (f.cast v_f) i hi with g cl,
          cases cl with x e_b ε_static,
          simp only [interpS] at h_map ⊢,
          cases_on_interp h_body : 
            interpS f fuel e_b 
              (list.update_nth ε_static x v_a) 
              (f.assume (f.assert σ (f.some choice.guard (f.cast v_f))) g) : 
            r_body,
          simp only [interpS] at h_map,
          simp [← h_map],
        },
      },
    },
    case app : o as {
      cases_on_interp h_as : mmap (λ (a : ℕ), ε.nth a) as : vs,
      simp only [interpS] at h,
      subst_vars,
      constructor_c,
      case h1 { apply mmap.length, assumption },
      case h2 {
        intros i hi_a hi_v,
        apply interpVar_evalS,
        exact mmap.eq_some h_as i hi_a hi_v,
      },
    },
    case let0 : x e_v e_b {
      cases_on_interp h_v : interpS f fuel e_v ε σ : r_v,
      cases r_v,
      case halt {
        simp only [interpS] at h,
        subst_vars,
        apply evalS.let0_halt,
        apply ih,
        assumption,
      },
      case ans {
        simp only [interpS] at h,
        apply_c evalS.let0,
        case [h1, h2] {
          all_goals { apply ih, assumption },
        },
      },
    },
    case if0 : a_c e_t e_e {
      cases_on_interp h_c : ε.nth a_c : v_c,
      simp only [interpS] at h,
      split_ifs at h with h_if h_if',
      case_c {
        apply_c evalS.if0_true,
        case hc { apply interpVar_evalS, assumption },
        case hv { assumption },
        case hr { apply ih, assumption },
      },
      case_c {
        apply_c evalS.if0_false,
        case hc { apply interpVar_evalS, assumption },
        case hv { assumption },
        case hr { apply ih, assumption },
      },
      case_c {
        cases_on_interp h_rt : interpS f fuel e_t ε (f.assume σ (f.truth v_c)) : rt,
        cases_on_interp h_rf : interpS f fuel e_e ε (f.assume σ (f.not (f.truth v_c))) : rf,
        simp only [interpS] at h,
        unfold_coes at h,
        simp only at h,
        subst_vars,
        apply_c evalS.if0_sym,
        case hc { apply interpVar_evalS, assumption },
        case hv { simp [h_if, h_if'] },
        case ht { apply ih, assumption },
        case hf { apply ih, assumption },
      },
    },
  },
end

lemma interpS_bump_fuel {fuel : ℕ}
  {e : exp D O} {ε : sym.env SymV} {r : sym.result SymB SymV} {σ : sym.state SymB}
  (h : interpS f fuel e ε σ = some r) : interpS f (fuel + 1) e ε σ = some r :=
begin
  induction fuel with fuel ih generalizing e ε σ r,
  case zero { contradiction },
  case succ {
    cases e, 
    all_goals { simp only [interpS] at h },
    case [error, abort, bool, datum, lam] {
      all_goals { 
        subst_vars,
        constructor_c,
      },
    },
    case var { simpa [interpS] },
    case call : a_f a_a {
      cases_on_interp h_f : ε.nth a_f : v_f,
      simp only [interpS] at h,
      cases_on_interp h_a : ε.nth a_a : v_a,
      simp only [interpS] at h,
      split_ifs at h with h_if,
      case_b {
        generalize_hyp h_map : list.mmap _ _ = r_map at h,
        cases_on_interp h_r : r_map : grs,
        simp only [interpS] at h,
        simp only [interpS, h_f, h_a, ← h],
        split_ifs,
        generalize h_map' : list.mmap _ _ = r_map',
        have : r_map = r_map' := by {
          cases r_map',
          case none {
            obtain ⟨i, hi, h_map''⟩ := mmap.eq_none h_map',
            have h_len := mmap.length h_map,
            replace h_map := mmap.eq_some h_map,
            specialize h_map i hi (by simp [← h_len, hi]),
            cases list.nth_le (f.cast v_f) i hi with g cl,
            cases cl with x e_b ε_static,
            simp only [interpS] at h_map h_map'',
            cases_on_interp h_body : 
              interpS f fuel e_b 
                (list.update_nth ε_static x v_a) 
                (f.assume (f.assert σ (f.some choice.guard (f.cast v_f))) g) : 
              r_body,
            replace ih := ih h_body,
            simp only [interpS] at ih,
            contra [ih, interpS] at h_map'',
          },
          case some {
            subst r_map,
            simp only,
            apply_c list.ext_le,
            case hl { simp [← mmap.length h_map, ← mmap.length h_map'] },
            case h {
              intros i hi hj,
              have h_len : i < (f.cast v_f).length := by simp [mmap.length h_map, hi],
              replace h_map := mmap.eq_some h_map i h_len hi,
              replace h_map' := mmap.eq_some h_map' i h_len hj,
              cases list.nth_le (f.cast v_f) i h_len with g cl,
              cases cl with x e_b ε_static,
              simp only [interpS] at h_map h_map',
              cases_on_interp h_body : 
                interpS f fuel e_b 
                  (list.update_nth ε_static x v_a) 
                  (f.assume (f.assert σ (f.some choice.guard (f.cast v_f))) g) : 
                r_body,
              replace ih := ih h_body,
              simp only [interpS] at ih h_map,
              simp only [ih, interpS] at h_map',
              simp [← h_map, ← h_map'],
            },
          },
        },
        simp [← this, h_r, interpS],
      },
      case_c { simpa [interpS, h_if, h_f, h_a] },
    },
    case app : o as {
      cases_on_interp h_as : mmap (λ (a : ℕ), ε.nth a) as : vs,
      simp [interpS, h_as, h],
    },
    case if0 : a_c e_t e_e {
      cases_on_interp h_c : ε.nth a_c : v_c,
      simp only [interpS] at h,
      simp only [interpS, h_c] at ⊢,
      split_ifs at h ⊢ with h_if h_if',
      case_c { exact ih h },
      case_c { exact ih h },
      case_c {
        cases_on_interp h_rt : interpS f fuel e_t ε (f.assume σ (f.truth v_c)) : r_t,
        cases_on_interp h_rf : interpS f fuel e_e ε (f.assume σ (f.not (f.truth v_c))) : r_f,
        simp only [interpS] at h,
        replace h_rt := ih h_rt,
        replace h_rf := ih h_rf,
        simp only [interpS] at h_rt h_rf,
        simp [h_rt, h_rf, interpS, h],
      },
    },
    case let0 : x e_v e_b {
      cases_on_interp h_v : interpS f fuel e_v ε σ : r_v,
      replace h_v := ih h_v,
      cases r_v,
      case halt {
        simp only [interpS] at h h_v,
        simp only [interpS, h_v],
        assumption,
      },
      case ans {
        simp only [interpS] at h h_v,
        simp only [interpS, h_v],
        exact ih h,
      },
    },
  },
end

lemma interpS_bump_large_fuel 
  {e : exp D O} {ε : sym.env SymV} {σ : sym.state SymB}
  {r : sym.result SymB SymV} {fuel : ℕ} (extra_fuel : ℕ)
  (h : interpS f fuel e ε σ = some r) :
  interpS f (fuel + extra_fuel) e ε σ = some r :=
begin
  induction extra_fuel,
  case zero { assumption },
  case succ { apply interpS_bump_fuel, assumption },
end

lemma interpS_bump_fuel_app_sym
  {gcs : choices SymB (clos D O SymV)} {grs : choices SymB (sym.result SymB SymV)}
  {v : SymV} {σ : sym.state SymB}
  (h : ∀ (i : ℕ) (hi_gcs : i < list.length gcs) (hi_grs : i < list.length grs),
    (λ (gc : choice SymB (clos D O SymV)),
      ∃ (fuel : ℕ), 
        interpS f fuel gc.value.exp (gc.value.env.update_nth gc.value.var v) (f.assume σ gc.guard) = 
        some (list.nth_le grs i hi_grs).value)
      (list.nth_le gcs i hi_gcs)) :
  ∃ (fuel : ℕ),
    ∀ (i : ℕ) (hi_gcs : i < list.length gcs) (hi_grs : i < list.length grs),
      (λ (gc : choice SymB (clos D O SymV)), 
        interpS f fuel gc.value.exp (gc.value.env.update_nth gc.value.var v) (f.assume σ gc.guard) = 
        some (list.nth_le grs i hi_grs).value)
      (list.nth_le gcs i hi_gcs) :=
begin 
  induction gcs with hd tl ih generalizing grs,
  case nil {
    use 0,
    intros,
    contra at hi_gcs,
  },
  case cons {
    cases grs,
    case nil {
      use 0,
      intros,
      contra at hi_grs,
    },
    case cons {
      cases hd with g v,
      specialize ih (by {
        intros,
        specialize h (i + 1) (by simpa) (by simpa),
        cases h with fuel h,
        use fuel,
        assumption,
      }),
      cases ih with fuel ih,
      specialize h 0 (by simp) (by simp),
      cases h with fuel' h,
      use fuel + fuel',
      intros,
      cases i,
      case zero {
        replace h := interpS_bump_large_fuel fuel h,
        rewrite (by linarith : fuel + fuel' = fuel' + fuel),
        subst_vars,
        assumption,
      },
      case succ {
        apply interpS_bump_large_fuel,
        apply ih,
      },
    },
  },
end

-- The symbolic interpreter is complete:
-- If `evalS` produces a symbolic result `r`
-- on a program `e` and a symbolic environment `ε`, then 
-- there exists a `fuel` such that running `interpS` with `fuel` also
-- produces `r` on `e` and `ε`
lemma interpS_completeness 
  {e : exp D O} {ε : sym.env SymV} {r : sym.result SymB SymV} {σ : sym.state SymB}
  (h : evalS f e ε σ r) : ∃ (fuel : ℕ), interpS f fuel e ε σ = some r :=
begin
  induction h,
  case [bool, error, abort, datum, lam] {
    all_goals {
      use 1, trivial,
    },
  },
  case call_halt : ε_static _ _ a_f a_a _ _ _ _ _ h_not_clos h_e_f h_e_a {
    use 1,
    cases h_e_f with _ h_e_f,
    replace h_e_f := interpS_bump_fuel h_e_f,
    cases h_e_a with _ h_e_a,
    replace h_e_a := interpS_bump_fuel h_e_a,
    
    simp only [interpS] at h_e_f h_e_a ⊢,
    cases_on_interp h_f : ε_static.nth a_f : v_f,
    cases_on_interp h_a : ε_static.nth a_a : v_a,
    simp only [interpS] at h_e_f h_e_a ⊢,
    cases h_e_a,
    cases h_e_f,
    subst_vars,
    simp [interpS, h_a, h_not_clos],
  },
  case call_sym : ε_static _ _ a_f a_a _ _ _ _ _ _ h_cond h_guard_same _ h_e_f h_e_a h_e_b {
    have h_len_g := h_guard_same,
    apply_fun list.length at h_len_g,
    simp only [list.length_map] at h_len_g,

    replace h_e_b := interpS_bump_fuel_app_sym h_e_b,
    cases h_e_b with fuel h_e_b,
    cases h_e_f with _ h_e_f,
    replace h_e_f := interpS_bump_fuel h_e_f,
    cases h_e_a with _ h_e_a,
    replace h_e_a := interpS_bump_fuel h_e_a,
    use fuel + 1,
    simp only [interpS] at h_e_f h_e_a ⊢,
    cases_on_interp h_f : ε_static.nth a_f : v_f,
    simp only [interpS] at h_e_f ⊢,
    cases_on_interp h_a : ε_static.nth a_a : v_a,
    simp only [interpS] at h_e_a ⊢,
    cases h_e_f,
    cases h_e_a,
    subst_vars,
    simp only [h_cond, bor_coe_iff, if_false, or_self],
    cases h_map : mmap _ _,
    case none {
      rcases mmap.eq_none h_map with ⟨i, hi, h_map'⟩,
      specialize h_e_b i hi (by { simpa [← h_len_g] }),
      cases list.nth_le (f.cast v_f) i hi with g cl,
      cases cl,
      contra [interpS, h_e_b] at h_map',
    },
    case some {
      have h_len := mmap.length h_map,
      replace h_map := mmap.eq_some h_map,
      simp only [interpS],
      congr,
      apply_c list.ext_le,
      case hl { simp [← h_len_g, ← h_len] },
      case h {
        intros i hi hj,
        have h_len_cast : i < list.length (f.cast v_f) := by simpa [h_len_g],
        specialize h_map i h_len_cast hi,
        specialize h_e_b i (by simpa [h_len]) hj,
        cases h_cast : list.nth_le (f.cast v_f) i h_len_cast with g cl,
        cases cl,
        simp only [h_cast] at h_e_b,
        simp only [interpS, h_e_b, h_cast] at h_map,
        cases h_nth : list.nth_le h_grs i hj,
        simp only [h_nth] at h_map,
        apply_fun choice.guard at h_nth,
        rw [list.nth_le_map_rev choice.guard, ← list.nth_le_of_eq h_guard_same] at h_nth,
        case_b { simpa },
        case_c {
          simp only [h_cast, list.nth_le_map'] at h_nth,
          simp [← h_map, h_nth],
        },
      },
    },
  },
  case var : ε' _ x h {
    use 1,
    generalize h' : ε'.nth_le x h = v,
    apply_fun some at h',
    simp only [← list.nth_le_nth] at h',
    simp [h', interpS],
  },
  case app : ε _ o xs vs h_len h ih {
    use 1,
    simp only [interpS],
    cases h_map : mmap (λ (a : ℕ), ε.nth a) xs,
    case none {
      rcases mmap.eq_none h_map with ⟨i, hi, h_map'⟩,
      have hi' : i < vs.length := by { simp only [h_len] at hi, assumption },
      specialize ih i hi hi',
      cases ih with _ ih,
      replace ih := interpS_bump_fuel ih,
      simp only at h_map',
      contra [interpS, h_map'] at ih,
    },
    case some {
      simp only [interpS],
      have h_len_eq := mmap.length h_map,
      replace h_map := mmap.eq_some h_map,
      congr,
      apply_c list.ext_le,
      case hl { cc },
      case h {
        intros i hi_a hi_v,
        have hi' : i < xs.length := by { simp only [← h_len] at hi_v, assumption },
        specialize h_map i (by assumption) (by assumption),
        specialize ih i (by assumption) (by assumption),
        specialize h i (by assumption) (by assumption),
        cases ih with _ ih,
        replace ih := interpS_bump_fuel ih,
        simp only [interpS] at ih,
        cases_on_interp h_interp : ε.nth (xs.nth_le i hi') : v,
        simp only [interpS] at ih,
        cases ih,
        subst_vars,
        simp only [h_interp] at h_map,
        simp [h_map],
      },
    },
  },
  case let0 : _ _ _ _ _ _ _ _ _ _ h_e_v h_e_b {
    cases h_e_v with fuel_v h_e_v,
    cases h_e_b with fuel_b h_e_b,
    use fuel_v + fuel_b + 1,
    simp only [
      interpS, 
      interpS_bump_large_fuel fuel_b h_e_v,
      ← interpS_bump_large_fuel fuel_v h_e_b
    ],
    congr' 1,
    linarith,
  },
  case let0_halt : _ _ _ _ _ _ _ h_e_v {
    cases h_e_v with fuel_v h_e_v,
    use fuel_v + 1,
    simp [interpS, h_e_v],
  },
  case [if0_true : ε _ a_c e_t e_e _ _ _ h_c _ h_e_c h_e_b, 
        if0_false : ε _ a_c e_t e_e _ _ _ h_c _ h_e_c h_e_b] {
    all_goals {
      cases h_e_c with _ h_e_c,
      cases h_e_b with fuel_b h_e_b,
      use fuel_b + 1,
      replace h_e_c := interpS_bump_fuel h_e_c,
      simp only [interpS] at ⊢ h_e_c,
      cases_on_interp h_interp : ε.nth a_c : v_c,
      simp only [interpS] at h_e_c,
      cases h_e_c,
      subst_vars,
      simp [h_e_b],
    },
    case_c {
      simp only [interpS, eq_ff_eq_not_eq_tt, ite_eq_left_iff],
      intro h,
      contra [h] at h_c,
    },
    case_c { 
      simp only [interpS, h_c, if_true, ite_eq_right_iff],
      intro h_contradict,
      simp only [f.is_ff_sound] at h_c,
      simp only [f.is_tt_sound] at h_contradict,
      simp only [h_contradict] at h_c,
      cases mk_tt_ne_mk_ff h_c,
    },  
  },
  case if0_sym : ε _ a_c e_t e_e _ _ _ _ h_c _ _ h_e_c h_e_t h_e_f {
    cases h_e_c with _ h_e_c,
    replace h_e_c := interpS_bump_fuel h_e_c,
    simp only [interpS] at h_e_c,
    cases_on_interp h_c' : list.nth ε a_c : v_c,
    simp only [interpS, true_and, eq_self_iff_true] at h_e_c,
    cases h_e_t with fuel_t h_e_t,
    cases h_e_f with fuel_f h_e_f,
    use fuel_t + fuel_f + 1,
    subst_vars,
    simp only [interpS, h_c', h_c, if_false],
    replace h_e_t := interpS_bump_large_fuel fuel_f h_e_t,
    replace h_e_f := interpS_bump_large_fuel fuel_t h_e_f,
    simp only [(by linarith : fuel_f + fuel_t = fuel_t + fuel_f)] at h_e_f,
    simp only [h_e_t, h_e_f, interpS],
    unfold_coes,
  },
end

end interp

end interp