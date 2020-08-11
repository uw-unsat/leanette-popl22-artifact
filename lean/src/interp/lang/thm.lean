import ...cs.lang
import .defs
import ..tactic
import ...basic.basic

namespace interp

section interp

variables 
  {D O : Type}
  {op : O → list (lang.val D O) → lang.result D O}

open lang

lemma interpVar_evalC  
  {a : ℕ} {ε : env D O} {v : val D O} 
  (h : ε.nth a = some v) : evalC op (exp.var a) ε (result.ans v) :=
begin
  simp only [list.nth_eq_some] at h,
  cases h with _ h',
  subst_vars,
  constructor,
end

-- The concrete interpreter is sound:
-- if running `interpC` with `fuel` produces a concrete result `r`
-- on a program `e` and a concrete environment `ε`, then 
-- `evalC` also produces `r` on `e` and `ε`.
lemma interpC_soundness 
  {e : exp D O} {ε : env D O} {r : lang.result D O} {fuel : ℕ}
  (h : interpC op fuel e ε = some r) : evalC op e ε r :=
begin
  induction fuel with fuel ih generalizing e ε r,
  case zero { contradiction },
  case succ {
    cases e,
    all_goals { simp only [interpC] at h },
    case [error, abort, bool, datum, lam] {
      all_goals { subst_vars, constructor },
    },
    case var : a {
      cases_on_interp h_a : ε.nth a : v,
      simp only [interpC] at h,
      subst_vars,
      apply interpVar_evalC,
      assumption,
    },
    case call : a_f a_a {
      cases_on_interp h_f : ε.nth a_f  : v_f,
      simp only [interpC] at h,
      cases_on_interp h_f : ε.nth a_a : v_a,
      cases v_f,
      case clos : x e_b ε_static {
        simp only [interpC] at h,
        constructor_c,
        case [h1, h2] {
          all_goals {
            apply interpVar_evalC,
            all_goals { assumption },
          },
        },
        case h3 { apply ih, assumption },
      },
      all_goals {
        simp only [interpC] at h,
        subst_vars,
        apply_c evalC.call_halt,
        case [h1, h2] {
          all_goals {
            apply interpVar_evalC,
            all_goals { assumption },
          },
        },
        case h3 { simp },
      },
    },
    case app : o as {
      cases_on_interp h_as : mmap (λ (a : ℕ), ε.nth a) as : vs,
      simp only [interpC] at h,
      subst_vars,
      constructor_c,
      case h1 { apply mmap.length, assumption },
      case h2 {
        intros i hi_a hi_v,
        apply interpVar_evalC,
        exact mmap.eq_some h_as i hi_a hi_v,
      },
    },
    case if0 : a_c e_t e_e {
      cases_on_interp h_c : ε.nth a_c : v_c,
      cases v_c,
      focus_case bool : b {
        cases b,
        case ff {
          cases_on_interp h_e : interpC op fuel e_e ε : r_e,
          simp only [interpC] at h,
          subst_vars,
          apply_c evalC.if0_false,
          case hc { apply interpVar_evalC, assumption },
          case hv { simp },
          case hr { apply ih, assumption },
        },
      },
      all_goals {
        simp only [interpC] at h,
        cases_on_interp h_t : interpC op fuel e_t ε : r_t,
        simp only [interpC] at h,
        subst_vars,
        apply_c evalC.if0_true,
        case hc { apply interpVar_evalC, assumption },
        case hv { simp },
        case hr { apply ih, assumption },
      },
    },
    case let0 : x e_v e_b {
      cases_on_interp h_v : interpC op fuel e_v ε : r_v,
      cases r_v,
      case halt {
        simp only [interpC] at h,
        subst_vars,
        apply evalC.let0_halt,
        apply ih,
        assumption,
      },
      case ans {
        simp only [interpC] at h,
        apply_c evalC.let0,
        case [h1, h2] {
          all_goals { apply ih, assumption },
        },
      },
    },
  },
end

lemma interpC_bump_fuel 
  {e : exp D O} {ε : env D O} {r : lang.result D O} {fuel : ℕ}
  (h : interpC op fuel e ε = some r) : interpC op (fuel + 1) e ε = some r :=
begin
  induction fuel with fuel ih generalizing e ε r,
  case zero { contradiction },
  case succ {
    cases e, 
    all_goals { simp only [interpC] at h },
    case [error, abort, bool, datum, lam] {
      all_goals { 
        subst_vars,
        constructor_c,
      },
    },
    case var { simpa [interpC] },
    case call : a_f a_a {
      cases_on_interp h_f : ε.nth a_f : v_f,
      simp only [interpC] at h,
      cases_on_interp h_a : ε.nth a_a : v_a,
      cases v_f,
      case clos {
        simp only [interpC] at h,
        simp only [interpC, h_f, h_a],
        exact ih h,
      },
      all_goals {
        simp only [interpC] at h,
        simp [interpC, h_f, h_a, h],
      },
    },
    case app : o as {
      cases_on_interp h_as : mmap (λ (a : ℕ), ε.nth a) as : vs,
      simp [interpC, h_as, h],
    },
    case if0 : a_c e_t e_e {
      cases_on_interp h_c : ε.nth a_c : v_c,
      cases v_c,
      focus_case bool : b { cases b },
      focus_case [bool ff] {
        simp only [interpC] at h,
        cases_on_interp h_e : interpC op fuel e_e ε,
      },
      focus_case [bool tt, clos, datum] {
        simp only [interpC] at h,
        cases_on_interp h_t : interpC op fuel e_t ε,
      },
      all_goals {
        simp only [interpC] at h,
        subst_vars,
        simp only [interpC, h_c],
        apply ih,
        assumption,
      },
    },
    case let0 : x e_v e_b {
      cases_on_interp h_v : interpC op fuel e_v ε : r_v,
      replace h_v := ih h_v,
      cases r_v,
      case halt {
        simp only [interpC] at h h_v,
        simp only [interpC, h_v],
        assumption,
      },
      case ans {
        simp only [interpC] at h h_v,
        simp only [interpC, h_v],
        exact ih h,
      },
    },
  },
end

lemma interpC_bump_large_fuel
  {e : exp D O} {ε : env D O} 
  {r : lang.result D O} {fuel : ℕ} (extra_fuel : ℕ)
  (h : interpC op fuel e ε = some r) :
  interpC op (fuel + extra_fuel) e ε = some r :=
begin
  induction extra_fuel,
  case zero { assumption },
  case succ { apply interpC_bump_fuel, assumption },
end

-- The concrete interpreter is complete:
-- If `evalC` produces a concrete result `r`
-- on a program `e` and a concrete environment `ε`, then 
-- there exists a `fuel` such that running `interpC` with `fuel` also
-- produces `r` on `e` and `ε`
lemma interpC_completeness 
  {e : exp D O} {ε : env D O} {r : lang.result D O}
  (h : evalC op e ε r) : ∃ (fuel : ℕ), interpC op fuel e ε = some r :=
begin
  induction h,
  case [bool, error, abort, datum, lam] {
    all_goals {
      use 1, trivial,
    },
  },
  case call_halt : ε a_f a_a _ _ _ _ h_not_clos h_e_f h_e_a {
    use 1,
    cases h_e_f with _ h_e_f,
    replace h_e_f := interpC_bump_fuel h_e_f,
    cases h_e_a with _ h_e_a,
    replace h_e_a := interpC_bump_fuel h_e_a,
    
    simp only [interpC] at h_e_f h_e_a ⊢,
    cases_on_interp h_f : ε.nth a_f : v_f,
    cases_on_interp h_a : ε.nth a_a : v_a,
    simp only [interpC] at h_e_f h_e_a ⊢,

    subst_vars,
    cases v_f,
    case clos { contra [val.is_clos] at h_not_clos },
    all_goals { simp [h_a, interpC] },
  },
  case call : ε a_f a_a _ _ _ _ _ _ _ _ h_e_f h_e_a h_e_b {
    cases h_e_b with the_fuel h_e_b,
    use (the_fuel + 1),
    cases h_e_f with _ h_e_f,
    replace h_e_f := interpC_bump_fuel h_e_f,
    cases h_e_a with _ h_e_a,
    replace h_e_a := interpC_bump_fuel h_e_a,
    simp only [interpC] at h_e_f h_e_a ⊢,
    cases_on_interp h_f : ε.nth a_f : v_f,
    cases_on_interp h_a : ε.nth a_a : v_a,
    simp only [interpC] at h_e_f h_e_a ⊢,
    subst_vars,
    simp [h_a, interpC, h_e_b],
  },
  case var : ε' x h {
    use 1,
    generalize h' : ε'.nth_le x h = v,
    apply_fun some at h',
    simp only [← list.nth_le_nth] at h',
    simp [h', interpC],
  },
  case app : ε o xs vs h_len h ih {
    use 1,
    simp only [interpC],
    cases h_map : mmap (λ (a : ℕ), ε.nth a) xs,
    case none {
      rcases mmap.eq_none h_map with ⟨i, hi, h_map'⟩,
      have hi' : i < vs.length := by { simp only [h_len] at hi, assumption },
      specialize ih i hi hi',
      cases ih with _ ih,
      replace ih := interpC_bump_fuel ih,
      simp only at h_map',
      contra [interpC, h_map'] at ih,
    },
    case some {
      simp only [interpC],
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
        replace ih := interpC_bump_fuel ih,
        simp only [interpC] at ih,
        cases_on_interp h_interp : ε.nth (xs.nth_le i hi') : v,
        simp only [interpC] at ih,
        subst_vars,
        simp only [h_interp] at h_map,
        simp [h_map],
      },
    },
  },
  case let0 : ε x e_v e_b v_v r_b _ _ h_e_v h_e_b {
    cases h_e_v with fuel_v h_e_v,
    cases h_e_b with fuel_b h_e_b,
    use fuel_v + fuel_b + 1,
    simp only [
      interpC, 
      interpC_bump_large_fuel fuel_b h_e_v,
      ← interpC_bump_large_fuel fuel_v h_e_b
    ],
    congr' 1,
    linarith,
  },
  case let0_halt : ε x e_v e_b _ _ h_e_v {
    cases h_e_v with fuel_v h_e_v,
    use fuel_v + 1,
    simp [interpC, h_e_v],
  },
  case [if0_true : ε a_c e_t e_e _ _ _ h_c _ h_e_c h_e_b, 
        if0_false : ε a_c e_t e_e _ _ _ h_c _ h_e_c h_e_b] {
    all_goals {
      cases h_e_c with _ h_e_c,
      cases h_e_b with fuel_b h_e_b,
      use fuel_b + 1,
      replace h_e_c := interpC_bump_fuel h_e_c,
      simp only [interpC] at ⊢ h_e_c,
      cases_on_interp h_interp : ε.nth a_c : v_c,
      simp only [interpC] at h_e_c,
      subst_vars,
      simp [h_e_b],
    },
    case_c {
      cases v_c,
      focus_case bool : b { 
        cases b,
        case ff { trivial },
      },
      all_goals { simp [interpC] },
    },
    case_c { simp [interpC] },  
  },
end

end interp

end interp