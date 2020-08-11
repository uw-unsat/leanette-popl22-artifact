-- This file contains theorems related to Lean / mathlib libraries.

import ..tactic.all

local attribute [simp] mmap return option.bind

attribute [simp] nat.succ_eq_add_one

section mmap

  lemma mmap.length {A V : Type} {f : A → option V} 
    {as : list A} {vs : list V}
    (h : mmap f as = some vs) :
    as.length = vs.length :=
  begin
    induction as with hd tl ih generalizing vs,
    case nil { finish [pure] },
    case cons {
      simp only [mmap] at h,
      cases f hd,
      case none { finish },
      case some {
        cases mmap f tl,
        all_goals { finish [pure] },
      },
    },
  end

  lemma mmap.eq_some {A V : Type} {f : A → option V}
    {as : list A} {vs : list V}
    (h : mmap f as = some vs) (i : ℕ) (hi_a : i < as.length) (hi_v : i < vs.length) :
    f (as.nth_le i hi_a) = some (vs.nth_le i hi_v) :=
  begin
    induction as with hd tl ih generalizing vs i,
    case nil { contra at hi_a },
    case cons {
      simp only [pure, option.bind_eq_some, mmap, return] at h,
      rcases h with ⟨a, h_hd, vs', h_tl, h_eq⟩,
      cases i,
      case zero { finish },
      case succ {  
        subst_vars,
        apply ih,
        assumption,
      },
    },
  end

  lemma mmap.eq_none {A V : Type} {f : A → option V} {as : list A}
    (h : mmap f as = none) :
    ∃ (i : ℕ) (hi_a : i < as.length), f (as.nth_le i hi_a) = none :=
  begin
    induction as with hd tl ih,
    case nil { contradiction },
    case cons {
      simp only [
        not_exists, option.bind_eq_some, option.bind_eq_none, 
        mmap, option.mem_def
      ] at h,
      cases h_hd : f hd,
      case none { use [0, by simpa] },
      case some {
        cases mmap f tl,
        case none {
          obtain ⟨i, _, _⟩ := ih (by simp),
          use [i + 1, by simpa],
          assumption,
        },
        case some : vs {
          specialize h (val :: vs) val h_hd vs,
          finish,
        },
      },
    },
  end

end mmap 

section list

  lemma list.append_eq_singleton_implies_other_eq_nil {τ : Type} 
    {xs ys : list τ} {x : τ} 
    (h : xs ++ (x :: ys) = [x]) : xs = [] ∧ ys = [] :=
  begin 
    apply_fun list.length at h,
    simp only [list.length_append, list.length] at h,
    split_c,
    all_goals { simp only [← list.length_eq_zero], linarith },
  end
  
end list