import ..tactic.all
import ..cs.lang
import ..cs.sym
import ..op.sym
import ..cs.util
import .defs
import ..cs.lib
import ..op.simp
import ..basic.basic
import ..op.basic
import ..basic.sym

namespace sym_factory

open sym
open op.sym
open op.lang.op

lemma mk_tt.sound {m : model} : evalB m mk_tt = tt := 
 by simp [mk_tt, op.sym.evalB, term.is_true, term.eval, lit.to_bool]

lemma mk_ff.sound {m : model} : evalB m mk_ff = ff :=
  by simp [mk_ff, op.sym.evalB, term.is_true, term.eval, lit.to_bool]

lemma is_tt.sound {t : term type.bool} : (is_tt t) ↔ (t = mk_tt) :=
begin 
  split_c,
  case mp {
    cases t,
    case lit : l {
      cases l with b,
      cases b,
      all_goals { simp [is_tt, mk_tt] }
    },
    all_goals { simp [is_tt] },
  },
  case mpr {
    intros h,
    simp [h, is_tt, mk_tt],
  },
end

lemma is_ff.sound {t : term type.bool} : (is_ff t) ↔ (t = mk_ff) :=
begin 
  split_c,
  case mp {
    cases t,
    case lit : l {
      cases l with b,
      cases b,
      all_goals { simp [is_ff, mk_ff] }
    },
    all_goals { simp [is_ff] },
  },
  case mpr {
    intros h,
    simp [h, is_ff, mk_ff],
  },
end

lemma pe_not.is_true {m : model} {t : term type.bool} :
  (pe_not t).is_true m = !(t.is_true m) :=
begin
  cases t,
  all_goals { simp only [pe_not, mk_ff, mk_tt, bnot] with term_is_true},
  case lit : l { cases l with b, simp [pe_not] with term_is_true },
  focus_case var  : x           { cases m type.bool x },
  focus_case ite  : t_c t_t t_e { cases ite ((t_c.eval m).to_bool) (t_t.eval m) (t_e.eval m) },
  focus_case expr : o t_a t_b   { cases o.eval (t_a.eval m) (t_b.eval m) },
  all_goals {
    unfold_coes,
    split_ifs with h_if,
    all_goals { finish },
  },
end

lemma pe_and.is_true {m : model} {t_a t_b : term type.bool} :
  (pe_and t_a t_b).is_true m = t_a.is_true m && t_b.is_true m :=
begin 
  cases t_a,
  all_goals { simp only [pe_and, mk_ff, mk_tt] with term_is_true },
  case lit : l_a {
    cases l_a with b_a,
    cases b_a,
    all_goals { 
      cases t_b,
      focus_case lit : l_b {
        cases l_b with b_b,
        cases b_b,
      },
      all_goals { simp [pe_and, mk_ff] with term_is_true },
    },
  },
  focus_case var  : x           { cases h_a : m type.bool x },
  focus_case ite  : t_c t_t t_e { cases h_a : ite ((t_c.eval m).to_bool) (t_t.eval m) (t_e.eval m) },
  focus_case expr : o t_l t_r   { cases h_a : o.eval (t_l.eval m) (t_r.eval m) },
  all_goals {
    cases t_b,
    case lit : l_b {
      cases l_b with b_b,
      cases b_b,
      all_goals { simp [pe_and, mk_ff, h_a] with term_is_true },
    },
    any_goals {
      solve1 {
        simp [pe_and, h_a] with term_is_true,
        unfold_coes,
        split_ifs,
        all_goals { finish },
      },
    },
  },
  all_goals {
    simp [pe_and],
    split_ifs with h_if,
    case_c {
      cases_matching* [_ ∧ _],
      subst_vars,
      simp [h_a] with term_is_true,
    },
  },
  all_goals {
    simp [h_a] with term_is_true,
    unfold_coes,
    split_ifs,
    all_goals { finish },
  },
end

lemma pe_or.is_true {m : model} {t_a t_b : term type.bool} :
  (pe_or t_a t_b).is_true m = t_a.is_true m || t_b.is_true m :=
begin 
  cases t_a,
  all_goals { simp only [pe_or, term.is_true, term.eval, mk_ff, mk_tt] },
  case lit : l_a {
    cases l_a with b_a,
    cases b_a,
    all_goals { 
      cases t_b,
      focus_case lit : l_b {
        cases l_b with b_b,
        cases b_b,
      },
      all_goals { simp [pe_or, mk_tt] with term_is_true },
    },
  },
  focus_case var  : x           { cases h_a : m type.bool x },
  focus_case ite  : t_c t_t t_e { cases h_a : ite ((t_c.eval m).to_bool) (t_t.eval m) (t_e.eval m) },
  focus_case expr : o t_l t_r   { cases h_a : o.eval (t_l.eval m) (t_r.eval m) },
  all_goals {
    cases t_b,
    case lit : l_b {
      cases l_b with b_b,
      cases b_b,
      all_goals { simp [pe_or, mk_tt, h_a] with term_is_true },
    },
    any_goals {
      solve1 {
        simp [pe_or, h_a] with term_is_true,
        unfold_coes,
        split_ifs,
        all_goals { finish },
      },
    },
  },
  all_goals {
    simp [pe_or],
    split_ifs with h_if,
    case_c {
      cases_matching* [_ ∧ _],
      subst_vars,
      simp [h_a] with term_is_true,
    },
  },
  all_goals {
    simp [h_a] with term_is_true,
    unfold_coes,
    split_ifs,
    all_goals { finish },
  },
end

lemma pe_not.sound {m : model} {t : term type.bool} :
  evalB m (pe_not t) = ¬ (evalB m t) :=
begin 
  simp [evalB, pe_not.is_true],
  cases h : t.is_true m,
  all_goals { simp [h] },
end

lemma pe_imp.sound {m : model} {t_a t_b : term type.bool} :
  evalB m (pe_imp t_a t_b) = ((evalB m t_a) → (evalB m t_b)) :=
begin 
  simp [evalB, pe_imp, pe_or.is_true, pe_not.is_true],
  cases h : t_a.is_true m,
  all_goals { simp [h] },
end


lemma truth.atom.sound {m : model} {v : val_atom} {w : op.lang.val}
  (h : evalV m (val.atom v) = w) :
  evalB m (truth.atom v) ↔ w ≠ @lang.val.bool op.lang.datum op.lang.op ff :=
begin 
  cases v,
  focus_case term : τ t {
    cases τ,
    case bool {
      simp only [truth.atom, evalB, term.is_true],
      simp only [evalV, val.eval, val_atom.eval] at h,
      subst_vars,
      cases t.eval m with b,
      simp [lit.to_bool, lit.to_val],
    },
    case int {
      simp only [evalV, val.eval] at h,
      cases int.evals_to_int h with _ h_int,
      subst_vars,
      simp [h_int, truth.atom, evalB] with term_is_true,
    },
  },
  case clos {
    simp only [evalV, val.eval] at h,
    have h_clos := clos.evals_to_clos h,
    cases w,
    case clos { simp [truth.atom, evalB] with term_is_true },
    all_goals { contra [lang.val.is_clos] at h_clos },
  },
  case list {
    simp only [evalV, val.eval] at h,
    have h_list := list.evals_to_list h,
    cases w,
    case list { simp [truth.atom, evalB] with term_is_true },
    all_goals { contra [op.lang.val.is_list] at h_list },
  },
end

lemma truth.sound {m : model} {v : val} :
  evalB m (truth v) ↔ evalV m v ≠ lang.val.bool ff :=
begin 
  cases v with v h_wf,
  cases v,
  case union : gvs {
    induction gvs with hd tl ih,
    case nil {
      simp [truth, evalV, val.eval, op.sym.choices.eval, evalB, op.lang.undef] 
        with term_is_true,
    },
    case cons {
      cases hd with g v,
      generalize h : evalV _ _ = w,
      cases g,
      case lit : l {
        simp only [evalV, val.eval, op.sym.choices.eval] at h,
        cases l with b,
        cases b,
        all_goals { simp only [truth], simp with term_is_true at h },
        case tt { exact @truth.atom.sound m v w (by simpa [evalV, val.eval]) },
        case ff { simp [ih, evalV, val.eval, h] },
      },
      all_goals { 
        simp only [evalV, val.eval, op.sym.choices.eval, term.is_true] at h,
        simp only [truth, evalB, term.is_true],
        simp only [term.eval] {single_pass := tt},
        split_ifs at h ⊢ with h_if,
        case_c { exact @truth.atom.sound m v w (by simpa [evalV, val.eval]) },
        case_c { 
          simp only [evalB, term.is_true] at ih, 
          simp [ih, evalV, val.eval, h] 
        },
      },
    },
  },
  all_goals {
    simp only [truth],
    apply truth.atom.sound,
    simp,
  },
end

lemma bval.sound {m : model} {b : bool} : evalV m (bval b) = lang.val.bool b :=
  by simp [evalV, bval, val.eval, val_atom.eval, lit.to_val] with term_is_true

lemma dval.sound {m : model} {d : op.lang.datum} : evalV m (dval d) = (lang.val.datum d) :=
begin
  cases d,
  case int { simp [evalV, dval, val.eval, val_atom.eval, lit.to_val, term.eval] },
  case undef { simp [evalV, dval, val.eval, op.sym.choices.eval, op.lang.undef] },
end

lemma cval.sound {m : model} {c : op.sym.clos} : evalV m (cval c) = c.eval ev m :=
begin
  cases c with x e ε,
  simp [evalV, cval, val.eval, val_atom.eval, clos.eval, env.eval_lift],
end

lemma adjust_core.sound {τ_val τ_result : Type} {m : model} {gvs : choices' τ_val} {t_acc : term type.bool} 
  {evalV : model → τ_val → τ_result} {default : τ_result} :
  (adjust_core t_acc gvs).eval (make_ev evalV) m default =
  if t_acc.is_true m = ff then default else sym.choices.eval (make_ev evalV) m default gvs :=
begin
  induction gvs with hd tl ih generalizing t_acc,
  case nil { simp [sym.choices.eval, adjust_core] },
  case cons {
    cases hd with g va,
    simp only [adjust_core, sym.choices.eval, pe_and.is_true, band, band_coe_iff, evalB],
    split_ifs with h_if h_if' h_if'' h_if''' h_if'''',
    case_c { contra [h_if'] at h_if },
    case_c { simp },
    case_c { contra [h_if''] at h_if },
    case_c {
      specialize @ih (pe_and (pe_not g) t_acc),
      simp only [pe_and.is_true, h_if''', if_true, eq_self_iff_true, band_ff] at ih,
      assumption,
    },
    case_c { contra [h_if''', h_if''''] at h_if },
    case_c {
      specialize @ih (pe_and (pe_not g) t_acc),
      simp only [eq_ff_eq_not_eq_tt, eq_tt_eq_not_eq_ff] at h_if''' h_if'''',
      simp [pe_and.is_true, pe_not.is_true, h_if''', h_if''''] at ih,
      assumption,
    },
  },
end


lemma adjust.sound {τ_val τ_result : Type} {m : model} {gvs : choices' τ_val} 
  {evalV : model → τ_val → τ_result} {default : τ_result} :
  (adjust gvs).eval (make_ev evalV) m default = gvs.eval (make_ev evalV) m default :=
  by simp [adjust, adjust_core.sound, mk_tt] with term_is_true

lemma adjust_core.none_after_true {τ_val τ_result : Type} {m : model} {gvs : choices' τ_val} 
  {t_acc : term type.bool} 
  {evalV : model → τ_val → τ_result}
  (h : t_acc.is_true m = ff) : 
  (adjust_core t_acc gvs).none (make_ev evalV) m :=
begin 
  simp only [choices.none, choices.true],
  induction gvs with hd tl ih generalizing t_acc,
  case nil { simp [adjust_core] },
  case cons {
    cases hd with g va,
    simp only [
      adjust_core, list.filter, ev, evalB, pe_and.is_true, 
      list.length, band, band_coe_iff, list.map
    ],
    split_ifs with h_if,
    case_c { contra [h] at h_if },
    case_c { apply ih, simp [pe_and.is_true, h] },
  },
end

lemma adjust.lone {τ_val τ_result : Type} {m : model} {gvs : choices' τ_val} 
  {evalV : model → τ_val → τ_result} : 
  (adjust gvs).lone (make_ev evalV) m :=
begin 
  simp only [choices.lone, choices.true, adjust],
  generalize : mk_tt = t_acc,
  induction gvs with hd tl ih generalizing t_acc,
  case nil { simp [adjust_core] },
  case cons {
    cases hd with g va,
    simp only [
      adjust_core, list.filter, ev, evalB, pe_and.is_true, 
      list.length, band, band_coe_iff, list.map
    ],
    split_ifs with h_if,
    case_c {
      simp only [add_le_iff_nonpos_left, list.length, nonpos_iff_eq_zero],
      apply adjust_core.none_after_true,
      unfold_coes at h_if,
      simp [pe_and.is_true, h_if, pe_not.is_true],
    },
    case_c { apply ih },
  },
end

lemma cast_choices.append {gvs_a gvs_b : choices' val_atom} : 
  cast_choices (gvs_a ++ gvs_b) = (cast_choices gvs_a) ++ (cast_choices gvs_b) :=
begin 
  induction gvs_a with hd tl ih,
  case nil { simp [cast_choices] },
  case cons {
    cases hd with g va,
    cases va,
    all_goals { simp [cast_choices, ih] },
  },
end

lemma cast_choices.preserves_none {m : model} {gvs : choices' val_atom}
  (h : gvs.none ev.atom m) : (cast_choices gvs).none ev.clos m :=
begin 
  simp only [choices.none_iff_none_true] at ⊢ h,
  induction gvs with hd tl ih,
  case nil { intros i hi, contra [cast_choices] at hi },
  case cons {
    cases hd with g va,
    specialize ih (by { intros j hj, exact h (j + 1) (by simpa) }),
    intros i hi,
    cases va,
    case clos {
      simp only [cast_choices, ev.clos],
      cases i,
      case zero {
        specialize h 0 (by simp),
        simp only [ev.atom, eq_ff_eq_not_eq_tt, list.nth_le] at h,
        simpa,
      },
      case succ { apply ih },
    },
    all_goals { simp only [cast_choices], apply ih },
  },
end

lemma merge_core.append {gvs gvs' : choices' val} : 
  (merge.core (gvs ++ gvs')) = merge.core gvs ++ merge.core gvs' :=
begin 
  induction gvs with hd tl ih,
  case nil { simp [merge.core] },
  case cons {
    cases hd with g v,
    cases v,
    case atom { simpa [merge.core] },
    case union { simp [merge.core, ih] },
  },
end

lemma merge_core.preserves_none {m : model} {gvs : choices' val}
  (h : gvs.none ev m) : (merge.core gvs).none ev.atom m :=
begin 
  induction gvs with hd tl ih,
  case nil { simp [merge.core, choices.none, choices.true] },
  case cons {
    cases hd with g v,
    cases v,
    case atom {
      simp only [merge.core],
      simp only [choices.none_iff_none_true] at ⊢ h,
      intros i hi,
      cases i,
      case zero { exact h 0 (by simp) },
      case succ {
        simp only [nat.succ_eq_add_one, list.nth_le],
        apply choices.none_implies_none_true,
        apply ih,
        simp only [choices.none_iff_none_true],
        intros j hj,
        exact h (j + 1) (by simpa),
      },
    },
    case union : gvs_sub {
      simp only [merge.core],
      simp [← choices.none_append],
      split_c,
      case left {
        simp only [choices.none_iff_none_true] at ⊢ h,
        replace h := h 0 (by simp),
        simp only [ev, evalB, eq_ff_eq_not_eq_tt, list.nth_le] at h,
        intros i hi,
        simp only [ev.atom, eq_ff_eq_not_eq_tt, list.nth_le_map', evalB],
        cases (adjust gvs_sub).nth_le i _,
        simp only [make_and, pe_and.is_true, band_eq_false_eq_eq_ff_or_eq_ff],
        left,
        assumption,
      },
      case right {
        apply ih,
        simp only [choices.none_iff_none_true] at ⊢ h,
        intros i hi,
        exact h (i + 1) (by simpa),
      },
    },
  },
end

lemma choices.none_iff_disjuction_false {τ_val τ_result : Type} 
  {m : model} {gvs : choices' τ_val} 
  {evalV : model → τ_val → τ_result} :
  (make_disjunction gvs).is_true m = ff ↔ gvs.none (make_ev evalV) m :=
begin 
  rw choices.none_iff_none_true,
  split_c,
  case mp {
    intros h,
    induction gvs with hd tl ih,
    case nil { simp },
    case cons {
      cases hd with g v,
      intros i hi,
      simp only [make_disjunction, pe_or.is_true, bor_eq_false_eq_eq_ff_and_eq_ff] at h,
      cases i,
      case zero { simp [make_disjunction, evalB, h] },
      case succ {
        simp only [h, eq_self_iff_true, forall_true_left] at ih,
        exact ih i (by { simp only [list.length, add_lt_add_iff_right, nat.succ_eq_add_one] at hi, assumption }),
      },
    },
  },
  case mpr {
    intros h,
    induction gvs with hd tl ih,
    case nil { simp [make_disjunction, mk_ff] with term_is_true },
    case cons {
      cases hd with g v,
      simp only [make_disjunction, pe_or.is_true, bor_eq_false_eq_eq_ff_and_eq_ff],
      split_c,
      case left {
        specialize h 0 (by simp),
        simp only [evalB, eq_ff_eq_not_eq_tt] at h,
        assumption,
      },
      case right {
        apply ih,
        intros i hi,
        exact h (i + 1) (by simpa),
      },
    },
  },
end

lemma choices.not_none_iff_disjuction_true {τ_val τ_result : Type} 
  {m : model} {gvs : choices' τ_val} 
  {evalV : model → τ_val → τ_result} :
  (make_disjunction gvs).is_true m = tt ↔ ¬ gvs.none (make_ev evalV) m :=
begin 
  rw ← choices.none_iff_disjuction_false,
  simp,
end

lemma merge_core.sound {gvs : choices' val} {m : model} 
  (h_lone : gvs.lone ev m) :
  evalV m (val.union (merge.core gvs)) = gvs.eval ev m op.lang.undef :=
begin 
  simp [evalV, val.eval, choices.eval_lift],
  replace h_lone := choices.lone_implies_one_or_none h_lone,
  cases h_lone,
  case inl : h_none {
    have h_none' := merge_core.preserves_none h_none,
    simp [
      choices.none_evals_none h_none, 
      choices.none_evals_none h_none'
    ],
  },
  case inr : h_one {
    generalize h_eval : choices.eval ev m op.lang.undef gvs = r,
    obtain ⟨pre, post, g, v, h_part, h_pre, h_post, h_true⟩ :=
      choices.one_implies_one_true h_one,
    simp only [ev] at h_true,
    simp only [h_part] at ⊢ h_eval,
    simp only [merge_core.append],
    have h_pre_merge : choices.none ev.atom m (merge.core pre) := by { 
      apply merge_core.preserves_none, 
      assumption,
    },
    rw choices.eval_skips_false h_pre_merge,
    rw choices.eval_skips_false h_pre at h_eval,
    simp only [ev.atom],
    simp only [ev] at h_eval,
    cases v,
    case atom {
      simp only [merge.core],
      simp only [sym.choices.eval, h_true, if_true, list.singleton_append] 
        at ⊢ h_eval,
      simp only [evalV, val.eval] at h_eval,
      assumption,
    },
    case union : gvs_sub {
      simp only [merge.core],
      simp only [
        sym.choices.eval, h_true, 
        if_true, list.append_nil, list.singleton_append
      ] at ⊢ h_eval,
      simp [evalV, val.eval] at h_eval,
      simp [choices.eval_lift, ev.atom] at h_eval,
      rw ← adjust.sound at h_eval,

      simp only [evalB] at h_true,
      unfold_coes at h_true,

      have h_lone := choices.lone_implies_one_or_none (@adjust.lone _ _ m gvs_sub evalVA),
      cases h_lone,
      case inl : h_none {
        subst_vars,
        simp only [choices.eval_lift, ev.atom, choices.none_evals_none h_none],
        rw choices.eval_skips_false,
        case_b {
          simp only [choices.none_iff_none_true],
          intros i hi,
          simp only [choices.none_iff_none_true] at h_none,
          specialize h_none i (by {
            simp only [list.length_map] at hi,
            assumption,
          }),
          simp only [evalB] at h_none,
          simp only [list.nth_le_map', evalB],
          cases (adjust gvs_sub).nth_le i _,
          simp [make_and, pe_and.is_true, h_true, h_none],
        },
        case_c {
          replace h_post := merge_core.preserves_none h_post,
          exact choices.none_evals_none h_post,
        },
      },
      case inr : h_one {
        obtain ⟨pre', post', g', va', h_part', h_pre', h_post', h_true'⟩ :=
          choices.one_implies_one_true h_one,
        simp only [evalB] at h_true',
        simp only [h_part', list.map_append, list.append_assoc] at ⊢ h_eval,
        simp only [list.map, make_and],
        rw choices.eval_skips_false,
        case_b {
          simp [choices.none_iff_none_true, evalB] at ⊢ h_pre',
          intros i hi,
          specialize h_pre' i hi,
          cases list.nth_le pre' i _,
          simp [make_and, pe_and.is_true, h_pre'],
        },
        case_c {
          rw choices.eval_skips_false h_pre' at h_eval,
          simp only [
            sym.choices.eval, h_true, h_true', evalB, pe_and.is_true, 
            if_true, coe_sort_tt, band, list.singleton_append
          ] at ⊢ h_eval,
          assumption,
        },
      },
    },
  },
end

lemma merge.sound {gvs : choices' val} {m : model} 
  (h_lone : gvs.lone ev m) :
  evalV m (merge gvs) = gvs.eval ev m op.lang.undef :=
begin 
  simp only [merge, evalV],
  cases h_merge_core : merge.core gvs,
  case nil { 
    simp only [merge], 
    simp [← h_merge_core],
    apply merge_core.sound,
    apply h_lone,
  },
  case cons : gr grs {
    cases gr with g r,
    cases grs,
    case nil { 
      simp only [merge], 
      split_ifs with h_if,
      case_c {
        rw ← merge_core.sound h_lone,
        simp only [is_tt.sound] at h_if,
        subst_vars,
        simp [val.eval, h_merge_core, evalV, op.sym.choices.eval, mk_tt] with term_is_true,
      },
      case_c {
        simp [← h_merge_core],
        apply merge_core.sound,
        apply h_lone,
      },
    },
    case cons {
      simp only [merge],
      simp [← h_merge_core],
      apply merge_core.sound,
      apply h_lone,
    },
  },
end

lemma make_disjunction_and_merge.sound {gvs : choices' val} {m : model}
  (h_lone : gvs.lone ev m) :
  (if (make_disjunction gvs).is_true m then 
    lang.result.ans ((merge gvs).eval m) 
   else 
    lang.result.halt ff) = 
  gvs.eval ev.result m (lang.result.halt ff) :=
begin 
  split_ifs with h_if,
  case_c { 
    have h_merge := merge.sound h_lone, 
    simp only [evalV] at h_merge,
    simp only [h_merge, ev.result],
    unfold_coes at h_if,
    rw @choices.not_none_iff_disjuction_true _ _ _ _ evalV at h_if,
    simp only [ev] at h_lone,
    replace h_lone := choices.lone_implies_one_or_none h_lone,
    simp [h_if] at h_lone,
    have h_oneR := h_lone,
    obtain ⟨pre, post, g, va, h_part, h_pre, h_post, h_true⟩ :=
      choices.one_implies_one_true h_lone,
    have h_pre' := h_pre,
    have h_post' := h_post,
    rw choices.none_changes_eval evalR at h_pre' h_post',
    simp only [h_part, ev],
    rw [choices.eval_skips_false h_pre, choices.eval_skips_false h_pre'],
    simp [sym.choices.eval, h_true, evalR],
  },
  case_c {
    simp only [eq_ff_eq_not_eq_tt] at h_if,
    rw @choices.none_iff_disjuction_false _ _ _ _ evalV at h_if,
    rw choices.none_changes_eval evalR at h_if,
    simp [ev.result, choices.none_evals_none h_if],
  },
end

end sym_factory
