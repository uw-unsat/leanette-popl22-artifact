import ..tactic.all
import ..cs.lang
import ..cs.sym
import ..op.sym
import ..cs.util
import .defs
import ..cs.lib
import ..op.simp
import ..basic.basic
import ..basic.sym
import ..op.basic
import .basic

namespace sym_factory

open sym
open op.sym
open op.lang.op

section core

lemma opS_core.sound_int_2 {m : model} {vas : list val_atom}
  {ws : list op.lang.val} {v : val} {o : op.lang.op_int_2}
  (h_eval_va : list.map (evalVA m) vas = ws) :
  (opS.core (int_2 o) vas = none → op.lang.opC (int_2 o) ws = lang.result.halt ff) ∧
  (opS.core (int_2 o) vas = some v → op.lang.opC (int_2 o) ws = lang.result.ans (v.eval m)) :=
begin
  cases ws,
  focus_case cons : w_a ws {
    cases ws,
    focus_case cons : w_b ws { cases ws },
  },
  all_goals {
    cases vas,
    focus_case cons : va_a vas {
      cases vas,
      focus_case cons : va_b vas { cases vas },
    },
  },
  any_goals { solve1 { contra at h_eval_va } },
  all_goals { cases o }, 
  all_goals { 
    simp only [
      op.lang.opC, op.lang.opC_int_2, opS.core, 
      forall_false_left, lang.err, eq_self_iff_true, forall_true_left, and_self
    ]
  },
  all_goals {
    simp only [evalVA, and_true, eq_self_iff_true, list.map, list.nth_le] at h_eval_va,
    cases h_eval_va with h_eval_a h_eval_b,
    -- first arg (val_atom)
    cases va_a,
    focus_case term : τ_a t_a {
      cases τ_a,
      case bool {
        cases bool.evals_to_bool h_eval_a with _ h_eval_a',
        simp [op.lang.opC_int_2, opS.core, h_eval_a'],
      },
      focus_case int {
        cases int.evals_to_int h_eval_a with _ h_eval_a',
        simp [h_eval_a'],
      },
    },
    case clos {
      replace h_eval_a := clos.evals_to_clos h_eval_a,
      cases w_a,
      case clos { simp [op.lang.opC_int_2, opS.core] },
      all_goals { contra at h_eval_a },
    },
    case list {
      replace h_eval_a := list.evals_to_list h_eval_a,
      cases w_a,
      case list { simp [op.lang.opC_int_2, opS.core] },
      all_goals { contra at h_eval_a },
    },
    -- second arg (val_atom)
    cases va_b,
    focus_case term : τ_b t_b {
      cases τ_b,
      case bool {
        cases bool.evals_to_bool h_eval_b with _ h_eval_b',
        simp [op.lang.opC_int_2, opS.core, h_eval_b'],
      },
      focus_case int {
        cases int.evals_to_int h_eval_b with _ h_eval_b',
        simp [h_eval_b'],
      },
    },
    case clos {
      replace h_eval_b := clos.evals_to_clos h_eval_b,
      cases w_b,
      case clos { simp [op.lang.opC_int_2, opS.core] },
      all_goals { contra [lang.val.is_clos] at h_eval_b },
    },
    case list {
      replace h_eval_b := list.evals_to_list h_eval_b,
      cases w_b,
      case list { simp [op.lang.opC_int_2, opS.core] },
      all_goals { contra at h_eval_b },
    },
    -- main
    simp [op.lang.opC_int_2, opS.core, opS.int_wrap],
    intro h,
    substs h_eval_a' h_eval_b',
    cases t_a,
    focus_case lit : l_a            { cases h_a : l_a },
    focus_case var : x_a            { cases h_a : m type.int x_a },
    focus_case ite : t_ac t_at t_ae { cases h_a : ite ((t_ac.eval m).to_bool) (t_at.eval m) (t_ae.eval m) },
    focus_case expr : o_a t_al t_ar { cases h_a : o_a.eval (t_al.eval m) (t_ar.eval m) },
    all_goals {
      cases t_b,
      focus_case lit : l_b            { cases h_b : l_b },
      focus_case var : x_b            { cases h_b : m type.int x_b },
      focus_case ite : t_bc t_bt t_be { cases h_b : ite ((t_bc.eval m).to_bool) (t_bt.eval m) (t_be.eval m) },
      focus_case expr : o_b t_bl t_br { cases h_b : o_b.eval (t_bl.eval m) (t_br.eval m) },
      all_goals {
        simp only [val_atom.eval, term.eval, h_a, h_b, lit.to_val] at h_eval_a h_eval_b, 
        simp only [← h, opS.int, val.eval, val_atom.eval, term.eval, h_a, h_b, h_eval_a, h_eval_b, typedop.eval, lit.to_val], 
      },
    },
  },
end

lemma opS_core.sound_list_proj {m : model} {vas : list val_atom}
  {ws : list op.lang.val} {v : val} {o : op.lang.op_list_proj}
  (h_eval : list.map (evalVA m) vas = ws) :
  (opS.core (list_proj o) vas = none → 
    op.lang.opC (list_proj o) ws = lang.result.halt ff) ∧
  (opS.core (list_proj o) vas = some v → 
    op.lang.opC (list_proj o) ws = lang.result.ans (v.eval m)) :=
begin
  cases ws,
  focus_case cons : w ws { cases ws },
  all_goals {
    cases vas,
    focus_case cons : va vas { cases vas },
  },
  any_goals { solve1 { contra at h_eval } },
  all_goals { cases o }, 
  all_goals { simp [op.lang.opC, op.lang.opC_list_proj, opS.core] },
  all_goals {
    simp only [evalVA, list.nth_le, and_true, eq_self_iff_true, list.map] at h_eval,
    cases va,
    case term : τ t {
      cases τ,
      case int {
        cases int.evals_to_int h_eval with _ h_eval',
        subst h_eval',
        simp [op.lang.opC_list_proj, opS.core],
      },
      case bool {
        cases bool.evals_to_bool h_eval with _ h_eval',
        subst h_eval',
        simp [op.lang.opC_list_proj, opS.core],
      },
    },
    case clos {
      replace h_eval := clos.evals_to_clos h_eval,
      cases w,
      case clos { simp [op.lang.opC_list_proj, opS.core] },
      all_goals { contra at h_eval },
    },
    focus_case list : vs {
      have h_list := list.evals_to_list h_eval,
      cases vs,
      case nil {
        simp only [val_atom.eval] at h_eval,
        subst_vars,
        simp [opS.core, op.lang.opC_list_proj, vals.eval],
      },
      focus_case cons {
        obtain ⟨w', ws', h_hd, h_tl, h_eval'⟩ := list.evals_cons h_eval,
        subst_vars,
        simp only [opS.core, op.lang.opC_list_proj, vals.eval, true_and, forall_false_left],
        intro h,
        subst_vars,
      },
    },
  },
  case_c { simp [h_eval', op.lang.opC_list_proj] },
  case_c { simp only [h_eval', op.lang.opC_list_proj, val.eval], cc },
end

lemma opS_core.sound
  {m : model} {o : op.lang.op} {vas : list val_atom} {ws : list op.lang.val} {v : val}
  (h_eval_va : list.map (evalVA m) vas = ws) : 
  (opS.core o vas = none → op.lang.opC o ws = lang.result.halt ff) ∧
  (opS.core o vas = some v → op.lang.opC o ws = lang.result.ans (v.eval m)) :=
begin 
  cases o,
  case list_null {
    cases ws,
    case nil {
      have : vas = [] := by {
        cases vas,
        case nil { simp },
        case cons { contra at h_eval_va },
      },
      subst_vars,
      simp only [opS.core, true_and, forall_false_left],
      intros,
      subst_vars,
      simp [op.lang.opC, val.eval, val_atom.eval, vals.eval],
    },
    case cons { 
      cases vas,
      case nil { contra at h_eval_va },
      case cons { simp [op.lang.opC, opS.core] },
    },
  },
  case int_2 {
    apply opS_core.sound_int_2,
    all_goals { assumption },
  },
  case list_proj {
    apply opS_core.sound_list_proj,
    all_goals { assumption },
  },
  case list_cons {
    cases ws,
    focus_case cons : w_a ws {
      cases ws,
      focus_case cons : w_b ws { cases ws },
    },
    all_goals {
      cases vas,
      focus_case cons : va_a vas {
        cases vas,
        focus_case cons : va_b vas { cases vas },
      },
    },
    any_goals { solve1 { contra at h_eval_va } },
    all_goals { 
      simp only [
        op.lang.opC, opS.core, 
        forall_false_left, lang.err, eq_self_iff_true, forall_true_left, and_self
      ] 
    },
    simp only [evalVA, and_true, eq_self_iff_true, list.map] at h_eval_va,
    cases h_eval_va with h_eval_a h_eval_b,
    cases va_b,
    case term : τ t {
      cases τ,
      case int {
        cases int.evals_to_int h_eval_b with _ h_eval_b',
        subst_vars,
        simp [opS.core, op.lang.opC, h_eval_b'],
      },
      case bool {
        cases bool.evals_to_bool h_eval_b with _ h_eval_b',
        subst_vars,
        simp [opS.core, op.lang.opC, h_eval_b'],
      },
    },
    case clos {
      replace h_eval_b := clos.evals_to_clos h_eval_b,
      cases w_b,
      case clos { simp [opS.core, op.lang.opC] },
      all_goals { contra at h_eval_b },
    },
    case list : vs {
      have h_list := list.evals_to_list h_eval_b,
      cases w_b,
      case [datum, bool, clos] {
        all_goals { contra at h_list },
      },
      case list {
        have h_undef := @val_atom.evals_no_undef va_a m,
        simp [opS.core, op.lang.opC],
        intro h,
        subst h,
        simp [val_atom.eval] at h_eval_b,
        simp [val.eval, val_atom.eval, h_eval_a, h_eval_b, vals.eval],
        cases w_a,
        case datum : d_a {
          cases d_a,
          case undef { contradiction },
          case int { simp [op.lang.opC] },
        },
        all_goals { simp [op.lang.opC] },
      },
    },
  },
  case list_is_null {
    cases ws,
    focus_case cons : w_a ws { cases ws },
    all_goals {
      cases vas,
      focus_case cons : va_a vas { cases vas },
    },
    any_goals { solve1 { contra at h_eval_va } },
    all_goals { 
      simp only [
        op.lang.opC, opS.core, 
        forall_false_left, lang.err, eq_self_iff_true, forall_true_left, and_self
      ] 
    },
    simp only [evalVA, and_true, eq_self_iff_true, list.map] at h_eval_va,
    cases va_a,
    case term : τ t {
      cases τ,
      case int {
        cases int.evals_to_int h_eval_va with _ h_eval_a',
        subst_vars,
        simp only [opS.core, op.lang.opC, h_eval_a', true_and],
        intros,
        subst_vars,
        simp [val.eval, val_atom.eval, term.eval, lit.to_val],
      },
      case bool {
        cases bool.evals_to_bool h_eval_va with _ h_eval_a',
        subst_vars,
        simp only [opS.core, op.lang.opC, h_eval_a', true_and],
        intros,
        subst_vars,
        simp [val.eval, val_atom.eval, term.eval, lit.to_val],
      },
    },
    case clos {
      have h_eval_a := clos.evals_to_clos h_eval_va,
      cases w_a,
      case clos { 
        simp only [opS.core, op.lang.opC, true_and], 
        intros,
        subst_vars,
        simp [val.eval, val_atom.eval, term.eval, lit.to_val],
      },
      all_goals { contra at h_eval_a },
    },
    case list : vs {
      have h_list := list.evals_to_list h_eval_va,
      cases w_a,
      case [datum, bool, clos] {
        all_goals { contra at h_list },
      },
      case list {
        cases vs,
        all_goals {
          simp [val_atom.eval, vals.eval] at h_eval_va,
          subst_vars,
          simp only [opS.core, op.lang.opC, true_and],
          intros,
          subst_vars,
          simp [val.eval, val_atom.eval, term.eval, lit.to_val],
        },
      },
    },
  },
end

lemma opC.eval_undef_err {o : op.lang.op} {ws : list op.lang.val}
  (h : op.lang.undef ∈ ws) :
  op.lang.opC o ws = lang.result.halt ff :=
begin 
  simp [op.lang.undef] at h,
  cases o,
  case int_2 {
    cases ws,
    focus_case cons : w_a ws {
      cases ws,
      focus_case cons : w_b ws {
        cases ws,
        case nil { 
          simp at h,
          cases h,
          case inl {
            subst_vars,
            cases w_b,
            all_goals { simp [op.lang.opC, op.lang.opC_int_2] },
          },
          case inr {
            subst_vars,
            cases w_a,
            case datum : d_a {
              cases d_a,
              all_goals { simp [op.lang.opC, op.lang.opC_int_2] },
            },
            all_goals { simp [op.lang.opC, op.lang.opC_int_2] },
          },
        },
      },
    },
    all_goals { simp [op.lang.opC, op.lang.opC_int_2] },
  },
  case list_proj {
    cases ws,
    focus_case cons : w ws {
      cases ws,
      case nil {
        simp only [list.mem_singleton] at h,
        subst_vars,
        cases o,
        all_goals { simp [op.lang.opC, op.lang.opC_list_proj] },
      },
    },
    all_goals { simp [op.lang.opC, op.lang.opC_list_proj] },
  },
  case list_null {
    cases ws,
    case nil { contra at h },
    case cons { simp only [op.lang.opC, lang.err] },
  },
  case list_cons {
    cases ws,
    focus_case cons : w_a ws {
      cases ws,
      focus_case cons : w_b ws {
        cases ws,
        case nil {
          simp at h,
          cases h,
          case inl {
            subst h,
            cases w_b,
            all_goals { simp [op.lang.opC] },
          },
          case inr {
            subst h,
            cases w_a,
            all_goals { simp [op.lang.opC] },
          },
        },
      },
    },
    all_goals { simp [op.lang.opC, lang.err] },
  },
  case list_is_null {
    cases ws,
    focus_case cons : w_a ws {
      cases ws,
      case nil {
        simp at h,
        subst h,
        simp [op.lang.opC],
      },
    },
    all_goals { simp [op.lang.opC] },
  },
end

lemma opC.eval_halt_err {o : op.lang.op} {ws : list op.lang.val} {b : bool}
  (h : op.lang.opC o ws = lang.result.halt b) : b = ff :=
begin
  cases o,
  case int_2 {
    cases ws,
    focus_case cons : w_a ws {
      cases ws,
      focus_case cons : w_b ws {
        cases ws,
        focus_case nil { 
          cases w_a,
          focus_case datum : d_a {
            cases w_b,
            focus_case datum : d_b {
              cases d_a,
              focus_case int {
                cases d_b,
                case int { contra [op.lang.opC, lang.err] at h },
              },
            },
          },
        },
      },
    },
    all_goals { simp only [op.lang.opC, op.lang.opC_int_2, lang.err] at h, simp [h] },
  },
  case list_proj {
    cases ws,
    focus_case cons : w ws {
      cases ws,
      focus_case nil {
        cases w,
        focus_case list : xs {
          cases xs,
          focus_case cons {
            cases o,
            all_goals {
              contra [op.lang.opC, lang.err, op.lang.opC_list_proj] at h,
            },
          },
        },
      },
    },
    all_goals {
      simp only [op.lang.opC, lang.err, op.lang.opC_list_proj] at h, 
      simp [h],
    },
  },
  case list_null {
    cases ws,
    case nil { contra [op.lang.opC] at h },
    case cons { simp only [op.lang.opC, lang.err] at h, simp [h] },
  },
  case list_cons {
    cases ws,
    focus_case cons : w_a ws {
      cases ws,
      focus_case cons : w_b ws {
        cases ws,
        focus_case nil {
          cases w_b,
          focus_case list { 
            cases w_a,
            focus_case datum : d_a {
              cases d_a,
              case int { contra [op.lang.opC, lang.err] at h },
            },
            case [bool, list, clos] {
              all_goals { contra [op.lang.opC, lang.err] at h },
            },
          },
        },
      },
    },
    all_goals { simp only [op.lang.opC, lang.err] at h, simp [h] },
  },
  case list_is_null {
    cases ws,
    focus_case cons : w_a ws {
      cases ws,
      focus_case nil {
        cases w_a,
        case list : ws {
          cases ws,
          all_goals { contra [op.lang.opC] at h },
        },
        case [bool, clos] {
          all_goals { contra [op.lang.opC] at h },
        },
        focus_case datum : d_a {
          cases d_a,
          case int { contra [op.lang.opC] at h },
        },
      },
    },
    all_goals {
      simp only [op.lang.opC, lang.err] at h,
      simp [h],
    },
  },
end

end core 

section main 

lemma opS_split.false_guard_implies_false_guard 
  {m : model} {o : op.lang.op} {vs : list val} {g_acc : term type.bool} {vas : list val_atom} 
  (h : g_acc.is_true m = ff) : (opS.split o vs g_acc vas).guard.is_true m = ff :=
begin 
  induction vs with hd tl ih generalizing g_acc vas,
  case nil {
    cases h_core : opS.core o vas.reverse,
    case none { simp [opS.split, h_core, mk_ff] with term_is_true },
    case some { simpa [opS.split, h_core] },
  },
  case cons {
    cases hd,
    case atom : va { apply ih, assumption },
    case union : gvs_sub {
      simp only [opS.split, opS.split_map],
      rw @choices.none_iff_disjuction_false _ _ _ _ evalV,
      rw choices.none_iff_none_true,
      intros i hi,
      simp only [evalB, eq_ff_eq_not_eq_tt, list.nth_le_map'],
      cases list.nth_le (adjust gvs_sub) i _,
      apply ih,
      simp [pe_and.is_true, h],
    },
  },
end

lemma opS_split_map_lone {m : model} {o : op.lang.op} {vs : list val} 
  {gvs : choices' val_atom} {g_acc : term type.bool} {vas : list val_atom} :
  choices.lone ev m (opS.split_map o vs gvs g_acc vas) :=
begin 
  have h_lone := choices.lone_implies_one_or_none (@adjust.lone _ _ m gvs evalVA),
  cases h_lone,
  case inl : h_none {
    apply choices.none_implies_lone,
    simp [choices.none_iff_none_true] at h_none ⊢,
    intros i hi,
    simp only [opS.split_map, list.length_map] at hi,
    specialize h_none i (by assumption),
    simp only [ev, evalB, opS.split_map, list.nth_le_map'],
    cases list.nth_le (adjust gvs) i _,
    simp only [evalB] at h_none,
    apply opS_split.false_guard_implies_false_guard,
    simp [pe_and.is_true, h_none],
  },
  case inr : h_one {
    simp only [opS.split_map],
    obtain ⟨pre, post, g, va, h_part, h_pre, h_post, h_true⟩ :=
      choices.one_implies_one_true h_one,
    simp only [h_part, list.map_append],
    generalize h_r_pre : list.map _ pre = r_pre,
    generalize h_r_post : list.map _ post = r_post,
    have h_pre' : choices.none ev m r_pre := by {
      subst r_pre,
      simp [choices.none_iff_none_true] at h_pre ⊢,
      intros i hi,
      specialize h_pre i (by assumption),
      cases list.nth_le pre i _,
      simp only [evalB] at h_pre,
      simp only [ev, opS.split],
      apply opS_split.false_guard_implies_false_guard,
      simp [pe_and.is_true, h_pre],
    },
    have h_post' : choices.none ev m r_post := by {
      subst r_post,
      simp [choices.none_iff_none_true] at h_post ⊢,
      intros i hi,
      specialize h_post i (by assumption),
      cases list.nth_le post i _,
      simp only [evalB] at h_post,
      simp only [ev, opS.split],
      apply opS_split.false_guard_implies_false_guard,
      simp [pe_and.is_true, h_post],
    },
    subst_vars,
    simp only [choices.none, choices.true, list.map_map] at h_pre' h_post',
    simp only [
      choices.lone, choices.true, h_pre', h_post', opS.split,
      list.filter_append, list.map_append, list.map_map, list.length_append,
      list.filter, list.map
    ], 
    split_ifs,
    all_goals { simp },
  },
end

def choice.eval : choice (term type.bool) val → model → op.lang.result
| ⟨g, v⟩ m := if g.is_true m then lang.result.ans (v.eval m) else lang.result.halt ff

lemma opS_split.sound {m : model} {vs : list val} {o : op.lang.op} 
  {ws ws' : list op.lang.val} {g_acc : term type.bool} {vas : list val_atom}
  (h_eval_v : list.map (evalV m) vs = ws)
  (h_eval_va : list.map (evalVA m) vas = ws') : 
  choice.eval (opS.split o vs g_acc vas) m = 
    if g_acc.is_true m then 
      op.lang.opC o ((list.reverse ws') ++ ws)
    else 
      lang.result.halt ff :=
begin 
  induction vs with hd tl ih generalizing ws ws' g_acc vas,
  case nil {
    simp [opS.split],
    simp at h_eval_v,
    subst h_eval_v,
    have h_opS_core_sound : ∀ (v : val), 
        (opS.core o vas.reverse = none → op.lang.opC o ws'.reverse = lang.result.halt ff) ∧ 
        (opS.core o vas.reverse = some v → op.lang.opC o ws'.reverse = lang.result.ans (v.eval m)) := by {
      intro v,
      apply opS_core.sound,
      apply_fun list.reverse at h_eval_va,
      simp only [← list.map_reverse] at h_eval_va,
      assumption,
    },
    cases h_core : opS.core o vas.reverse,
    case none {
      simp only [opS.split, choice.eval, mk_ff] with term_is_true,
      obtain ⟨h_opS_core_sound', _⟩ := h_opS_core_sound (val.union []),
      simp [h_opS_core_sound' h_core],
    },
    case some {
      simp [opS.split, choice.eval, mk_ff] with term_is_true,
      split_ifs with h_if,
      case_b { simp },
      case_c {
        obtain ⟨_, h_opS_core_sound'⟩ := h_opS_core_sound val,
        simp [h_opS_core_sound' h_core],
      },
    },
  },
  case cons {
    cases ws,
    case nil { contradiction },
    case cons : w ws {
      simp at h_eval_v,
      cases h_eval_v with h_eval_current h_eval_tl,
      replace ih : ∀ (g_acc : term type.bool)
                     (va : val_atom),
          evalVA m va = w →
          choice.eval (opS.split o tl g_acc (va :: vas)) m = 
          if (g_acc.is_true m) then
            op.lang.opC o ((w :: ws').reverse ++ ws)
          else 
            lang.result.halt ff := by {
        intros,
        apply_c ih,
        case h_eval_v { assumption },
        case h_eval_va { simpa [h_eval_va] },
      },
      cases hd,
      case atom : va {
        simp [evalV, val.eval] at h_eval_current,
        simp [opS.split, ih g_acc va (by simp [evalVA, h_eval_current])],
      },
      case union : gvs_sub {
        simp only [opS.split, choice.eval],
        simp only [make_disjunction_and_merge.sound (@opS_split_map_lone m o tl gvs_sub g_acc vas)],
        simp only [evalV, val.eval, choices.eval_lift, ev.atom] at h_eval_current,
        rw ← adjust.sound at h_eval_current,
        have h_lone := choices.lone_implies_one_or_none (@adjust.lone _ _ m gvs_sub evalVA),
        cases h_lone,
        case inl : h_none {
          have h_none' : choices.none ev.result m(opS.split_map o tl gvs_sub g_acc vas) := by {
            simp only [opS.split_map],
            simp [choices.none_iff_none_true] at ⊢ h_none,
            intros i hi,
            specialize h_none i hi,
            cases list.nth_le (adjust gvs_sub) i _,
            simp only [opS.split_map],
            apply opS_split.false_guard_implies_false_guard,
            simp only [evalB] at h_none,
            simp [pe_and.is_true, h_none],
          },
          rw choices.none_evals_none h_none',
          rw choices.none_evals_none h_none at h_eval_current,
          subst h_eval_current,
          rw opC.eval_undef_err,
          case_c { simp },
          case_c { simp },
        },
        case inr : h_one {
          obtain ⟨pre, post, g, va, h_part, h_pre, h_post, h_true⟩ := 
            choices.one_implies_one_true h_one,
          simp only [opS.split_map, ev],  
          simp only [h_part, list.map_append],
          rw choices.eval_skips_false,
          case_b {
            simp [choices.none_iff_none_true] at ⊢ h_pre,
            intros i hi,
            specialize h_pre i hi,
            cases h_nth : list.nth_le pre i _ with g' va',
            simp only [h_nth, evalB] at h_pre,
            simp only [opS.split_map],
            apply opS_split.false_guard_implies_false_guard,
            simp [pe_and.is_true, h_pre],
          },
          case_c {
            simp only [h_part] at h_eval_current,
            rw choices.eval_skips_false at h_eval_current,
            case_b {
              simp only [choices.none_iff_none_true] at ⊢ h_pre,
              intros i hi,
              specialize h_pre i hi,
              cases h_nth : list.nth_le pre i _ with g' va',
              simp only [h_nth, evalB] at h_pre,
              simp [opS.split, evalB, h_pre],
            },
            case_c {
              simp only [opS.split_map, list.singleton_append, list.map],
              cases h_split : opS.split o tl (pe_and g_acc g) (va :: vas),
              simp only [h_split, opS.split_map, list.singleton_append, list.map, sym.choices.eval],
              specialize ih (pe_and g_acc g) va (by {
                simp only [sym.choices.eval, h_true, list.singleton_append, if_true] at h_eval_current,
                simp [h_eval_current],
              }),
              generalize h_post' : choices.eval _ _ _ (list.map _ post) = r_post,
              rw (by simp : post = post ++ []) at h_post',
              simp only [list.map_append] at h_post',
              rw choices.eval_skips_false at h_post',
              case_b {
                simp [choices.none_iff_none_true] at ⊢ h_post,
                intros i hi,
                specialize h_post i hi,
                cases h_nth : list.nth_le post i _ with g' va',
                simp only [h_nth, evalB] at h_post,
                simp only [opS.split_map],
                apply opS_split.false_guard_implies_false_guard,
                simp [pe_and.is_true, h_post],
              },
              case_c {
                simp only [sym.choices.eval, list.map] at h_post',
                subst_vars,
                simp only [h_split, choice.eval, ev, list.reverse_cons, list.append_assoc, list.singleton_append] at ih,
                simp only [evalB] at h_true,
                split_ifs at ⊢ ih with h_if_0 h_if_1 h_if_2 h_if_3 h_if_4 h_if_5 h_if_6,
                case_c { assumption },
                case_c { contra [pe_and.is_true, h_if_1, h_true] at h_if_2 },
                case_c { contra [pe_and.is_true, h_if_1] at h_if_3 },
                case_c { contradiction },
                case_c { assumption },
                case_c { contra [pe_and.is_true, h_true, h_if_4] at h_if_5 },
                case_c { simp },
                case_c { simp },
              },
            },
          },
        },
      },
    },
  },
end

lemma opS.sound {m : model} {vs : list val} {o : op.lang.op} : 
  (opS o vs).eval ev m = (op.lang.opC o (vs.map (evalV m))) :=
begin 
  generalize h_eval : vs.map _ = ws,
  simp only [opS],
  have h_split := @opS_split.sound _ _ o _ [] mk_tt [] h_eval (by simp),
  cases opS.split o vs mk_tt list.nil with g v,
  simp only [opS],
  split_ifs with h,
  case_c {
    simp only [is_ff.sound] at h,
    subst h,
    simp only [result.eval],  
    cases h_opC : op.lang.opC o ws,
    all_goals { simp [choice.eval, mk_ff, h_opC] with term_is_true at h_split },
    case ans { contradiction },
    case halt { simp [state.aborted, ev, mk_tt.sound, opC.eval_halt_err h_opC] },
  },
  case_c {
    simp only [
      mk_tt, choice.eval, ev, evalV,
      if_true, coe_sort_tt, list.nil_append, list.reverse_nil
    ] at h_split,
    simp only [ev],
    cases h_opC : op.lang.opC o ws,
    case ans {
      simp only [h_opC, evalB] at h_split,
      cases v,
      case atom : v {
        simp only [opS, result.eval, evalV, val.eval],
        simp only [
          val.eval,
          (by simp with term_is_true : (term.lit (lit.bool tt)).is_true m)
        ] at h_split,
        split_ifs at h_split with h_if,
        case_c {
          simp only [h_split, result.eval, state.normal, mk_tt.sound], 
          simp [evalB, h_if],
        },
        case_c { contradiction },
      },
      case union : gvs {
        simp only [(by simp with term_is_true : (term.lit (lit.bool tt)).is_true m)] 
          at h_split,
        split_ifs at h_split with h_if,
        case_c {
          simp only [result.eval, state.normal, mk_tt.sound],
          simp [evalB, h_if, evalV, h_split],
        },
        case_c { contradiction },
      },
    },
    case halt {
      have := opC.eval_halt_err h_opC,
      subst_vars,
      simp only [h_opC] at h_split,
      cases v,
      case atom {
        simp only [result.eval],
        simp only [
          val.eval,
          (by simp with term_is_true : (term.lit (lit.bool tt)).is_true m)
        ] at h_split,
        split_ifs at h_split with h_if,
        case_c { contradiction },
        case_c {
          simp [state.normal, mk_tt.sound],
          simp [evalB, h_if, state.aborted],
        },
      },
      case union : gvs {
        simp only [result.eval],
        simp only [(by simp with term_is_true : (term.lit (lit.bool tt)).is_true m)] 
          at h_split,
        split_ifs at h_split with h_if,
        case_c { contradiction },
        case_c {
          simp [state.normal, mk_tt.sound],
          simp [evalB, h_if, state.aborted],
        },
      },
    },
  },
end

lemma opS.legal {m : model} {o : op.lang.op} {vs : list val} : (opS o vs).legal ev m := 
begin 
  simp only [opS],
  cases h : opS.split o vs mk_tt list.nil with g v,
  simp only [opS, h],
  split_ifs, 
  case_c { simp [result.legal, state.legal, state.normal, ev, mk_tt.sound, mk_ff.sound] },
  case_c {
    cases v,
    focus_case union : gvs {
      cases gvs,
      focus_case cons : gva gvs {
        cases gva,
        cases gvs,
      },
    },
    all_goals { simp [opS, result.legal, state.legal, ev, mk_tt.sound] },
  },
end

end main

end sym_factory