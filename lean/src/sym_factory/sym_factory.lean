import ..tactic.all
import ..cs.lang
import ..cs.sym
import ..cs.conc
import ..op.sym
import ..cs.util
import .defs
import ..cs.lib
import ..op.simp
import ..basic.basic
import ..basic.sym
import ..op.basic
import .basic
import .opS

namespace sym_factory

open sym
open op.sym
open op.lang.op

lemma cast_choices.sound.valid_input {m : model}
  (gvs : choices' val_atom) (w : op.lang.val)
  (h_clos : lang.val.is_clos w)
  (h_e : choices.eval (make_ev evalVA) m op.lang.undef gvs = w)
  (h_one : choices.one (make_ev evalVA) m gvs) :
  choices.one ev.clos m (cast_choices gvs) ∧
    choices.eval ev.clos m w (cast_choices gvs) = w :=
begin
  obtain ⟨pre, post, g, va, h_part, h_pre, h_post, h_true⟩ := 
      choices.one_implies_one_true h_one,
  simp only [h_part, cast_choices.append],
  simp only [
    h_part, choices.eval_skips_false h_pre, sym.choices.eval, h_true, 
    if_true, list.singleton_append
  ] at h_e,
  replace h_pre := cast_choices.preserves_none h_pre,
  replace h_post := cast_choices.preserves_none h_post,
  simp only [choices.one, choices.true, list.map_append, list.filter_append],
  cases va,
  case term : τ t {
    cases τ,
    case bool {
      cases bool.evals_to_bool h_e with _ h_w,
      subst h_w,
      contradiction,
    },
    case int {
      cases int.evals_to_int h_e with _ h_w,
      subst h_w,
      contradiction,
    },
  },
  case list {
    replace h_e := list.evals_to_list h_e,
    cases w,
    all_goals { contra at h_e h_clos },
  },
  case clos {
    split_c,
    case left {
      simp only [choices.none, choices.true] at h_pre h_post,  
      simp only [h_pre, h_post, add_zero, list.length_append, zero_add],
      simp [cast_choices, list.filter, ev.clos, h_true],
    },
    case right {
      simp only [choices.eval_skips_false h_pre, cast_choices],
      simp only [evalVA] at h_e,
      simp [sym.choices.eval, ev.clos, h_true, ← clos.eval_lift, h_e],
    },
  },
end


lemma cast_choices.sound.invalid_input {m : model} {gvs : choices' val_atom} {w : op.lang.val}
  (h : gvs.eval ev.atom m op.lang.undef = w)
  (h_clos : ¬ w.is_clos)
  (h_lone : gvs.lone ev.atom m) : (cast_choices gvs).none ev.clos m :=
begin
  cases @choices.lone_implies_one_or_none _ _ _ _ ev.atom _ _ h_lone,
  case inl : h_none {
    apply cast_choices.preserves_none,
    assumption,
  },
  case inr : h_one {
    obtain ⟨pre, post, g, va, h_part, h_pre, h_post, h_true⟩ := 
      choices.one_implies_one_true h_one,
    simp only [h_part] at ⊢ h,
    simp only [cast_choices.append, ← choices.none_append],
    split_c,
    case left { apply cast_choices.preserves_none, assumption },
    case right left {
      cases va,
      case clos {
        rw choices.eval_skips_false h_pre at h,
        simp only [sym.choices.eval, h_true, if_true, list.singleton_append] at h,
        simp only [ev.atom, evalVA] at h,
        replace h := clos.evals_to_clos h,
        contra [h] at h_clos,
      },
      all_goals { simp [cast_choices, choices.none, choices.true] },
    },
    case right right { apply cast_choices.preserves_none, assumption },
  },
end

lemma cast.sound.valid_input {m : model} {v : val} 
  (h_clos : (evalV m v).is_clos) : 
  (cast v).one ev.clos m ∧ 
  (cast v).eval ev.clos m (evalV m v) = evalV m v :=
begin 
  cases v,
  case atom {
    generalize_hyp h : evalV _ _ = w at h_clos,
    simp only [evalV, val.eval] at h,
    cases v,
    case clos { 
      simp [
        cast, choices.one, choices.true, list.filter, ev.clos, mk_tt.sound,
        sym.choices.eval, evalV, val.eval, clos.eval_lift
      ],
    },
    case term : τ t {
      cases τ,
      case bool {
        cases bool.evals_to_bool h with _ h',
        contra [h'] at h_clos,
      },
      case int {
        cases int.evals_to_int h with _ h',
        contra [h'] at h_clos,
      },
    },
    case list {
      replace h := list.evals_to_list h,
      cases w,
      all_goals { contra at h_clos h },
    },
  },
  case union : gvs {
    generalize_hyp h_e : evalV m (val.union gvs) = w at h_clos ⊢,
    simp only [cast],
    simp only [evalV, val.eval] at h_e, 
    simp only [choices.eval_lift, ev.atom] at h_e,
    rw ← adjust.sound at h_e,
    have h_eval : choices.eval ev.atom m op.lang.undef (adjust gvs) ≠ op.lang.undef := by {
      simp only [ev.atom],
      cases choices.eval (make_ev evalVA) m op.lang.undef (adjust gvs),
      case clos { simp [op.lang.undef] },
      all_goals { subst_vars, contradiction },
    },
    replace h_eval := choices.not_none_implies_not_none h_eval,
    have h_lone := @adjust.lone _ _ m gvs evalVA,
    simp only [ev.atom] at h_eval,
    replace h_lone := choices.lone_implies_one_or_none h_lone,
    simp only [h_eval, false_or] at h_lone,
    apply cast_choices.sound.valid_input,
    all_goals { assumption },
  },
end

lemma cast.sound.invalid_input {m : model} {v : val} 
  (h_clos : ¬(evalV m v).is_clos) : (cast v).none ev.clos m :=
begin 
  cases v,
  case atom {
    cases v,
    case clos {
      generalize_hyp h : evalV _ _ = w at h_clos,
      simp only [evalV, val.eval] at h,
      contra [clos.evals_to_clos h] at h_clos,
    },
    all_goals { simp [cast, choices.none, choices.true] },
  },
  case union : gvs {
    simp only [cast],
    generalize_hyp h : evalV _ _ = w at h_clos,
    simp only [evalV] at h,
    simp only [val.eval, choices.eval_lift, ev.atom] at h,
    rw ← @adjust.sound _ _ _ _ evalVA at h,
    apply_c cast_choices.sound.invalid_input,
    case h_clos { assumption },
    case h { assumption },
    case h_lone { exact @adjust.lone _ _ _ _ evalVA },
  },
end

-- A complete symbolic factory
@[reducible]
def sym_factory : factory _ _ _ _ _ := {
  mk_tt := mk_tt,
  mk_ff := mk_ff,
  is_tt := is_tt,
  is_ff := is_ff,
  not := pe_not,
  and := pe_and,
  or := pe_or,
  imp := pe_imp,
  truth := truth,
  bval := bval,
  dval := dval,
  cval := cval,
  cast := cast,
  merge := merge,
  opC := op.lang.opC,
  opS := opS,
  evalB := op.sym.evalB,
  evalV := op.sym.evalV,
  mk_tt_sound := by { simp [mk_tt.sound] },
  mk_ff_sound := by { simp [mk_ff.sound] },
  is_tt_sound := by { simp [is_tt.sound] },
  is_ff_sound := by { simp [is_ff.sound] },
  not_sound := by { simp [pe_not.sound] },
  and_sound := by { simp [pe_and.is_true, evalB] },
  or_sound := by { simp [pe_or.is_true, evalB] },
  imp_sound := by { simp [pe_imp.sound] },
  truth_sound := by { apply truth.sound },
  bval_sound := by { simp [bval.sound] },
  cval_sound := by { apply cval.sound },
  dval_sound := by { simp [dval.sound] },
  cast_sound := by {
    intros,
    split_c,
    case left { apply cast.sound.valid_input },
    case right { apply cast.sound.invalid_input },
  },
  merge_sound := by { 
    intros, 
    simp only [default, evalV, val.eval, op.sym.choices.eval],
    apply merge.sound,
    apply choices.one_implies_lone,
    assumption,
  },
  opS_sound := by {
    intros,
    split_c,
    case left { apply opS.sound },
    case right { apply opS.legal },
  },
}

end sym_factory