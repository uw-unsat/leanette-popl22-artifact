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
import .sym_factory

namespace sym_factory

open sym
open op.sym
open op.lang.op

def ind_principle 
  (P : op.lang.val → Prop) 
  (H_bool : ∀ b, P (lang.val.bool b)) 
  (H_datum : ∀ d, P (lang.val.datum d)) 
  (H_list_nil : P (lang.val.list []))
  (H_list_cons : ∀ x xs, P x → P (lang.val.list xs) → P (lang.val.list (x :: xs)))
  (H_clos_nil : ∀ x e, P (lang.val.clos x e []))
  (H_clos_cons : ∀ x e v vs, P v → P (lang.val.clos x e vs) → P (lang.val.clos x e (v :: vs)))
  : ∀ v, P v 
| (lang.val.bool b) := H_bool b
| (lang.val.datum d) := H_datum d
| (lang.val.list []) := H_list_nil
| (lang.val.list (x :: xs)) := H_list_cons x xs (ind_principle x) (ind_principle (lang.val.list xs))
| (lang.val.clos x e []) := H_clos_nil x e
| (lang.val.clos x e (v :: vs)) := 
  H_clos_cons x e v vs (ind_principle v) (ind_principle (lang.val.clos x e vs))

lemma lift_sound {m : model} {w : op.lang.val} : evalV m (lift w) = w :=
begin 
  induction w using sym_factory.ind_principle,
  case H_bool {
    simp [lift, evalV, val.eval, val_atom.eval, term.eval, lit.to_val],
  },
  case H_datum : d {
    cases d,
    case int {
      simp [lift, evalV, val.eval, val_atom.eval, term.eval, lit.to_val],
    },
    case undef {
      simp [lift, evalV, val.eval, op.sym.choices.eval, op.lang.undef],
    },
  },
  case H_list_nil {
    simp [lift, evalV, val.eval, val_atom.eval, lifts, vals.eval],
  },
  case H_list_cons : w ws ih ih' {
    simp [evalV] at ih,
    simp [lift, evalV, val.eval, val_atom.eval] at ih',
    simp [lift, evalV, val.eval, val_atom.eval, lifts, vals.eval, ih, ih'],
  },
  case H_clos_nil {
    simp [evalV, lift, val.eval, val_atom.eval, lifts, vals.eval],
  },
  case H_clos_cons : _ _ w ws ih ih' {
    simp [evalV] at ih,
    simp [lift, evalV, val.eval, val_atom.eval] at ih',
    simp [evalV, lift, val.eval, val_atom.eval, lifts, vals.eval, ih, ih'],
  },
end

def is_tf (b : term type.bool) := is_tt b ∨ is_ff b

lemma pe_not.red {b : term type.bool} (h : is_tf b) : is_tf (pe_not b) :=
begin 
  cases b,
  case [var, ite, expr] {
    all_goals {
      contra [is_tf, is_tt, is_ff] at h,
    },
  },
  case lit : l {
    cases l with b,
    cases b,
    all_goals { simp [pe_not, is_tf, is_tt, is_ff] },
  },
end

lemma pe_and.red {a b : term type.bool} (h_a : is_tf a) (h_b : is_tf b) : 
  is_tf (pe_and a b) :=
begin 
  cases a,
  case [var, ite, expr] {
    all_goals {
      contra [is_tf, is_tt, is_ff] at h_a,
    },
  },
  case lit : l_a {
    cases b,
    case [var, ite, expr] {
      all_goals {
        contra [is_tf, is_tt, is_ff] at h_b,
      },
    },
    case lit : l_b {
      cases l_a with b_a,
      cases l_b with b_b,
      cases b_a,
      all_goals {
        cases b_b,
        all_goals {
          simp [pe_and, is_tf, is_tt, is_ff, mk_ff, mk_tt],
        },
      },
    },
  },
end

lemma pe_or.red {a b : term type.bool} (h_a : is_tf a) (h_b : is_tf b) : 
  is_tf (pe_or a b) :=
begin 
  cases a,
  case [var, ite, expr] {
    all_goals {
      contra [is_tf, is_tt, is_ff] at h_a,
    },
  },
  case lit : l_a {
    cases b,
    case [var, ite, expr] {
      all_goals {
        contra [is_tf, is_tt, is_ff] at h_b,
      },
    },
    case lit : l_b {
      cases l_a with b_a,
      cases l_b with b_b,
      cases b_a,
      all_goals {
        cases b_b,
        all_goals {
          simp [pe_or, is_tf, is_tt, is_ff, mk_ff, mk_tt],
        },
      },
    },
  },
end

lemma pe_imp.red {a b : term type.bool} (h_a : is_tf a) (h_b : is_tf b) : 
  is_tf (pe_imp a b) :=
begin 
  cases a,
  case [var, ite, expr] {
    all_goals {
      contra [is_tf, is_tt, is_ff] at h_a,
    },
  },
  case lit : l_a {
    cases b,
    case [var, ite, expr] {
      all_goals {
        contra [is_tf, is_tt, is_ff] at h_b,
      },
    },
    case lit : l_b {
      cases l_a with b_a,
      cases l_b with b_b,
      cases b_a,
      all_goals {
        cases b_b,
        all_goals {
          simp [pe_imp, pe_not, pe_or, is_tf, is_tt, is_ff, mk_ff, mk_tt],
        },
      },
    },
  },
end

lemma truth.red {w : op.lang.val} : is_tf (truth (lift w)) :=
begin 
  cases w,
  case bool : b {
    cases b,
    all_goals { simp [lift, truth, truth.atom, is_tf, is_tt, is_ff] },
  },
  case datum : d {
    cases d,
    all_goals { simp [lift, truth, truth.atom, is_tf, is_tt] },
  },
  case list : xs {
    simp [lift, lifts, truth, truth.atom, is_tf, is_tt]
  },
  case clos : _ _ ε {
    simp [lift, lifts, truth, truth.atom, is_tf, is_tt]
  },
end

lemma bval.red {b : bool} : (lift (lang.val.bool b)) = (bval b) := 
  by simp [lift, bval]

lemma dval.red {d : op.lang.datum} : (lift (lang.val.datum d)) = (dval d) := 
begin 
  cases d,
  all_goals { simp [lift, dval] },
end

lemma lifts.eq_map {ε : list op.lang.val} : list.map lift ε = lifts ε := 
begin 
  induction ε with hd tl ih,
  case nil { simp [lifts] },
  case cons { simpa [lifts] },
end

lemma cval.red {w : op.lang.val} {c : clos op.lang.datum op.lang.op val} : 
  w.to_clos lift = some c ↔ (lift w) = (cval c) := 
begin 
  cases c with _ _ c_ε,
  cases w,
  case [bool, list] {
    all_goals { simp [lang.val.to_clos, lift, cval] },
  },
  case datum : d {
    cases d,
    all_goals { simp [lang.val.to_clos, lift, cval] },
  },
  case clos : _ _ ε {
    simp [lang.val.to_clos, lift, cval, lang.env.lift],
    intros,
    simp [lifts.eq_map],
  },
end

lemma cast.red {w : op.lang.val} : (w.to_clos lift = none → cast (lift w) = []) ∧ 
  (∀ c, w.to_clos lift = some c → cast (lift w) = [⟨mk_tt, c⟩]) := 
begin 
  cases w,
  case [bool, list] {
    all_goals { simp [lang.val.to_clos, lift, cast] },
  },
  case datum : d {
    cases d,
    all_goals { simp [lang.val.to_clos, lift, cast, cast_choices, adjust, adjust_core] },
  },
  case clos : _ _ ε {
    simp [lang.val.to_clos, lift, cast, lang.env.lift, lifts.eq_map],
  },
end

lemma merge.red {w : op.lang.val} : merge ([⟨mk_tt, lift w⟩]) = lift w := 
begin 
  cases w,
  case [bool, list, clos] {
    all_goals { simp [merge, lift, merge.core, is_tt, mk_tt] },
  },
  case datum : d {
    cases d,
    all_goals { simp [merge, adjust, adjust_core, lift, merge.core, is_tt, mk_tt] },
  },
end

def result.lift (lift : op.lang.val → val) : op.lang.result → op.sym.result 
| (lang.result.ans w)   := sym.result.ans ⟨mk_tt, mk_tt⟩ (lift w)
| (lang.result.halt tt) := sym.result.halt ⟨mk_ff, mk_tt⟩  
| (lang.result.halt ff) := sym.result.halt ⟨mk_tt, mk_ff⟩ 

lemma opS_split.red_pos {o : op.lang.op} {ws : list op.lang.val} {vas : list val_atom}
  (h : op.lang.undef ∈ ws) :
  opS.split o (list.map lift ws) mk_tt vas = ⟨mk_ff, val.union []⟩ :=
begin 
  induction ws with hd tl ih generalizing vas,
  case nil { contra at h },
  case cons {
    cases h,
    case inl {
      subst_vars,
      simp [
        lift, op.lang.undef, opS.split, opS.split_map, adjust, adjust_core, 
        make_disjunction, merge, merge.core
      ],
    },
    case inr {
      cases hd,
      focus_case datum {
        cases hd,
        case undef {
          simp [
            lift, op.lang.undef, opS.split, opS.split_map, adjust, adjust_core, 
            make_disjunction, merge, merge.core
          ],
        },
      },
      all_goals { 
        simp [lift, opS.split],
        apply ih,
        apply h,
      },
    },
  },
end

lemma opS_split.red_neg {o : op.lang.op} {ws : list op.lang.val} {vas : list val_atom}
  (h : op.lang.undef ∉ ws) :
  opS.split o (list.map lift ws) mk_tt vas = 
    match opS.core o (list.reverse vas ++ list.map lift.atom ws) with 
    | none := ⟨mk_ff, val.union []⟩
    | some v := ⟨mk_tt, v⟩
    end :=
begin 
  induction ws with hd tl ih generalizing vas,
  case nil {
    cases h' : opS.core _ _,
    all_goals {
      simp at h',
      simp [opS.split, h'],
    },
  },
  case cons {
    simp [not_or_distrib] at h,
    cases hd,
    focus_case datum {
      cases hd,
      case undef { contra [op.lang.undef] at h },
    },
    all_goals {
      cases h with _ h,
      simp [opS.split, lift],
      cases h' : opS.core _ _,
      case none {
        rw ih h,
        cases h'' : opS.core _ _,
        case none { simp },
        case some {
          simp [lift.atom] at h',
          contra [h'] at h'',
        },
      },
      case some {
        rw ih h,
        cases h'' : opS.core _ _,
        case none {
          simp [lift.atom] at h',
          contra [h'] at h'',
        },
        case some {
          simp [lift.atom] at h',
          simp [h'] at h'',
          subst h'',
        },
      },
    },
  },
end

lemma opS.red {o : op.lang.op} {ws : list op.lang.val} :
  (opS o (ws.map lift)) = result.lift lift (op.lang.opC o ws) :=
begin 
  simp [opS],
  by_cases_c h : op.lang.undef ∈ ws,
  case pos {
    rw opC.eval_undef_err h,
    simp [@opS_split.red_pos o ws [] h, opS, is_ff.sound, result.lift],
  },
  case neg {
    simp [@opS_split.red_neg o ws [] h],
    cases h' : opS.core _ _,
    case none {
      simp [opS, is_ff.sound],
      simp at h',
      cases o,
      case int_2 {
        cases ws,
        focus_case cons : w_a ws {
          cases ws,
          focus_case cons : w_b ws {
            cases ws,
            focus_case nil {
              cases w_a,
              focus_case datum {
                cases w_b,
                focus_case datum {
                  cases w_a,
                  focus_case int {
                    cases w_b,
                    focus_case int {
                      cases o,
                      all_goals { contra [opS.core, lift.atom] at h' },
                    },
                  },
                },
              },
            },
          },
        },
        all_goals { simp [op.lang.opC, op.lang.opC_int_2, result.lift] },
      },
      case list_proj {
        cases ws,
        focus_case cons : w ws {
          cases ws,
          focus_case nil {
            cases w,
            focus_case list : xs {
              cases xs,
              case cons {
                cases o,
                all_goals { contra [opS.core, lift.atom, lifts] at h' },
              },
            },
          },
        },
        all_goals { simp [op.lang.opC, op.lang.opC_list_proj, result.lift] },
      },
      case list_cons {
        cases ws,
        focus_case cons : w_a ws {
          cases ws,
          focus_case cons : w_b ws {
            cases ws,
            focus_case nil {
              cases w_b,
              case list {
                cases w_a,
                focus_case datum {
                  cases w_a,
                  case undef { simp [op.lang.opC, result.lift] },
                },
                all_goals { contra [opS.core, lift.atom, lifts] at h' },
              },
            },
          },
        },
        all_goals { simp [op.lang.opC, result.lift] },
      },
      case list_is_null {
        cases ws,
        focus_case cons : w ws {
          cases ws,
          case nil {
            cases w,
            focus_case datum {
              cases w,
              case undef { simp [op.lang.opC, result.lift] },
            },
            all_goals { contra [opS.core, lift.atom, lifts] at h' },
          },
        },
        all_goals { simp [op.lang.opC, result.lift] },
      },
      case list_null {
        cases ws,
        case nil { contra [opS.core, lift.atom, lifts] at h' },
        case cons { simp [op.lang.opC, result.lift] },
      },
    },
    case some {
      simp [opS, is_ff.sound, mk_tt, mk_ff],
      simp at h',
      cases o,
      case int_2 {
        cases ws,
        focus_case cons : w_a ws {
          cases ws,
          focus_case cons : w_b ws {
            cases ws,
            focus_case nil {
              cases w_a,
              focus_case datum {
                cases w_b,
                focus_case datum {
                  cases w_a,
                  focus_case int {
                    cases w_b,
                    focus_case int {
                      cases o,
                      all_goals { 
                        simp [opS.core, lift.atom] at h',
                        simp [
                          ← h', mk_tt, op.lang.opC, lift, result.lift, 
                          op.lang.opC_int_2, opS.int_wrap, opS.int
                        ],
                      },
                    },
                  },
                },
              },
            },
          },
        },
        any_goals { solve1 { contra [opS.core, lift.atom] at h' } },
        all_goals {
          cases w_a,
          all_goals { contra [opS.core, lift.atom] at h' },
        },
      },
      case list_proj {
        cases ws,
        focus_case cons : w ws {
          cases ws,
          focus_case nil {
            cases w,
            focus_case list : xs {
              cases xs,
              case cons {
                cases o,
                all_goals { 
                  simp [opS.core, lift.atom, lifts] at h',
                  simp [
                    ← h', mk_tt, op.lang.opC, lift, result.lift, 
                    op.lang.opC_list_proj
                  ],
                },
              },
            },
            focus_case datum { cases w },
          },
        },
        all_goals { contra [opS.core, lift.atom, lifts] at h' },
      },
      case list_cons {
        cases ws,
        focus_case cons : w_a ws {
          cases ws,
          focus_case cons : w_b ws {
            cases ws,
            focus_case nil {
              cases w_b,
              case list {
                cases w_a,
                focus_case datum {
                  cases w_a,
                  case undef { contra [op.lang.undef] at h },
                },
                all_goals { 
                  simp [opS.core, lift.atom, lifts] at h',
                  simp [← h', mk_tt, op.lang.opC, lift, result.lift, lifts],
                },
              },
              focus_case datum {
                cases w_b,
                case undef { contra [op.lang.undef] at h },
              }
            },
          },
        },
        all_goals { contra [opS.core, lift.atom, lifts] at h' },
      },
      case list_is_null {
        cases ws,
        focus_case cons : w ws {
          cases ws,
          case nil {
            cases w,
            focus_case datum {
              cases w,
              case undef { contra [op.lang.undef] at h },
            },
            focus_case list { cases w },
            all_goals {
              simp [opS.core, lift.atom, lifts] at h',
              simp [← h', mk_tt, op.lang.opC, lift, result.lift, lifts],
            },
          },
        },
        all_goals { contra [opS.core, lift.atom, lifts] at h' },
      },
      case list_null {
        cases ws,
        case nil { 
          simp [opS.core, lift.atom, lifts] at h',
          simp [← h', mk_tt, op.lang.opC, lift, result.lift, lifts],
        },
        case cons { contra [opS.core, lift.atom, lifts] at h' },
      },
    },
  },
end

def reducing_factory : reducer _ _ _ _ _ := {
  lift := lift,
  lift_sound := by { simp [lift_sound] },
  not_red := by {
    intro b,
    have := @pe_not.red b,
    simp [is_tf, factory.is_tf] at ⊢ this,
    exact this,
  },
  and_red := by {
    intros a b,
    have := @pe_and.red a b,
    simp [is_tf, factory.is_tf] at ⊢ this,
    exact this,
  },
  or_red := by {
    intros a b,
    have := @pe_or.red a b,
    simp [is_tf, factory.is_tf] at ⊢ this,
    exact this,
  },
  imp_red := by {
    intros a b,
    have := @pe_imp.red a b,
    simp [is_tf, factory.is_tf] at ⊢ this,
    exact this,
  },
  truth_red := by {
    intros w,
    have := @truth.red w,
    simp [is_tf, factory.is_tf] at ⊢ this,
    exact this,
  },
  bval_red := by { simp [bval.red] },
  dval_red := by { simp [dval.red] },
  cval_red := by { simp [cval.red] },
  cast_red := by { apply cast.red },
  merge_red := by { apply merge.red },
  opS_red := by { 
    intros o ws,
    have := @opS.red o ws,
    simp,
    cases op.lang.opC o ws,
    case ans {
      simp [result.lift, lang.result.lift] at ⊢ this,
      assumption,
    },
    case halt : h {
      cases h,
      all_goals {
        simp [result.lift, lang.result.lift] at ⊢ this,
        assumption,
      },
    },
  },
  ..sym_factory,
}

end sym_factory