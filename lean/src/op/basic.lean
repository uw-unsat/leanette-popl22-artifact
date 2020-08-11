import .sym
import ..cs.sym
import ..cs.lib
import ..tactic.all

open op.sym

lemma int.evals_to_int {m : model} {t : term type.int} {w : op.lang.val}
  (h : (val_atom.term t).eval m = w) :
  ∃ {i : ℤ}, w = lang.val.datum (op.lang.datum.int i) := 
begin 
  simp only [val_atom.eval] at h,
  cases t.eval m with _ i,
  simp only [lit.to_val] at h,
  use i,
  simp [h],
end

lemma bool.evals_to_bool {m : model} {t : term type.bool} {w : op.lang.val}
  (h : (val_atom.term t).eval m = w) :
  ∃ {b : bool}, w = (lang.val.bool b) := 
begin 
  simp only [val_atom.eval] at h,
  cases t.eval m with b,
  simp only [lit.to_val] at h,
  use b,
  simp [h],
end

lemma env.eval_lift {m : model} {ε : env} : 
  vals.eval ε m = sym.env.eval ev m ε :=
begin 
  induction ε with hd tl ih,
  case nil { simp [sym.env.eval, vals.eval] },
  case cons { simp [sym.env.eval, vals.eval, ih, ev, evalV, list.map] },
end

lemma clos.eval_lift {m : model} 
  {x : ℕ} {e : op.lang.exp} {ε : list val} :
  (val_atom.clos x e ε).eval m = sym.clos.eval ev m ⟨x, e, ε⟩ :=
  by simp [sym.clos.eval, val_atom.eval, env.eval_lift]

lemma choices.eval_lift {m : model} {gvs : choices' val_atom} :
  choices.eval gvs m = gvs.eval ev.atom m op.lang.undef :=
begin 
  induction gvs with hd tl ih,
  case nil { simp [choices.eval, sym.choices.eval] },
  case cons {
    cases hd with g va,
    simp only [choices.eval, sym.choices.eval, ev.atom, evalB],
    split_ifs,
    case_c { simp [evalVA] },
    case_c { assumption },
  },
end

lemma clos.evals_to_clos {m : model} {w : op.lang.val}
  {x : ℕ} {e : op.lang.exp} {ε : op.sym.env} 
  (h : (val_atom.clos x e ε).eval m = w) : w.is_clos :=
begin 
  apply_c sym.clos.evals_to_clos,
  case ev { exact ev },
  case c { exact ⟨x, e, ε⟩ },
  case_c { simpa [← clos.eval_lift] },
end

lemma list.evals_to_list {m : model} {w : op.lang.val}
  {vs : list val}
  (h : (val_atom.list vs).eval m = w) : w.is_list :=
begin 
  cases vs,
  case nil {
    simp only [val_atom.eval] at h,
    simp [← h],
  },
  case cons : hd tl { simp [← h, val_atom.eval] },
end

lemma list.evals_cons {m : model} {w : op.lang.val}
  {v : val} {vs : list val}
  (h : (val_atom.list (v :: vs)).eval m = w) : 
  ∃ w' ws', 
    v.eval m = w' ∧ 
    (val_atom.list vs).eval m = lang.val.list ws' ∧ 
    w = lang.val.list (w' :: ws') :=
begin 
  simp only [val_atom.eval, vals.eval] at h,
  use [v.eval m, vals.eval vs m],
  simp [val_atom.eval, h],
end

lemma choices.none_changes_eval {SymV_0 SymV SymV' SymR SymR' : Type} {m : model} 
  {gvs : sym.choices (term type.bool) SymV_0}
  {evalV : model → SymV → SymR} (evalV' : model → SymV' → SymR') :
  sym.choices.none (make_ev evalV) m gvs ↔ sym.choices.none (make_ev evalV') m gvs :=
  by simp [sym.choices.none, sym.choices.true]

lemma val_atom.evals_no_undef {va : val_atom} {m : model} :
  va.eval m ≠ op.lang.undef :=
begin 
  generalize h : va.eval m = w,
  cases va,
  case term : τ t {
    cases τ,
    case bool {
      cases bool.evals_to_bool h with _ h',
      subst h',
      simp [op.lang.undef],
    },
    case int {
      cases int.evals_to_int h with _ h',
      subst h',
      simp [op.lang.undef],
    },
  },
  case clos {
    replace h := clos.evals_to_clos h,
    cases w,
    all_goals { contradiction },
  },
  case list {
    replace h := list.evals_to_list h,
    cases w,
    all_goals { contradiction },
  },
end