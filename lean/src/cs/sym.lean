import tactic.basic
import .lang

namespace sym

section eval 

  structure has_eval (Model SymB SymV SymR : Type) := 
  (evalB : Model → SymB → bool)
  (evalV : Model → SymV → SymR)
  

end eval 


structure choice (SymB SymV : Type) :=
(guard : SymB)
(value : SymV)

@[reducible] def choices (SymB SymV : Type) := list (choice SymB SymV)

section choices

  variables 
    {Model SymB SymV SymR : Type}
    (ev : has_eval Model SymB SymV SymR)
    (m  : Model)

  def choices.true {α} (gvs : choices SymB α) : list SymB := 
    (gvs.map choice.guard).filter (λ g, ev.evalB m g)

  def choices.lone {α} (gvs : choices SymB α) : Prop := 
  (gvs.true ev m).length ≤ 1

  def choices.none {α} (gvs : choices SymB α) : Prop := 
  (gvs.true ev m).length = 0

  def choices.one {α} (gvs : choices SymB α) : Prop := 
  (gvs.true ev m).length = 1

  def choices.eval (default : SymR) : (choices SymB SymV) → SymR
  | []            := default
  | (⟨g, v⟩::gvs) := if (ev.evalB m g) then (ev.evalV m v) else (choices.eval gvs)

end choices

structure state (SymB : Type) : Type := 
(assumes : SymB) 
(asserts : SymB)

-- def has_eval_state { Model SymB SymV SymR : Type } (ev : has_eval Model SymB SymV SymR) : 
-- has_eval Model SymB (state SymB) (state bool) := 
-- ⟨ev.evalB, λ m σ, some ⟨ev.evalB m σ.assumes, ev.evalB m σ.asserts⟩⟩

section state

  variables 
    {Model SymB SymV SymR : Type}
    (ev : has_eval Model SymB SymV SymR)
    (m  : Model)

  def state.normal  (σ : state SymB) : bool := 
  (ev.evalB m σ.assumes) ∧ (ev.evalB m σ.asserts)  

  def state.aborted (σ : state SymB) : bool := 
  ¬ (ev.evalB m σ.assumes) ∧ (ev.evalB m σ.asserts)  

  def state.errored (σ : state SymB) : bool := 
  (ev.evalB m σ.assumes) ∧ ¬ (ev.evalB m σ.asserts)

  def state.legal (σ : state SymB) : bool := 
  (ev.evalB m σ.assumes) ∨ (ev.evalB m σ.asserts)  

  def state.eqv (σ' σ : state SymB) := 
  ev.evalB m σ'.assumes = ev.evalB m σ.assumes ∧ 
  ev.evalB m σ'.asserts = ev.evalB m σ.asserts 

  @[refl]
  protected lemma state.eqv.refl {σ : state SymB} : 
  σ.eqv ev m σ := by {simp [state.eqv],}

  @[symm]
  protected lemma state.eqv.symm {σ' σ : state SymB} : 
  σ'.eqv ev m σ → σ.eqv ev m σ' := by { finish [state.eqv], }

  @[trans]
  protected lemma state.eqv.trans {σ'' σ' σ : state SymB}  :
  σ''.eqv ev m σ' → σ'.eqv ev m σ → σ''.eqv ev m σ := by { finish [state.eqv], }



end state


inductive result (SymB SymV : Type) : Type
| ans  : (state SymB) → SymV → result 
| halt : (state SymB) → result

section result

  variables {SymB SymV : Type}

  def result.is_ans : result SymB SymV → bool 
  | (result.ans _ _) := true 
  | _ := false

  def result.is_halt : result SymB SymV → bool 
  | (result.halt _) := true 
  | _ := false

  def result.state : result SymB SymV → state SymB
  | (result.ans σ _) := σ 
  | (result.halt σ)  := σ

  def result.value (default : SymV) : result SymB SymV → SymV 
  | (result.ans _ v) := v 
  | (result.halt _)  := default

end result

section result 

  variables 
    {Model SymB SymV D O : Type}
    (ev : has_eval Model SymB SymV (lang.val D O))
    (m  : Model)

  def result.eval : (result SymB SymV) → (lang.result D O)  
    | (result.ans σ v) := 
      if (σ.normal ev m) 
      then lang.result.ans (ev.evalV m v) 
      else lang.result.halt (σ.aborted ev m)
    | (result.halt σ)  := lang.result.halt (σ.aborted ev m) 

  def result.legal : (result SymB SymV) → bool  
  | (result.ans σ v) := (σ.legal ev m)  
  | (result.halt σ)  := (σ.legal ev m) ∧ ¬ (σ.normal ev m)

  def has_eval_result { Model SymB SymV D O : Type } (ev : has_eval Model SymB SymV (lang.val D O)) : 
  has_eval Model SymB (result SymB SymV) (lang.result D O) := 
  ⟨ev.evalB, (result.eval ev)⟩

end result 

def env (SymV : Type) := list SymV

section env 

  variables 
    {Model SymB SymV D O : Type}
    (ev : has_eval Model SymB SymV (lang.val D O))
    (m  : Model)

  def env.eval (ε : env SymV) : lang.env D O := ε.map (ev.evalV m) 

end env 

structure clos (D O SymV : Type) :=
(var : ℕ)
(exp : lang.exp D O)
(env : env SymV)

section clos 

  variables
    {Model SymB SymV D O : Type}
    (ev : has_eval Model SymB SymV (lang.val D O))
    (m  : Model) 

  def clos.eval (c : clos D O SymV) : lang.val D O :=
    lang.val.clos c.var c.exp (c.env.eval ev m)

  def has_eval_clos { Model SymB SymV D O : Type } (ev : has_eval Model SymB SymV (lang.val D O)) : 
  has_eval Model SymB (clos D O SymV) (lang.val D O) := ⟨ev.evalB, clos.eval ev⟩

end clos

structure factory (Model SymB SymV D O : Type) [inhabited Model] [inhabited SymV]
extends has_eval Model SymB SymV (lang.val D O) :=

(mk_tt : SymB)                                  -- Returns a SymB representing the literal tt.
(mk_ff : SymB)                                  -- Returns a SymB representing the literal ff.
(is_tt : SymB → bool)                           -- Returns tt iff a SymB represents the literal tt. 
(is_ff : SymB → bool)                           -- Returns tt iff a SymB represents the literal ff.

(not   : SymB → SymB)  
(and   : SymB → SymB → SymB)
(or    : SymB → SymB → SymB)
(imp   : SymB → SymB → SymB)

(truth : SymV → SymB)                           -- Returns a SymB that evalutes to ff iff SymV does too.
(bval  : bool → SymV)                           -- Returns a SymV representing the given SymB.
(dval  : D → SymV)                              -- Returns a SymV representing the given datum.
(cval  : (clos D O SymV) → SymV)                -- Returns a SymV representing a closure. 
(cast  : SymV → (choices SymB (clos D O SymV))) -- Reduces a SymV to guarded closures, if any.

(merge : (choices SymB SymV) → SymV)

(opC  : O → list (lang.val D O) → (lang.result D O)) -- Concrete ops.
(opS  : O → list SymV → (result SymB SymV))          -- Corresponding symbolic ops.

(mk_tt_sound : ∀ m, evalB m mk_tt = tt)
(mk_ff_sound : ∀ m, evalB m mk_ff = ff)
(is_tt_sound : ∀ b, (is_tt b) ↔ (b = mk_tt))
(is_ff_sound : ∀ b, (is_ff b) ↔ (b = mk_ff))
(not_sound   : ∀ m b1, (evalB m (not b1)) = ¬ (evalB m b1))
(and_sound   : ∀ m b1 b2, (evalB m (and b1 b2)) = ((evalB m b1) ∧ (evalB m b2)))
(or_sound    : ∀ m b1 b2, (evalB m (or b1 b2)) = ((evalB m b1) ∨ (evalB m b2)))
(imp_sound   : ∀ m b1 b2, (evalB m (imp b1 b2)) = ((evalB m b1) → (evalB m b2)))

(truth_sound : ∀ m v, ((evalB m (truth v)) ↔ ((evalV m v) ≠ (lang.val.bool ff))))
(bval_sound  : ∀ m b, evalV m (bval b) = (lang.val.bool b))
(dval_sound  : ∀ m d, evalV m (dval d) = (lang.val.datum d))

(cval_sound : ∀ m c, evalV m (cval c) = c.eval to_has_eval m)
(cast_sound : ∀ m v, 
                ((evalV m v).is_clos → 
                  ((cast v).one (has_eval_clos to_has_eval) m ∧ 
                   (cast v).eval (has_eval_clos to_has_eval) m (evalV m v) = (evalV m v))) ∧ 
                (¬(evalV m v).is_clos → 
                  (cast v).none (has_eval_clos to_has_eval) m)) 

(merge_sound : ∀ m (gvs : choices SymB SymV), 
                (gvs.one to_has_eval m) → 
                evalV m (merge gvs) = gvs.eval to_has_eval m (evalV m (default SymV)))

(opS_sound   : ∀ m o (vs : list SymV),
                (opS o vs).eval to_has_eval m = (opC o (vs.map (evalV m))) ∧ 
                (opS o vs).legal to_has_eval m)

section factory

  variables 
    {Model SymB SymV D O : Type} 
    [inhabited Model] [inhabited SymV]
    (f : factory Model SymB SymV D O)

  def factory.some {α} (fn : α → SymB) (xs : list α) : SymB := 
  xs.foldr (λ x g, f.or (fn x) g) f.mk_ff

  def factory.all {α} (fn : α → SymB) (xs : list α) : SymB := 
  xs.foldr (λ x g, f.and (fn x) g) f.mk_tt

end factory

end sym