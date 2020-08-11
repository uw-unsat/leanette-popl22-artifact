import ..cs.lang
import ..cs.sym
import .lang
import ..lib.dict 

namespace op

namespace sym

open sym
open dictionary

section terms 

inductive type : Type 
| bool : type 
| int  : type 

@[derive decidable_eq]
inductive var : type → Type 
| mk : ∀ (t : type), ℕ → var t

@[derive decidable_eq]
inductive lit : type → Type 
| bool : bool → lit type.bool 
| int  : int → lit type.int

instance (t : type) : inhabited (lit t) :=
⟨match t with
 | type.bool := lit.bool ff
 | type.int  := lit.int 0
 end⟩

def lit.to_bool : (lit type.bool) → bool
| (lit.bool b) := b

def lit.to_int : (lit type.int) → int
| (lit.int i) := i

@[derive decidable_eq]
inductive typedop : type → Type 
| add : typedop type.int
| mul : typedop type.int
| lt : typedop type.bool
| eq : typedop type.bool

@[derive decidable_eq]
inductive term : type → Type 
| lit   : ∀ {t : type}, (lit t) → term t
| var   : ∀ {t : type}, (var t) → term t
| ite   : ∀ {t : type}, (term type.bool) → (term t) → (term t) → (term t)
| expr  : ∀ {t : type}, (typedop t) → (term type.int) → (term type.int) → (term t) 

def term.is_int : ∀ {t : type}, term t → Prop 
| type.int _ := true 
| _ _        := false

def term.is_bool : ∀ {t : type}, term t → Prop 
| type.bool _ := true 
| _ _         := false

def term.is_lit : ∀ {t : type}, term t → Prop 
| _ (term.lit _) := true 
| _ _ := false 

def term.is_ff : term type.bool → bool 
| (term.lit (lit.bool ff)) := tt 
| _ := ff 

def term.is_tt : term type.bool → bool 
| (term.lit (lit.bool tt)) := tt 
| _ := ff 

def model := ∀ (t : type), dict (var t) (lit t)

instance : inhabited model :=
⟨λ (t : type) (v : var t), 
  match t with 
  | type.bool := lit.bool tt 
  | type.int := lit.int 0
  end⟩

def typedop.eval : ∀ {t : type}, (typedop t) → (lit type.int) → (lit type.int) → (lit t)
| _ typedop.add (lit.int i) (lit.int j) := lit.int (i + j)
| _ typedop.mul (lit.int i) (lit.int j) := lit.int (i * j)
| _ typedop.lt  (lit.int i) (lit.int j) := lit.bool (i < j)
| _ typedop.eq  (lit.int i) (lit.int j) := lit.bool (i = j)

def term.eval : ∀ {t : type}, (term t) → model → (lit t)
| _ (term.lit l)      _ := l
| _ (term.var v)      m := m _ v
| _ (term.ite c t f)  m := if (c.eval m).to_bool then (t.eval m) else (f.eval m)
| _ (term.expr o l r) m := o.eval (l.eval m) (r.eval m)

def term.is_true (t : term type.bool) (m : model) : bool := (t.eval m).to_bool

@[reducible] def choices' (τ : Type) := choices (term type.bool) τ

end terms 

section values

mutual inductive val_atom, val
with val_atom : Type
| term {τ : type} (t : term τ) : val_atom
| clos (x : ℕ) (e : lang.exp) (ε : list val) : val_atom
| list (vs : list val) : val_atom
with val : Type
| atom (va : val_atom) : val
| union (gvs : choices' val_atom) : val

instance : inhabited val :=
⟨val.union []⟩

def val.is_atom    : val → bool
| (val.atom _) := true
| _            := false

def val_atom.is_clos    : val_atom → bool
| (val_atom.clos _ _ _) := true
| _                := false

def val_atom.is_int  : val_atom → Prop
| (val_atom.term t)  := t.is_int
| _             := false

def val_atom.is_bool : val_atom → Prop
| (val_atom.term t)  := t.is_bool
| _             := false

def val_atom.is_list : val_atom → Prop
| (val_atom.list _)  := true
| _             := false

def lit.to_val : ∀ {t : type}, (lit t) → lang.val 
| _ (lit.bool b) := lang.val.bool b 
| _ (lit.int i)  := lang.val.datum (lang.datum.int i) 

mutual def val.eval, choices.eval, vals.eval, val_atom.eval
with val.eval : val → model → lang.val 
| (val.union gvs) m := choices.eval gvs m
| (val.atom a) m := val_atom.eval a m
with choices.eval : choices' val_atom → model → lang.val
| []            _ := lang.undef
| (⟨g, v⟩ :: gvs) m := if g.is_true m then val_atom.eval v m else choices.eval gvs m
with vals.eval : list val → model → list lang.val
| [] _ := []
| (v :: vs) m := (v.eval m) :: (vals.eval vs m)
with val_atom.eval : val_atom → model → lang.val
| (val_atom.term t)       m := (t.eval m).to_val
| (val_atom.clos y x ε)   m := lang.val.clos y x (vals.eval ε m)
| (val_atom.list xs) m := lang.val.list (vals.eval xs m)
  

end values 

section eval

@[reducible] def result := sym.result (term type.bool) val
@[reducible] def env := sym.env val
@[reducible] def clos := sym.clos lang.datum lang.op val

def evalB (m : model) (t : term type.bool) : bool := t.is_true m
def evalV (m : model) (v : val) : lang.val := v.eval m
def evalVA (m : model) (va : val_atom) : lang.val := va.eval m
def evalR (m : model) (v : val) : lang.result := lang.result.ans (evalV m v)

@[reducible] def make_ev {τ τ' : Type} (evalV : model → τ → τ') := {
  has_eval .
  evalB := evalB,
  evalV := evalV,
}

def ev := make_ev evalV
def ev.clos := make_ev (clos.eval ev)
def ev.atom := make_ev evalVA
def ev.result := make_ev evalR

end eval


end sym

end op
