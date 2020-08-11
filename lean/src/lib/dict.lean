namespace dictionary

meta def tactic.dec_trivial := `[exact dec_trivial]

/- Definitions -/
section defs
variables (κ α : Type*)

def dict := κ → α

instance [inhabited α] : inhabited (dict κ α) :=
⟨λ _, default α⟩

end defs

/- Operations and lemmas -/
section ops
variables {κ α : Type*} [decidable_eq κ]

def dict.update (name : κ) (val : α) (s : dict κ α) : dict κ α :=
λ name', if name' = name then val else s name'

notation e `{` name ` ↦ ` val `}` := dict.update name val e

@[simp] lemma dict.update_apply (name : κ) (val : α) (e : dict κ α) :
e{name ↦ val} name = val :=
if_pos rfl

@[simp] lemma dict.update_apply_ne (name name' : κ) (val : α) (e : dict κ α)
    (h : name' ≠ name . tactic.dec_trivial) :
  e{name ↦ val} name' = e name' :=
if_neg h

@[simp] lemma dict.update_override (name : κ) (val₁ val₂ : α) (e : dict κ α) :
  e{name ↦ val₂}{name ↦ val₁} = e{name ↦ val₁} :=
begin
  apply funext,
  intro name',
  by_cases name' = name;
    simp [h]
end

@[simp] lemma dict.update_swap (name₁ name₂ : κ) (val₁ val₂ : α) (e : dict κ α)
    (h : name₁ ≠ name₂ . tactic.dec_trivial) :
  e{name₂ ↦ val₂}{name₁ ↦ val₁} = e{name₁ ↦ val₁}{name₂ ↦ val₂} :=
begin
  apply funext,
  intro name',
  by_cases name' = name₁;
    by_cases name' = name₂;
    simp * at *
end

@[simp] lemma dict.update_id (name : κ) (e : dict κ α) :
  e{name ↦ e name} = e :=
begin
  apply funext,
  intro name',
  by_cases name' = name;
    simp * at *
end
end ops

end dictionary

