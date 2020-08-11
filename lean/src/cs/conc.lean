import .sym

section defs 

  variables 
    {SymV D O : Type}
    (lift : (lang.val D O) → SymV)

  def lang.env.lift (e : lang.env D O) : sym.env SymV := e.map lift

  def lang.val.to_clos : lang.val D O → option (sym.clos D O SymV)
  | (lang.val.clos y x e) := some (sym.clos.mk y x (lang.env.lift lift e))
  | _                     := none 

end defs 

section factory 

  variables 
    {Model SymB SymV D O : Type} 
    [inhabited Model] [inhabited SymV]
    (f : sym.factory Model SymB SymV D O)
  
  def sym.factory.is_tf (b : SymB) : bool := f.is_tt b ∨ f.is_ff b

  def lang.result.lift (lift : (lang.val D O) → SymV) : lang.result D O → sym.result SymB SymV 
  | (lang.result.ans w)   := sym.result.ans ⟨f.mk_tt, f.mk_tt⟩ (lift w)
  | (lang.result.halt tt) := sym.result.halt ⟨f.mk_ff, f.mk_tt⟩  
  | (lang.result.halt ff) := sym.result.halt ⟨f.mk_tt, f.mk_ff⟩  

end factory 

namespace sym 

section reducer
  
  -- A symbolic factory is a reducer if it provides the function lift for 
  -- lifting arbitrary concrete values to symbolic values, if lift is consistent 
  -- with the already provided lifting function, and if all other 
  -- functions reduce lifted inputs to lifted outputs.
  structure reducer (Model SymB SymV D O : Type) [inhabited Model] [inhabited SymV]
  extends factory Model SymB SymV D O :=
  (lift       : (lang.val D O) → SymV)
  (lift_sound : ∀ m w, evalV m (lift w) = w)
  (not_red    : ∀ b, to_factory.is_tf b → to_factory.is_tf (not b))
  (and_red    : ∀ b1 b2, to_factory.is_tf b1 → to_factory.is_tf b2 → to_factory.is_tf (and b1 b2))
  (or_red     : ∀ b1 b2, to_factory.is_tf b1 → to_factory.is_tf b2 → to_factory.is_tf (or b1 b2)) 
  (imp_red    : ∀ b1 b2, to_factory.is_tf b1 → to_factory.is_tf b2 → to_factory.is_tf (imp b1 b2)) 
  (truth_red  : ∀ w, to_factory.is_tf (truth (lift w)))
  (bval_red   : ∀ b, (lift (lang.val.bool b)) = (bval b))
  (dval_red   : ∀ d, (lift (lang.val.datum d)) = (dval d))
  (cval_red   : ∀ (w : lang.val D O) c, w.to_clos lift = some c ↔ (lift w) = (cval c))
  (cast_red   : ∀ (w : lang.val D O), 
                  (w.to_clos lift = none → cast (lift w) = []) ∧ 
                  (∀ c, w.to_clos lift = some c → cast (lift w) = [⟨mk_tt, c⟩]))
  (merge_red  : ∀ w, merge ([⟨mk_tt, lift w⟩]) = lift w)
  (opS_red    : ∀ o (ws : list (lang.val D O)), 
                  (opS o (ws.map lift)) = (opC o ws).lift to_factory lift)

end reducer 

end sym