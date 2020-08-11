import .lang 
import .sym

namespace sym

open lang 
open sym.result

section svm 

  variables 
    {Model SymB SymV D O : Type}
    [inhabited Model] [inhabited SymV]
    (f : factory Model SymB SymV D O)

  def factory.assume (σ : state SymB) (g : SymB) : state SymB := 
  ⟨f.and σ.assumes (f.imp σ.asserts g), σ.asserts⟩

  def factory.assert (σ : state SymB) (g : SymB) : state SymB := 
  ⟨σ.assumes, f.and σ.asserts (f.imp σ.assumes g)⟩

  def factory.compose (σ σ' : state SymB) : state SymB := 
  ⟨f.and σ.assumes (f.imp σ.asserts σ'.assumes), f.and σ.asserts (f.imp σ.assumes σ'.asserts)⟩ 

  def factory.halted (σ : state SymB) : bool := -- Returns true iff σ.assumes or σ.asserts  
  f.is_ff σ.assumes || f.is_ff σ.asserts        -- is reduced to the literal ff.

  def factory.halt_or_ans (σ : state SymB) (v : SymV) := 
  if (f.halted σ) then halt σ else ans σ v

  def factory.strengthen (σ : state SymB) : result SymB SymV → result SymB SymV 
  | (halt σ')  := halt (f.compose σ σ')
  | (ans σ' v) := f.halt_or_ans (f.compose σ σ') v

  def factory.merge_φ (σ : state SymB) (grs : choices SymB (result SymB SymV)) (field : state SymB → SymB) : SymB := 
  f.and 
    (field σ) 
    (f.all (λ (gr : choice SymB (result SymB SymV)), f.imp gr.guard (field gr.value.state)) grs)

  def factory.merge_σ (σ : state SymB) (grs : choices SymB (result SymB SymV)) : state SymB :=
  ⟨f.merge_φ σ grs state.assumes, f.merge_φ σ grs state.asserts⟩ 

  def factory.merge_υ (grs : choices SymB (result SymB SymV)) : SymV := 
  f.merge (grs.map (λ gr, ⟨gr.guard, gr.value.value (default SymV)⟩)) 

  def factory.merge_ρ (σ : state SymB) (grs : choices SymB (result SymB SymV)) : result SymB SymV := 
  if grs.all (λ gr, gr.value.is_halt) 
  then halt (f.merge_σ σ grs)
  else f.halt_or_ans (f.merge_σ σ grs) (f.merge_υ grs) 

  inductive evalS : exp D O → env SymV → state SymB → result SymB SymV → Prop
  | bool {ε σ b}  : evalS (exp.bool b)  ε σ (ans σ (f.bval b))
  | datum {ε σ d} : evalS (exp.datum d) ε σ (ans σ (f.dval d))
  | lam {ε σ y x} : evalS (exp.lam y x) ε σ (ans σ (f.cval (clos.mk y x ε)))
  | var {ε σ y}    
    (hy : y < list.length ε) : 
    evalS (exp.var y) ε σ (ans σ (ε.nth_le y hy))
  | app {ε σ o} {xs : list ℕ} {vs : list SymV} 
    (h1 : xs.length = vs.length)
    (h2 : ∀ (i : ℕ) (hx : i < xs.length) (hv : i < vs.length), 
      evalS (exp.var (xs.nth_le i hx)) ε σ (ans σ (vs.nth_le i hv))) :
    evalS (exp.app o xs) ε σ (f.strengthen σ (f.opS o vs))
  | call_sym {ε σ σ' x1 x2 c v} {grs : choices SymB (result SymB SymV)}
    (h1 : evalS (exp.var x1) ε σ (ans σ c))
    (h2 : evalS (exp.var x2) ε σ (ans σ v))
    (h3 : σ' = f.assert σ (f.some choice.guard (f.cast c)))
    (h4 : ¬ f.is_ff (f.some choice.guard (f.cast c)) ∧ ¬ f.halted σ')
    (h5 : (f.cast c).map choice.guard = grs.map choice.guard)
    (h6 : ∀ (i : ℕ) (hc : i < (f.cast c).length) (hr : i < grs.length),
          let gi := ((f.cast c).nth_le i hc).guard in
          let ci := ((f.cast c).nth_le i hc).value in
          let ri := (grs.nth_le i hr).value in 
            evalS ci.exp (ci.env.update_nth ci.var v) (f.assume σ' gi) ri) : 
    evalS (exp.call x1 x2) ε σ (f.merge_ρ σ' grs)
  | call_halt {ε σ σ' x1 x2 c v}
    (h1 : evalS (exp.var x1) ε σ (ans σ c))
    (h2 : evalS (exp.var x2) ε σ (ans σ v))
    (h3 : σ' = f.assert σ (f.some choice.guard (f.cast c)))
    (h4 : f.is_ff (f.some choice.guard (f.cast c)) ∨ f.halted σ') : 
    evalS (exp.call x1 x2) ε σ (halt σ') 
  | let0 {ε σ σ' y x1 x2 v r}
    (h1 : evalS x1 ε σ (ans σ' v))
    (h2 : evalS x2 (ε.update_nth y v) σ' r) : 
    evalS (exp.let0 y x1 x2) ε σ r 
  | let0_halt {ε σ σ' y x1 x2}
    (h1 : evalS x1 ε σ (halt σ')) : 
    evalS (exp.let0 y x1 x2) ε σ (halt σ')
  | if0_true {ε σ xc xt xf v r}
    (hc : evalS (exp.var xc) ε σ (ans σ v))
    (hv : f.is_tt (f.truth v))
    (hr : evalS xt ε σ r):
    evalS (exp.if0 xc xt xf) ε σ r
  | if0_false {ε σ xc xt xf v r}
    (hc : evalS (exp.var xc) ε σ (ans σ v))
    (hv : f.is_ff (f.truth v))
    (hr : evalS xf ε σ r):
    evalS (exp.if0 xc xt xf) ε σ r
  | if0_sym {ε σ xc xt xf v rt rf}
    (hc : evalS (exp.var xc) ε σ (ans σ v))
    (hv : ¬ f.is_tt (f.truth v) ∧ ¬ f.is_ff (f.truth v))
    (ht : evalS xt ε (f.assume σ (f.truth v)) rt)
    (hf : evalS xf ε (f.assume σ (f.not (f.truth v))) rf) :
    evalS (exp.if0 xc xt xf) ε σ (f.merge_ρ σ [⟨f.truth v, rt⟩, ⟨f.not (f.truth v), rf⟩])
  | error {ε σ} : evalS (exp.error) ε σ (halt (f.assert σ f.mk_ff))
  | abort {ε σ} : evalS (exp.abort) ε σ (halt (f.assume σ f.mk_ff))
  
end svm

end sym