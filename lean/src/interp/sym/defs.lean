import ...cs.sym
import ...cs.svm

namespace interp

open sym
open lang.exp
open sym.result

section interp 

variables 
  {Model SymB SymV D O : Type}
  [inhabited Model] [inhabited SymV]
  (f : sym.factory Model SymB SymV D O)

-- The symbolic interpreter:
-- `interpS` consumes a `fuel`, an program `e`, a symbolic environment `ε`, and 
-- returns either
-- - `none` if the interpretation runs out of `fuel` or references 
--   a variable out of scope.
-- - `some` symbolic result `r`
def interpS : ℕ → lang.exp D O → env SymV → sym.state SymB → option (sym.result SymB SymV)
| 0 _ _ _ := none
| (fuel+1) e ε σ :=
  match e with
  | bool b := some (ans σ (f.bval b))
  | datum d := some (ans σ (f.dval d))
  | lam x e_b := some (ans σ (f.cval (clos.mk x e_b ε)))
  | var x := 
    match ε.nth x with 
    | none := none 
    | some v := some (ans σ v)
    end
  | app o as := 
    match list.mmap (λ a, ε.nth a) as with 
    | none := none
    | some vs := some $ (f.strengthen σ (f.opS o vs))
    end
  | call a_f a_a := 
    match ε.nth a_f with 
    | none := none 
    | some v_f := 
      match ε.nth a_a with 
      | none := none 
      | some v_a := 
        let casted      := f.cast v_f,
            disjunction := f.some choice.guard casted,
            σ'          := f.assert σ disjunction in
          if f.is_ff disjunction || f.halted σ' then 
            some $ halt σ'
          else
            let agg : option (choices SymB (sym.result SymB SymV)) := 
              casted.mmap 
                (λ (gv),
                  match gv with ⟨g, ⟨x, e_b, ε_static⟩⟩ :=  
                    match interpS fuel e_b (ε_static.update_nth x v_a) (f.assume σ' g) with 
                    | none := none 
                    | some v := some ⟨g, v⟩
                    end                   
                  end) in 
              match agg with 
              | none := none 
              | some grs := some (f.merge_ρ σ' grs)
              end 
      end
    end
  | let0 x e_v e_b := 
    match interpS fuel e_v ε σ with 
    | none := none 
    | some (halt σ') := some (halt σ')
    | some (ans σ' v_v) := interpS fuel e_b (ε.update_nth x v_v) σ'
    end
  | if0 a_c e_t e_e := 
    match ε.nth a_c with 
    | none := none 
    | some v := 
      let truth := f.truth v in 
        if f.is_tt truth then 
          interpS fuel e_t ε σ
        else if f.is_ff truth then 
          interpS fuel e_e ε σ
        else 
          match interpS fuel e_t ε (f.assume σ truth) with 
          | none := none 
          | some rt := 
            match interpS fuel e_e ε (f.assume σ (f.not truth)) with 
            | none := none 
            | some rf := f.merge_ρ σ [⟨f.truth v, rt⟩, ⟨f.not truth, rf⟩]
            end
          end          
    end
  | error := some (halt (f.assert σ f.mk_ff))
  | abort := some (halt (f.assume σ f.mk_ff))
  end

  end interp

  end interp 