import ...cs.lang

namespace interp

open lang
open lang.result
open lang.exp
open lang.val

section interp 

variables 
  {D O : Type}
  (op : O → list (val D O) → lang.result D O)

-- The concrete interpreter:
-- `interpC` consumes a `fuel`, an program `e`, a concrete environment `ε`, and 
-- returns either
-- - `none` if the interpretation runs out of `fuel` or references 
--   a variable out of scope.
-- - `some` concrete result `r`
def interpC : ℕ → exp D O → env D O → option (lang.result D O)
| 0 _ _ := none
| (fuel+1) e ε :=
  match e with
  | bool b := some (ans (bool b))
  | datum d := some (ans (datum d))
  | lam x e_b := some (ans (clos x e_b ε))
  | var x := 
    match ε.nth x with 
    | none := none 
    | some v := some (ans v)
    end
  | app o as := 
    match list.mmap (λ a, ε.nth a) as with 
    | none := none
    | some vs := some $ op o vs
    end
  | call a_f a_a := 
    match ε.nth a_f with 
    | none := none 
    | some v_f := 
      match ε.nth a_a with 
      | none := none 
      | some v_a := 
        match v_f with
        | clos x e_b ε_static :=
          interpC fuel e_b (ε_static.update_nth x v_a)
        | _ := some err
        end
      end
    end
  | let0 x e_v e_b := 
    match interpC fuel e_v ε with 
    | none := none 
    | some (halt b) := some (halt b)
    | some (ans v_v) := interpC fuel e_b (ε.update_nth x v_v)
    end
  | if0 a_c e_t e_e := 
    match ε.nth a_c with 
    | none := none 
    | some (bool ff) := interpC fuel e_e ε
    | some _ := interpC fuel e_t ε
    end
  | error := some err
  | abort := some abt
  end

  end interp

  end interp 