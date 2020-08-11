namespace lang

/-  
Syntax and semantics for Core Scheme, extended with 
error and abort. We adopt a more permissive version of 
A-normal form for the syntax, in order to simplify the 
semantics. With this syntax, we need only two halt rules 
for the core expressions: one for calling a procedure, and 
one for evaluating a let binding. The syntax and semantics 
are both parameterized by the type D of primitive data types 
other than bool, and the type O of primitive operators. The 
semantics is additionally parameterized by the function op 
for evaluating primitive operations, which are allowed to 
abort and error. 

Flanagan, Sabry, Duba, Felleisen.
"The Essence of Compiling with Continuations", PLDI'93. 

https://users.soe.ucsc.edu/~cormac/papers/pldi93.pdf
-/

section syntax

inductive exp  (D O : Type) 
| bool  : bool → exp 
| datum : D → exp 
| lam   : ℕ → exp → exp 
| var   : ℕ → exp
| app   : O → list ℕ → exp 
| call  : ℕ → ℕ → exp
| let0  : ℕ → exp → exp → exp 
| if0   : ℕ → exp → exp → exp
| error : exp 
| abort : exp

end syntax

section semantics 

inductive val (D O : Type)  : Type 
| bool   : bool → val
| datum  : D → val 
| list   : (list val) → val
| clos   : ℕ → exp D O → (list val) → val

@[simp] def val.is_clos {D O : Type} : val D O → bool 
| (val.clos _ _ _) := tt 
| _ := ff

def env (D O : Type) := list (val D O)

inductive result (D O : Type) : Type 
| ans  : val D O → result 
| halt : bool → result 

open result 

@[simp] def abt {D O : Type} : result D O := (halt tt)
@[simp] def err {D O : Type} : result D O := (halt ff)

inductive evalC {D O : Type} (op : O → list (val D O) → result D O) : 
exp D O → env D O → result D O → Prop
| bool {e b}  : evalC (exp.bool b)  e (ans (val.bool b))
| datum {e d} : evalC (exp.datum d) e (ans (val.datum d))
| lam {e y x} : evalC (exp.lam y x) e (ans (val.clos y x e))
| var {e y}    
    (hy : y < list.length e) : 
    evalC (exp.var y) e (ans (e.nth_le y hy))
| app {e o} {xs : list ℕ} {vs : list (val D O)} 
    (h1 : xs.length = vs.length)
    (h2 : ∀ (i : ℕ) (hx : i < xs.length) (hv : i < vs.length), 
          evalC (exp.var (xs.nth_le i hx)) e (ans (vs.nth_le i hv))) :
    evalC (exp.app o xs) e (op o vs)
| call {e x1 x2 py px pe v r}
    (h1 : evalC (exp.var x1) e (ans (val.clos py px pe)))
    (h2 : evalC (exp.var x2) e (ans v))
    (h3 : evalC px (pe.update_nth py v) r) : 
    evalC (exp.call x1 x2) e r
| call_halt {e x1 x2 v1 v2}
    (h1 : evalC (exp.var x1) e (ans v1))
    (h2 : evalC (exp.var x2) e (ans v2))
    (h3 : ¬ (val.is_clos v1)) : 
    evalC (exp.call x1 x2) e err
| let0 {e y x1 x2 v r}
    (h1 : evalC x1 e (ans v))
    (h2 : evalC x2 (e.update_nth y v) r) : 
    evalC (exp.let0 y x1 x2) e r
| let0_halt {e y x1 x2 b}
    (h1 : evalC x1 e (halt b)) : 
    evalC (exp.let0 y x1 x2) e (halt b)
| if0_true {e xc xt xf v r}
    (hc : evalC (exp.var xc) e (ans v))
    (hv : v ≠ (val.bool ff))
    (hr : evalC xt e r) :
    evalC (exp.if0 xc xt xf) e r
| if0_false {e xc xt xf v r}
    (hc : evalC (exp.var xc) e (ans v))
    (hv : v = (val.bool ff))
    (hr : evalC xf e r) :
    evalC (exp.if0 xc xt xf) e r
| error {e} : evalC (exp.error) e err 
| abort {e} : evalC (exp.abort) e abt

end semantics

end lang