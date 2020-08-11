import ..cs.lang
import ..cs.sym
import ..op.sym
import ..op.lang
import ..tactic.all

namespace sym_factory

open sym
open op.sym

def mk_tt : term type.bool := term.lit $ lit.bool tt
def mk_ff : term type.bool := term.lit $ lit.bool ff

def is_tt : term type.bool → bool
| (term.lit (lit.bool tt)) := tt 
| _ := ff

def is_ff : term type.bool → bool
| (term.lit (lit.bool ff)) := tt 
| _ := ff

def pe_not : term type.bool → term type.bool
| (term.lit (lit.bool b)) := (term.lit (lit.bool (bnot b)))
| t := term.ite t mk_ff mk_tt

def pe_and : term type.bool → term type.bool → term type.bool
| (term.lit (lit.bool tt)) t_b := t_b
| (term.lit (lit.bool ff)) t_b := mk_ff
| t_a (term.lit (lit.bool tt)) := t_a
| t_a (term.lit (lit.bool ff)) := mk_ff
| t_a t_b := 
  if t_a = t_b then 
    t_a 
  else
    term.ite t_a t_b mk_ff

def pe_or : term type.bool → term type.bool → term type.bool
| (term.lit (lit.bool tt)) t_b := mk_tt
| (term.lit (lit.bool ff)) t_b := t_b
| t_a (term.lit (lit.bool tt)) := mk_tt
| t_a (term.lit (lit.bool ff)) := t_a
| t_a t_b := 
  if t_a = t_b then 
    t_a 
  else 
    term.ite t_a mk_tt t_b

def pe_imp (t_a : term type.bool) (t_b : term type.bool) : term type.bool :=
  pe_or (pe_not t_a) t_b

mutual def truth, truth.atom
with truth : val → term type.bool
| (val.atom va) := truth.atom va
| (val.union []) := term.lit $ lit.bool tt
| (val.union (⟨term.lit (lit.bool tt), va⟩ :: vs)) := truth.atom va
| (val.union (⟨term.lit (lit.bool ff), _⟩ :: vs)) := truth (val.union vs)
| (val.union (⟨g, va⟩ :: vs)) := term.ite g (truth.atom va) (truth (val.union vs))
with truth.atom : val_atom → term type.bool
| (@val_atom.term type.bool t) := t
| _ := term.lit $ lit.bool tt

def bval (b : bool) : val := (val.atom (val_atom.term (term.lit (lit.bool b))))

def dval : op.lang.datum → val
| (op.lang.datum.int i) := val.atom (val_atom.term (term.lit (lit.int i)))
| op.lang.datum.undef := val.union []

def cval : op.sym.clos → val
| ⟨x, e, ε⟩ := val.atom (val_atom.clos x e ε)

def adjust_core {τ : Type} : term type.bool → choices' τ → choices' τ
| t_acc [] := []
| t_acc (⟨g, va⟩ :: gvs) := ⟨pe_and g t_acc, va⟩ :: adjust_core (pe_and (pe_not g) t_acc) gvs

def adjust {τ : Type} : choices' τ → choices' τ := adjust_core mk_tt

def cast_choices : choices' val_atom → choices' clos
| [] := []
| (⟨g, val_atom.clos x e ε⟩ :: gvs) := ⟨g, ⟨x, e, ε⟩⟩ :: cast_choices gvs
| (⟨g, _⟩ :: gvs) := cast_choices gvs

def cast : val → choices' clos
| (val.atom (val_atom.clos x e ε)) := [⟨mk_tt, ⟨x, e, ε⟩⟩]
| (val.atom _) := []
| (val.union gvs) := cast_choices (adjust gvs)

def make_and (g : term type.bool) : choice (term type.bool) val_atom → choice (term type.bool) val_atom
| ⟨g', v'⟩ := ⟨pe_and g g', v'⟩

def merge.core : choices' val → choices' val_atom
| [] := []
| (⟨g, val.union gvs_sub⟩ :: gvs) := (adjust gvs_sub).map (make_and g) ++ merge.core gvs
| (⟨g, val.atom va⟩ :: gvs) := ⟨g, va⟩ :: merge.core gvs

def merge (gvs : choices' val) := 
  match merge.core gvs with 
  | [⟨g, v⟩] := 
    if is_tt g then 
      val.atom v 
    else 
      val.union [⟨g, v⟩]
  | grs := val.union grs
  end    

def infeasible_choice : choice (term type.bool) val_atom := ⟨mk_ff, val_atom.term mk_ff⟩

def opS.int {τ : type} 
  (fC : ℤ → ℤ → op.sym.lit τ) 
  (fS : term type.int → term type.int → term τ) :
  term type.int → term type.int → val_atom 
| (term.lit (lit.int i_a)) (term.lit (lit.int i_b)) := 
  val_atom.term (term.lit (fC i_a i_b))
| t_a t_b := val_atom.term (fS t_a t_b)

def opS.int_wrap : op.lang.op_int_2 → term type.int → term type.int → val_atom
| op.lang.op_int_2.add t_a t_b := opS.int (λ a b, lit.int $ a + b) (term.expr typedop.add) t_a t_b
| op.lang.op_int_2.mul t_a t_b := opS.int (λ a b, lit.int $ a * b) (term.expr typedop.mul) t_a t_b
| op.lang.op_int_2.lt t_a t_b := opS.int (λ a b, lit.bool $ a < b) (term.expr typedop.lt) t_a t_b
| op.lang.op_int_2.eq t_a t_b := opS.int (λ a b, lit.bool $ a = b) (term.expr typedop.eq) t_a t_b


def opS.core : op.lang.op → list val_atom → option val
| (op.lang.op.int_2 o) vas :=   
  match vas with
  | [va_a, va_b] := 
    match va_a, va_b with 
    | @val_atom.term type.int t_a, @val_atom.term type.int t_b := 
      some $ val.atom (opS.int_wrap o t_a t_b)
    | _, _ := none 
    end
  | _ := none
  end
| (op.lang.op.list_proj o) vas := 
  match vas with 
  | [va] :=
    match va with 
    | val_atom.list (v :: vs) := 
      match o with 
      | op.lang.op_list_proj.first := some v 
      | op.lang.op_list_proj.rest := some $ val.atom $ val_atom.list vs
      end 
    | _ := none
    end
  | _ := none
  end
| op.lang.op.list_cons vas := 
  match vas with 
  | [va_x, va_y] :=
    match va_y with 
    | val_atom.list vs := some $ val.atom $ val_atom.list (val.atom va_x :: vs)
    | _ := none
    end
  | _ := none
  end
| op.lang.op.list_null vas :=
  match vas with 
  | [] := some $ val.atom $ val_atom.list []
  | _ := none
  end
| op.lang.op.list_is_null vas := 
  match vas with 
  | [va] := 
    some $ val.atom $ val_atom.term $ term.lit $ lit.bool $
      match va with 
      | val_atom.list [] := tt
      | _ := ff
      end
  | _ := none
  end

def make_disjunction {τ : Type} : choices (term type.bool) τ → term type.bool
| [] := mk_ff
| (⟨g, _⟩ :: gvs) := pe_or g (make_disjunction gvs)

def measure : psum (list val) (list val) → ℕ
| (psum.inl vs) := 2 * vs.length
| (psum.inr vs) := (2 * vs.length) + 1

lemma measure_decreases {n : ℕ} : 2 * n + 1 < 2 * (n + 1) := by linarith

mutual def opS.split, opS.split_map (o : op.lang.op) 
with opS.split : list val → term type.bool → list val_atom → choice (term type.bool) val
| [] := λ g_acc vas, 
  match opS.core o (list.reverse vas) with 
  | none := ⟨mk_ff, val.union []⟩
  | some v := ⟨g_acc, v⟩
  end
| ((val.union gvs) :: vs) := 
  λ g_acc vas, 
    have measure (psum.inr vs) < measure (psum.inl ((val.union gvs) :: vs)) := by {
      simp only [measure],
      apply measure_decreases,
    },
    let gvs' := opS.split_map vs gvs g_acc vas in
      ⟨make_disjunction gvs', merge gvs'⟩
| ((val.atom va) :: vs) := 
  λ g_acc vas ,
    have measure (psum.inl vs) < measure (psum.inl ((val.atom va) :: vs)) := by simp [measure],
    opS.split vs g_acc (va :: vas) 
    
with opS.split_map : list val → choices' val_atom → term type.bool → list val_atom → choices' val
| vs := 
  λ gvs g_acc vas, 
    have measure (psum.inl vs) < measure (psum.inr vs) := by simp [measure],
    (adjust gvs).map (λ ⟨g, va⟩, opS.split vs (pe_and g_acc g) (va :: vas))
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf measure⟩]}

def opS (o : op.lang.op) (xs : list val) : op.sym.result :=
  match opS.split o xs mk_tt [] with ⟨g, v⟩ := 
    if is_ff g then 
      result.halt ⟨mk_tt, mk_ff⟩
    else 
      result.ans ⟨mk_tt, g⟩ v
  end

mutual def lift, lifts
with lift : op.lang.val → val
| (lang.val.datum (op.lang.datum.int x)) := 
  val.atom (val_atom.term (term.lit (lit.int x)))
| (lang.val.datum op.lang.datum.undef) := 
  val.union []
| (lang.val.list xs) := 
  val.atom (val_atom.list (lifts xs))
| (lang.val.bool v) := 
  val.atom (val_atom.term (term.lit (lit.bool v)))
| (lang.val.clos x e ε) := 
  val.atom (val_atom.clos x e (lifts ε))
with lifts : list op.lang.val → list val 
| [] := []
| (x :: xs) := lift x :: lifts xs

def lift.atom : op.lang.val → val_atom
| (lang.val.datum (op.lang.datum.int x)) := 
  val_atom.term (term.lit (lit.int x))
| (lang.val.datum op.lang.datum.undef) := 
  val_atom.list [] -- deadcode
| (lang.val.list xs) := 
  val_atom.list (lifts xs)
| (lang.val.bool v) := 
  val_atom.term (term.lit (lit.bool v))
| (lang.val.clos x e ε) := 
  val_atom.clos x e (lifts ε)


end sym_factory
