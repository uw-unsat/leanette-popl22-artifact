import ..cs.lang

namespace op 

namespace lang

open lang

inductive datum : Type 
| int : ℤ → datum 
| undef : datum

inductive op_int_2 : Type 
| add : op_int_2
| mul : op_int_2
| lt : op_int_2
| eq : op_int_2

inductive op_list_proj : Type 
| first : op_list_proj
| rest : op_list_proj

inductive op : Type 
| int_2 (o : op_int_2) : op
| list_proj (o : op_list_proj) : op
| list_cons : op 
| list_null : op
| list_is_null : op

@[reducible] def val := @lang.val datum op
@[reducible] def result := @lang.result datum op
@[reducible] def exp := @lang.exp datum op

def undef := @lang.val.datum datum op datum.undef

open datum
open lang.op 
open lang.op_int_2
open lang.op_list_proj

def opC_int_2 (o : op_int_2) : list val → result
| [v_a, v_b] :=
  match v_a, v_b with 
  | val.datum d_a, val.datum d_b := 
    match d_a, d_b with 
    | int x, int y := 
      result.ans 
        (match o with 
        | add := val.datum $ datum.int (x + y)
        | mul := val.datum $ datum.int (x * y)
        | lt := val.bool (x < y)
        | eq := val.bool (x = y)
        end)
    | _, _ := err
    end
  | _, _ := err 
  end
| _ := err 

def opC_list_proj (o : op_list_proj) : list val → result 
| [v] := 
  match v with 
  | val.list (x :: xs) := 
    match o with 
    | first := result.ans $ x 
    | rest := result.ans $ val.list xs
    end
  | _ := err
  end
| _ := err


def opC : op → list val → result
| (int_2 o) vs := opC_int_2 o vs
| (list_proj o) vs := opC_list_proj o vs
| list_cons vs := 
  match vs with 
  | [x, y] := 
    match y with 
    | val.list xs := 
      match x with 
      -- dead code, needed for soundness
      | val.datum datum.undef := err 
      | x := result.ans $ val.list (x :: xs)
      end
    | _ := err
    end 
  | _ := err
  end
| list_null vs := 
  match vs with 
  | [] := result.ans $ val.list []
  | _ := err 
  end
| list_is_null vs := 
  -- We use Racket's semantics: (null? 1) should return false
  -- not an error
  match vs with 
  | [v] := 
    match v with 
    | val.datum datum.undef := err
    | val.list [] := result.ans $ val.bool $ tt
    | _ := result.ans $ val.bool $ ff 
    end
  | _ := err
  end

@[simp]
def val.is_list : val → bool 
| (val.list _) := tt 
| _ := ff

end lang

end op