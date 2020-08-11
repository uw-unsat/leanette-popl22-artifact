import ..op.sym

open op.sym

def vars.to_str : list ℕ → string 
| [] := ""
| (x :: xs) := " " ++ to_string x ++ vars.to_str xs

def op.sym.typedop_int.to_str : typedop type.int → string 
| typedop.add := "add"
| typedop.mul := "mul"

def op.sym.typedop_bool.to_str : typedop type.bool → string 
| typedop.lt := "lt"
| typedop.eq := "eq"

def op.lang.op.to_str : op.lang.op → string 
| (op.lang.op.int_2 op.lang.op_int_2.add) := "+"
| (op.lang.op.int_2 op.lang.op_int_2.mul) := "*"
| (op.lang.op.int_2 op.lang.op_int_2.lt) := "<"
| (op.lang.op.int_2 op.lang.op_int_2.eq) := "="
| (op.lang.op.list_proj op.lang.op_list_proj.first) := "first"
| (op.lang.op.list_proj op.lang.op_list_proj.rest) := "rest"
| op.lang.op.list_null := "make-null"
| op.lang.op.list_cons := "link"
| op.lang.op.list_is_null := "null?"  


def op.lang.exp.to_str : op.lang.exp → string 
| (lang.exp.let0 x e_v e_b) :=
  "(let0 " ++ to_string x ++ " " ++ 
    op.lang.exp.to_str e_v ++ " " ++ op.lang.exp.to_str e_b ++ ")"
| (lang.exp.datum (op.lang.datum.int z)) := "(datum (op.lang.datum.int " ++ to_string z ++ "))"
| (lang.exp.datum op.lang.datum.undef) := "undef"
| (lang.exp.app o xs) := "(app " ++ o.to_str ++ vars.to_str xs ++ ")"
| (lang.exp.call x y) := "(call " ++ to_string x ++ " " ++ to_string y ++ ")"
| (lang.exp.var x) := "(var " ++ to_string x ++ ")"
| (lang.exp.if0 x e_t e_e) := 
  "(if0 " ++ to_string x ++ " " ++ 
             op.lang.exp.to_str e_t ++ " " ++ 
             op.lang.exp.to_str e_e ++ ")"
| (lang.exp.bool tt) := "#t"
| (lang.exp.bool ff) := "#f"
| (lang.exp.lam x e_b) := "(λ " ++ to_string x ++ " " ++ op.lang.exp.to_str e_b ++ ")"
| lang.exp.error := "(make-error)"
| lang.exp.abort := "(make-abort)"

mutual def op.sym.term_int.to_str, op.sym.term_bool.to_str
with op.sym.term_int.to_str : term type.int → string 
| (term.lit (lit.int z)) := to_string z
| (term.var (@var.mk type.int x)) := "(var " ++ to_string x ++ ")"
| (term.ite c t e) := 
  "(ite " ++ op.sym.term_bool.to_str c ++ " " ++ 
             op.sym.term_int.to_str t ++ " " ++ 
             op.sym.term_int.to_str e ++ ")"
| (term.expr o l r) := 
  "(expr " ++ op.sym.typedop_int.to_str o ++ " " ++ 
              op.sym.term_int.to_str l ++ " " ++ 
              op.sym.term_int.to_str r ++ ")"
with op.sym.term_bool.to_str : term type.bool → string 
| (term.lit (lit.bool tt)) := "#t"
| (term.lit (lit.bool ff)) := "#f"
| (term.var (@var.mk type.bool x)) := "(var " ++ to_string x ++ ")"
| (term.ite c t e) := 
  "(ite " ++ op.sym.term_bool.to_str c ++ " " ++ 
             op.sym.term_bool.to_str t ++ " " ++ 
             op.sym.term_bool.to_str e ++ ")"
| (term.expr o l r) := 
  "(expr " ++ op.sym.typedop_bool.to_str o ++ " " ++ 
              op.sym.term_int.to_str l ++ " " ++ 
              op.sym.term_int.to_str r ++ ")"

mutual def op.sym.val_atom.to_str, op.sym.val.to_str, op.sym.vals.to_str, op.sym.vals.to_str_aux, op.sym.choices'.to_str
with op.sym.val_atom.to_str : val_atom → string 
| (op.sym.val_atom.list vs) := op.sym.vals.to_str vs
| (@op.sym.val_atom.term type.int t) := "(term_int " ++ op.sym.term_int.to_str t ++ ")"
| (@op.sym.val_atom.term type.bool t) := "(term_bool " ++ op.sym.term_bool.to_str t ++ ")"
| (op.sym.val_atom.clos x e_b ε) := "(clos " ++ to_string x ++ " " ++ e_b.to_str ++ " " ++ op.sym.vals.to_str ε ++ ")"
with op.sym.val.to_str : val → string 
| (op.sym.val.atom a) := a.to_str
| (op.sym.val.union gvs) := "(union" ++ gvs.to_str ++ ")"
with op.sym.vals.to_str : list val → string 
-- we really need only one case, but the well-foundedness for mutual recursion 
-- is stupid, so let's unroll one more iteration
| [] := "(list)"
| (v :: vs) := "(list " ++ op.sym.val.to_str v ++ op.sym.vals.to_str_aux vs ++ ")"
with op.sym.vals.to_str_aux : list val → string 
| [] := ""
| (v :: vs) := " " ++ op.sym.val.to_str v ++ op.sym.vals.to_str_aux vs 
with op.sym.choices'.to_str : choices' val_atom → string 
| [] := ""
| (⟨g, va⟩ :: xs) := " (choice " ++ op.sym.term_bool.to_str g ++ " " ++ 
                                    op.sym.val_atom.to_str va ++ ")" ++ 
                     op.sym.choices'.to_str xs

def sym.state.to_str : sym.state (term type.bool) → string 
| ⟨assumes, asserts⟩ := "(state " ++ op.sym.term_bool.to_str assumes ++ " " ++
                                     op.sym.term_bool.to_str asserts ++ ")"

def result.to_str : option op.sym.result → string 
| none := "none"
| (some (sym.result.ans σ v)) := "(ans " ++ σ.to_str ++ " " ++ v.to_str ++ ")"
| (some (sym.result.halt σ)) := "(halt " ++ σ.to_str ++ ")" 
