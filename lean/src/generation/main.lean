import ..sym_factory.sym_factory

def initial_state : sym.state (op.sym.term op.sym.type.bool) := 
  ⟨sym_factory.sym_factory.mk_tt, sym_factory.sym_factory.mk_tt⟩
