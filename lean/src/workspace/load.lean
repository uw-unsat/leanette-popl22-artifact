
import ..sym_factory.sym_factory
import ..generation.main
import ..generation.printer
import ..interp.sym.defs
import ..op.sym

open lang.exp
open op.sym

def input_exp : lang.exp op.lang.datum op.lang.op
  := (bool tt)

#eval result.to_str $
  (interp.interpS sym_factory.sym_factory 100
    input_exp
    [] initial_state) 
