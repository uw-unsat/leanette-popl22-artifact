import .sym
import data.subtype

namespace op.sym 

run_cmd mk_simp_attr `term_is_true

attribute [term_is_true] 
  term.is_true term.eval lit.to_bool

end op.sym
