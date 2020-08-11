import .sym_factory
import tactic.find_unused

@[main_declaration]
def dummy := sym_factory.sym_factory

#list_unused_decls ["src/sym_factory/sym_factory.lean", "src/sym_factory/basic.lean", "src/sym_factory/opS.lean", "src/op/basic.lean", "src/basic/sym.lean"]
