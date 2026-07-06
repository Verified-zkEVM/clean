/-
Minimal WASM binary emitter. Placeholder — text emitter is the primary output path.
Binary emission will be completed when the AST refactor is done.
-/
import Clean.Backends.Wasm.Ast

namespace Backends.Wasm.Binary

open Ast (Module)

/-- Placeholder: use wat2wasm for binary conversion. -/
def Module.toBinary (_m : Module) : List UInt8 := []

end Backends.Wasm.Binary
