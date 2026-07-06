/-
WASM binary emitter. Emits the AST to standard WASM binary format.
-/
import Clean.Backends.Wasm.Ast

namespace Backends.Wasm.Binary

open Ast (Module)

/-- Encode module to binary WASM bytes. Uses wat2wasm for production; this is a direct encoder. -/
-- TODO: fix LEB128 ℕ type inference, then implement full binary encoding
def Module.toBinary (_m : Module) : ByteArray := ByteArray.empty

end Backends.Wasm.Binary
