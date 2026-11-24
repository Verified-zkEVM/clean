import Midnight.Field
import Midnight.Expression
import Midnight.BatchedLookup

namespace Midnight.Keygen

/-- Gate and lookup polynomials are Clean's own `Halo2.Expression` over the native field. -/
abbrev E := Halo2.Expression F Halo2.Query

/-- Native LogUp groups several input tuples against one table. The grouping is
retained for helper counts and exact key derivation; active-row membership is
connected to upstream Halo2 lookups in `Midnight.Configuration`. -/
abbrev BatchedLookup := Midnight.LookupBatch E

end Midnight.Keygen
