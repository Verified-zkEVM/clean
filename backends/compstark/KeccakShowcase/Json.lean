module

public import CompStark.Stark.Proof
public import CompStark.Stark.Challenge
public import CompStark.Mont32.BaseField

/-! # STARK proofs as Plonky3's JSON

A proof as Plonky3's `serde_json` writes it for KoalaBear: field elements as Montgomery words,
extension elements `{"value":[…],"_phantom":null}`, Merkle caps `{"cap":[…],"_marker":null}`, the
fields of every structure in Plonky3's order and no whitespace. Plonky3's verifier reads it, and
for a proof equal to Plonky3's the text is byte for byte Plonky3's (`CompStark.Stark.Json.parse`
reads it back).
-/

@[expose] public section

namespace KeccakShowcase.Json
open CompStark.Stark Montgomery.Native32

variable {p : ℕ} [Mont32Field p] {EF : Type} [CompStark.BaseField (FastField p)]
  [CompStark.Challenge (FastField p) EF]

/-- A list, comma separated in brackets. -/
def list {α : Type} (f : α → String) (xs : List α) : String :=
  "[" ++ ",".intercalate (xs.map f) ++ "]"

/-- A field element: its Montgomery word. -/
def field (x : FastField p) : String := toString x.1.toNat

def ext (x : EF) : String :=
  "{\"value\":" ++ list field (CompStark.Challenge.coeffs x) ++ ",\"_phantom\":null}"

def digest (d : Digest (FastField p)) : String := list field d.toList

def cap (c : Cap (FastField p)) : String :=
  "{\"cap\":" ++ list digest c.toList ++ ",\"_marker\":null}"

def siblings (s : Array (Digest (FastField p))) : String :=
  "{\"sibling_hashes\":" ++ list digest s.toList ++ "}"

def optional {α : Type} (f : α → String) : Option α → String
  | none => "null"
  | some x => f x

def exts (xs : Array EF) : String := list ext xs.toList

def multiOpening (m : MultiOpening (FastField p)) : String :=
  "{\"opened_values\":" ++ list (fun q => list (fun row => list field row.toList) q.toList)
    m.values.toList ++ ",\"opening_proof\":" ++ siblings m.siblings ++ "}"

def commitOpening (c : CommitOpening (FastField p) EF) : String :=
  "{\"sibling_values\":" ++ list exts c.siblings.toList ++ ",\"opening_proof\":" ++
    siblings c.path ++ "}"

def friProof (f : FriProof (FastField p) EF) : String :=
  "{\"batch_pow_witness\":" ++ field f.batchWitness ++
  ",\"commit_phase_commits\":" ++ list cap f.commits.toList ++
  ",\"commit_pow_witnesses\":" ++ list field f.commitWitnesses.toList ++
  ",\"input_openings\":" ++ list multiOpening f.inputs.toList ++
  ",\"commit_phase_openings\":" ++ list commitOpening f.folds.toList ++
  ",\"final_poly\":" ++ exts f.finalPoly ++
  ",\"query_pow_witness\":" ++ field f.queryWitness ++ "}"

def openedValues (o : OpenedValues EF) : String :=
  "{\"trace_local\":" ++ exts o.traceLocal ++
  ",\"trace_next\":" ++ optional exts o.traceNext ++
  ",\"preprocessed_local\":" ++ optional exts o.preprocessedLocal ++
  ",\"preprocessed_next\":" ++ optional exts o.preprocessedNext ++
  ",\"quotient_chunks\":" ++ list exts o.quotientChunks.toList ++ ",\"random\":null}"

/-- A proof as Plonky3's JSON. -/
def proof (pf : Proof (FastField p) EF) : String :=
  "{\"commitments\":{\"trace\":" ++ cap pf.traceCommit ++ ",\"quotient_chunks\":" ++
    cap pf.quotientCommit ++ ",\"random\":null},\"opened_values\":" ++ openedValues pf.opened ++
    ",\"opening_proof\":" ++ friProof pf.fri ++ ",\"degree_bits\":" ++ toString pf.degreeBits ++
    ",\"ood_pow_witness\":" ++ field pf.oodWitness ++ "}"

end KeccakShowcase.Json
