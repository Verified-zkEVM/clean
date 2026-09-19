/-
Signatures: named collections of interfaces (the "trait" level).

An `Interface` is one method: a single input/output contract. A `Sig` is a family of methods
indexed by a type of names; `Sig.Impl B S` is an implementation of every method on `B`.
A gadget generic over "some arithmetic" takes a `Sig.Impl B Arith.sig`; a backend provides one;
lowering passes are functions between `Sig.Impl`s.
-/
module

public import Clean2.Core.Formal

@[expose] public section

namespace Clean2
universe u
variable {F : Type}

/-- A single method: an interface together with its input/output shapes. -/
structure Method (F : Type) where
  Input : TypeMap
  Output : TypeMap
  [instInput : ProvableType Input]
  [instOutput : ProvableType Output]
  iface : Interface F Input Output

attribute [instance] Method.instInput Method.instOutput

@[reducible]
def Interface.toMethod {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (iface : Interface F Input Output) : Method F :=
  ⟨Input, Output, iface⟩

@[circuit_norm] theorem Interface.toMethod_iface {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (iface : Interface F Input Output) : iface.toMethod.iface = iface := rfl

/-- A signature: methods indexed by names. -/
structure Sig (F : Type) where
  Name : Type u
  method : Name → Method F

/-- An implementation of every method of a signature. -/
def Sig.Impl (B : Backend) (S : Sig.{u} B.Native) : Type u :=
  ∀ m : S.Name, Clean2.Impl B (S.method m).iface

namespace Sig

/-- The one-method signature. -/
def single {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (iface : Interface F Input Output) : Sig.{u} F :=
  ⟨PUnit, fun _ => iface.toMethod⟩

/-- Both sets of methods. -/
def union (S T : Sig.{u} F) : Sig.{u} F :=
  ⟨S.Name ⊕ T.Name, Sum.elim S.method T.method⟩

/-- A sub-signature: the methods reachable through a renaming. -/
def restrict (S : Sig.{u} F) {N : Type u} (f : N → S.Name) : Sig.{u} F :=
  ⟨N, S.method ∘ f⟩

namespace Impl
variable {B : Backend}

def single {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {iface : Interface B.Native Input Output} (impl : Clean2.Impl B iface) : (Sig.single iface).Impl B :=
  fun _ => impl

def union {S T : Sig.{u} B.Native} (x : S.Impl B) (y : T.Impl B) : (S.union T).Impl B
  | Sum.inl m => x m
  | Sum.inr m => y m

def restrict {S : Sig.{u} B.Native} (x : S.Impl B) {N : Type u} (f : N → S.Name) : (S.restrict f).Impl B :=
  fun m => x (f m)

end Impl
end Sig

/-! ## Refinement: an implementation of a stronger interface implements a weaker one -/

/-- `i.Refines j`: `i` assumes less and promises more than `j`. -/
structure Interface.Refines {Input Output : TypeMap} (i j : Interface F Input Output) : Prop where
  assumptions : ∀ x, j.Assumptions x → i.Assumptions x
  spec : ∀ x y, j.Assumptions x → i.Spec x y → j.Spec x y
  proverAssumptions : ∀ x, j.ProverAssumptions x → i.ProverAssumptions x
  proverSpec : ∀ x y, j.ProverAssumptions x → i.ProverSpec x y → j.ProverSpec x y

def Impl.refine {B : Backend} {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {i j : Interface B.Native Input Output} (h : i.Refines j) (impl : Impl B i) : Impl B j where
  main := impl.main
  advance := impl.advance
  output := impl.output
  advance_eq := impl.advance_eq
  output_eq := impl.output_eq
  consistent := impl.consistent
  spatial := impl.spatial
  soundness s env input h_assumptions h_holds :=
    h.spec _ _ h_assumptions (impl.soundness s env input (h.assumptions _ h_assumptions) h_holds)
  completeness s env input h_honest h_prover :=
    let r := impl.completeness s env input h_honest (h.proverAssumptions _ h_prover)
    ⟨r.1, h.proverSpec _ _ h_prover r.2⟩

end Clean2
