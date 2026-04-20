# soundChannels_addTable with Full Channel Equality

This note captures a possible refactor path for proving `soundChannels_addTable` without relying on name-based filtering (`RawChannel.filter`) in theorem statements and proof steps.

## Problem

Current proof attempts mix two channel identity notions:

- Interaction extraction via `RawChannel.filter` is keyed by channel name (and arity checks in casts).
- Property-level statements (`FullChannelGuarantees`, `FullChannelRequirements`) use full channel equality (`i.channel = channel`).

This mismatch can block equivalence/bridge lemmas conceptually, not just tactically.

## Goal

For the `soundChannels_addTable` theorem family, use only full channel identity (`i.channel = channel`) in interaction extraction and in assumptions/conclusions.

Constraint: do not rewrite core definitions such as `localAdds`.

## Proposed Eq-Based Layer (new defs)

Add theorem-local (or example-local) interaction extractors that do **not** use `RawChannel.filter`:

```lean
noncomputable def FlatOperation.interactionsEq
  (channel : RawChannel F) (env : Environment F) :
  List (FlatOperation F) -> List (F × Vector F channel.arity)
```

```lean
noncomputable def Operations.interactionsEq
  (channel : RawChannel F) (env : Environment F) :
  Operations F -> List (F × Vector F channel.arity)
```

Shape:

- `witness/assert/lookup`: recurse.
- `interact i`:
  - if `h : i.channel = channel`, emit
    `(i.mult.eval env, (i.msg.map env).cast (by simpa using congrArg RawChannel.arity h))`.
  - else recurse.
- `subcircuit s` (for `Operations.interactionsEq`):
  `FlatOperation.interactionsEq channel env s.ops.toFlat ++ ...`.

Then add wrappers:

```lean
noncomputable def TableWitness.interactionsEq ...
noncomputable def Ensemble.verifierInteractionsEq ...
noncomputable def Ensemble.interactionsEq ...
```

## Replace Partial-Balance Formulation

Current formulation uses a global `extraInteractions` plus `channel.filter extraInteractions`.

For eq-based semantics, use per-channel extras directly:

```lean
def Ensemble.PartialBalancedChannelsEq ... : Prop :=
  ∃ extra : (channel : RawChannel F) → List (F × Vector F channel.arity),
    (∀ channel ∈ ens.channels,
      BalancedInteractions (ens.interactionsEq publicInput witness channel ++ extra channel)) ∧
    (∀ channel ∈ finished,
      (extra channel).Forall (fun (m,msg) => channel.Requirements m msg witness.data))
```

This avoids cross-channel name filtering entirely.

## Eq-Based SoundChannels Statement

Define:

```lean
def Ensemble.SoundChannelsEq ... : Prop := ...
```

mirroring existing `SoundChannels`, but using:

- `interactionsEq`,
- `PartialBalancedChannelsEq`,
- eq-based per-channel interaction obligations.

Then target theorem:

```lean
theorem soundChannels_addTable_eq ... :
  (ens.addTable table).SoundChannelsEq h_finished
```

## Useful Bridge Lemmas (expected)

These should be straightforward in the eq-based layer because both sides use full equality:

- `Operations.interactionsEq_requirements`:
  `ops.FullChannelRequirements channel env ->
   (ops.interactionsEq channel env).Forall (...)`
- `Operations.interactionsEq_guarantees`:
  `(ops.interactionsEq channel env).Forall (...) ->
   ops.FullChannelGuarantees channel env`
- row/table/ensemble lifted versions.

## Remaining Independent Issue

Even with eq-based filtering, one blocker remains in current `old_requirements` flow:

- verifier requirements are naturally about `emptyEnvironment.data`,
- while theorem goals ask requirements at `witness.data`.

This needs a separate bridge, e.g. one of:

- an explicit data-independence assumption for relevant channel requirements,
- or a verifier-side requirement statement already parameterized by witness data.

## Migration Plan (minimal risk)

1. Add `interactionsEq` defs (do not touch existing `interactionsWithChannel` / `RawChannel.filter`).
2. Add `PartialBalancedChannelsEq` + `SoundChannelsEq` alongside existing defs.
3. Prove `soundChannels_addTable_eq` in the new layer.
4. Optionally prove compatibility lemmas to connect old/new formulations where assumptions allow.

This keeps existing infrastructure intact while enabling fully eq-based proofs for the problematic theorem family.
