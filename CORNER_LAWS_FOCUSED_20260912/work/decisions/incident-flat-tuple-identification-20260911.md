# Incident flat gaps: exact deletion tuple and root identification

2026-09-11. Same-model technical assistance only. **DERIVED IDENTITIES / UNCHECKED LEAN IMPLEMENTATION PLAN**: no kernel or build was run, and no stronger-model fidelity approval or source acceptance is supplied. Progress remains 39/192 accepted (20.3%), targets 0/8.

## Arity and the common answer

Let the parent have N vertices, N ≥ 4. The incoming case uses root j - 1 and the right gap of `incomingFlatTriple`: positions 1 through N - 1. The outgoing case uses root j and the left gap of `outgoingFlatTriple`: positions 0 through N - 2. Each gap has N - 2 leaves, hence its closed tuple has N - 1 vertices. Both ordered words are exactly the retained cyclic list j + 1, j + 2, …, j - 1.

For Lean, first implement at parent arity `m + 4` and child arity `m + 3`. Both gap arities then reduce definitionally to `m + 3`: incoming leaves reduce from `((m + 4) - 1) - 1`, and outgoing leaves from `((m + 4) - 2) - 0`. This avoids transporting `ZMod` labels across an arity equality. It loses no source case: for a general N ≥ 4 obtain `∃ m, N = m + 4` with witness `N - 4` and arithmetic, then substitute N. Do not assert that the two tuple types at symbolic N are definitionally equal before this step.

Write `tIn := incomingFlatTriple (n := m + 4) (by omega)`, `tOut := outgoingFlatTriple (n := m + 4) (by omega)`, and `Q := deleteVertex (n := m + 3) P j`. The desired tuple identities are:

```lean
restrictedWordTuple P (j - 1) tIn.rightInterval =
  shift (-1 : ZMod (m + 3)) Q
restrictedWordTuple P j tOut.leftInterval =
  shift (-1 : ZMod (m + 3)) Q
```

Equation pair (1). These are equalities of entire labelled tuples, with no geometric or wall hypothesis needed.

## Prove the label identities first

For every `i : ZMod (m + 3)`, prove:

```lean
restrictedVertexIndex (j - 1) tIn.rightInterval i = deletionIndex j (i - 1)
restrictedVertexIndex j tOut.leftInterval i = deletionIndex j (i - 1)
```

Equation pair (2). The `restrictedVertexIndex` definition is in `work/checks/RestrictedCriticalG1.body.lean`; it is exactly the label sampled by `restrictedWordTuple`.

To verify every position explicitly, set `v := (i - 1).val`. The incoming global position has value `1 + v`; its boundary label is `(j - 1) + ↑(1 + v) + 1`. Apply `Nat.cast_add` and `Nat.cast_one`, then ring arithmetic to obtain `↑v + (j + 1)`. The outgoing global position has value `0 + v`; its boundary label is `j + ↑v + 1`. Remove the zero and reorder addition to obtain the same `↑v + (j + 1)`. Finally, `deletionIndex` unfolds to `insertIndex (i - 1) + (j + 1)`, and `insertIndex` unfolds to the natural-value cast `↑v`. These steps prove both equalities in (2), including the wrap at i = 0; no natural-subtraction rule for `ZMod.val` is needed.

Relevant unfolding list: `restrictedVertexIndex`, `BoundaryInterval.globalPosition`, `BoundaryInterval.leaves`, the appropriate triple and interval definitions, `boundaryIndex`, `deletionIndex`, `insertIndex`. Then use the cast rewrites and `ring`. These tactic suggestions are untested.

For (1), use function extensionality, apply P to (2), and unfold `restrictedWordTuple`, `boundaryWord`, `deleteVertex`, and `shift`. The argument `i + (-1)` from `shift` is `i - 1` by `sub_eq_add_neg`. This proves the full tuple equality directly, rather than inferring it from endpoint agreement.

## Transport the coefficient with its physical root

The existing API is:

```lean
treeCoefficient_shift (P : LabelledTuple n) (hP : G1 P)
  (g a : ZMod n) (hn : 3 ≤ n) :
  treeCoefficient (shift a P) (g1_shift_forward a hP) (g - a) hn =
    treeCoefficient P hP g hn
```

Use this with `P := Q`, **both** `g := -1` and `a := -1`, and child arity `m + 3`. Since `g - a = 0`, it yields:

```lean
treeCoefficient (shift (-1) Q) (g1_shift_forward (-1) hQ) 0 (by omega) =
  treeCoefficient Q hQ (-1) (by omega)
```

Equation (3). Rewrite the appropriate tuple equality (1), including its G1 witness; proof irrelevance handles different proofs of that same G1 proposition. Under `hz : pointZeroTriples P = {turnSupport j}`, obtain `hQ` using the existing `g1_deleteVertex hz`. No parent G1 is needed.

The root correspondence is also literal: local labels 0 and 1 of either gap map under (2) to deletion labels -1 and 0. `deletionIndex_last` and `deletionIndex_zero` then give the ordered physical points `P (j - 1)` and `P (j + 1)`. The existing `fusionIndex_prev j` and `fusionIndex_deleted j` identify `fusionIndex j (j - 1)` and `fusionIndex j j`, respectively, with this same child label -1. Thus (3) is the coefficient at the source fused edge, with the root transported by the proved cyclic covariance.

Finally, to identify the integer B in the flat response, unfold `criticalIntervalIntegerOutput` in the appropriate nonleaf gap. Its leaf count is `m + 2 ≥ 2`, so the formal-leaf branch is excluded. The remaining term is exactly the gap tree coefficient just identified with `treeCoefficient Q hQ (fusionIndex j g)`. This supplies both incident geometric identifications; epsilon values, scalar normalization, and side order remain for the flat-law assembly.

## Inspected sources

The mathematical comparison is with `sm-2-amplitude.tex` lines 380–386 and 435–452. Core APIs were read in `RestrictedWordRoot`, `IntervalRestriction`, `DeletionIndices`, `DeletedTuple`, `FusionIndices`, `DeletionG1`, `Polygon`, and `TreeCoefficient`.

The observed `FlatBoundaryPositions.body.lean` SHA-256 was `13f01dbe3050125a22ce407f5d6e01101ee680b98627f6b226ff325964a6fc56`; root was checking this candidate, so this plan supplies no pass claim for it. `RestrictedWordRoot.lean` was `a2d45634865602373437222b5e190794f31375624fa3021745ae6a0043551e8e`, `TreeCoefficient.lean` was `d070e70dfbb61e036641f0d5fac4adae83fd1cadfe22f3ce2ffd8c8e1de9ab06`, and the authoritative source was `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf`.

No existing Lean body, canonical file, map, or acceptance status was edited.
