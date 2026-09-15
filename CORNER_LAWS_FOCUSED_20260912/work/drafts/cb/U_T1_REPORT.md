# U_T1_REPORT — unit T1: transport of `Record.restrictCrossings` along a `RecordIso`

Prover, 2026-09-14. File: `work/drafts/cb/U_T1.lean` (copy of Skeleton_FINAL.lean; only the T1 leaf body and one
helper changed). Compile: `cd work/lean && lake env lean ../drafts/cb/U_T1.lean` → exit 0, **0 errors**, 16 warnings
(13 `declaration uses sorry` for the other units' leaves at lines 259–400, none at the T1 leaf; two pre-existing
warnings in the frozen glue: unused `hT` at :409, deprecated `Set.mem_setOf_eq` at :481 — not touched).
`grep -c sorry`: 18 before → 17 after (exactly the T1 leaf).

## Leaves

| leaf | status | lines |
|---|---|---|
| `SM.CB.restrictCrossings_iso_of_recordIso` | **PROVED** (term-mode, 13 lines) | U_T1.lean:362–378 |

Leaves left: none in this unit. Statement, name and docstring are byte-identical to Skeleton_FINAL.lean.

## Helpers added (all before the leaf, same namespace `SM.CB`)

* `SM.CB.t1_crossKeep_iff` (U_T1.lean:355–360): `ρ'.CrossKeep X' (ι.Φ v) ↔ ρ.CrossKeep X v` from the
  occurrence-level hypothesis `hX`. It is just `(hX v).symm` — `Record.CrossKeep X v` unfolds to
  `ρ.crossingOf v ∈ X` (SM/MarkedProducts.lean:194) — but stating it in `CrossKeep` form is what
  `Equiv.subtypeEquiv` and `firstReturn_map_val` want, and it documents the orientation.

## Proof

Direct construction (no `RecordIso.ofOcc` needed — `restrictCrossings` keeps `comps` unchanged, so the circle
bijection is `ι.e` itself). It is the accepted `RecordIso.restrict` pattern (SM/LinkRecordExtras.lean:447–458,
restriction to a set of circles) with `CrossKeep` in place of `RestrictKeep`:

* `e := ι.e` (`(ρ.restrictCrossings X).comps = ρ.comps` is `rfl`);
* `Φ := Equiv.subtypeEquiv ι.Φ (fun v => (t1_crossKeep_iff ι hX v).symm)` — `ι.Φ` restricted to the retained
  occurrences `{v // ρ.CrossKeep X v}`;
* `comp_eq` := `ι.comp_eq v.1` (restricted `comp v = ρ.comp v.1` definitionally);
* `succ_eq` := `Subtype.ext (firstReturn_map_val ι.Φ ρ.succ ρ'.succ (ρ.CrossKeep X) (ρ'.CrossKeep X') ι.succ_eq
  (t1_crossKeep_iff ι hX) v).symm` — the restricted successor is `firstReturn ρ.succ (ρ.CrossKeep X)`
  (MarkedProducts.lean:214, also `restrictCrossings_succ_val` :3810), and the accepted
  `SM.Link.firstReturn_map_val` (SM/LinkRecordExtras.lean:394, via `returnTime_map` :383 and `map_pow_apply`)
  says the first return is natural in an intertwining bijection whose predicates correspond;
* `pair_eq` := `Subtype.ext (ι.pair_eq v.1)` (restricted pair = `ρ.pair.subtypePerm _`);
* `bit_eq`, `sgn_eq` := `ι.bit_eq v.1`, `ι.sgn_eq v.1` (inherited verbatim).

Axioms (checked on the identical prototype /workspace/scratch/t1/proto.lean with the same imports/namespace):
`propext, Classical.choice, Quot.sound` — no SM axiom enters.

## Pitfalls / notes for the assembler and the executor

* `SM.Link.firstReturn_map_val` lives in `SM/LinkRecordExtras.lean` (imported through `SM.Smoothing`); it IS
  reachable from the skeleton's imports (`CV.X1`, `CV.PieceCurve`, `SM.MarkedProducts`, `SM.CornerStateSum`),
  verified by `#check` under exactly those imports. If the ported module `SM/CBRecordIsoTransport.lean` gets a
  slimmer import list, it must still (transitively) import `SM.LinkRecordExtras` (or `SM.MarkedProducts`, which
  suffices).
* `DecidablePred` instances: `restrictCrossings` elaborates its `firstReturn` with
  `Record.instDecidablePredCrossKeep` (`Classical.decPred _`), while the file has
  `attribute [local instance] Classical.propDecidable`. No mismatch arose — `Subtype.ext (… ).symm` closed
  `succ_eq` by defeq (`Classical.decPred p` unfolds to `fun _ => Classical.propDecidable _`). If a future edit
  changes the instance context and `succ_eq` fails with a `Decidable` mismatch, pass the instances explicitly
  (`@firstReturn_map_val … (ρ.instDecidablePredCrossKeep X) …`) or go through `firstReturn_congr_pred`
  (SM/Stack.lean:217).
* The leaf is far shorter than the plan's ≈150-line estimate (13 lines + a 6-line helper) because the
  `RecordIso.restrict` template already existed for the circle-set restriction; the estimated
  `RecordIso.ofOcc` route (rebuilding `e` from `Φ` on occupied circles + `FreeComp`) is unnecessary here since
  `restrictCrossings` does not change `comps`.
* Consumers (KL3's `gaussRecord_restrict_iso` composition in `record_iso_blockRecord`, AS): the hypothesis `hX`
  is stated per occurrence `v : ρ.M`; to derive it from a crossing-level statement use
  `RecordIso.crossingOf_eq` (SM/LinkRecord.lean:628: `ρ'.crossingOf (ι.Φ v) = ⟨(ρ.crossingOf v).1.map ι.Φ.toEmbedding, …⟩`)
  or, for `X' = {p | label … ∈ T'}`-style sets, unfold membership and use the spec of `Φ` (KL1's
  `positiveLiftRecordIso_val`).
* Nothing else in the file was modified (diff against the pre-edit copy /workspace/scratch/t1/U_T1.before.lean:
  only the inserted helper at 355–361 and the replaced leaf body at 366–378).
