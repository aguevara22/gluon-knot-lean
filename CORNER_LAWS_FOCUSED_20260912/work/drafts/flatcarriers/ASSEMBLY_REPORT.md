# ASSEMBLY_REPORT — def:flat-carriers / cor:flat-carriers

Written 2026-09-13 22:45 UTC / 6:45pm ET by the assembler subagent.
File: `work/drafts/flatcarriers/FlatCarriers_Assembled.lean` (5667 lines, 243 declarations).
Check: `cd work/lean && lake env lean ../drafts/flatcarriers/FlatCarriers_Assembled.lean`
→ exit 0, **11 s** wall clock (Mathlib olean load dominates; each unit alone took 9–10 s),
zero errors, zero warnings, zero `sorry`. Output, verbatim:
```
'SM.flat_carriers_definition' depends on axioms: [propext, Classical.choice, Quot.sound]
'SM.flat_carriers' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Statements of both row theorems are byte-identical to `Statement_FINAL.lean` (lines 950 and 1272;
checked by `diff` of the extracted 9-line statements) and sit in the same context
(`namespace SM`, `open GeoCarrier`, local `Classical.propDecidable`, `variable {n : ℕ} [NeZero n]`).
Nothing in `SM.FlatCarriersDefs` was touched; nothing was written under `work/lean`.

## Layout
Imports: union of the units' (`SM.FlatCarriersDefs`, `SM.AppendRotation`, `SM.RegularPerturbation`,
`SM.GermNeighborhood`, `SM.GeometricParameters`). Then the five units verbatim, in order
U1 → U2 → U3 → U4 → U5, each kept as its own `namespace SM … end SM` block (own sections,
`variable`s, `open`s, module docs), then a final block with `section Wiring` (helpers) and
`section RowTheorems` (the two theorems), then the two `#print axioms`.

## De-duplication (kept the first copy in file order; deleted later exact duplicates)
| declaration | kept | deleted | note |
|---|---|---|---|
| `LawfulBEq (α ⊕ β)` instance | U1 `Sum.lawfulBEq` | U2 `sumLawfulBEq`, U4 `sumLawfulBEq`, U5 `instLawfulBEqSum` (+ its `#print axioms`) | Prop-valued class, one instance suffices |
| `visitTransport_visitTwin` | U1 (`SM.`) | U2 (`SM.`), U3 (`SM.GeoCarrier.`) | identical explicit args |
| `fusionVisitEquiv_visitTwin` | U1 (`SM.`, on `P`) | U3 (`SM.GeoCarrier.`) | identical explicit args |
| `markTransport_inl` | U1 (`@[simp]`) | U5 | identical |
| `geoMarkSuccessor_no_mark_between` | U1 (`SM.`) | U2, U3 (both `SM.GeoCarrier.`) | identical explicit args |
| `isTrueCorner_markTransport` | U2 | U5 | identical |
| `mem_transportSupport_iff`, `mem_deletionSupport_iff` | U2 (`SM.`) | U3 (`SM.GeoCarrier.`) | identical explicit args |
| `geoCornerMark_mem_cornerList` | U3 (`SM.GeoCarrier.`) | U5's `geoCornerMark_mem` (same statement) | see renames |

The `SM.GeoCarrier.X` copies had to go (not merely be tolerated): with both `SM.X` and
`SM.GeoCarrier.X` present, every reference to `X` from inside `namespace GeoCarrier` is ambiguous
(`resolveUsingNamespace` returns both). A scan of all 3148 library names under `SM.` found no
unit name shadowing or duplicating a library name.

## Renames (later copy differed in statement; renamed throughout that unit only)
- U2 `fusionVisitEquiv_visitTwin` (stated on `g : WallGerm`, `g.pointZeros`) → `fusionVisitEquiv_visitTwin_germ`.
- U3 `geoMarkSuccessor_ne_self` (needs `3 ≤ n`; U2's needs `2 ≤ n`) → `geoMarkSuccessor_ne_self_of_three_le`.
- U5 references `geoCornerMark_mem` → `geoCornerMark_mem_cornerList` (U3's lemma, after deleting U5's copy;
  U5's other `geoCornerMark_mem` had a different statement from U3's `SM.GeoCarrier.geoCornerMark_mem`).
After these, a fully-qualified scan of the assembled file shows no duplicate full names and no
short-name collisions across namespaces.

## Wiring (final block)
- `exists_sideParameter_lt g hδ : ∃ t : g.SideParameter, t.val < δ` (`t := min δ g.radius / 2`).
- `u2Interface_of t hsd hs S hS : U2Interface … t hs S` := U1's `identify_sides_marks_of`,
  `identify_deletion_marks_of`, `independent_supports_of` (sides) → U2 `flat_carriers_U2`,
  its seven conjuncts fed to U1's `U2Interface` fields (verbatim types).
- `u3Interface_of t hsd hsf hs S hS : U3Interface …` := U3 `flat_carriers_U3` with `hspec` = U2's
  `centre_carriers`, `hST`/`hSD` = U1's `independent_supports_of`, `hsf` = U3's `SideFacts`
  (from `flat_sides_side_facts … hF`); `mu_j_between`/`mu_j_fused_multiples` fill
  `central_vs_deletion_geometry`.
- `u5Interface_of …` := U5 `selector_identity` (with the five-conjunct
  `central_vs_deletion_through_mu_j` rebuilt from U2's three + U3's two) and `other_selectors_agree`.
- `flat_carriers_definition` := U1 `flat_carriers_definition_of hsc ⟨δF, …, u2Interface_of ….centre_carriers⟩`,
  `δF` from U1 `flat_side_records (flat_sides hn g hz hb hc hsc)`.
- `flat_carriers`: radii `δF` (side records), `δS` (`flat_sides_side_facts`), `δR` (U4 `same_rotation`,
  whose uniform hypotheses `hneC`/`hnaC` for every independent `S` are U3's `flat_centre_edge_ne_zero`
  / `flat_centre_not_antiparallel` at the centre spec obtained from ONE side parameter
  `t₀ < δF` via `exists_sideParameter_lt`). Then U1 `flat_carriers_of hsc hU2 hU3 hU4 hU5` with
  `OnSmallRadius` packages on `δF`, `min δF δS`, `min δF (min δS δR)`, `min δF δS`; the U4 package
  passes `hcorr` = U2 `geoComponentCornerList_markTransport … (hs b) (identify_sides_marks_of … b)`,
  `hown` = `correspond_deletion.2.1`, `hsucc`/`hcycJ` = `central_vs_deletion_marks.1/.2.2`,
  `hcycO` = `others_unchanged.2.1`, `hturnC` = `turns_nonzero.1`, `hneD` = `nonzero_segments.2.2.2.1`,
  `hnaD` = `no_antiparallel.2.1`. U1's `flat_carriers_of` takes the overall `min` and `δ ≤ g.radius`.

## Left unproved
Nothing. No `sorry`, no new axioms, no `set_option maxHeartbeats`, no changes to any unit's proofs
beyond the deletions/renames listed above.
