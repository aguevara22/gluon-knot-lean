# CV-DOM unit U0 — REPORT (2026-09-14, ~02:32 UTC / 10:32pm ET)

Prover: Claude Code subagent (claude-fable-5-1) of the pod executor. Spec: work/drafts/cvdom/DECISION_FINAL.md
§3 (rulings R1–R4) and §5 row **U0**. Nothing under work/lean was written. Paths relative to the package
root /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912.

## Deliverables

| file | intended home | lines | status |
|---|---|---:|---|
| `work/drafts/cvdom/U0/GeoCarrierGeometry.lean` | `work/lean/SM/GeoCarrierGeometry.lean` (new module, namespace `SM` / `SM.GeoCarrier`, CV-free) | 275 | `cd work/lean && lake env lean ../drafts/cvdom/U0/GeoCarrierGeometry.lean` → exit 0, no warnings, no `sorry` |
| `work/drafts/cvdom/U0/CVCarrierBridges.lean` | head of `work/lean/CV/Carriers.lean` (after `import SM.GeoCarrierGeometry`) | 82 | exit 0, no warnings, no `sorry` (check recipe below) |

`#print axioms` on all 22 declarations: `[propext, Classical.choice, Quot.sound]` only (standard).
Imports: SM module `SM.FlatCarriersDefs`, `SM.RegularLocus`; CV module `CV.Events` (which imports `CV.Setup`),
`SM.GeoCarrierGeometry`. Both are picked up by the lakefile globs `SM.+` / `CV.+`. No new name collides with
anything under work/lean (`grep -rn` of every new name: empty). No accepted declaration is redefined, shadowed or
modified; no accepted `geo*` name is re-declared (ruling R3 / risk 1).

**Check recipe for the CV file while the SM module is still a draft** (Lean resolves a module from the first search
root containing the package directory `SM/`, so an extra root must shadow the whole `SM` package):
```
cd work/lean
LIB=$PWD/.lake/build/lib/lean
mkdir -p /tmp/u0/src/SM /tmp/u0/olean/SM /tmp/u0/olean2/SM
cp ../drafts/cvdom/U0/GeoCarrierGeometry.lean /tmp/u0/src/SM/
lake env lean -R /tmp/u0/src -o /tmp/u0/olean/SM/GeoCarrierGeometry.olean /tmp/u0/src/SM/GeoCarrierGeometry.lean
for f in $LIB/SM/*; do ln -sf "$f" /tmp/u0/olean2/SM/; done; cp /tmp/u0/olean/SM/GeoCarrierGeometry.olean /tmp/u0/olean2/SM/
lake env bash -c 'LEAN_PATH="/tmp/u0/olean2:$LEAN_PATH" lean ../drafts/cvdom/U0/CVCarrierBridges.lean'
```
Once the assembler ports `SM/GeoCarrierGeometry.lean` into work/lean (and `lake build`s it), the plain
`lake env lean` check applies to the CV file.

## Declarations, tier by tier, and the accepted lemma each replaces

Tiers (R1): tier 0 = accepted `CrossingGeometry P` (SM/CrossingGeometry.lean:11); tier 1 = NEW `CarrierGeometry P`;
tier 2 = accepted `WeakGeneric P` (SM/WeakGeneric.lean:11). Analyst A's `CornerGeometry` is dropped (R1).

### `SM/GeoCarrierGeometry.lean` (namespace `SM`, then `SM.GeoCarrier` for §4)

| # | declaration | tier | signature (abridged) | replaces / source | spec item |
|---|---|:-:|---|---|---|
| 1 | `structure SM.CarrierGeometry (P : LabelledTuple n) : Prop` fields `cg : CrossingGeometry P`, `vertex_off : ∀ k e, ¬ incident k e → P k ∉ edgeSegment P e` | 1 | — | new (R1, exactly the prototype's structure) | U0 |
| 2 | `CarrierGeometry.ofWeak (hW : WeakGeneric P) : CarrierGeometry P` | 2→1 | `⟨weak_crossingGeometry hW, hW.2.2.1⟩` | accepted `weak_crossingGeometry` + clause 3 of `WeakGeneric` | U0 |
| 3 | `WeakGeneric.carrierGeometry (hW) : CarrierGeometry P` | 2→1 | dot-notation alias of 2 | — | U0 (R1) |
| 4 | `CarrierGeometry.ofGeneric (hn : 3 ≤ n) (hP : Generic P) : CarrierGeometry P` | SM-generic→1 | via accepted `generic_implies_weak hn` | — | U0 |
| 5 | `CarrierGeometry.crossingGeometry (hG) : CrossingGeometry P` | 1→0 | `hG.cg` | symmetry with `CV.Diagrammatic.crossingGeometry` / `CV.Generic.crossingGeometry` | helper |
| 6 | `CarrierGeometry.edge_ne_zero (hG) (i) : edge P i ≠ 0` | 1 (0) | `hG.cg.1 i` | `g1_edge_ne_zero hn hP.1` (Generic.lean:79) | helper |
| 7 | `CarrierGeometry.vertex_not_mem_edge (hG) {i k} (hk0 : k ≠ i) (hk1 : k ≠ i+1) : P k ∉ edgeSegment P i` | 1 | via accepted `nonincident_iff` | `g1_vertex_not_mem_edge hP.1 i k (next_ne_self i).symm hk0 hk1` (Generic.lean:112; lane site CarrierSelfIntersections.lean:316) | "tier-1 replacement of g1_vertex_not_mem_edge" |
| 8 | `CarrierGeometry.vertex_ne_edgePoint (hG) {i k} (hk0) (hk1) {t} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : P k ≠ edgePoint P i t` | 1 | segment form | `g1_vertex_off_edge_line hP.1 i k _ hk0 hk1 t` (Generic.lean:103; lane site CarrierSelfIntersections.lean:51, inside an `edgeInterior` membership). NB: the full-line statement is FALSE at tier 1 (a vertex may lie on the line of a non-incident edge outside the closed segment); the lane only ever consumes the segment form (ANALYSIS_A §2) | "tier-1 replacement of g1_vertex_off_edge_line" |
| 9 | `meet_next_eq_corner_of_vertex_off (hn : 3 ≤ n) (hvert : ∀ k e, ¬ incident k e → P k ∉ edgeSegment P e) (i) {x} (hx : x ∈ edgeSegment P i) (hx' : x ∈ edgeSegment P (i+1)) : x = P (i+1)` | (vertex clause only) | word-for-word CV-free copy of the accepted `CV.meet_next_eq_corner` (CV/Setup.lean, after `Diagrammatic`) | the fold-back exclusion of ruling R4 (`p_i ∈ e_{i+1}` or `p_{i+2} ∈ e_i`) | helper (R4 core) |
| 10 | `CarrierGeometry.meet_next_eq_corner (hn) (hG) (i) {x} (hx) (hx') : x = P (i+1)` | 1 | 9 at `hG.vertex_off` | mirror of accepted `regular_adjacent_meet` (SM/CS3.lean:84) with `CarrierGeometry` for `Regular` | helper |
| 11 | `CarrierGeometry.successive_edges_meet (hn) (hG) (i) : edgeSegment P i ∩ edgeSegment P (i+1) = {P (i+1)}` | 1 | | `g1_successive_intersection hn hP.1` (G1Consequences.lean:20), `turns_successive_intersection` (WeakGeometry.lean:22) | helper |
| 12 | **`CarrierGeometry.adjacent_edges_meet (hn : 3 ≤ n) (hG : CarrierGeometry P) {i j} (hij : i ≠ j) (hadj : adjacent i j) : (j = i + 1 ∧ edgeSegment P i ∩ edgeSegment P j = {P j}) ∨ (i = j + 1 ∧ edgeSegment P i ∩ edgeSegment P j = {P i})`** | 1 | exact shape of §5 U0 | `g1_adjacent_intersection hn hP.1` (G1Consequences.lean:47) and `turns_adjacent_intersection hturn` (WeakGeometry.lean:44), as consumed at CarrierSelfIntersections.lean:245 (`csi_edgeSegment_meet`); so `cg_edgeSegment_meet` / `cg_edge_mem_of_crossingPoint_mem` of the prototype (there at `CornerGeometry`) drop to tier 1 in U2c | U0 |
| 13 | `CarrierGeometry.regularPair_succ (hn) (hG) (i) : RegularPair (edge P i) (edge P (i+1))` | 1 | antiparallel `e_{i+1} = r•e_i`, `r<0` ⇒ the point at parameter `1/(1-r)` is a second common point, against 10 | new; the R4 fact in the form `geoCornerPolygon_regular` consumes at vertex corners (`Regular` = `∀ i, RegularPair (edge P (i-1)) (edge P i)`, RegularLocus.lean:12) | R4 support |
| 14 | `CarrierGeometry.regular (hn) (hG) : Regular P` | 1 | from 13 | tier-1 analogue of accepted `g1_regular` (RegularLocus.lean) / `CV.Generic.regular_sm`; compiled evidence for R4's claim "a `CarrierGeometry` polygon is regular" (risk 3 of §7 discharged at the polygon level) | R4 support |
| 15 | `GeoCarrier.cg_vertex_not_mem_edgeInterior (hG) (k i) : P k ∉ edgeInterior P i` | 1 | from prototype (A) | `csi_vertex_not_mem_edgeInterior hn hP` (CarrierSelfIntersections.lean:40; consumed `g1_edge_ne_zero`, `g1_vertex_off_edge_line`) | U0 |
| 16 | `GeoCarrier.cg_crossingPoint_ne_vertex (hG) (c : Crossing P) (k) : crossingPoint c ≠ P k` | 1 | from prototype (A); uses accepted `crossingPoint_interior_of_geometry` | `csi_crossingPoint_ne_vertex hn hP` (CarrierSelfIntersections.lean:60; consumed `crossingPoint_interior`) | U0 |

None of 1–16 needs `[NeZero n]`; `hn : 3 ≤ n` is taken exactly where the source proofs use it (9–14: `Fact (1 < n)`
for `next_ne_self`, `prev_ne_next hn`) — ruling R5.

### `CVCarrierBridges.lean` (namespaces `SM`, then `CV`)

| # | declaration | tier | proof | accepted input | spec item |
|---|---|:-:|---|---|---|
| 17 | `SM.CarrierGeometry.ofDiagrammatic (hD : CV.Diagrammatic P) : CarrierGeometry P` | CV diagrammatic→1 | `⟨hD.crossingGeometry, hD.2.2.2.2⟩` | `CV.Diagrammatic.crossingGeometry` (CV/Setup.lean:1566), clause 5 of `CV.Diagrammatic` | U0 |
| 18 | `SM.CarrierGeometry.ofCV [NeZero n] (hG : CV.Generic P) : CarrierGeometry P` | CV generic→1 | `.ofWeak hG.weakGeneric` | `CV.Generic.weakGeneric` (CV/Setup.lean:1135, F1). `[NeZero n]` because `CV.Generic` is declared under it | U0 |
| 19 | `SM.carrierGeometry_iff_diagrammatic (hn : 3 ≤ n) : CarrierGeometry P ↔ CV.Diagrammatic P` | 1 = CV diagrammatic | `NeZero n` derived from `hn`; `CV.diagrammatic_iff hn P` | `CV.diagrammatic_iff` (CV/Setup.lean:1630, F3) | U0 |
| 20 | `CV.mem_Ind_iff_geoIndependent (hP) (S) : S ∈ Ind hP ↔ GeoIndependent hP S` | 0 | `mem_Ind_iff hP S` (definitional) | `CV.mem_Ind_iff` (CV/Events.lean:186), `GeoIndependent` (FlatCarriersDefs.lean:457) | U0 (R2) |
| 21 | `CV.mem_N_iff (hP) (S) (y) : y ∈ N hP S ↔ ∃ x ∈ S, GeometricInterlaces hP y x` | 0 | `mem_N` | `CV.mem_N` (CV/Events.lean:194) | U0 re-export |
| 22 | `CV.mem_U_iff (hP) (S) (y) : y ∈ U hP S ↔ y ∉ S ∧ ∀ x ∈ S, ¬ GeometricInterlaces hP y x` | 0 | `mem_U`, `mem_N`, `simp` | `CV.mem_U` (CV/Events.lean:199) | U0 re-export |

## Notes for the assembler / downstream units

- **Exactly the §5 U0 list plus seven helpers** (5, 6, 9, 10, 11, 13, 14). 9–11 are the proof of 12 factored so
  U2b/U4 can use the corner form directly; 13–14 are the R4 fold-back fact in `RegularPair`/`Regular` form —
  the form `geoCornerPolygon_regular` will consume at vertex corners (the corner polygon's edges are positive
  multiples of P's edges, U2b's `geoCornerPolygon_edge_smul`, and `RegularPair` is invariant under positive
  rescaling). If the executor prefers the literal list, 13–14 can be moved to U2b unchanged.
- **Tier of the corner-polygon geometry (R4).** With 12 and 14 compiled, nothing in the "adjacent original
  edges" group needs nonzero turns: `csi_edgeSegment_meet` (CarrierSelfIntersections.lean:245) ports at tier 1
  by replacing `g1_adjacent_intersection hn hP hij hadj` with `hG.adjacent_edges_meet hn hij hadj`
  (identical case shape), so the prototype's `cg_edgeSegment_meet` / `cg_edge_mem_of_crossingPoint_mem`
  (stated at `CornerGeometry`) become tier-1 in U2c. Only `turn ≠ 0` at vertex corners remains tier 2.
- **Dot notation.** `hG.adjacent_edges_meet hn hij hadj`, `hG.meet_next_eq_corner hn i hx hx'`,
  `hG.regular hn`, `hW.carrierGeometry`, `hG.vertex_not_mem_edge hk0 hk1`, `hG.cg`.
- **Naming.** §5 U0 names kept verbatim (`cg_*` for the two CarrierSelfIntersections §0 lemmas, as the row
  specifies, rather than R3's generic `geo_*`); the new helpers use descriptive names in the `CarrierGeometry`
  namespace so they cannot collide with any future `geo*` port.
- **Time.** ≈ 1 h including reading the decision, the accepted sources and two compile rounds (the first draft
  of `regularPair_succ` had an over-eager `← one_smul` rewrite; `ofCV` needed `[NeZero n]`).
