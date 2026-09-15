# U7c-fix — REPORT (row 143, CV:lem:piececurve: the second half of the datum)

Written 2026-09-14 05:25 UTC / 1:25am ET by the U7c-fix prover subagent (claude-fable-5-1). Paths relative to the package root
`/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912`. Nothing under
`work/lean` was written; the repair lives in a copy and was checked with `lake env lean` only.

## 0. Deliverables and status

| item | value |
|---|---|
| file | `work/drafts/cvdom/U7c-fix/PieceCurve.lean` (863 lines; the library file `work/lean/CV/PieceCurve.lean` has 685) — intended to replace `work/lean/CV/PieceCurve.lean` verbatim |
| byte diff | `work/drafts/cvdom/U7c-fix/PieceCurve.diff` (`diff -u work/lean/CV/PieceCurve.lean work/drafts/cvdom/U7c-fix/PieceCurve.lean`): 7 hunks, +186 / −7 lines, see §4 |
| compile | `source /workspace/envs/lean/env.sh; cd work/lean && lake env lean ../drafts/cvdom/U7c-fix/PieceCurve.lean` → **exit 0, no output** (≈7 s); grep for the placeholder keyword: **0 hits** |
| axioms (on a /tmp copy with `#print axioms` appended) | `CV.piececurve`: **[propext, Classical.choice, Quot.sound]**; `CV.pieceShadow_rotationSystem`, `CV.cornerPolygon_edge_of_crossingPoint_mem`, `CV.pieceShadowCrossingEquiv_crossingPoint`: the same three; `CV.piecediagram_definition` (row 142, untouched): `[propext, Classical.choice, Quot.sound, SM.lit_homfly]` as before |
| row 142 | `PieceDiagramData`, `piecediagram_definition` and every definition (`pieceSupport`, `pieceCarrier`, `pieceCurve`, `pieceShadow`, `pieceDiagram`, `pieceHomfly`, …) **byte-identical** (per-declaration comparison, §4) |
| `CV/X1.lean` | compiles against an `.olean` built from the copy (overlay recipe, §5): **exit 0**; `CV.X1_definition` axioms unchanged `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` |
| names | row theorem still `CV.piececurve : PieceCurveData hn hD S hS H`; bundle still `CV.PieceCurveData` (now 11 fields, was 10). No `geo*` name re-declared (ruling R3); the 4 new names were checked against the library (`grep` over `work/lean`, excluding `.lake`): 0 collisions |

## 1. The refutation and the repair

The review of row 143 (NOT FAITHFUL, two refuters): the printed lemma ends (d1_setup.tex:608–609) "In particular
that restricted word is realizable, and the datum of Definition def:piecediagram is the datum of $C_H$"; the datum
(def:piecediagram, d1:577–585) is "the parent Gauss word restricted to the crossings of $H$, in the parent's cyclic
order, together with the parent's per-crossing counter-clockwise half-edge order restricted to the surviving
half-edges … So the datum is a word *together with a rotation system*, not a bare word"; the proof's Step 5 closes
(d1:664–666) "Its rotation system at each surviving crossing is the carrier's, which is the parent's, since smoothing
at other points does not disturb the half-edge order at a survivor; that is the second half of the datum."
`PieceCurveData` had no field for the rotation-system half, and its `realizable : Nonempty (_ ≃ _)` was a
cardinality statement only.

Repair (row 143 only):
1. new field `rotation_system` — the second half of the datum (§2.1);
2. `realizable` strengthened to a crossing-point-preserving bijection (§2.2);
3. both proved (§3), through four new lemmas placed in §6 of the module (`section PieceCurveGeometry`);
4. module docstring: a new clause-map section "The datum of def:piecediagram, both halves (row 143, last printed
   sentence; U7c-fix)" before "## Tiers", the "Checked with" line, a second header note after the 04:34Z port note,
   and the `PieceCurveData` docstring (one added sentence). No other docstring changed.

## 2. The row-143 bundle after the repair (verbatim from the copy)

### 2.1 New field `rotation_system` (copy lines 704–721)

```lean
  /-- "and the datum of Definition def:piecediagram is the datum of `C_H`" — the **second half of the
  datum, the rotation system** (d1:580–585: "together with the parent's per-crossing counter-clockwise
  half-edge order restricted to the surviving half-edges … So the datum is a word *together with a
  rotation system*, not a bare word"; proof d1:664–666: "Its rotation system at each surviving crossing
  is the carrier's, which is the parent's, since smoothing at other points does not disturb the
  half-edge order at a survivor; that is the second half of the datum"): at every surviving crossing
  `c ∈ H`, the two strands of `C_H` through `crossingPoint c` are the two parent edges of `c` — for the
  double point `x` of the shadow of `C_H` at `crossingPoint c`, a bijection between the strands of `x`
  and the two edges of `c` under which each strand is directed along its parent edge with a positive
  factor (`dir s = t • edge P i`, `t > 0`). Hence the four half-edges of `C_H` at `x` are the parent's
  four half-edges at `c`, in the same counter-clockwise order: the parent's rotation system at `c`,
  restricted to `H` -/
  rotation_system : ∀ c ∈ pieceLabels hD.crossingGeometry S H,
    ∀ x : (pieceShadow hn hD hS H).Crossing,
      (pieceShadow hn hD hS H).crossingPoint x = crossingPoint c →
        ∃ e : {s // s ∈ x.val} ≃ {i // i ∈ c.val},
          ∀ s : {s // s ∈ x.val}, ∃ t : ℝ, 0 < t ∧
            (pieceShadow hn hD hS H).dir s.1 = t • edge P (e s).1
```

Vocabulary (all accepted): `pieceShadow hn hD hS H = geoCarrierShadow … (pieceCarrier …) = Shadow.single ⟨k, _, C_H⟩`
(SM/GeoPositiveLift.lean:97, the one-component shadow of the corner polygon `C_H = pieceCurve`);
`Shadow.Crossing` = a pair of non-adjacent meeting strands (SM/LinkDiagram.lean:246–251), `x.val : Finset Strand`
its two strands; `Shadow.crossingPoint` (LinkDiagram.lean:372); `Shadow.dir s = edge C_H s.2` (LinkDiagram.lean:106,
`single_dir` 1636) the direction vector of a strand; `Crossing P` = the pair `c.val` of remote parent edges
(SM/Crossings.lean:15), `crossingPoint c` (Crossings.lean:41); `edge P i = P (i+1) − P i` (SM/Polygon.lean:49).

Why this is the printed second half: at a transverse double point the four half-edges are the two directed strands
entering and leaving it; their counter-clockwise order is determined by the two direction vectors up to positive
scaling. The field says the two strands of `C_H` at the survivor `c` are in bijection with the two parent edges of
`c`, each with a positively proportional direction, and (hypothesis) pass through the same point `crossingPoint c`;
so the four half-edges of `C_H` at `x` are the parent's four half-edges at `c` in the same counter-clockwise order —
"the carrier's, which is the parent's", "restricted to the surviving half-edges" = restricted to `c ∈ H`. This is the
form the review brief asked for ("C_H's two strands through the point are directed along P's two edges there:
positively proportional direction vectors and the same crossing point").

### 2.2 Strengthened field `realizable` (copy lines 695–703)

```lean
  /-- "In particular that restricted word is realizable, and the datum of Definition def:piecediagram is
  the datum of `C_H`" — the **first half of the datum, the word** (d1:577–580 "the parent Gauss word
  restricted to the crossings of `H`, in the parent's cyclic order"): the restricted word is read off an
  actual closed plane curve — the double points of the shadow of `C_H` are in bijection with `H`, each
  double point of the shadow sitting at the crossing point of the crossing of `H` it corresponds to -/
  realizable : ∃ e : (pieceShadow hn hD hS H).Crossing ≃
      {c : Crossing P // c ∈ pieceLabels hD.crossingGeometry S H},
    ∀ x : (pieceShadow hn hD hS H).Crossing,
      (pieceShadow hn hD hS H).crossingPoint x = crossingPoint (e x).1
```

(was: `realizable : Nonempty ((pieceShadow hn hD hS H).Crossing ≃ {c : Crossing P // c ∈ pieceLabels hD.crossingGeometry S H})`.)

### 2.3 The proof (copy lines 724–735)

```lean
theorem piececurve : PieceCurveData hn hD S hS H where
  … (eight fields unchanged) …
  realizable := ⟨pieceShadowCrossingEquiv hn hD hS H, pieceShadowCrossingEquiv_crossingPoint hn hD hS H⟩
  rotation_system := fun _ hc x hx => pieceShadow_rotationSystem hn hD hS H hc x hx
```

## 3. Lemmas

### 3.1 New (all in `section PieceCurveGeometry`, after `pieceShadowCrossingEquiv`; copy lines 523–636)

* `CV.pieceShadowCrossingEquiv_crossingPoint (x) : (pieceShadow hn hD hS H).crossingPoint x = crossingPoint (pieceShadowCrossingEquiv hn hD hS H x).1`
  — term proof: `(crossingPoint_geoCarrierCrossingEquiv hn (CarrierGeometry.ofDiagrammatic hD) (pieceSupport_geoIndependent hD hS H) (pieceCarrier hD hS H) x).symm`
  (U4, SM/GeoPositiveLift.lean:707; the transport `Equiv.subtypeEquivRight` along `pieceCarrier_geoCarrierCrossings` keeps the underlying crossing definitionally).
* `CV.cornerPolygon_edge_of_crossingPoint_mem (hn) (hG : CarrierGeometry P) {T} (hT : GeoIndependent hG.cg T) (q) {c} (hc : c ∈ geoCarrierCrossings hG.cg T q) (k) (hk : crossingPoint c ∈ edgeSegment (geoCornerPolygon hG.cg T q) k) : ∃ i ∈ c.val, ∃ t : ℝ, 0 < t ∧ edge (geoCornerPolygon hG.cg T q) k = t • edge P i`
  — the geometric fact the brief anticipated might be missing from the library ("corner polygon's edges vs P's edges");
  it is general (any carrier of any independent set, tier 1), stated in the `CV` namespace without a `geo` prefix (R3). Proof:
  `geoCornerPolygon_edge_smul` (U2b, SM/GeoPositiveLift.lean:400: `edge Q k = t • edge P (geoOutSlot (geoCornerMark k)).1`, `t > 0`) supplies the edge and the factor; it remains to show that parent edge is in `c.val`:
  `geo_edgeSegment_param` (GeoPositiveLift.lean:241) traces the crossing point on edge `k` either at a block parameter `(ρ^r c_k, u)`, `u ∈ [0,1)`, `GeoBlockInterior k r` — then `geoIsCarrierParameter_block` (:172) + `geo_carrier_crossingPoint_parameters` (U2c, SM/GeoCarrierSelfIntersections.lean:457) give `ρ^r c_k = Sum.inr w`, `w.1 = c`; `r ≥ 1` since `c ∉ T` (`mem_geoCarrierCrossings`) while `c_k` is a true corner (`isTrueCorner_geoCornerMark`, `isTrueCorner_visit`); so `GeoBlockInterior.visit_edge` (:160) gives `w.2.val = (geoOutSlot (geoCornerMark k)).1` and `w.2.property : w.2.val ∈ c.val` —
  or at the end corner `Q (k+1)` — excluded by `geo_carrier_selfIntersection_not_corner … .2.2.2` (GeoCarrierSelfIntersections.lean:683, "no crossing point is the plane point of a true corner") with `geoCornerPolygon_apply`.
  (Same route as the library's own `geo_carrierCrossing_edges`, GeoPositiveLift.lean:621, run in the opposite direction.)
* `CV.pieceShadow_strand_dir {c} (hc : c ∈ pieceLabels …) (x) (hx : crossingPoint x = crossingPoint c) {s} (hs : s ∈ x.val) : ∃ i ∈ c.val, ∃ t : ℝ, 0 < t ∧ (pieceShadow hn hD hS H).dir s = t • edge P i`
  — the previous lemma at `q_H` with `pieceCarrier_geoCarrierCrossings` (`c ∈ H ↔ c` a crossing of `q_H`) and `Shadow.crossingPoint_mem` (LinkDiagram.lean:375, the crossing point lies on each strand).
* `CV.pieceShadow_rotationSystem {c} (hc) (x) (hx) : ∃ e : {s // s ∈ x.val} ≃ {i // i ∈ c.val}, ∀ s, ∃ t : ℝ, 0 < t ∧ (pieceShadow hn hD hS H).dir s.1 = t • edge P (e s).1`
  — `f s := Classical.choose (pieceShadow_strand_dir …)`; injective: two distinct strands of `x` are non-adjacent and meet (`Shadow.crossing_pair_spec`, LinkDiagram.lean:291), so `pieceShadow_generic.transverse` (U4, the `Generic.transverse` clause, LinkDiagram.lean:397) gives `det (dir s) (dir s') ≠ 0`, whereas two positive multiples of one parent edge have `det = 0` (`simp [det, Prod.smul_fst, Prod.smul_snd]; ring`); bijective by `Fintype.bijective_iff_injective_and_card` with `Fintype.card_coe`, `Shadow.crossing_card_two` (LinkDiagram.lean:284) and `SM.crossing_card_two` (Crossings.lean:25); `Equiv.ofBijective`.

### 3.2 Library lemmas used (none modified)

U2b `geoCornerPolygon_edge_smul`; U4 `geo_edgeSegment_param`, `geoIsCarrierParameter_block`, `GeoBlockInterior.visit_edge`,
`geoCornerPolygon_apply`, `crossingPoint_geoCarrierCrossingEquiv`, `geoCarrierShadow_generic` (through the module's
`pieceShadow_generic`); U2c `geo_carrier_crossingPoint_parameters`, `geo_carrier_selfIntersection_not_corner`;
U2a `mem_geoCarrierCrossings`; SM `isTrueCorner_geoCornerMark`, `isTrueCorner_visit`, `Shadow.crossingPoint_mem`,
`Shadow.crossing_pair_spec`, `Shadow.crossing_card_two`, `Generic.transverse`, `crossing_card_two`; the module's
own `pieceCarrier_geoCarrierCrossings`, `pieceSupport_geoIndependent`, `pieceShadowCrossingEquiv`, `pieceShadow_generic`,
`CarrierGeometry.ofDiagrammatic`. Mathlib: `Fintype.bijective_iff_injective_and_card`, `Fintype.card_coe`,
`Equiv.ofBijective`, `Equiv.Perm.one_apply`, `Subtype.ext`.

## 4. Byte-diff summary (`PieceCurve.diff`)

`sha256`: library `989fef23b6f3811f8ae2515e5a410a2826a53a12d57761a6186eeead11befaf7`, copy
`7e3a87a0a5af1ba3befec47a40b776eb2de2f5673b6c983cf4fcd10f17338b2b`. 7 hunks, **+186 / −7** lines:

| hunk (library → copy) | what |
|---|---|
| `@@ -4,6 +4,16 @@` | header: second `/-! Repaired … -/` note added after the 04:34Z port note (module comment, no declaration) |
| `@@ -78,6 +88,40 @@` | module docstring: new clause-map section "The datum of def:piecediagram, both halves" before "## Tiers" |
| `@@ -85,7 +129,8 @@` | module docstring: "Checked with" line extended by the U7c-fix command (1 line removed, 2 added) |
| `@@ -476,6 +521,113 @@` | §6: the four new lemmas inserted before `end PieceCurveGeometry` (pure insertion) |
| `@@ -488,7 +640,10 @@` | `PieceCurveData` docstring: one sentence added (the closing line re-emitted: 1 removed, 4 added) |
| `@@ -538,10 +693,32 @@` | the `realizable` field: old docstring tail (2 lines) + old statement (2 lines) removed; new `realizable` + new `rotation_system` added |
| `@@ -554,7 +731,8 @@` | `piececurve`: `realizable := ⟨…⟩` replaced by the two field proofs |

The 7 removed lines, exhaustively: the "Checked with" docstring line; the last line of the `PieceCurveData` docstring;
the two tail lines of the old `realizable` docstring; the two lines of the old `realizable` statement; the old
`realizable := ⟨pieceShadowCrossingEquiv hn hD hS H⟩`. Per-declaration comparison (script splitting both files at
declaration heads and comparing head+body text): 51 declarations in the library file, 55 in the copy; **NEW** =
`pieceShadowCrossingEquiv_crossingPoint`, `cornerPolygon_edge_of_crossingPoint_mem`, `pieceShadow_strand_dir`,
`pieceShadow_rotationSystem`; **CHANGED** = `PieceCurveData`, `piececurve` (the two row-143 declarations); **REMOVED** =
none. Every other declaration — row 142's `PieceDiagramData`/`piecediagram_definition`, all definitions, all §1–§5
combinatorics, all §6 geometry lemmas, all §8 piece-diagram lemmas — is byte-identical.

## 5. `CV/X1.lean` check

`CV/X1.lean` imports `CV.PieceCurve` and uses `pieceHomfly`, `pieceDiagram`, `pieceWrithe`, `piecesOn`, `pieceLabels`
… — none of the row-143 declarations; still, it was compiled against the repaired module (U7c report recipe):
```
mkdir -p /tmp/u7cfix_root/CV /tmp/u7cfix_olean/CV
cp work/drafts/cvdom/U7c-fix/PieceCurve.lean /tmp/u7cfix_root/CV/PieceCurve.lean
cd work/lean
ln -s $PWD/.lake/build/lib/lean/CV/<every CV olean/ilean except PieceCurve.*> /tmp/u7cfix_olean/CV/
lake env bash -c 'lean --root=/tmp/u7cfix_root /tmp/u7cfix_root/CV/PieceCurve.lean -o /tmp/u7cfix_olean/CV/PieceCurve.olean -i /tmp/u7cfix_olean/CV/PieceCurve.ilean'   # exit 0
lake env bash -c 'LEAN_PATH="/tmp/u7cfix_olean:$LEAN_PATH" lean /tmp/u7cfix_x1/X1.lean'   # copy of work/lean/CV/X1.lean: exit 0, no output
```
That the overlay olean (and not the library's) was loaded was confirmed by appending
`#check @CV.pieceShadow_rotationSystem` and `#check @CV.PieceCurveData.rotation_system` to a second copy of X1.lean
(both resolve; they exist only in the repaired module) together with `#print axioms CV.X1_definition` (unchanged).

## 6. Porting

Copy `work/drafts/cvdom/U7c-fix/PieceCurve.lean` over `work/lean/CV/PieceCurve.lean` (nothing else changes: X1.lean
needs no edit; the two header notes already record the port and the repair), rebuild, and re-run the row-143 review
against the clause map in the module docstring (§"The datum of def:piecediagram, both halves") and the two field
docstrings of §2 above. The review's two refuters are answered by: `rotation_system` (the rotation-system half,
d1:580–585 / 664–666) and the strengthened `realizable` (the bijection is the crossing-point-preserving one, no
longer a cardinality statement).
