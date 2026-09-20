# DESIGN B — comparison lane: rows 122 prop:anchor-values, 127 thm:comparison, 128 cor:C-inherits (proof-feasibility emphasis)

Architect B, 2026-09-15 ~16:40Z / 12:40pm ET.  Sketch: `work/drafts/comparison/Sketch_B.lean` (706 lines).
Check: `cd work/lean && lake env lean ../drafts/comparison/Sketch_B.lean` → **0 errors, 18 s warm**; `sorry` in exactly
4 declarations: the ONE geometric leaf `cu_cusp_deletion_generic` (sm-6:335-359) and the three row theorems of §5 (D-F11/D-F14
placeholders).  `#print axioms`: `anchor_values_of`, `thm_comparison_of`, `trianglesC_of` = [propext, Classical.choice,
Quot.sound, SM.lit_homfly] (sorry-free); `cor_C_inherits_of` adds `sorryAx` only through the cusp leaf.
Sources (SM15): sm-5-transport.tex 461-476 (122; proof 477-505); sm-6-comparison.tex 299-303 (127; proof 304-311), 313-319
(128; proof 320-372).  Dependencies (tools/claims.py): 122 ← thm:C-soft; 127 ← lem:corner-values, thm:C-S7, thm:C-soft;
128 ← thm:comparison.  Fixed names (work/lean/axiom-policy.json): `SM.thm_comparison`, `SM.cor_C_inherits`; hyp:R mode
`explicit_parameter`.  Proposed: `SM.prop_anchor_values : AnchorValuesData`.

## 0. Verdict in one paragraph

The three rows are ASSEMBLY rows: the accepted `SM.uniqueness` (SM/Uniqueness.lean:441) already contains the whole transport
and anchor argument, `SM.A_lawful : ALawfulData` (SM/ALawful.lean:37) carries every A-identity, and the accepted C rows
prop:C-chamber / prop:C-silent / thm:C-S3 / thm:C-S5 / hyp:R have exactly the shapes of thm:uniqueness's hypotheses (a), (b),
(d).  What is genuinely new is small and is now PROVED in the sketch except one leaf: (i) the descent of `cornerStateSum` to
the polygon space (`cornerPolygon`, §1); (ii) the abstract anchor-values argument for an arbitrary chamber-constant soft
function `F` and its `A_g` clause at nonsoft roots (`av_*`, §2 — 100 lines, adapted from `unA_softAnchor_delta`,
SM/Uniqueness.lean:324); (iii) the bridge from thm:C-S3's `δ`-bounded `IsRightSide/IsLeftSide` form to thm:uniqueness's
`w.Parameter` form (`cs3_flat_bridge`, 35 lines); (iv) the triangle values `C(K₁) = −1`, `C(K₋₁) = 1` from lem:corner-values (i)
(`tri_*`, 60 lines, PROVED conditionally on `CornerValuesData.embedded_value`); (v) the ONE open leaf: the deletion at a simple
cusp wall with (G1) deletion is generic (sm-6:335-359), ≈ 300-500 lines of plane geometry (unit U-CUSPGEN).  The rows are
conditional library theorems `anchor_values_of : CSoftData → …`, `thm_comparison_of : hyp_R → CS7Data → CSoftData →
CornerValuesData → …`, `cor_C_inherits_of : (same) → CInheritsData`; the row theorems become one-liners when rows 105/110/112
land (D-F11/D-F14).  Total remaining prover work ≈ 400-600 lines / 8-14 h, dominated by U-CUSPGEN.

## 1. Statements — clause maps (printed → Lean), with the readings FR-CM-* recorded BEFORE stating

Conventions shared with every accepted sibling: `C(P) = cornerStateSum hn hP : ℤ` on a generic labelled tuple (def:C,
SM/CornerStateSum.lean:166); `A(P) = amplitude P hP.1 hn` (cor:A-lawful, root 0, root-independent, shift-invariant);
a "function on generic polygons of all arities" is `F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ` (thm:uniqueness's
reviewed reading, work/reviews/thm-uniqueness.json); walls, sides, deletion, halves, soft insertion, stars exactly as in
`UniquenessHypotheses` / `ALawfulData` (SM/Uniqueness.lean:34-79, SM/ALawful.lean:37-130).

### Row 122 (sm-5:461-476) → `AnchorValuesHypotheses F` + `AnchorValuesData` (Sketch_B.lean:113, 134), 9 fields

| printed | Lean | status |
|---|---|---|
| "F … constant on chambers and satisfying the soft theorem in the form of thm:C-soft at every admissible soft insertion into a generic polygon" | `AnchorValuesHypotheses F` = `UniquenessHypotheses.chamber` and `.soft` copied verbatim (`toAnchorValuesHypotheses` PROVED) | stated |
| "F(Z) = 0 for every zero anchor" | `zero : ∀ F hF m r (A : ZeroAnchor m r), F (m+1) (proj ⟨A.polygon, A.polygon_generic⟩) = 0` | PROVED (`av_zero`) |
| "F(Y) = τ_j(P) F(P) for every loop anchor" | `loop` (LoopAnchor, case (L)) and `loopZero` (LoopAnchorZero, case (L₀)): `F (m+1) (proj Y) = (turn A.parent A.vertex : ℤ) * F m (proj P)` | PROVED (`av_loop`) |
| "In case (L), τ_j(P) = −sgn(r)" | `loop_turn : turn A.parent A.vertex = -SignType.sign r` | PROVED (= `LoopAnchor.parent_turn`) |
| "in case (L₀), it is the orientation sign of the parent triangle" | `loopZero_turn : ∃ τ ≠ 0, (∀ i, turn A.parent i = τ) ∧ turn A.parent A.vertex = τ` | PROVED (`A_small_values_i`) |
| "The function C satisfies these hypotheses" | `C_hypotheses : AnchorValuesHypotheses cornerPolygon` | PROVED modulo thm:C-soft (`cornerPolygon_anchorValuesHypotheses_of`) |
| "The same identities hold for A_g at every anchor root other than the soft edge, with the corresponding parent root on the right" | `A_zero : ∀ A a, a ≠ A.softEdge → A_a(Z) = 0`; `A_loop`/`A_loopZero : ∀ A a, a ≠ A.softEdge → ∃! g, a = softParentEdge A.vertex g ∧ A_a(Y) = τ_j(P) · A_g(P)` | PROVED (`av_treeCoefficient_anchor`, `av_A_zero`, `av_A_loop`) |

Companions PROVED: `cornerStateSum_zeroAnchor_of`, `cornerStateSum_loopAnchor_of` (the C identities in labelled form).

**FR-CM-1 (F's domain).**  `F : ∀ n [NeZero n], GenericPolygon n → ℤ`, exactly thm:uniqueness's `F` (the consumer of this row);
"constant on chambers" and "the soft theorem in the form of thm:C-soft" are the fields (a-chamber) and (e) of the accepted
`UniquenessHypotheses`, copied verbatim (so `toAnchorValuesHypotheses` is definitional).  The row does not assume (a-silent),
(b), (c), (d), (f).
**FR-CM-2 (anchors as data).**  Zero/loop anchors are the accepted `ZeroAnchor`/`LoopAnchor`/`LoopAnchorZero` (def:anchors,
SM/Anchors.lean:40-98); the anchor polygon is `A.polygon = softInsertion A.parent A.vertex A.vector A.param`, the parent
`A.parent`, `j = A.vertex`, `τ_j(P) = turn A.parent A.vertex`; the geometric bound `A.bound` with `bound_spec` is "part of the
anchor data" as printed (sm-5:392-395).  The identities are stated at the anchor's OWN parameter `ε = A.param` (the printed
"at the original ε").
**FR-CM-3 (orientation sign of the parent triangle).**  Read as the common sign of the three turns of the generic parent
triangle (lem:chi-basic (i), lem:A-small-values (i): all turns of a (G1) triangle have one nonzero sign); `τ_j(P)` is that sign.
Not read as `sgn rot(P)` (equivalent by lem:rot, unused).
**FR-CM-4 (the A_g clause).**  "every anchor root other than the soft edge" = `a : ZMod (m+1)`, `a ≠ A.softEdge`
(`= softOldIndex A.vertex A.vertex`, def:anchors); "the corresponding parent root" = the unique `g` with
`a = softParentEdge A.vertex g` (thm:A-soft's correspondence, SM/SoftTheoremTree.lean:32-34; return edge ↔ `E_j`), stated with
`∃!` exactly as thm:A-soft.  `A_g = treeCoefficient` at the given (G1) witnesses.
**FR-CM-5 (C on the polygon space).**  "The function C" is `cornerPolygon n : GenericPolygon n → ℤ`, the `Quotient.lift` of
`cornerStateSum` along def:C's cyclic quotient (compatibility = accepted `cornerStateSum_genericShift`, SM/CChamber.lean:1362;
zero below arity 3 where def:C assigns nothing); `cornerPolygon_projection` identifies it with `cornerStateSum` on every
labelled representative, so nothing is lost (the CV/R tail's FR-CC-13 anticipated exactly this adapter).

### Row 127 (sm-6:299-303) → `SM.thm_comparison (hR : hyp_R) : ∀ n [NeZero n] (hn) (P) (hP : Generic P), cornerStateSum hn hP = amplitude P hP.1 hn`

One printed clause, one bare theorem (the shape of the accepted `SM.uniqueness`), hyp:R an explicit parameter.
Companion PROVED: `thm_comparison_polygon_of` — `cornerPolygon n Q = alA_polygonAmplitude hn Q` on `GenericPolygon n`.
**FR-CM-6 (generic polygon).**  "for every generic polygon P" read on generic labelled representatives (every accepted C row's
convention); both sides descend (cor:A-lawful `descends`, `cornerStateSum_genericShift`), so the labelled equality is the
polygon equality (companion).  `[NeZero n]`, `hn : 3 ≤ n` are the presupposition binders of def:C.
**FR-CM-7 (hyp:R).**  `(hR : hyp_R)` explicit (policy `explicit_parameter`; the printed status "hypothesis (d) discharged by
citing Hypothesis R by label"); `hyp_R`'s two-parameter side form is literally `UniquenessHypotheses.triple` with `(tp, tm) =
(t, s)`.  No `Bridge.sm_R` is used inside the row.

### Row 128 (sm-6:313-319) → `SM.cor_C_inherits (hR : hyp_R) : CInheritsData` (Sketch_B.lean:557), 11 fields

`CInheritsData` is the accepted `ALawfulData` FIELD FOR FIELD with `cornerStateSum` for `amplitude` (same binders, same sides,
same signs), minus `root_independent` (A-specific; C has no root) and minus the A-specific per-induced-root sub-clause of the
cusp law; the three Props `CuspLawC`, `ReversalLawC`, `TrianglesC` are the CV/R tail's VERBATIM (see §4).

| cor:A-lawful identity (ALawfulData field, SM/ALawful.lean) | `CInheritsData` field | proof source |
|---|---|---|
| well defined on polygons: `shift_invariant`, `descends` | same, with `(generic_shift k P).mpr hP`; `C' = cornerPolygon n` | `cornerStateSum_genericShift`, `cornerPolygon_projection` |
| `chamber_constant` (labelled and polygon chambers) | same | `cornerStateSum_eq_of_mem_labelledChamber` (CChamber.lean:1366), `prop_C_chamber.constant` |
| `silent` (E), (C) | same | `prop_C_silent.extension/.cut` (CSilent.lean:1846-1852) |
| `flat_law` (`Generic (deletion) ∧ ∀ sRight sLeft …`) | `∃ hQ : Generic (deletion), ∀ sRight sLeft …` (the witness is needed inside `C`) | `cs3_flat_law_C` ← `thm_C_S3` + `generic_deleteVertex` |
| `cusp_law` ((G1) deletion; `∃ b, ∃ κ = ±1, rot jump ∧ law`) | `cusp_law : CuspLawC` — hypothesis `G1 (deletion)`, conclusion `∃ hQ : Generic (deletion), ∃ b … ∃ κ … rot jump ∧ C-law` | `cu_cuspLawC_of` ← `A_lawful.cusp_law` + `thm_comparison_of` + LEAF `cu_cusp_deletion_generic` |
| `vertex_edge_law` (`Generic λ₁ ∧ Generic λ₂ ∧ ∀ s t …`) | same, halves' witnesses `vertex_halves_children hn w hc` | `CS7Data.vertex_edge_law` (tp,tm)=(t,s) |
| `triple_law` | same | `hyp_R` |
| `soft_theorem` (`∃ ε₁ > 0, ∀ ε < ε₁, ∃ hQ, …` in ℚ) | same (`∃ hQ` as in ALawfulData) | `CSoftData.soft_theorem` + `soft_family_generic` (the corner FINAL's `exists_generic` companion, re-proved) |
| `reversal_law` | `ReversalLawC` | `A_lawful.reversal_law` + `thm_comparison_of` at `P`, `P̄` |
| `triangles` | `TrianglesC` | `trianglesC_of` (lem:corner-values (i)) |

**FR-CM-8 (domains and genericity witnesses).**  "on the domains stated there": every argument of an identity is generic
before `C = A` is substituted, as the printed proof requires (sm-6:322-333): sides by `sideTuple.property`, the flat deletion
by lem:children (i) (`generic_deleteVertex`), the halves by lem:children (ii) (`vertex_halves_children`), `P_ε` by
lem:soft-generic (i), `P̄` by `generic_reversal`, `K_{±1}` by lem:star-generic (iii); the cusp deletion by the printed domain
check (LEAF).  Witnesses are asserted (∧ / ∃), never assumed, exactly as in `ALawfulData`.
**FR-CM-9 (cusp law domain).**  Hypothesis "when the deletion satisfies (G1)" = `G1 (deleteVertex w.center j)`; the
conclusion asserts `Generic (deletion)` and the law with `κ = ±1` the rotation jump, both sides at every side parameter, no
emptiness hypothesis (threaded cusps included).  The A-specific "every induced root" sub-clause has no C analogue.
**FR-CM-10 (root independence).**  cor:A-lawful's first sentence "A(P) := A_g(P) (any g) is well defined" has as C-analogue
only cyclic invariance + descent (`shift_invariant`, `descends`); no root field.
**FR-CM-11 (side conventions).**  `C(P_±)` at every pair of side parameters (the accepted C-row convention, equivalent to
def:germ's chamber values by prop:C-chamber, `cornerStateSum_side_eq` SM/HypR.lean); flat sides named by the turn at `j`
(thm:A-S3 / thm:uniqueness (b)), thm:C-S3's `IsRightSide/IsLeftSide` are the same predicates at a side point.

## 2. Proof routes (accepted lemmas by file:line; where the corner rows enter)

### 2.1 Row 122 (sm-5:477-505)

* Abstract identity `F(P_ε) = ((χ₋+χ₊)/2) F(P)` for any `SoftAnchorData` (`av_softAnchor_value`, PROVED): `hF.soft` gives
  `δ_F`; choose `ε' = min(ε, δ_F)/2`; `A.bound_spec` (def:anchors, the lem:soft-generic chamber clause) puts `P_ε` and `P_ε'` in
  one chamber of the polygon space; `hF.chamber` equates `F` there; `hF.soft` at `ε'`.  This is `unA_softAnchor_delta`
  (SM/Uniqueness.lean:324) with `F` in place of `Δ`.  Zero anchors: `softAmplitudeMultiplier_mixed` (SoftAmplitudeSectors.lean:110)
  at `ZeroAnchor.mixed`; loop anchors: `softAmplitudeMultiplier_loop` (:120) at `LoopAnchor.loop`/`LoopAnchorZero.loop`.
* `A_g` clause (`av_treeCoefficient_anchor`, PROVED): thm:A-soft `soft_theorem_treeCoefficient` (SM/SoftTheoremTree.lean:25)
  with `ε0 := A.bound` gives `ε₁` and, at `ε' = min(ε, ε₁)/2`, `∃! g, a = softParentEdge j g ∧ A_a(P_ε') = mult · A_g(P)`
  (plus the three sector forms); `bound_spec`'s LABELLED chamber clause + prop:A-chamber
  `tree_data_labelled_chamber_constant` (SM/TreeChamber.lean:29) makes `A_a` constant between `ε'` and `ε` — the printed
  "every initially nonzero determinant keeps its sign along the connected parameter interval, so prop:A-chamber makes A_g
  constant" (sm-5:498-503); uniqueness of `g` by `softParentEdge_injective` (SoftParentEdges.lean:49).  "Without using root
  independence" — indeed `root_independence` is not used.
* (L₀) turn clause: `subst A.triangle`, `A_small_values_i` (SM/SmallValues.lean via SmallValuesLemma).
* "C satisfies these hypotheses" (`cornerPolygon_anchorValuesHypotheses_of hs`): chamber = `prop_C_chamber.constant`
  transported through `Quotient.inductionOn₂` + `cornerPolygon_projection`; soft = `CSoftData.soft_theorem` — **thm:C-soft
  enters here and only here** (explicit hypothesis `hs : CSoftData`).

### 2.2 Row 127 (sm-6:304-311)

`thm_comparison_of hR h7 hs hCV := uniqueness cornerPolygon (uniquenessHypotheses_C_of hR h7 hs (trianglesC_of hCV))`,
then `cornerPolygon_projection`.  The hypotheses (a)–(f) for `cornerPolygon`:
(a) `cornerPolygon_chamber` (prop_C_chamber, CChamber.lean:1373-1385) and `prop_C_silent` (CSilent.lean:1844-1859), `(s,t) ↦ (tm,tp)`;
(b) `cs3_flat_bridge thm_C_S3` (CS3.lean:2478-2507): unfold `FlatAt` into `hz hb hc hsc` (they coincide, reviewed reading of
thm:C-S3, work/reviews/thm-C-S3.json), get `δ`; represent `sRight`, `sLeft` as side points (`ri_sideTuple_true/false_val`,
RootIndependence.lean:122-128); evaluate the law at the common small parameter `δ/2` on both sides with `IsRightSide/IsLeftSide`
transported by `side_turn_constant` (GermTurnSigns.lean:27); move back along each side by `cornerStateSum_side_eq`
(HypR.lean, prop:C-chamber); the deletion witnesses are proof-irrelevant;
(c) `CS7Data.vertex_edge_law` — **thm:C-S7 enters here** (`h7`), literally the consumer shape (the corner lane's FR-CC-13);
(d) `hR : hyp_R` (HypR.lean:74) — literally `UniquenessHypotheses.triple`;
(e) `cornerPolygon_soft_of hs` — **thm:C-soft enters here**;
(f) `trianglesC_of hCV` — **lem:corner-values (i) enters here** (`hCV.embedded_value`; clause (ii) unused):
`tri_cornerStateSum_crossingFree` (PROVED): for a crossing-free generic `P` with all turns `τ ≠ 0`, `∅` is the unique
decomposition (`Finset.eq_empty_of_isEmpty`, `empty_mem_independentSupports` InterlaceSupports.lean:44), it is uniform (every
corner mark of every carrier is a vertex mark: `mem_ccpCornerList` CarrierCornerPolygon.lean:329, `IsTrueCorner`
CarrierTrueCorners.lean:44, `ccpCornerPolygon_turn_vertex` :598), every carrier has `m_Q = 0`, so `c(Q) = 1` by
`embedded_value` and def:C gives `(−1)^{ℓ(P)}`; `tri_triangle_no_crossing` (`remote` = ¬`adjacent`, Polygon.lean:63-66, `decide`
on ZMod 3); `ℓ(K₁) = 3`, `ℓ(K₋₁) = 0` from lem:star-generic (i)/(iii) (StarGenericLaw.lean).  This is the printed sentence
"Its only decomposition is empty, so def:C gives −1 when ℓ = 3 and +1 when ℓ = 0" made literal.

### 2.3 Row 128 (sm-6:320-372)

`cor_C_inherits_of hR h7 hs hCV`: every field except `cusp_law` is a ≤ 6-line adapter (table in §1); `reversal_law` and
`triangles` substitute `C = A` (thm_comparison_of) into `A_lawful.reversal_law` / use `trianglesC_of`.  `cusp_law`
(`cu_cuspLawC_of`, PROVED modulo the leaf): `A_lawful.cusp_law n w j hf hQ1` gives `b`, uniqueness, `κ`, the rotation jump and
the amplitude law for a generic deletion; the LEAF `cu_cusp_deletion_generic` supplies `Generic (deletion)` (the printed
domain check sm-6:335-359); then `C = A` at the two sides and at the deletion.  The corner rows enter only through
`thm_comparison_of` (and `h7`/`hs` directly for `vertex_edge_law`/`soft_theorem`).

## 3. How hyp:R enters

`hyp_R` (SM/HypR.lean:74, `def … : Prop`) is an explicit parameter of `thm_comparison_of`, `thm_comparison`, `cor_C_inherits_of`,
`cor_C_inherits` — the policy mode `explicit_parameter` and the CV/R tail's expectation `cor_C_inherits (hR : hyp_R)`
(cvtail Statements_FINAL.lean:937, 990).  Inside, it is consumed exactly once, as thm:uniqueness's (d) (`uniquenessHypotheses_C_of`,
field `triple`) and once as `CInheritsData.triple_law`.  Row 122 does not mention R (as printed).  The row-184 assembly
discharges it with `Bridge.sm_R` (cvtail §5) — not this lane's business.

## 4. The row-128 bundle shared with the CV/R tail's row 184 — ADOPT with field-type changes

`CuspLawC`, `ReversalLawC`, `TrianglesC` are adopted VERBATIM from work/drafts/cvtail/Statements_FINAL.lean:874-905 (they are the
three types `corner_laws_and_soft_of` reads: `hinh.cusp_law`, `hinh.reversal_law`, `hinh.triangles`, :973-987) — the
consumer check `example (hinh : CInheritsData) : CuspLawC ∧ ReversalLawC ∧ TrianglesC` (Sketch_B.lean:699) typechecks, so
**`corner_laws_and_soft_of` needs NO change** (its `hinh : CInheritsData` parameter keeps its name and its three field reads).
`CInheritsData` itself REPLACES the cvtail proposal in three fields only (field-TYPE changes, as FR-F-184-4 allows):
`vertex_edge_law : CS7Data` → the `ALawfulData`-shaped law with `Generic λ₁ ∧ Generic λ₂ ∧ ∀ s t …`;
`triple_law : hyp_R` → the `∀ n hn w e f k, TripleAt → ∀ s t, C(P₊) = C(P₋)` form (definitionally `hyp_R` up to argument order);
`soft_theorem : CSoftData` → the `∃ hQ` form of `ALawfulData.soft_theorem`.  Reason: "every identity of cor:A-lawful" is then
literally `ALawfulData` with `C` for `A`, one field per printed identity, no nesting of other rows' bundles (a reviewer compares
the two structures line by line); the cvtail keeps the row bundles `CS7Data`/`CSoftData` as separate fields of
`CornerLawsAndSoftData` anyway.  The cvtail's `CyclicLawC` is subsumed by `shift_invariant` (cvtail discharges `cyclic`
from `cornerStateSum_genericShift` directly, unchanged).  If the judge prefers the cvtail's nesting, the change is again
field-type only (the proofs are `h7`, `hR`, `hs`).

## 5. Unit decomposition (byte-identical skeleton copies of Sketch_B.lean's statements; leaves `sorry`; helpers prefixed)

Check per unit: `cd work/lean && lake env lean ../drafts/comparison/U_<unit>.lean` (18 s warm).  Assembly: concatenate in file order,
clash scan, `#print axioms` (expected [propext, Classical.choice, Quot.sound, SM.lit_homfly]), port after statement review; §0
deleted when the corner module lands; §5 row theorems declared and mapped only then (D-F11/D-F14).  Reassessment rule per unit
(2 attempts / 60 min).

| unit | prefix | content | status | lines | hours |
|---|---|---|---|---|---|
| U-CPOLY | `cp_` | `cornerPolygon`, `cornerPolygon_projection`, `cornerPolygon_chamber` (§1) | DONE | 35 | review 0.5 |
| U-AV | `av_` | row 122: `av_softAnchor_value`, `av_zero/loop`, `av_treeCoefficient_anchor`, `av_A_*`, `av_loopZero_turn`, `anchor_values_of` | DONE | 150 | review 1 |
| U-TRI | `tri_` | `tri_cornerStateSum_crossingFree`, `tri_triangle_no_crossing`, `tri_leftTurns_*`, `trianglesC_of` | DONE (conditional on `CornerValuesData`) | 75 | review 0.5 |
| U-CS3 | `cs3_` | `cs3_param_side`, `cs3_flat_bridge`, `cs3_flat_law_C` | DONE | 55 | review 0.5 |
| U-CMP | — | `uniquenessHypotheses_C_of`, `thm_comparison_of`, `thm_comparison_polygon_of` | DONE | 55 | review 0.5 |
| U-CUSPGEN | `cu_` | LEAF `cu_cusp_deletion_generic` (sm-6:335-359): (G2) of `Q = P(0) ∖ j` at a simple cusp wall with (G1) `Q` | OPEN | 300-500 | 6-10 |
| U-INH | `cu_`/— | `cu_cuspLawC_of`, `cor_C_inherits_of` | DONE modulo U-CUSPGEN | 60 | review 0.5 |
| U-ROWS | — | §5 one-liners at `thm_C_soft`, `thm_C_S7`, `corner_values`; port `SM/AnchorValues.lean`, `SM/Comparison.lean`, `SM/CInherits.lean`; map rows 122/127/128; delete §0 | after rows 105/110/112 | 30 | 1 |
| total | | | 1 leaf open | ≈ 760 + 300-500 new | ≈ 8-14 prover-h + 4 h review/port |

Route for U-CUSPGEN (the printed proof, with the accepted vocabulary): `CuspAt` (CuspDefinition.lean:41) gives `Z_pt =
{{j−1,j,j+1}}`, `Z_c = ∅` (`concurrenceTriples w.center = ∅`), collinearity of `A = μ_{j−1}(0), M = μ_j(0), B = μ_{j+1}(0)` with
`M` outside `[A,B]`; `CuspCase` (:12) says which cusp edge is the longer one containing `[A,B]`.  (G1) of `Q` is the hypothesis.
(G2): mimic `g2_deleteVertex` (SM/DeletionGeneric.lean:31-35, the flat case, where the fused edge is the union `[A,M] ∪ [M,B]`)
with the fused edge now CONTAINED in the longer cusp edge: map the three pairwise-remote edges of `Q` to edges of `P(0)`
(fused ↦ longer cusp edge, others ↦ themselves via `deleteVertex`'s index map), show injectivity (neither cusp edge is an edge
of `Q`), remoteness in `P(0)` (adjacency in `P(0)` of surviving edges ⇔ adjacency in `Q`; the longer cusp edge's neighbours are
the other cusp edge and an edge adjacent to the fused edge), and the common relative-interior point (relative interior of
`[A,B]` ⊆ relative interior of the longer edge) — contradiction with `Z_c = ∅`.  Start by reading `g2_deleteVertex` and the
`concurrenceTriples` membership lemma (GermDefinition.lean:27-36); the flat proof's edge-map bookkeeping should port with the
containment replacing the union.  Fallback if it stalls (2 attempts / 60 min): state `CuspLawC` with the additional
hypothesis `Generic (deletion)` (weaker than printed; disclosed as FR-CM-9′) — `cu_cuspLawC_of` already proves that form —
and keep the leaf as library debt; the CV/R tail's row 184 would then need the same weakening of its `cusp` field.

## 6. Riskiest steps (ranked) and their status

1. **U-CUSPGEN** (the only open leaf): plane geometry with `deleteVertex`'s index bookkeeping; 300-500 lines; precedent
   `g2_deleteVertex` exists for the flat case.  Fallback in §5.
2. **Statement review of `CInheritsData`** — the choice ALawful-shaped vs cvtail-nested (§4) is a judgment call; both are
   field-type-only changes for the consumer.  Mitigation: the docstring names the removed A-specific clauses (FR-CM-9/10).
3. **`AnchorValuesData.loopZero_turn`** reading (FR-CM-3): "orientation sign" as the common turn sign; a reviewer may want
   `sgn rot(P)`; adding `rotationNumber A.parent = (τ : ℝ)` is a 5-line companion via `rotationNumber_triangle`
   (RotationTriangle.lean:25) if requested.
4. **`cornerPolygon` below arity 3** (`fun _ => 0`): irrelevant to every clause (all quantify `3 ≤ n`), disclosed (FR-CM-5).
5. **Unification with the corner lane**: §0 copies `CornerValuesData`, `CS7Data`, `CSoftData` VERBATIM from
   work/drafts/corner/Statements_FINAL.lean (2026-09-15 judge's FINAL); if that lane's shapes move, only §0 and the three
   `_of` signatures change — the proofs consume `embedded_value`, `vertex_edge_law`, `soft_theorem` by name.
6. **Deprecation warning** `dif_pos` (Sketch_B.lean:89): cosmetic; replace by `dite_eq_left`/`dif_pos` alternative at port.
7. Nothing in this lane depends on GAP-2 except through rows 105/110/112 (thm:floor); all four `_of` theorems are
   unconditional library theorems NOW and can be ported after statement review as library material (D-F11/D-F14),
   mapped only when the rows land.
