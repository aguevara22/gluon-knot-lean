# PLAN_FINAL — thm:C-S3 (the flat law) `C(P_right) − C(P_left) = C(P(0) ∖ j)`

Written 2026-09-14 by the judge of the two independent plans (PLAN_A.md / Skeleton_A.lean, PLAN_B.md /
Skeleton_B.lean). Target: `SM.thm_C_S3 : CS3Data`, statement FIXED in `work/drafts/CS3_statement.lean`
(copied verbatim at the end of the skeleton). Source: reference/SM/sm-4-knotlaws.tex:153-229.
Skeleton: `work/drafts/cs3/Skeleton_FINAL.lean` — **1376 lines, 93 declarations, 10 sorried**, checked
with `cd work/lean && lake env lean ../drafts/cs3/Skeleton_FINAL.lean` (no errors, no warnings other than
`declaration uses sorry`); `#print axioms SM.thm_C_S3` = `propext, sorryAx, Classical.choice, Quot.sound,
SM.lit_homfly` (the permitted literature axiom of axiom-policy.json). `thm_C_S3` is PROVED from the chain;
every `sorry` is a leaf of the chain.

## 0. Judgement

| | Plan A | Plan B |
|---|---|---|
| (a) correctness against the fixed statement | 9 | 9 |
| (b) provability with the existing library | 8 | 7 |
| (c) minimality | 8 | 7 |
| **winner** | **A** (base route) | grafts taken |

Both routes are mathematically sound and, at the two genuinely new geometric inputs, identical: the
positive lift of a side copy is compared with the deletion copy through the *centre* corner polygon
(a `Deform` along the accepted `cornerFamily` towards the side, generic at every time because at `u > 0`
it is a re-indexing of an accepted carrier polygon and at `u = 0` it is a re-indexing (`q ≠ Q_*`) or a
positive-flat subdivision (`q = Q_*`) of the generic deletion copy's polygon), and the subdivision is a
`Reparam` of the one-component positive diagram. Neither assigns a state-sum value at the flat centre;
both reduce the two side parameters of the fixed statement to one by chamber constancy along a side
(prop:C-chamber) plus turn constancy. Neither has hidden assumptions. Both inherit that the two
subdivision lemmas (genericity, `Reparam`) do not exist in the library (`grep` over `SM/*.lean` for
`appendVertex`/`insertVertex`/`subdiv` in the link layer: nothing; `StrandMap.seg_eq` demands segment
equality up to a plane bijection, so a subdivision is not a `StrandMap` and `pullback` is unusable).

Why A: its skeleton has already closed exactly the dependent-type bookkeeping that B left open — the
three state-sum reindexings (A sums the lem:C-X1 summand as a *total* function over all
`Finset (Crossing P)` and reindexes with `Fintype.sum_equiv` along a crossing equivalence, sidestepping
`attach`/`Finset.sum_nbij`/`dite` entirely; B's F7.1/F7.2 are 120 open lines of that), the geo ↔ accepted
bridge as *equalities* (`geoCornerPolygon_eq_generic`, `carrierCrossings_eq_geo`; B's F2.1/F2.3 open) and
the `q ≠ Q_*` deletion re-indexing on geo polygons (`reindexed_deletion_other`; B's F6c open). B had
instead closed the geometric assembly (F6e/F6f/F6g), which is low-risk on A's geo-level statements — and
indeed the judge closed all of it in the final skeleton (see §3). B's abstract transport layer
(`refCoefficient`, T1–T4) is elegant but an extra layer; A's route is more direct.

Grafts from B into the final: (1) `regular_adjacent_meet` (B's L0.7a) as an isolated lemma — the one
genuinely geometric fact behind both new link-layer lemmas (the label pairs that become non-adjacent
under the subdivision do not meet); (2) the `hoff` hypothesis on the subdivision `Reparam` (B's L0.8 shape;
A's statement omitted it — true but harder, since `hoff` would have to be re-derived from `hX'.tail_off`);
(3) the off-edge clause bundled into the flat-subdivision statement (B's F6d shape), so both consumers get
it; (4) B's `single_generic_centre` / `planarIsotopic_centre_del` / `planarIsotopic_side_centre` as the
templates for A's assembly lemmas (now proved). Judge's additions: the circle map of the subdivision
stated as its own definition `subdivPt` with three lemmas (bijective, key-monotone, same trace), so the
`Reparam` prover only assembles `ReparamData`; segment helpers for `appendVertex`; existential size in
the list-surgery outputs (no `recastTuple` juggling).

## 1. The route (skeleton order; ✓ = proved in Skeleton_FINAL.lean, ◻ = `sorry`)

Printed proof (sm-4:160-229) → Lean:
1. eq. ccf:selector-sum: accepted `C_X1.selector_form` → `cornerStateSum_eq_sum_stateTerm` ✓ (total
   function `stateTerm`, zeros off `Ind`).
2. lem:flat-sides identifies crossings / interlacement / independent supports: `independent_supports_of`
   (FlatCarriers:510) → `stateTerm_law` ✓, `sum_finsetMapEquiv` ✓ along `crossingTransport (hs b)`,
   `fusionCrossingEquiv`.
3. cor:flat-carriers (i): carriers correspond → `sideCarrierEquiv` ✓, `deletionCarrierEquiv` ✓ (deletion
   facts indexed by the centre carrier `q` through `(deletionCarrierEquiv hF).symm q`).
4. cor (ii) slots agree → `card_geoCarrierCrossings_side/deletion` ✓, `rotationNumber_side/deletion` ✓.
5. "lc:presentations and lp:core identify the H polynomials" (NOT in the library) → lit:homfly
   `homfly_planar` on: side lift = `Deform` along `sideCornerPath` = centre diagram (`homfly_side_eq_centre` ✓)
   = `Reparam`/re-indexing = deletion lift (`homfly_deletion_eq_centre` ✓); `c(Q)` read on geo data
   (`cornerCoefficient_eq_geo` ✓) → `cornerCoefficient_side_eq_deletion` ✓ → `cornerProduct_side_eq_deletion` ✓.
6. cor (iii) selectors: `selector_other` ✓, `selector_central` ✓ → `wind_law` ✓ (`Fintype.prod_eq_mul_prod_compl`).
7. Sum: `flat_law_at` ✓; two side parameters → one: `cornerStateSum_side_const` ✓ (GermSides +
   `cornerStateSum_eq_of_mem_labelledChamber`), `isLeftSide_of_side` ✓ (`generic_family_turn_constant`);
   `thm_C_S3` ✓ with radius `min δC δF` (`flat_carriers`, `exists_flatFamilyData`).

### Section A — link-layer lemmas on one-component shadows (general)

| lemma | status |
|---|---|
| `Reindexed.trans`, `Reindexed.symm`, `reindexed_recastTuple`, `edgeSegment_recastTuple`, `getElem_congr_lists` | ✓ |
| `regular_adjacent_meet` (graft B) | ◻ U1 |
| `edgeSegment_appendVertex_old` | ✓ |
| `edgeSegment_appendVertex_last_subset`, `edgeSegment_appendVertex_new_subset` | ✓ |
| `edgeSegment_appendVertex_union` | ◻ U1 |
| `appendVertex_new_pairs_disjoint` | ◻ U1 |
| `Link.single_generic_shift`, `Link.single_generic_of_reindexed`, `Link.homfly_positiveDiagram_single_of_reindexed` | ✓ |
| `Link.deform_positiveDiagram_single_of_family`, `Link.homfly_positiveDiagram_single_of_family` | ✓ |
| `Link.single_generic_appendVertex` | ◻ U1 |
| `Link.subdivPt` (def), `Link.traversalEvaluation_subdivPt`, `Link.traversalBetween_subdivPt` | ✓ |
| `Link.subdivPt_bijective`, `Link.traversalKey_subdivPt_lt_iff` | ◻ U2 |
| `Link.reparam_positiveDiagram_single_appendVertex` | ◻ U2 |
| `Link.homfly_positiveDiagram_single_appendVertex` | ✓ |
| `exists_appendVertex_of_erase_flat` | ◻ U3 |

### Section B — geo data = accepted data on a generic polygon: all ✓
`geoCornerCount_eq_generic`, `geoCornerPolygon_eq_generic`, `geoCornerCount_ge_three_generic`,
`carrierShadow_eq_single_geo`, `single_geo_generic`, `positiveLift_eq_geo`, `cornerSelector_recastTuple`,
`carrierWeight_eq_cornerSelector`, `carrierWeight_eq_geoCarrierSelector`, `wind_eq_prod_geoCarrierSelector`,
`carrierCrossings_eq_geo`, `carrierCrossingCount_eq_geo`, `carrierRotation_eq_geo`, `cornerCoefficient_eq_geo`.

### Section C — carrier bijections at one `t`: all ✓
`sideCarrierEquiv` (+`_owner`, `_central`), `deletionCarrierEquiv` (+`_owner`, `_deletionCopy`,
`_symm_central`), `card_geoCarrierCrossings_side/deletion`, `rotationNumber_side/deletion`.

### Section D — the centre corner polygons

| lemma | status |
|---|---|
| `geoCornerCount_side`, `geoCornerCount_ge_three_centre`, `reindexed_deletion_other` | ✓ |
| `mu_j_unique_edge` | ◻ U3 |
| `exists_appendVertex_central` | ◻ U3 |
| `centre_shadow_generic`, `homfly_deletion_eq_centre` | ✓ (closed by the judge from the U1/U3 statements) |

### Section E — the deformation through the flat centre: all ✓
`FlatFamilyData`, `exists_flatFamilyData`, `continuousAt_markPointOn_of`, `sideParamPath` (+`_zero`, `_one`,
`continuous_`, `abs_…_lt`, `_eq_sideTime`), `sideCornerPath` (+`_zero`, `_one`),
`geoCornerPolygon_side_eq_cornerFamily`, `cornerFamily_side_generic`, `geoDiagram_side_eq_cornerFamily`,
`homfly_side_eq_centre`.

### Sections F–I — coefficients, selectors, sums, reduction, theorem: all ✓
`cornerCoefficient_side_eq_deletion`, `cornerProduct_side_eq_deletion`, `wind_side_eq_prod`,
`wind_deletion_eq_prod`, `selector_other`, `selector_central`, `wind_law`, `stateTerm` (+`_of_not`,
`_of_decomposition`), `cornerStateSum_eq_sum_stateTerm`, `finsetMapEquiv`, `sum_finsetMapEquiv`,
`stateTerm_law`, `flat_law_at`, `cornerStateSum_side_const`, `side_turn_const`, `isLeftSide_of_side`,
`CS3Data`, `thm_C_S3`.

## 2. The ten open lemmas — exact statements, proof sketches, estimates

All in `namespace SM`, `open Link Carrier GeoCarrier`, `Classical.propDecidable` local instance.

### U1 — subdivision genericity (pure polygon geometry, ~310 lines)

```lean
theorem regular_adjacent_meet {k : ℕ} [NeZero k] {Q : LabelledTuple k} (hQ : Regular Q)
    (i : ZMod k) {x : Plane} (hx : x ∈ edgeSegment Q i) (hx' : x ∈ edgeSegment Q (i + 1)) :
    x = Q (i + 1)
```
Sketch (40): `obtain ⟨s,_,_,hs⟩ := hx; obtain ⟨t,_,_,ht⟩ := hx'`. Case `det (edge Q i) (edge Q (i+1)) ≠ 0`:
`intersection_parameters_unique` (Segment.lean:55) as in `Link.consecutive_meet` (LinkPositiveLift:698)
with the second solution `(s,t) = (1,0)`. Case `det = 0`: `RegularPair` (`hQ (i+1)`, `regular_iff_edges`)
excludes antiparallel and zero, so `edge Q (i+1) = c • edge Q i` with `c > 0` (`principalAngle_zero_iff_det_zero`
+ `principalAngle_eq_zero_iff`, as in `flat_of_turn_eq_zero`); then `Q i + s•E = Q(i+1) + t•c•E =
Q i + (1 + t c)•E` with `E ≠ 0` gives `s = 1 + tc ≤ 1`, so `t = 0` and `x = Q (i+1)`.

```lean
theorem edgeSegment_appendVertex_union {m : ℕ} [NeZero m] (X : LabelledTuple m) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    edgeSegment X (-1) =
      edgeSegment (appendVertex X u) (insertIndex (-1 : ZMod m)) ∪
        edgeSegment (appendVertex X u) (insertedIndex m)
```
Sketch (30): `⊇` by the two proved `_subset` lemmas; `⊆`: a point `edgePoint X (-1) s` with `s ≤ u` is
`edgePoint X' (insertIndex (-1)) (s/u)` (if `u = 0` then `s = 0`, the point is `X (-1)`, parameter `0`),
with `s ≥ u` it is `edgePoint X' (insertedIndex m) ((s-u)/(1-u))` (if `u = 1`, parameter `0` again);
`edge_appendVertex_last/new`, `appendVertex_old/new`, `smul_smul`, `div_mul_cancel₀`.

```lean
theorem appendVertex_new_pairs_disjoint {m : ℕ} [NeZero m] (hm : 3 ≤ m) {X : LabelledTuple m}
    (hX : Regular X) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (∀ x, x ∈ edgeSegment (appendVertex X u) (insertIndex (-1 : ZMod m)) →
      x ∉ edgeSegment (appendVertex X u) (insertIndex (0 : ZMod m))) ∧
    (∀ x, x ∈ edgeSegment (appendVertex X u) (insertedIndex m) →
      x ∉ edgeSegment (appendVertex X u) (insertIndex (-2 : ZMod m)))
```
Sketch (60): first clause: `x ∈ [X(-1), p] ⊆ E_{-1}` (`_last_subset`) and `x ∈ E_0`
(`edgeSegment_appendVertex_old` with `0 ≠ -1` from `hm`), so `x = X 0` by `regular_adjacent_meet hX (-1)`
(`-1 + 1 = 0`); but `X 0 = X(-1) + s•(u•E_{-1})` with `s ≤ 1` forces `s u = 1` (`edgePoint_injective`
on `E_{-1} ≠ 0`), contradicting `u < 1`. Second clause symmetric with `E_{-2}`, `E_{-1}` meeting only at
`X(-1)`, and `X(-1) ∈ [p, X 0]` forcing `u + s(1-u) = 0`, contradicting `u > 0`.

```lean
theorem Link.single_generic_appendVertex {m : ℕ} [NeZero m] (hm : 3 ≤ m) (X : LabelledTuple m)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hX : (Shadow.single ⟨m, hm, X⟩).Generic)
    (hoff : ∀ e : ZMod m, e ≠ -1 → edgePoint X (-1) u ∉ edgeSegment X e) :
    (Shadow.single ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩).Generic
```
Sketch (180): `Shadow.single_generic_of` (LinkPositiveLift:160) in label form. Read the label-level facts of
`hX` through `Shadow.single_incidentTail_iff/single_adjacent_iff/single_seg/single_dir/single_interior`
(as `crossingGeometry_of_single_generic`, CChamber:582, does). Labels of `ZMod (m+1)` by
`insertion_indices_exhaust`: `insertIndex i` (`i ≠ -1`: `edgeSegment_appendVertex_old`,
`edge_appendVertex_old`), `insertIndex (-1)` (`_last_subset`, `edge_appendVertex_last`), `insertedIndex m`
(`_new_subset`, `edge_appendVertex_new`). `regular`: `regular_appendVertex`. `tail_off`: vertices
`appendVertex_old/new`; an old vertex on an old edge: `hX.tail_off`; an old vertex on a half-edge lies on
`E_{-1}` (subset lemmas), so by `hX.tail_off` it is `X (-1)` or `X 0`, and incidence with the half-edge
follows unless it is the wrong end, excluded by parameter comparison (`edgePoint_injective`, `u ∈ (0,1)`);
the new vertex `p` on an old edge `e ≠ -1`: `hoff`; `p` on a half-edge: incident. `transverse`: two old
labels: adjacency in `ZMod (m+1)` of `insertIndex i, insertIndex i'` (both `≠ -1`) agrees with adjacency
in `ZMod m` (values `< m - 1`, differences in `(-(m-1), m-1)`), so `hX.transverse`; a half-edge against an
old edge `i`: the meeting point is in `E_{-1} ∩ E_i`, and the pair `(-1, i)` is non-adjacent in `ZMod m`
unless `i ∈ {0, -2}` (then `appendVertex_new_pairs_disjoint` contradicts the meeting) or `i = -1`
(excluded), so `hX.transverse` gives `det E_{-1} E_i ≠ 0` and the half-edge direction is `u•E_{-1}` or
`(1-u)•E_{-1}` (`det_smul_left`); the two half-edges are adjacent. `no_triple`: interiors of new edges
lie in interiors of old edges (`edgeInterior` versions of the subset lemmas, or via
`remote_closed_point_interior`), the two half-edges have disjoint interiors (parameters `< u` vs `> u` on
`E_{-1}`), so three distinct new labels give three distinct old labels unless two are the half-edges —
then their interiors are disjoint — and `hX.no_triple` closes.

### U2 — subdivision Reparam (~400 lines; may assume the U1 statements)

```lean
theorem Link.subdivPt_bijective {m : ℕ} [NeZero m] {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    Function.Bijective (subdivPt (m := m) hu0 hu1)
```
Sketch (60): explicit inverse `ψ : TraversalPoint (m+1) → TraversalPoint m`: `(j, s) ↦` if
`j = insertedIndex m` then `(-1, u + (1-u) s)`, else if `j = insertIndex (-1)` then `(-1, u s)`, else
`((j.val : ZMod m), s)` (`j.val < m` by `insertion_indices_exhaust`, `insertIndex_val`); `ψ ∘ subdivPt = id`
and `subdivPt ∘ ψ = id` by `split_ifs`, `insertIndex_injective`, `insertIndex_ne_inserted`, `Subtype.ext`,
`div_mul_cancel₀`, `mul_div_cancel₀`; or prove injective + surjective directly. Statement of `subdivPt`
(proved def, Skeleton_FINAL.lean §A): `(i,s) ↦ (insertIndex i, s)` for `i ≠ -1`; `(-1, s) ↦
(insertIndex (-1), s/u)` for `s < u`; `(-1, s) ↦ (insertedIndex m, (s-u)/(1-u))` for `s ≥ u`.

```lean
theorem Link.traversalKey_subdivPt_lt_iff {m : ℕ} [NeZero m] {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (p q : TraversalPoint m) :
    traversalKey (subdivPt hu0 hu1 p) < traversalKey (subdivPt hu0 hu1 q) ↔
      traversalKey p < traversalKey q
```
Sketch (80): `traversalKey (i, s) = i.val + s` (Traversal.lean:17). Define the auxiliary real map
`κ : ℝ → ℝ` on `[0, m)`: identity on `[0, m-1)`, `x ↦ (m-1) + (x-(m-1))/u` on `[m-1, m-1+u)`, `x ↦ m +
(x-(m-1)-u)/(1-u)` on `[m-1+u, m)`; show `traversalKey (subdivPt p) = κ (traversalKey p)` by cases
(`insertIndex_val`, `insertedIndex_val`, `zmod_val_neg_one`) and `κ` strictly increasing (piecewise, with
the values at the two break points agreeing: `κ(m-1) = m-1`, `κ(m-1+u) = m`). Alternatively case on
`traversalKey_lt_iff` (Traversal.lean) for both sides: label comparison (`insertIndex_val`,
`insertedIndex_val`, `zmod_val_neg_one`: the new labels of the closing edge have values `m-1`, `m`, every
other label keeps its value `< m-1`) and, on equal labels, parameter comparison (`div_lt_div_iff_of_pos_right`,
`sub_lt_sub_iff_right`).

```lean
theorem Link.reparam_positiveDiagram_single_appendVertex {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (X : LabelledTuple m) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hX : (Shadow.single ⟨m, hm, X⟩).Generic)
    (hoff : ∀ e : ZMod m, e ≠ -1 → edgePoint X (-1) u ∉ edgeSegment X e)
    (hX' : (Shadow.single ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩).Generic) :
    Reparam ((Shadow.single ⟨m, hm, X⟩).positiveDiagram hX)
      ((Shadow.single ⟨m + 1, Nat.le_succ_of_le hm, appendVertex X u⟩).positiveDiagram hX')
```
Sketch (260): `⟨{ e := Equiv.refl _, φ := fun _ => Equiv.ofBijective _ (subdivPt_bijective hu0 hu1),
between := fun _ => traversalBetween_subdivPt hu0 hu1, eval_eq := fun _ => traversalEvaluation_subdivPt X hu0 hu1,
over_map := …, over_surj := … }⟩` (`ReparamData`, LinkMoves.lean:370; `Diagram.Γ.Pt` is `Σ i : Fin 1, TraversalPoint`,
`Shadow.single_pt_ext` (CChamber:675) reduces equalities of points to their second components).
`over_map`: for a crossing `x = {⟨0,a⟩, ⟨0,b⟩}` of `single X` (`Shadow.single_isCrossing_iff`: `IsCrossing X {a,b}`,
`a, b` remote), with over strand `o` (say `a`) and `z := crossingPoint x = edgePoint X a (crossingParam)`
(`crossingParam_spec`), define the new labels `a' b'`: `insertIndex a` if `a ≠ -1`; if `a = -1`, the half-edge
containing `z` (`edgeSegment_appendVertex_union`; `z ≠ p` since `p ∉ E_b` by `hoff` while `z ∈ E_b`, so the
half-edge is determined and `z` is interior to it). `{a', b'}` is a crossing of `appendVertex X u`: non-adjacent
(`insertIndex` preserves non-adjacency off `-1`; against a half-edge, `b ∉ {0, -2}` because `{-1, b}` is remote
in `ZMod m`), meeting at `z`. Its positive over strand is `a'` because `det (edge X' a') (edge X' b') =
c • det (edge X a) (edge X b)` with `c > 0` (`edge_appendVertex_old_scaled`, `edge_appendVertex_new`,
`det_smul`), and the over strand of a positive diagram is the unique strand with positive determinant
(`Shadow.positiveDiagram_det_pos`, `positiveDiagram_isPositive`; `det_swap` for uniqueness). The over-visit
point: `visitPt` has parameter `crossingParam'` with `edgePoint X' a' crossingParam' = z` (`crossingParam_spec`,
`Generic.common_point_unique`), and `subdivPt (a, crossingParam) = (a', rescaled)` by `edgePoint_injective` on
the nonzero edge `a'` (template `shiftPullback_overVisit_snd`, CChamber:762-817). `over_surj`: a crossing
`x' = {a', b'}` of the subdivision maps to the old labels (`insertedIndex m ↦ -1`, `insertIndex i ↦ i`); the
segments are contained (`edgeSegment_appendVertex_old/last_subset/new_subset`), the old pair is remote unless
`x'` is `{insertIndex (-1), insertIndex 0}` or `{insertedIndex m, insertIndex (-2)}` (their segments do not
meet, `appendVertex_new_pairs_disjoint`) or the two half-edges (adjacent), so `x'` comes from the crossing
`{a, b}` of `X` and the same bookkeeping applies. Fallbacks: (a) a general lemma "a bijection of the
traversal circle of a one-component positive diagram preserving `traversalKey`-order and the trace, and
mapping crossing points to crossing points, is a `Reparam`" (same content, reusable); (b) state for
`insertVertex X i t₀ = appendVertex (shift (i+1) X) t₀` if convenient (interchangeable through
`single_generic_shift`/`reparam_positiveDiagram_single_shift`).

### U3 — flat-vertex list surgery and the point `μ_j` (~290 lines)

```lean
theorem exists_appendVertex_of_erase_flat {α β : Type*} [BEq α] [LawfulBEq α]
    (f : α → Plane) (L : List α) [NeZero L.length] (hnd : L.Nodup) {x : α} (hx : x ∈ L)
    (hflat : ∀ k : ZMod L.length, L[k.val]'(ZMod.val_lt k) = x →
      ∃ s : ℝ, 0 < s ∧ edge (markPolygon f L) k = s • edge (markPolygon f L) (k - 1))
    (g : α → β) (f' : β → Plane) (hf' : ∀ a ∈ L, a ≠ x → f' (g a) = f a)
    (L' : List β) [NeZero L'.length] (hL' : (L.erase x).map g ~r L') :
    ∃ (m : ℕ) (_ : NeZero m) (Q : LabelledTuple m) (u : ℝ), 0 < u ∧ u < 1 ∧
      Reindexed (markPolygon f' L') Q ∧ Reindexed (appendVertex Q u) (markPolygon f L) ∧
      edgePoint Q (-1) u = f x
```
Sketch (120): copy the accepted proof of `rotationNumber_erase_flat` (FlatCarriers.lean:4164-4283) up to
`h6`/`hx'`/`ht0`/`ht1` and stop before the `calc`. Witnesses: `m := (L₂ ++ L₁).length` (instance `hMne`),
`Q := markPolygon f (L₂ ++ L₁)`, `u := 1 / (1 + s)`. First `Reindexed`: `h1.symm.trans (h2.symm.trans (h3 ▸ h4))`
(`Reindexed.symm/.trans` of Skeleton_FINAL §A; `h3 : markPolygon (f' ∘ g) (L₁ ++ L₂) = markPolygon f (L₁ ++ L₂)`).
Second: `h6.trans h5.symm`. Point: `hx'`. Drop `hreg` (only used by `rotationNumber_appendVertex`).

```lean
theorem mu_j_unique_edge (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (hS_D : IsDecomposition hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S))
    (e e' : ZMod (geoCornerCount (flatDeletionCG hn g j hz hb hc)
      (deletionSupport hn g j hz hb hc S) (deletionCopyThroughJ hn g j hz hb hc S)))
    (he : g.center j ∈ edgeSegment (geoCornerPolygon (flatDeletionCG hn g j hz hb hc)
      (deletionSupport hn g j hz hb hc S) (deletionCopyThroughJ hn g j hz hb hc S)) e)
    (he' : g.center j ∈ edgeSegment (geoCornerPolygon (flatDeletionCG hn g j hz hb hc)
      (deletionSupport hn g j hz hb hc S) (deletionCopyThroughJ hn g j hz hb hc S)) e') :
    e = e'
```
Sketch (100): `rw [geoCornerPolygon_eq_generic hn (generic_deleteVertex …), edgeSegment_recastTuple] at he he'`
(the `flatDeletionCG`/`generic_crossingGeometry` proofs coincide by proof irrelevance) to land on the accepted
`ccpCornerPolygon hn hP S_D qD`, `qD := geoComponentEquivGeneric … (deletionCopyThroughJ …)`, labels
`ê := Equiv.cast … e`, `ê'`. `by_contra hne`; `by_cases hadj : adjacent ê ê'`. Not adjacent:
`Link.nonadjacent_meet_crossing hn hP S_D qD hS_D hadj he he'` gives a deletion crossing `c` with
`g.center j = crossingPoint c`; `c = fusionCrossingEquiv … c₀` (`Equiv.surjective`), `crossingPoint_fusion`
(FusionCrossions:42) makes `g.center j = crossingPoint c₀` at the centre, contradicting
`(flat_germ_spatial_data (by omega) g hz hb hc g.zeroParameter).2.2 c₀ j` (`g.curve g.zeroParameter = g.center`
by `rfl`/`WallGerm.curve_zero`). Adjacent with `ê' = ê + 1` (or symmetric): `Link.consecutive_meet` gives
`g.center j = ccpCornerPolygon … (ê+1) = ` the point of the deletion corner mark `b := ccpCornerMark … (ê+1)`
(`ccpCornerPolygon_apply`), `b ∈ ccpCornerList = geoComponentCornerList D …` (`geoComponentCornerList_eq_generic`,
`List.getElem_mem`); by `Cycle.coe_eq_coe.mp hF.central_vs_deletion_through_mu_j.2.2.1` and
`List.IsRotated.mem_iff`, `List.mem_map`, `List.mem_erase_of_ne`: `b = delMark a` with `a` a centre corner,
`a ≠ Sum.inl j`; `deletion_mark_point` (FlatCarriers:4285) gives `g.center j = ` centre point of `a`: `a = Sum.inl k`
with `k ≠ j` contradicts `(flat_center_geometry (by omega) hz hb).1` (injectivity; `geoMarkPosition_evaluation_vertex`),
`a = Sum.inr v` contradicts the spatial data again (`geoMarkPosition_evaluation_visit`). Then `e = e'` from `ê = ê'`
(`Equiv.injective`).

```lean
theorem exists_appendVertex_central (hF : FlatCarriersData hn g j hz hb hc t hs S)
    (hS_D : IsDecomposition hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)) :
    ∃ (m : ℕ) (_ : NeZero m) (Q : LabelledTuple m) (u : ℝ), 0 < u ∧ u < 1 ∧
      Reindexed (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (deletionCopyThroughJ hn g j hz hb hc S)) Q ∧
      Reindexed (appendVertex Q u)
        (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S (centralCarrierThroughJ hn g j hz hb hc S)) ∧
      edgePoint Q (-1) u = g.center j ∧
      (∀ e : ZMod m, e ≠ -1 → edgePoint Q (-1) u ∉ edgeSegment Q e)
```
Sketch (70): `exists_appendVertex_of_erase_flat` applied exactly as `rotationNumber_erase_flat` is applied in
`rotationNumber_deletionCopyThroughJ` (FlatCarriers:4324-4381): `f := fun m => traversalEvaluation g.center
(geoMarkPosition (flatCentreCG …) m)`, `L := geoComponentCornerList (flatCentreCG …) S (centralCarrierThroughJ …)`,
`geoComponentCornerList_nodup`, `x := Sum.inl j` with `(mem_geoComponentCornerList _ _ _ _).mpr ⟨rfl, isTrueCorner_vertex S j⟩`,
`hflat k hk := flat_of_turn_eq_zero hregC ((hF.turns_nonzero.1 _ k).mpr hk)` where `hregC := (regular_iff_edges _).mpr
fun k => ⟨hF.nonzero_segments.2.1 _ k, hF.no_antiparallel.1 _ k⟩`, `g := delMark hn g j hz hb hc`, `f' := fun m =>
traversalEvaluation (deleteVertex g.center j) (geoMarkPosition (flatDeletionCG …) m)`, `hf' a _ ha := deletion_mark_point … a ha`,
`L' := geoComponentCornerList (flatDeletionCG …) _ (deletionCopyThroughJ …)`, `hL' := Cycle.coe_eq_coe.mp
hF.central_vs_deletion_through_mu_j.2.2.1`. The two `Reindexed` and the point are the outputs
(`geoCornerPolygon_eq_markPolygon` is `rfl`; `f (Sum.inl j) = g.center j` by `geoMarkPosition_evaluation_vertex`).
Off-edge clause: `obtain ⟨hm, r, hr⟩ := h1` (first `Reindexed`), `subst hm`, so `Q = shift r' Q_D`
(`reindexed_eq_shift`); if `μ_j ∈ edgeSegment Q e` then `μ_j ∈ edgeSegment Q_D (e + r')` (`edgeSegment_shift`) and
also `μ_j = edgePoint Q (-1) u ∈ edgeSegment Q (-1) = edgeSegment Q_D (-1 + r')`; `mu_j_unique_edge` gives
`e + r' = -1 + r'`, so `e = -1`, contradiction.

## 3. What the judge closed beyond the two skeletons (all ✓ in Skeleton_FINAL.lean)

`edgeSegment_appendVertex_old` (simp), `edgeSegment_appendVertex_last_subset`, `edgeSegment_appendVertex_new_subset`,
`Link.traversalEvaluation_subdivPt`, `Link.traversalBetween_subdivPt`, `sideCornerPath` (+`_zero`, `_one`),
`geoCornerPolygon_side_eq_cornerFamily` (`funext`, `erw [markPolygon_apply]` — plain `rw` fails because `k : ZMod
(geoCornerCount …)` is only defeq to `ZMod (cornerList).length` —, `markPointOn_side`, `getElem_congr_lists`
along `geoComponentCornerList_markTransport`, `List.getElem_map`, `zmod_val_cast` with the size equation passed
explicitly), `cornerFamily_side_generic`, `geoDiagram_side_eq_cornerFamily`, `centre_shadow_generic`,
`homfly_deletion_eq_centre` (the `(deletionCarrierEquiv …).symm Q_*` in dependent positions is handled by
`generalize hqD : … = qD; rw [deletionCarrierEquiv_symm_central] at hqD; subst hqD`), `homfly_side_eq_centre`.
So route A's former "U4" (side identification + assembly, ~300 lines) is done; the two big geometric inputs and the
list surgery remain.

## 4. Prover units (independent; each may assume the *statements* of the others' lemmas)

| unit | lemmas | may assume | est. new lines |
|---|---|---|---|
| **U1 subdivision genericity** | `regular_adjacent_meet`, `edgeSegment_appendVertex_union`, `appendVertex_new_pairs_disjoint`, `Link.single_generic_appendVertex` | library only (+ the proved helpers of §A) | 310 |
| **U2 subdivision Reparam** | `Link.subdivPt_bijective`, `Link.traversalKey_subdivPt_lt_iff`, `Link.reparam_positiveDiagram_single_appendVertex` | U1 statements (`regular_adjacent_meet`, `edgeSegment_appendVertex_union`, `appendVertex_new_pairs_disjoint`) + proved helpers | 400 |
| **U3 list surgery and μ_j** | `exists_appendVertex_of_erase_flat`, `mu_j_unique_edge`, `exists_appendVertex_central` | library only (+ `Reindexed.trans/symm`, `edgeSegment_recastTuple`, `geoCornerPolygon_eq_generic` of the skeleton) | 290 |

Dependency order for the final assembly: U1 → U2 (U2 uses U1's disjointness); U3 independent. Total new ≈ 1000
lines; finished module ≈ 2350 lines.

## 5. Risks and fallbacks (updated)

1. **U2 `reparam_positiveDiagram_single_appendVertex`** (the long pole, ~260 lines of `over_map`/`over_surj`
   bookkeeping). Mitigated: the circle map, its order preservation and its trace are separate lemmas (two of them
   already proved); the template `shiftReparamData`/`shiftPullback_overVisit_snd` (CChamber:762-846) shows the
   `visitPt`/`crossingParam_spec`/`edgePoint_injective` pattern; `Shadow.single_pt_ext` reduces point equalities.
   Fallback: the general "order- and trace-preserving circle bijection is a Reparam" lemma (§2, U2).
2. **U1 `single_generic_appendVertex`** (~180 lines of label case analysis in `ZMod (m+1)` vs `ZMod m`).
   Mitigated by the segment helpers and `appendVertex_new_pairs_disjoint`. Fallback: prove `Shadow.Generic` of
   the centre corner polygon directly from the flat-centre ambient geometry by porting
   `ccpCornerPolygon_tail_off/_transverse/_no_triple` (LinkPositiveLift:520-580) to `CrossingGeometry` (~400
   lines) — only if U1 stalls; it would also remove the need for `hoff` in U2.
3. **U3 `mu_j_unique_edge`** (~100 lines; the cycle-membership bookkeeping `List.IsRotated.mem_iff`,
   `List.mem_map`, `List.mem_erase_of_ne` and the recast to `ccpCornerPolygon`). Fallback: state the two cases
   as separate lemmas (`mu_j_not_crossingPoint_deletion`, `mu_j_not_corner_deletion`) and prove the corner case on
   the *mark list* (`geoComponentMarkList`, field `.2.1` of `central_vs_deletion_through_mu_j`) instead of the
   corner list.

Secondary: the existential size `∃ (m) (_ : NeZero m) (Q : LabelledTuple m)` in U3's outputs is consumed by
`subst` in the (proved) consumers — verified to typecheck; `NeZero` is a `Prop` class so the duplicate local
instance is harmless.

## 6. Reuse list

As in PLAN_A.md §2 (all names verified in work/lean), plus: `Link.consecutive_meet` (LinkPositiveLift:698),
`Link.nonadjacent_meet_crossing` (:520), `intersection_parameters_unique` (Segment.lean:55),
`flat_germ_spatial_data` (FlatSpatial:23), `flat_center_geometry` (FlatCenter:30), `crossingPoint_fusion`
(FusionCrossings:42), `deletion_mark_point` (FlatCarriers:4285), `flat_of_turn_eq_zero` (:4312),
`geoComponentCornerList_markTransport` (:1631), `markPointOn_side` (:4460), `cornerFamily_eq_markPolygon`
(:4518), `geoCornerPolygon_eq_markPolygon` (:4070), `markPolygon_apply` (:4054), `insertion_indices_exhaust`,
`insertIndex_val`, `insertedIndex_val`, `insertIndex_injective`, `insertIndex_ne_inserted` (InsertionIndices),
`appendVertex_old/new`, `edge_appendVertex_old/last/new/old_scaled` (InsertedTuple), `regular_appendVertex`
(AppendRotation:26), `traversalKey_lt_iff`, `traversalKey_same_edge`, `traversalKey_injective` (Traversal.lean),
`ReparamData` (LinkMoves:370), `Shadow.single_generic_of` (LinkPositiveLift:160), `Shadow.positiveDiagram_det_pos`,
`Shadow.single_isCrossing_iff`, `Shadow.single_pt_ext` (CChamber:675), `crossingParam_spec` (LinkDiagram:1416),
`Generic.common_point_unique` (LinkDiagram:~415), `edgePoint_injective` (Crossings.lean:88).
