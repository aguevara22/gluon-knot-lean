# W2_SFTD_REPORT — unit U112-D, leaf `sft_loop` (the loop sector of thm:C-soft)

Prover subagent, 2026-09-15 (wave 2).  File: `work/drafts/corner/W2_SFTD.lean` (9982 lines) =
`Partial_Assembled.lean` (7390 lines, byte-identical skeleton) + the helper block (prefix `sftd_`, 2566 lines,
inserted immediately before the docstring of `sft_loop`, inside `section Soft`) + the 26-line body of `sft_loop`
in place of its `sorry`.  Nothing written under `work/lean`; no import added.

## 0. Result

**`sft_loop` is PROVED** (statement frozen, untouched).

* `cd work/lean && lake env lean ../drafts/corner/W2_SFTD.lean`: **0 errors**, ~21 s warm; the only
  `declaration uses sorry` warnings are the 5 other open leaves (`sg_daughters_products`, `s7_sliding_law_at`,
  `s7_bigon_law_at`, `s7_corner_product`, `sft_same_sign`) and the 4 §6 row theorems — 9 in total, as in the
  partial assembly minus `sft_loop`.  No other warning is emitted from the new block.
* `grep -c sorry`: `Partial_Assembled.lean` 12 → `W2_SFTD.lean` 11 (the leaf's `  sorry` is the only removed line).
* `diff Partial_Assembled.lean W2_SFTD.lean`: hunks `7261a7262,9827` (helper block) and `7272c9838,9863`
  (`  sorry` → the body); the only removed line is `  sorry`.
* `python3 tools/stmt_check.py W2_SFTD.lean`: **49/49 frozen statements byte-identical, PASS**.
* `#print axioms SM.sft_loop` (scratch copy): `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm,
  SM.lp_lm_uniqueness]` — no `sorryAx`; the same policy interfaces as `corner_values_i`/`cornerHomfly_ne_zero`
  (through `cornerStateSum`/`homfly` and lc:presentations).  `sftd_LoopTransport.homfly_residual` has the same
  axioms; `sftd_residual_rotation_bound` is standard-only.
* The hypothesis `hCV : CornerValuesData` is used exactly once, at `hCV.isolated_zero` (the supports omitting the
  newborn — where row 105 (ii), hence the floor, enters); clause (i) enters through the PROVED `corner_values_i`
  for the triangle.

## 1. Route (PLAN_FINAL §3.4 "Loop", sm-4:1067-1143) and where each printed sentence lives

Data at one parameter (`sftd_LoopData`, packaged by `sftd_soft_loop_data'` from `soft_family_generic` clauses
(i)-(iv) and `soft_newborn_small_empty_arc`): persistence/classification `hp hclass`, same-edge visit order
`hord`, the newborn parameter bounds `hbound` (inherited visits on `E_{j-1}` before `a`, on the return edge
after `b`), the empty short arc `hnob` ("its visits are adjacent in the Gauss word"), unchanged directions and
turns at `k ≠ j`, `−χ₋`, `−χ₊` at `μ_j`, `M_ε`, the two newborn determinant signs `sgn det(u, D_ε) = τ`,
`sgn det(D_ε, u) = −τ`, the inherited crossing signs, the inherited crossing points and the newborn point.

1. **Abstract loop transport** `sftd_LoopTransport hn hP hQ` (§B of the block): vertex map, new vertex, attachment,
   newborn `y` with visits `a b`, injective crossing/visit maps onto everything but `y`, the sorted mark list of
   `Q` = the parent list with `μ_att` replaced by the block `a, μ_att, M_ε, b` up to rotation
   (`sftd_IsLoopInsertion`, list layer §A with the four `next` computations), preserved interlacement of
   inherited crossings, `y` isolated.  From it (all PROVED): the cyclic successor through the block
   (`markSuccessor_toMark/_a/_vatt/_new/_b`), the residual map `toMark'` (`μ_att ↦ a`) commuting with the
   smoothing successors at `S ∪ {y}` (`smoothingSuccessor_supportY_toMark'`: "process `y` first … the remaining
   swaps `S` act only on the residual cycle"), the triangle cycle `b → μ_att → M_ε → b`, the carrier
   equivalence `Option (Component S) ≃ Component (S ∪ {y})` (`residual`, `tri`, `componentEquiv`), and for a
   support omitting `y` both newborn visits on one carrier (`owner_support_a_eq_b`, lem:carriers (iii)).
2. **Carriers at `S ∪ {y}`** (§C): `carrierCrossings_residual` (transported), `carrierCrossings_tri = ∅`,
   `isDecomposition_supportY_iff` (needs `y_isolated`), `componentMarkList_residual`/`ccpCornerList_residual`
   (rotations of the residual image; the corner `μ_att` is replaced by the smoothing corner `a`),
   `ccpCornerList_tri ~r [μ_att, M_ε, b]`, `ccpCornerCount_tri = 3`, uniformity `carrierUniform_residual_iff`
   (given `markTurn Q (toMark' m) = markTurn P m`), `carrierUniform_tri`, the index set
   `mem_uniformDecompositions_supportY_iff`.
3. **Supports omitting `y`** (`cornerProduct_support_eq_zero`): `y ∈ carrierCrossings (support S) Q'` with `Q'`
   the carrier through `a` and `b`; every other crossing of `Q'` is inherited, so `y` interlaces none of them;
   `hCV.isolated_zero` ⇒ `c(Q') = 0` ⇒ the product vanishes (sm-4:1076-1084).
4. **Supports containing `y`**: `cornerCoefficient_tri = 1` by `corner_values_i` (crossing-free, uniform of sign
   `−τ`), `cornerProduct_supportY` (reindexing along `componentEquiv`), `sum_transport`:
   `Σ_{uD(Q)} = −Σ_{uD(P)}` (`Finset.sum_filter_add_sum_filter_not` on `y ∈ S'`, `Finset.sum_nbij` along
   `supportY`, `|S ∪ {y}| = |S| + 1`), `leftTurns_transport` (additive form), `cornerStateSum_transport`:
   `C(Q) = −(−1)^{ℓ(Q)+ℓ(P)} C(P)`.
5. **Coefficient equality of residual carriers** — the two "named-record" sentences of the printed proof:
   * polynomials (`homfly_residual`, §E): `positiveLiftRecordIso` (cb:products KL1) identifies the record of each
     positive lift with the restricted Gauss record `CB.gaussRecord (cg) X`; `gaussRecordIso` is a
     `RecordIso` between the two restricted Gauss records (occurrences by the inherited visits; the Gauss list of
     `Q` at the transported crossings IS the transported Gauss list, `gaussList_transport`, by sortedness
     (`sfta_soft_visitKey_lt_iff`) and `List.Perm.eq_of_pairwise`; pairing by `twin_eq`; over bits by the
     inherited determinant signs `sftd_soft_positiveOverBit`); then lc:presentations (`presentations`) and
     `P_eq_homfly`.  No isotopy is needed.
   * rotations (§F): the residual corner polygon is, up to `recastTuple`/`shift`, the family
     `sftd_cornerFamily ε` (vertices fixed, `μ_j ↦ softNewbornPoint`, inherited points `softInheritedPoint`);
     it is continuous at `0` (`softNewborn_continuousAt_zero`, `continuousAt_softInheritedPoint` with
     `crossing_det_ne_zero_of_geometry`) with value the parent's corner polygon (`sftd_cornerFamily_zero`), the
     rotation number is continuous at a regular polygon (`sftd_rotationNumber_continuousAt` from
     `continuousAt_principalAngle`), it is an integer on the interval (`carrierRotation_exists_int`), so it is
     eventually the parent's (`sftd_eventually_eq_of_continuousAt_int`); one `ε₂` for all finitely many `(S, q)`
     (`sftd_finite_min`, `sftd_residual_rotation_bound`).  This is the printed "convergence to the old integer
     implies equality for all sufficiently small parameters"; the printed one-sided limits are the library's
     two-sided ones.
6. **Sign bookkeeping** (`sftd_sign_arith`, `sftd_neg_sign_pow`): `ℓ(Q) + [τ=1] = ℓ(P) + 2[−τ=1]` ⇒
   `−(−1)^{ℓ(Q)+ℓ(P)} = τ` ⇒ `C(P_ε) = τ C(P)`.
7. **The soft instance** (§D): `sftd_soft_markList_insertion` (sortedness of the four-mark block; `j ≠ 0`
   literal, `j = 0` one rotation by two with `M_ε` at label `0` — `sftd_key_*`, `sftd_keys_zero`),
   `sftd_interlaces_transport` (injective-map version of `sfta_interlaces_transport`), `sftd_soft_y_isolated`,
   `sftd_softLoopTransport`, the turn data `sftd_softLoopTransport_markTurn'` (the smoothing corner `a` turns by
   `sgn det(u, D_ε) = τ`, clause (ii)) and `sftd_softLoopTransport_tri_turns` (all three `−τ`).

The leaf body: `sftd_soft_loop_data'` and `sftd_residual_rotation_bound` supply `δ`, `ε₂`; take `min`; build
`τ := sftd_loopTransport`; `cornerStateSum_transport hCV hturn htri hcoef`; `leftTurns_transport d.hvert`;
`sftd_sign_arith`; `sftd_neg_sign_pow`.

## 2. Fidelity notes

* FR-CC-11/12 respected: the frozen statement is in `ℤ` with `∀ hQ`; the proof produces one `ε₁` from the
  lem:soft-generic interval intersected with the rotation interval.
* "Order independence in lem:carriers (i)" is not used as a lemma: the residual/triangle decomposition is read
  directly off `smoothingSuccessor (S ∪ {y})` (`selectedMarkPerm` is defined from the support alone).
* "No (G1) claim about the intermediate residual polygon is needed" — indeed none is made; every carrier used is
  a carrier of the generic `P_ε` or of `P`.
* The isolation of `y` is derived from the empty short arc (clause (iv) `∀ w, ¬ traversalBetween a w b`), not
  from the `nextGaussVisit` clause.
* The coefficient identification uses the record bridge exactly as the printed "Carrier records and
  coefficients" paragraph (isomorphic named records ⇒ lem:rp:record-polynomial ⇒ lp:core), through the accepted
  `positiveLiftRecordIso` and `presentations`.

## 3. Dependencies and notes for the assembler

* The block depends on the U_SFTA helpers (`sfta_IsInsertion` list lemmas `sfta_next_eq_of_getElem`,
  `sfta_insert_getElem_att`, `sfta_next_congr`; `sfta_carrierUniform_iff_forall_mem`;
  `sfta_interlaces_iff_visits`; the key lemmas `sfta_markKey_visit_eq`, `sfta_markKey_vertex_eq`,
  `sfta_softMap`, `sfta_soft_markKey_lt_iff/_le_iff`, `sfta_soft_new_key`, `sfta_soft_zero_keys`,
  `sfta_softOldIndex_*`, `sfta_softParentEdge_*`, `sfta_softMap_injective`, `sfta_softMap_new_notMem`,
  `sfta_markList_head`, `sfta_soft_visitKey_lt_iff`, `sfta_soft_traversalBetween_iff`;
  `sfta_InsertMarkTransport.sfta_sign_cancel`) and on ONE U_SFTB helper (`sftb_sub_one_ne`).  It must therefore
  stay below both blocks (its anchor, before `sft_loop`'s docstring, is below them).
* Accepted library used beyond the frozen imports' closure: nothing new — `SM.CB.*` (CBProducts: `cg`,
  `gaussList`, `gaussRecord`, `gaussSucc_val`, `gaussPair_val`, `positiveOverBit`, `kl2_*`,
  `positiveLiftRecordIso`), `presentations`, `P_eq_homfly`, `Carrier.MarkTransport.isRotated_filter_map_of_forall`
  and `.getElem_eq_map_of_rotate_eq`, `recastTuple`/`zmod_val_cast`/`rotationNumber_recastTuple` (CChamber),
  `continuousAt_principalAngle` (RotationContinuity), `soft_newborn_small_empty_arc`,
  `soft_small_crossing_transport_data`, `softNewborn_values_zero`, `softNewborn_continuousAt_zero`,
  `continuousAt_softInheritedPoint`, `softInheritedPoint_zero_crossing`, `crossing_det_ne_zero_of_geometry`.
* Generic lemmas that could be ported to library modules at port time: `sftd_next_map` (`List.next` of a mapped
  list), `sftd_interlaces_transport` (generalizes `sfta_interlaces_transport` to injective maps),
  `sftd_rotationNumber_continuousAt` (RotationContinuity), `sftd_eventually_eq_of_continuousAt_int`,
  `sftd_finite_min`, `sftd_sign_arith`.
* No `sorry` anywhere in the block; no statement/definition/docstring of the skeleton touched; no other unit's
  leaf touched.

## 4. Sizes

Block 2566 lines, 188 declarations (all `sftd_*` or `sftd_LoopTransport.*`): list layer 230, abstract transport
(structure, successors, cycles, carriers) 590, carriers/decompositions/corner lists/uniformity/sum 520, soft
instance (mark list, interlacement, isolation, turns) 640, record bridge 150, data structure + rotation limit +
signs 430; leaf body 26 lines.  Wall time ≈ 5 h; ≈ 25 compile rounds of the 9.9k-line file (≈ 21 s each).

## 5. Helpers added (188)

- `sftd_IsLoopInsertion`
- `sftd_block_length`
- `sftd_block_perm`
- `sftd_block_nodup`
- `sftd_block_mem`
- `sftd_block_getElem_lt`
- `sftd_block_getElem_y₁`
- `sftd_block_getElem_att`
- `sftd_block_getElem_y₂`
- `sftd_block_getElem_y₃`
- `sftd_block_getElem_gt`
- `sftd_block_next_of_ne`
- `sftd_block_next_y₁`
- `sftd_block_next_att`
- `sftd_block_next_y₂`
- `sftd_block_next_y₃`
- `sftd_markSuccessor_ne_self`
- `sftd_LoopTransport`
- `sftd_LoopTransport.toMark`
- `sftd_LoopTransport.toMark_inl`
- `sftd_LoopTransport.toMark_inr`
- `sftd_LoopTransport.toMark'`
- `sftd_LoopTransport.toMark'_att`
- `sftd_LoopTransport.toMark'_of_ne`
- `sftd_LoopTransport.toMark'_inr`
- `sftd_LoopTransport.markList_insertion'`
- `sftd_LoopTransport.markList_perm`
- `sftd_LoopTransport.three_cons_map_nodup`
- `sftd_LoopTransport.toMark_injective`
- `sftd_LoopTransport.a_notMem_map`
- `sftd_LoopTransport.new_notMem_map`
- `sftd_LoopTransport.b_notMem_map`
- `sftd_LoopTransport.toMark_ne_a`
- `sftd_LoopTransport.toMark_ne_new`
- `sftd_LoopTransport.toMark_ne_b`
- `sftd_LoopTransport.visit_injective`
- `sftd_LoopTransport.vert_injective`
- `sftd_LoopTransport.vert_ne_new`
- `sftd_LoopTransport.visit_ne_a`
- `sftd_LoopTransport.visit_ne_b`
- `sftd_LoopTransport.exhaust`
- `sftd_LoopTransport.vert_exhaust`
- `sftd_LoopTransport.visit_exhaust`
- `sftd_LoopTransport.visit_fst_eq_y_iff`
- `sftd_LoopTransport.visit_range`
- `sftd_LoopTransport.cross_range`
- `sftd_LoopTransport.visit_fst_eq_iff`
- `sftd_LoopTransport.twin_eq`
- `sftd_LoopTransport.twin_a`
- `sftd_LoopTransport.twin_b`
- `sftd_LoopTransport.toMark'_injective`
- `sftd_LoopTransport.toMark'_ne_b`
- `sftd_LoopTransport.toMark'_ne_vatt`
- `sftd_LoopTransport.toMark'_ne_new`
- `sftd_LoopTransport.exhaust'`
- `sftd_LoopTransport.markSuccessor_toMark`
- `sftd_LoopTransport.markSuccessor_a`
- `sftd_LoopTransport.markSuccessor_vatt`
- `sftd_LoopTransport.markSuccessor_new`
- `sftd_LoopTransport.markSuccessor_b`
- `sftd_LoopTransport.support`
- `sftd_LoopTransport.mem_support`
- `sftd_LoopTransport.y_notMem_support`
- `sftd_LoopTransport.support_card`
- `sftd_LoopTransport.support_injective`
- `sftd_LoopTransport.support_surjective_of_notMem`
- `sftd_LoopTransport.supportY`
- `sftd_LoopTransport.y_mem_supportY`
- `sftd_LoopTransport.mem_supportY_cross`
- `sftd_LoopTransport.supportY_card`
- `sftd_LoopTransport.supportY_injective`
- `sftd_LoopTransport.supportY_surjective_of_mem`
- `sftd_LoopTransport.selectedMarkPerm_supportY_toMark`
- `sftd_LoopTransport.selectedMarkPerm_supportY_a`
- `sftd_LoopTransport.selectedMarkPerm_supportY_b`
- `sftd_LoopTransport.selectedMarkPerm_support_toMark`
- `sftd_LoopTransport.selectedMarkPerm_support_a`
- `sftd_LoopTransport.selectedMarkPerm_ne_att`
- `sftd_LoopTransport.smoothingSuccessor_supportY_toMark'`
- `sftd_LoopTransport.smoothingSuccessor_supportY_b`
- `sftd_LoopTransport.smoothingSuccessor_supportY_vatt`
- `sftd_LoopTransport.smoothingSuccessor_supportY_new`
- `sftd_LoopTransport.smoothingSuccessor_support_a`
- `sftd_LoopTransport.smoothingSuccessor_support_vatt`
- `sftd_LoopTransport.smoothingSuccessor_support_new`
- `sftd_LoopTransport.owner_support_a_eq_b`
- `sftd_LoopTransport.pow_toMark'`
- `sftd_LoopTransport.sameCycle_toMark'_iff`
- `sftd_LoopTransport.pow_b_mem_tri`
- `sftd_LoopTransport.not_sameCycle_b_toMark'`
- `sftd_LoopTransport.residual`
- `sftd_LoopTransport.residual_owner`
- `sftd_LoopTransport.tri`
- `sftd_LoopTransport.owner_vatt_eq_tri`
- `sftd_LoopTransport.owner_new_eq_tri`
- `sftd_LoopTransport.residual_injective`
- `sftd_LoopTransport.residual_ne_tri`
- `sftd_LoopTransport.owner_toMark'_eq_residual_iff`
- `sftd_LoopTransport.owner_toMark'_ne_tri`
- `sftd_LoopTransport.component_cases`
- `sftd_LoopTransport.componentEquiv`
- `sftd_LoopTransport.componentEquiv_none`
- `sftd_LoopTransport.componentEquiv_some`
- `sftd_LoopTransport.carrierCrossings_residual`
- `sftd_LoopTransport.carrierCrossingCount_residual`
- `sftd_LoopTransport.carrierCrossings_tri`
- `sftd_LoopTransport.carrierCrossingCount_tri`
- `sftd_LoopTransport.isDecomposition_supportY_iff`
- `sftd_LoopTransport.isTrueCorner_toMark'`
- `sftd_LoopTransport.notMem_att_of_insertion`
- `sftd_LoopTransport.componentMarkList_residual`
- `sftd_LoopTransport.ccpCornerList_residual`
- `sftd_LoopTransport.ccpCornerCount_residual`
- `sftd_LoopTransport.mem_ccpCornerList_residual`
- `sftd_LoopTransport.componentMarkList_tri`
- `sftd_LoopTransport.ccpCornerList_tri`
- `sftd_LoopTransport.ccpCornerCount_tri`
- `sftd_LoopTransport.mem_ccpCornerList_tri`
- `sftd_LoopTransport.carrierUniform_residual_iff`
- `sftd_LoopTransport.carrierUniform_tri`
- `sftd_LoopTransport.uniformDecomposition_supportY_iff`
- `sftd_LoopTransport.mem_uniformDecompositions_supportY_iff`
- `sftd_LoopTransport.cornerProduct_support_eq_zero`
- `sftd_LoopTransport.cornerSlot_residual`
- `sftd_LoopTransport.cornerCoefficient_residual`
- `sftd_LoopTransport.cornerCoefficient_tri`
- `sftd_LoopTransport.cornerProduct_supportY`
- `sftd_LoopTransport.sum_transport`
- `sftd_LoopTransport.leftTurns_transport`
- `sftd_LoopTransport.cornerStateSum_transport`
- `sftd_interlaces_transport`
- `sftd_soft_mark_exhaust`
- `sftd_softMap_ne_a`
- `sftd_softMap_ne_b`
- `sftd_soft_key_a`
- `sftd_soft_key_b`
- `sftd_key_lt_a_of_ne_zero`
- `sftd_key_b_lt_of_ne_zero`
- `sftd_key_block_of_ne_zero`
- `sftd_keys_zero`
- `sftd_soft_markList_insertion`
- `sftd_soft_y_isolated`
- `sftd_softLoopTransport`
- `sftd_softLoopTransport_vert`
- `sftd_softLoopTransport_new`
- `sftd_softLoopTransport_att`
- `sftd_softLoopTransport_y`
- `sftd_softLoopTransport_a`
- `sftd_softLoopTransport_b`
- `sftd_softLoopTransport_cross`
- `sftd_softLoopTransport_visit`
- `sftd_softLoopTransport_toMark`
- `sftd_softLoopTransport_markTurn'`
- `sftd_softLoopTransport_tri_turns`
- `sftd_soft_loop_data`
- `sftd_next_map`
- `sftd_LoopTransport.crossSet`
- `sftd_LoopTransport.mem_crossSet`
- `sftd_LoopTransport.gaussList_transport`
- `sftd_LoopTransport.occMap`
- `sftd_LoopTransport.occMap_val`
- `sftd_LoopTransport.occMap_bijective`
- `sftd_LoopTransport.gaussRecordIso`
- `sftd_LoopTransport.homfly_residual`
- `sftd_soft_positiveOverBit`
- `sftd_LoopData`
- `sftd_soft_loop_data'`
- `sftd_soft_generic_small`
- `sftd_loopTransport`
- `sftd_loopTransport_markTurn'`
- `sftd_loopTransport_tri_turns`
- `sftd_loopTransport_homfly`
- `sftd_LoopTransport.residualCornerPolygon`
- `sftd_LoopTransport.exists_ccpCornerMark_residual`
- `sftd_LoopTransport.exists_ccpCornerPolygon_residual`
- `sftd_LoopTransport.carrierRotation_residual_eq`
- `sftd_cornerPoint`
- `sftd_cornerFamily`
- `sftd_cornerFamily_zero`
- `sftd_cornerFamily_continuousAt`
- `sftd_rotationNumber_continuousAt`
- `sftd_eventually_eq_of_continuousAt_int`
- `sftd_residualCornerPolygon_eq`
- `sftd_residual_rotation_eventually`
- `sftd_finite_min`
- `sftd_residual_rotation_bound`
- `sftd_sign_arith`
- `sftd_neg_sign_pow`
