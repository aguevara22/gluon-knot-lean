# U_S7B_REPORT — unit U110-B (helper unit, prefix `s7b_`; halves ↔ intervals), 2026-09-15

File: `work/drafts/corner/U_S7B.lean` = `Statements_FINAL.lean` + ONE import line (`import SM.VertexSides`, after
`import SM.GermSides`) + ONE inserted block of 1714 lines (lines 455-2168) inside `section VertexEdge`, immediately
before the docstring of `s7_sliding_law_at` (the first leaf that consumes it — U110-E; U110-F/K consume the bigon
half).  `diff Statements_FINAL.lean U_S7B.lean`: `16a17` (the import) and `453a455,2168` (the block); **0 lines removed**
— no definition, structure, statement, name or docstring touched.
Check: `cd work/lean && lake env lean ../drafts/corner/U_S7B.lean` — **0 errors, 0 non-sorry warnings**, exactly the
14 `declaration uses sorry` warnings of the other units' leaves and the §6 row theorems; 15.4 s warm.
`grep -c sorry`: 16 before → 16 after (helper unit: no leaf of its own; 16 = 14 declarations + 2 prose mentions).
Clash scan: `grep -rln "s7b_" work/lean/SM work/lean/CV work/lean/Bridge` empty.
Axioms (`#print axioms`, scratch copy): every checked `s7b_` declaration (`s7b_ReturnTransport.cycleEquiv`,
`s7b_sumCongr_cycleEquiv`, `s7b_remote_cyclicRange_iff`, `s7b_crossingPoint_firstHalfCrossing`,
`s7b_visitParameter_secondHalfVisit_cut`, `s7b_PivotSplit.slidingEquiv`, `s7b_slidingMark_injective`,
`s7b_SlidingTransport.componentEquiv`, `s7b_SlidingTransport.carrierCrossingCount_eq_first`,
`s7b_slidingDecompositionEquiv`, `s7b_eligibleDecompositionEquiv`) = [propext, Classical.choice, Quot.sound]; nothing in
this unit touches `homfly`/`P`, so no `lit_homfly`/`lp_lm`.

## 0. IMPORT NOTE FOR THE ASSEMBLER (load-bearing)

None of lem:wall-sides (V) is reachable from the 16 frozen imports: `ContactAffected`, `VertexCrossingData`,
`SlidingCrossingPattern`, `vertex_sides`, `VertexSidesData`, `VertexLocalData`, `contactVisitTransport`,
`ContactParameterWindows`, `contact_pair_data`, `contact_unaffected_pair_geometry`, `IsInteriorCrossing` all fail
`#check` under `Statements_FINAL.lean`'s imports (probe: work/scratch … /probe.lean).  PLAN_FINAL §3.3 names
`vertex_sides` (VertexSides.lean:40), `VertexCrossingData` and `contactVisitTransport` as the setup inputs of the
whole sliding branch, so U110-A/E must import it too.  This unit adds `import SM.VertexSides` (built: `.lake/build/lib/
lean/SM/VertexSides.olean` exists; compile time unchanged, 15 s).  The assembler must union the imports; no
statement depends on the import (the frozen text is unchanged).

## 1. What is proved (151 declarations: 102 top-level, 49 in the namespaces `s7b_ReturnTransport`,
`s7b_SupportSplit`, `s7b_PivotSplit`, `s7b_SlidingTransport`; all PROVED, no `sorry` added)

PLAN §3.3 gives U110-B no fixed statements ("halves ↔ intervals: support bijections (sliding, eligible), carrier
correspondences, `L*, L₁, L₂` as carriers of `Tᵢ` on `λᵢ`; build the transport on MARKS, FlatCarriers is the
precedent").  The rendering, in dependency order:

### Part I — the first-return transport of permutations (pure; the mark-level engine)
FlatCarriers' `skipJ` skips ONE mark (`μ_j`).  A sliding row skips a SET (the second visit of `x₋` and every visit
of a crossing interlacing `x₋`), so the device is generalised:
* `structure s7b_ReturnTransport (f : Perm α) (g : Perm β) (ι : β → α) : Prop` — `inj : Injective ι`;
  `step : ∀ b, ∃ k > 0, (f ^ k) (ι b) = ι (g b) ∧ ∀ 0 < j < k, (f ^ j) (ι b) ∉ range ι` (`g` is the first-return map of
  `f` on the image); `hit : ∀ a, ∃ j, (f ^ j) a ∈ range ι` (every point reaches the image).
* `sameCycle_step`, `sameCycle_pow_of`, `sameCycle_of` (`g.SameCycle b b' → f.SameCycle (ι b) (ι b')`),
  `sameCycle_of_pow_eq` (strong induction on the number of `f`-steps), **`sameCycle_iff`**
  (`f.SameCycle (ι b) (ι b') ↔ g.SameCycle b b'`), `cycleMap`, `cycleMap_mk`, `cycleMap_bijective`,
  **`cycleEquiv : Quotient (SameCycle.setoid g) ≃ Quotient (SameCycle.setoid f)`** (`⟦b⟧ ↦ ⟦ι b⟧`, `cycleEquiv_mk`),
  `mk_eq_of_pow_eq`.
* Sum types: `s7b_sumCongr_pow_inl/_inr`, `s7b_sumCongr_sameCycle_inl/_inr`, `s7b_sumCongr_not_sameCycle`,
  **`s7b_sumCongr_cycleEquiv : Quotient (setoid (sumCongr g₁ g₂)) ≃ Quotient (setoid g₁) ⊕ Quotient (setoid g₂)`**
  (`_inl`, `_inr` computation rules, `rfl`).
`Component hn hP S` IS `Quotient (SameCycle.setoid (smoothingSuccessor hn hP S))` and `owner = Quotient.mk`, so these
apply verbatim to carriers.

### Part II — labels, remoteness, crossings, visits and parameters of the halves vs the wall centre `P`
(hypotheses `hn : 3 ≤ n`, `hsep : ContactSeparated M a`, `hm : P M ∈ edgeInterior P a`, `hz : pointZeroTriples P =
{contactSupport M a}` — all fields of `g.VertexEdgeAt M a`: `h.1`, `h.2.2.2.1`, `h.2.1`)
* Cyclic-range arithmetic: `s7b_adjacent_iff` (`adjacent i j ↔ j = i ∨ j = i+1 ∨ i = j+1`), `s7b_adjacent_zero_neg_one`,
  `s7b_adjacent_neg_one_zero`, `s7b_cyclicRange_succ_iff` (`k < n`: `ι j = ι i + 1 ↔ i ≠ -1 ∧ j = i + 1`),
  `s7b_adjacent_cyclicRange_iff`, `s7b_zero_ne_neg_one`, `s7b_one_ne_neg_one`,
  **`s7b_remote_cyclicRange_iff (hk : k < n) (hk3 : 3 ≤ k) : remote (ι i) (ι j) ↔ remote i j ∨ (i = -1 ∧ j = 0) ∨ (j = -1 ∧ i = 0)`**
  — the ONLY adjacent pair of a half whose image is remote in `P` is its wrap-around pair, i.e. the contact-affected
  pair `{a, M}` (first half) / `{a, M−1}` (second half).  Specialised: `s7b_remote_firstHalfIndex_iff`,
  `s7b_remote_secondHalfEdgeIndex_iff`; sizes `s7b_firstHalfSize_lt`, `s7b_secondHalfSize_lt`.
* Ranges: `s7b_firstHalfIndex_ne_pred` (`M−1` is no label of `λ₁`), `s7b_secondHalfEdgeIndex_ne` (`M` is no edge label
  of `λ₂`), `s7b_firstHalfIndex_eq_secondHalfEdgeIndex` (a common label forces `i = -1 ∧ j = 0`, i.e. the label `a`),
  `s7b_firstHalfIndex_ne_secondHalfIndex` (vertex ranges `M..a` and `a+1..M−1` are disjoint).
* Crossings: `s7b_isCrossing_firstHalf_image / _secondHalf_image` (a crossing `{i, j}` of `λᵢ` gives the crossing
  `{ι i, ι j}` of the centre: remoteness by the iff, segments by def:deletion-halves' `first/second_segment_inclusions`),
  `s7b_firstHalf_image_not_affected / _secondHalf_image_not_affected` (never a contact pair),
  `def s7b_firstHalfCrossing / s7b_secondHalfCrossing : Crossing λᵢ → Crossing P` (`_val`, `_injective`, `_not_affected`).
* Segments: `s7b_edgeSegment_firstHalf / _secondHalf` (off the cut the segments are literally equal),
  **`s7b_mem_edgeSegment_firstHalf_cut : x ∈ edgeSegment λ₁ (-1) ↔ ∃ u ∈ [0, r], x = edgePoint P a u`**,
  **`s7b_mem_edgeSegment_secondHalf_cut : x ∈ edgeSegment λ₂ 0 ↔ ∃ u ∈ [r, 1], x = edgePoint P a u`** (the printed
  "`λ₁` closes with `[μ_a, μ_M] ⊂ E_a`; `λ₂` opens with `[μ_M, μ_b] ⊂ E_a`", sm-4:807-810).
* Visits: `def s7b_firstHalfVisit / s7b_secondHalfVisit : Visit λᵢ → Visit P` (`_fst`, `_edge` rfl, `_injective`,
  **`_visitTwin`** — the maps commute with the crossing pairing).
* Geometry: `s7b_centre_meet_unique` (two remote unaffected edges of the centre meet in at most one point:
  `contact_unaffected_pair_geometry` + `intersection_parameters_unique`), **`s7b_crossingPoint_firstHalfCrossing /
  _secondHalfCrossing`** (`crossingPoint (ι c) = crossingPoint c`), and the four parameter laws
  **`s7b_visitParameter_firstHalfVisit`** (off the cut: equal), **`s7b_visitParameter_firstHalfVisit_cut`**
  (`= r · t`), **`s7b_visitParameter_secondHalfVisit`**, **`s7b_visitParameter_secondHalfVisit_cut`**
  (`= r + (1−r) t`) — the rescalings of def:deletion-halves' `cut_segments`, i.e. exactly the `hmono`/`hcut` inputs of
  U110-D's `s7d_cornerCoefficient_eq_of_cut` (same-edge order is preserved, the cut rescales monotonically).

### Part IV — the support bijections (eq. s7c:sliding-bijection, s7c:eligible-bijection)
* `s7b_Indep R S := ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ R x y`; `s7b_isDecomposition_iff_indep : IsDecomposition hn hP S ↔
  s7b_Indep (Interlaces hn hP) S` (`mem_independentSupports_iff`).
* `structure s7b_SupportSplit R R₁ R₂ ι₁ ι₂ : Prop` — `inj₁ inj₂`, `disjoint : ι₁ c₁ ≠ ι₂ c₂`,
  `rel₁ : R (ι₁ c) (ι₁ c') ↔ R₁ c c'`, `rel₂`, `cross : ¬ R (ι₁ c₁) (ι₂ c₂)`, `cross'`.
* `s7b_pre ι S` (preimage, `s7b_mem_pre`), `s7b_img hι S` (image, `s7b_mem_img`, `s7b_apply_mem_img`, `s7b_pre_img`,
  `s7b_img_pre_subset`); `joinSupport S₁ S₂ := ι₁ S₁ ∪ ι₂ S₂` (`mem_joinSupport`, `indep_joinSupport`,
  `pre₁_joinSupport`, `pre₂_joinSupport`, `joinSupport_pre`), `indep_pre₁/₂`.
* **`s7b_SupportSplit.eligibleEquiv : {T // s7b_Indep R T ∧ ∀ y ∈ T, y ∈ range ι₁ ∪ range ι₂} ≃ {S₁ // Indep R₁ S₁} × {S₂ // Indep R₂ S₂}`**
  (`_apply`: the preimages; `_symm_apply`: `joinSupport`; `card_symm_apply : |T| = |T₁| + |T₂|`).
* `structure s7b_PivotSplit R R₁ R₂ ι₁ ι₂ x : Prop` — `split : s7b_SupportSplit …`, `x_not₁/₂ : ιᵢ c ≠ x`,
  `x_free₁/₂ : ¬ R x (ιᵢ c) ∧ ¬ R (ιᵢ c) x`, **`x_split : ∀ y ≠ x, ¬ R x y → ¬ R y x → y ∈ range ι₁ ∪ range ι₂`**
  (the printed "every other selected chord is internal to one interval, by independence", sm-4:322-323).
* **`s7b_PivotSplit.slidingEquiv : {S // s7b_Indep R S ∧ x ∈ S} ≃ {S₁ // Indep R₁ S₁} × {S₂ // Indep R₂ S₂}`**
  ("with explicit inverse" `(S₁, S₂) ↦ {x} ∪ ι₁ S₁ ∪ ι₂ S₂`: `slidingEquiv_apply`, `slidingEquiv_symm_apply`,
  `insert_join_pre`, `pre₁_insert`, `pre₂_insert`, `indep_insert`; **`card_symm_apply : |S| = |S₁| + |S₂| + 1`** — the
  sign `(−1)^{|S|} = −(−1)^{|S₁|}(−1)^{|S₂|}` of U110-E's distributivity step).
* On the actual decompositions: **`s7b_slidingDecompositionEquiv hn hsep hm hQC hQ h₁ h₂ x hsplit :
  {S // IsDecomposition hn hQ S ∧ x ∈ S} ≃ {S₁ // IsDecomposition hn₁ h₁ S₁} × {S₂ // IsDecomposition hn₂ h₂ S₂}`** and
  **`s7b_eligibleDecompositionEquiv`** (eligible `T` = decompositions inside the two images), with
  `hnᵢ := (contactHalfSizes_bounds hn hsep).i.1` — the size proofs the frozen statement uses.

### Part III — the halves on a SIDE polygon `Q`, the sliding mark map, the transport structure
(`hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s)` = the last clause of `VertexCrossingData`,
from `vertex_sides hn g h` (`.2.2.2.1 s t`) for `Q := (g.sideTuple b t).val`, `P := g.center`)
* `s7b_sideCrossing hQC c hc : Crossing Q`; `def s7b_firstCrossingQ / s7b_secondCrossingQ : Crossing λᵢ → Crossing Q`
  (`_val` = `c.val.image (firstHalfIndex M a)` / `(secondHalfEdgeIndex M a)`, `_not_affected`, `_injective`,
  **`s7b_firstCrossingQ_ne_secondCrossingQ`** — the two images are disjoint); `def s7b_firstVisitQ / s7b_secondVisitQ :
  Visit λᵢ → Visit Q` (`_fst`, `_edge`, `_injective`, `_visitTwin`), **`s7b_visit_of_firstCrossingQ / _second`** (every
  visit of an image crossing is the image of a visit).
* **`def s7b_slidingMark hn hsep hm hQC vm : Mark λ₁ ⊕ Mark λ₂ → Mark Q`** — `inl (inl i) ↦ inl (firstHalfIndex i)`
  (vertices `M..a`), `inl (inr v) ↦ inr (firstVisitQ v)`, `inr (inl 0) ↦ inr vm` (the vertex `μ_M` of `λ₂` IS the
  smoothing corner at `x₋`'s leg visit), `inr (inl i) ↦ inl (secondHalfIndex i)` (`i ≠ 0`: vertices `a+1..M−1`),
  `inr (inr v) ↦ inr (secondVisitQ v)`; computation rules `_inl_inl`, `_inl_inr`, `_inr_inl_zero`, `_inr_inl`, `_inr_inr`;
  **`s7b_slidingMark_injective (hvm : ContactAffected M a vm.1.val)`**.  The marks of `Q` NOT in the image are exactly
  `inr (visitTwin vm)` (the `x₋`-visit on `E_a`, the extra corner of eq. s7c:short-direction-lists) and the visits of the
  crossings interlacing `x₋` (dominated).
* **`structure s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm : Prop`** — `affected : ContactAffected M a vm.1.val`,
  `pivot_mem : vm.1 ∈ S`, `first_pre : S₁ = s7b_pre (s7b_firstCrossingQ …) S`, `second_pre`, and the ONE geometric field
  **`ret : s7b_ReturnTransport (smoothingSuccessor hn hQ S) (sumCongr (smoothingSuccessor hn₁ h₁ S₁) (smoothingSuccessor hn₂ h₂ S₂)) (s7b_slidingMark …)`**.
  Consequences (namespace `s7b_SlidingTransport`, all PROVED from `ret`): `owner_inl_iff`, `owner_inr_iff`,
  `owner_inl_ne_inr`; **`componentEquiv : Component hn hQ S ≃ Component hn₁ h₁ S₁ ⊕ Component hn₂ h₂ S₂`** (eq.
  s7c:sliding-residual on carriers) with `componentEquiv_owner_inl/_inr`, `_owner_firstVisit/_secondVisit`,
  **`componentEquiv_owner_vertexM`** (the carrier of `Q` through `μ_M` ↔ `λ₁`'s carrier through its vertex `0`) and
  **`componentEquiv_owner_pivot`** (the carrier through `vm` ↔ `λ₂`'s carrier through its vertex `0`) — these two are
  the literal "`Lᵢ` as a `Component` of the decomposition `Sᵢ` of the generic half `λᵢ`" for the sliding row;
  `firstCrossingQ_mem_carrierCrossings_iff`, `secondCrossingQ_mem_carrierCrossings_iff`,
  `secondCrossingQ_notMem_carrierCrossings`, `firstCrossingQ_notMem_carrierCrossings`; with the pivot split and
  `hS : IsDecomposition`: `carrierCrossings_mem_range` (a carrier crossing interlacing `x₋ ∈ S` would have its visits on
  two carriers, lem:carriers (iii) `neighbor_visits_separated`), **`carrierCrossings_eq_img_first/_second`**
  (`carrierCrossings Q S q = ιᵢ (carrierCrossings λᵢ Sᵢ qᵢ)`) and **`carrierCrossingCount_eq_first/_second`**
  (`m_q = m_{qᵢ}`; the self-crossing part of eq. s7c:sliding-residual and the `m_Q` input of `d_Q`).

## 2. Not proved (the remaining geometric content of U110-B) — stated as the hypotheses of the structures above

1. **The first-return law `s7b_SlidingTransport.ret`** for the actual smoothing successors.  Needs, on the side
   polygon `Q`: (i) `nextMark` characterised by keys (the next visit on the same edge by parameter, else the next
   vertex — `nextMark_no_mark_between` gives one half; FlatCarriers' `geoMarkSuccessor_on_edge`/`_position_cases`
   (SM/FlatCarriers.lean:1338, 2729) are the precedent on `CrossingGeometry`); (ii) the same-edge order of the
   carried visits equals the halves' order (part II's parameter laws: equality off the cut, monotone rescaling on the
   cut) and equals `Q`'s order (`VertexLocalData.visit_order` / `ContactOrderAgrees`, lem:wall-sides (V));
   (iii) the contact geometry: `ρ_S (inr (visitTwin vm)) = inl M` (the leg visit is the last mark before `μ_M`:
   `visit_windows`), the visits on `E_a` before/after `x₋`'s `E_a`-visit are those with centre parameter `< r` / `> r`
   (`ContactParameterWindows` clauses 2-3 give `Q`'s parameters are `> 3η` from `r` while the contact visit is within
   `η`; the side-of-`r` agreement with the CENTRE parameter needs `|edgeParameter Q i j − edgeParameter P i j| < η`,
   which is `contact_persistent_parameters_approach` (ContactWindows.lean, an `∀ᶠ` statement) — NOT a field of
   `VertexLocalData`; U110-A should intersect it into its radius).  Estimated 600-900 lines.
2. **The interlacement transfer** `s7b_PivotSplit (Interlaces hn hQ) (Interlaces hn₁ h₁) (Interlaces hn₂ h₂)
   (s7b_firstCrossingQ …) (s7b_secondCrossingQ …) x₋` (fields `rel₁ rel₂ cross cross' x_free x_split`) and its
   bigon version `s7b_SupportSplit` on `P₀`.  `Interlaces` is `traversalBetween` of visit positions
   (Interlacement.lean:10-19); `rel₁` is "the cyclic order of `λ₁`'s visits is the restriction of `Q`'s" — a rotation
   of keys (`(M + i.val).val` vs `i.val`, cut at the wrap) plus the same-edge order (as in 1(ii)); `cross`/`x_split`
   are the interval dichotomy (both visits of a non-neighbour of `x₋` lie in one of the two arcs cut by `x₋`'s
   visits).  U110-D's `s7d_gaussList_isRotated_of_cut` is the analogous cut argument for Gauss lists.  Estimated
   500-800 lines.  `disjoint`, `inj₁`, `inj₂`, `x_not₁/₂` are PROVED here (`s7b_firstCrossingQ_ne_secondCrossingQ`,
   `_injective`, `_not_affected` vs `affected`).
3. **Corner lists / turns**: the corner SET of the carrier through the contact is the corner set of `λ₁`'s carrier plus
   the one extra smoothing corner `inr (visitTwin vm)` (from `componentEquiv` + `IsTrueCorner`), but the ORDERED
   `ccpCornerList`/`ccpCornerPolygon` correspondence (needed for U110-C's `e : {i // i ≠ j} ≃ ZMod k₁` turn-preserving
   bijection and the rotation equality of U110-A/I) is not built: it needs the mark-ORDER statement of 1(ii) at the
   level of `componentMarkList = markList.filter (owner = q)` (rotation-equivalence of the filtered lists, as
   FlatCarriers' `geoComponentMarkList_deletion_rotated` :2125).  Estimated 400-600 lines.
4. **The bigon mark map** (eligible `T` on `P₀`, no pivot; the contact carrier `L*` through `μ_M` with BOTH halves'
   `μ_M`-vertices identified — a `Mark λ₁ ⊕ Mark λ₂ → Mark P₀` map that is NOT injective at `inl (inl 0)`, `inr (inl 0)`
   (both ↦ `inl M`), so it needs the first-return device on the quotient identifying the two vertices; the closed
   halves `L₁, L₂` then arise as `componentEquiv`-images exactly as in the sliding case) and the `ε = 0` case
   `T ∪ {x, y}` on `P₂` (two extra smoothing corners forming the contact triangle, sm-4:437-447).  Not started;
   `s7b_ReturnTransport` and `s7b_eligibleDecompositionEquiv` are ready for it.  Estimated 700-1000 lines.

Nothing believed false: every printed sentence rendered here (sm-4:315-329 the sliding bijection and residual;
420-433 the eligible bijection; 800-835 the discharge "closing the interval at the cut closes the boundary successor
of `T` into the carrier of the decomposition `Tᵢ` of `λᵢ` through the corner `μ_M`") is literally true under the
first-return law; the one thing to watch is item 1(iii): the side-of-`r` classification of an unaffected `E_a`-visit
on `Q` is NOT derivable from `VertexLocalData` alone (its `windows` field has no approach clause), only from the
eventual `contact_persistent_parameters_approach`.

## 3. How the consumers use this unit

* **U110-E (`s7_sliding_law_at`)**: fix `t`, `Q₋ := (g.sideTuple false t).val`, `Q₊ := (g.sideTuple true t).val`,
  `hQC` from `vertex_sides`; `x₋` from `SlidingCrossingPattern` (`vertex_sides … .2.2.2.1 t t |>.2.2.1 h.2`).  The sum
  over `Ind(G_{Q₋})` splits into `{S : x₋ ∉ S}` (spectator sector, cancels against `Q₊` by U110-A's persistent
  transport + U110-D) and `{S : x₋ ∈ S}` ≃ `Ind(λ₁) × Ind(λ₂)` by `s7b_slidingDecompositionEquiv` (needs the
  `s7b_PivotSplit` of §2.2); per row, `S₁ = s7b_pre … S` (definitionally the `slidingEquiv` components,
  `slidingEquiv_apply`), `|S| = |S₁| + |S₂| + 1` (`card_symm_apply` — through `Equiv.subtypeEquivRight`/`prodCongr`
  the underlying finsets are unchanged, `rfl`), carriers `Component Q S ≃ Component λ₁ S₁ ⊕ Component λ₂ S₂`
  (`componentEquiv`, needs `ret`), spectator coefficients via U110-D's cut form with part II's parameter laws
  (`hmem` from `carrierCrossings_eq_img_*`, `htwin` from `_visitTwin`, `hbit` via `s7d_positiveOverBit_eq_of_smul`
  with the cut vectors `r • edge P a`, `(1−r) • edge P a` of `HalvesData.cut_segments`; `hr` from U110-A/I), and the
  contact carrier's selector from U110-C's `s7c_carrierWeight_refine` (corner bijection = §2.3).  Uniformity of `S`
  ↔ uniformity of `S₁, S₂` off the contact carrier follows from `componentEquiv` once the corner correspondence (§2.3)
  gives equal turn multisets.
* **U110-F/K (bigon)**: `s7b_eligibleDecompositionEquiv` on `P₀` with `s7b_SupportSplit`; the "`Lᵢ` literally a
  `Component hn' hλᵢ Tᵢ`" discharge for the floor is `componentEquiv_owner_vertexM`/`_pivot`'s analogue for the
  bigon mark map (§2.4) — for the sliding row it is proved here.
* **U110-J (floor reads)**: `hF.slot_le_of_signed hn₁ (firstHalf g.center M a) h₁ S₁ hS₁ q₁ …` with `q₁ :=` the
  `Sum.inl`-component of `componentEquiv (owner … (Sum.inl M))` and `hS₁ := (s7b_slidingDecompositionEquiv …).1.2`
  — the types match the floor's domain exactly (`Component (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁` with
  `hsep := h.1`, the very `hn₁` of the frozen `s7_sliding_law_at`).

## 4. Mathlib / Lean pitfalls met (v4.34.0-rc2 pin)

1. A `structure … : Prop extends Parent` did NOT produce a `toParent` projection usable as `h.toParent` (unknown
   constant); `s7b_PivotSplit` therefore carries an explicit field `split : s7b_SupportSplit …`.
2. `Equiv.trans_apply` cannot be `rw`-applied when the `Equiv`'s type is stated with `Component …` while the
   underlying term has `Quotient …` (motive not type-correct at `implicit` transparency); `show` the goal in the
   definitional `f (e x)` form first (`componentEquiv_owner_inl`).
3. Rewriting `crossingPoint (ι v).1` fails when the goal also contains `(ι v).2` (its type depends on `.1`); state
   the crossing-point equation with the explicit crossing/edge images (`s7b_visitParameter_*`).
4. Section `variable (hn : 3 ≤ n) (hsep : …)` are only included in declarations that MENTION them; lemmas about
   labels alone (`s7b_firstHalfIndex_eq_secondHalfEdgeIndex`) must take them explicitly.
5. `Set.mem_setOf_eq` is deprecated → `Set.mem_ofPred_eq`; `haveI` for a `Fact` in a proof triggers the
   `haveILetI` linter → `have`; `mul_div_cancel₀ (a) (h : b ≠ 0) : b * (a / b) = a` is the current name.
6. `ZMod.natCast_eq_natCast_iff' a b c : (a : ZMod c) = b ↔ a % c = b % c` + `Nat.mod_eq_of_lt` is the cleanest way to
   read a `ZMod n` identity between small naturals; `last_index_val_succ : (-1 : ZMod k).val + 1 = k`,
   `zmod_val_next_of_ne_last`, `ZMod.val_eq_zero`, `ZMod.val_one (Fact (1 < k))`.
7. `Equiv.Perm.SameCycle.exists_pow_eq'` needs `[Finite α]`; the transport lemmas carry `[Finite α] [Finite β]`
   (satisfied by `Mark _` via `Fintype`).
8. `rcases` on `hb : b ∈ Set.range ι` gives `ι c = b` (not `b = ι c`) — rewrite forward.
