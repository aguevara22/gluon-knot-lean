# Row 85 fd:parameter-avoidance — report

Date: 2026-09-14.  Row 85 of tools/claims.py, lemma `fd:parameter-avoidance` ("Compact parameter
avoidance"), reference/SM/sm-3-statesum.tex:2561-2570 (statement), 2571-2584 (proof).  First row
of the fd block 84-88 (AUTHOR_NOTES "deferrals", 2026-09-14: scheduled after the certificate rows,
85 first as the most tractable).  Pure analysis; Mathlib only; no dependency on the project's
diagram layer.

| item | value |
|---|---|
| file | `work/drafts/fd/ParameterAvoidance.lean` (514 lines) |
| main declaration | `SM.fd_parameter_avoidance : SM.ParameterAvoidanceData` |
| bundle | `SM.ParameterAvoidanceData` (3 fields, one per printed clause of the conclusion), hypotheses `SM.ParameterAvoidanceHyp` (4 fields, one per printed clause of the hypothesis) |
| check | `cd work/lean && lake env lean ../drafts/fd/ParameterAvoidance.lean` — 0 errors, 0 warnings, about 7 s |
| axioms | `#print axioms SM.fd_parameter_avoidance` on a /tmp copy: `[propext, Classical.choice, Quot.sound]` (same for `SM.exists_param_avoiding`, `SM.volume_iUnion_zeroParams_eq_zero`, `SM.ParameterAvoidanceHyp.dimH_zeroParams_le`) |
| placeholders | none; every declaration is proved |
| intended home | `work/lean/SM/ParameterAvoidance.lean` (imports Mathlib only; add the port header at porting time) |

## 1. Clause → field map

Printed statement (sm-3:2561-2568): "Let K be a compact subset of a smooth d-dimensional
coordinate manifold and B ⊂ ℝ^m a closed parameter ball. Suppose that F is smooth on a
neighbourhood of K × B, takes values in ℝ^q, and has derivative of rank q > d at every zero in that
product. The parameters a for which F(t,a) = 0 for some t ∈ K form a closed set with empty
interior. The same assertion holds simultaneously for a finite collection of such maps."

Notation: `ℝ^n` is the local notation for `EuclideanSpace ℝ (Fin n)`.

### Hypotheses: `ParameterAvoidanceHyp d m q K c r F : Prop` (`K : Set (ℝ^d)`, `c : ℝ^m`, `r : ℝ`, `F : ℝ^d × ℝ^m → ℝ^q`)

| tex | printed clause | field |
|---|---|---|
| 2562-2563 | "Let K be a compact subset of a smooth d-dimensional coordinate manifold" | `compact : IsCompact K` (chart reading FR-PA-1: `K ⊂ ℝ^d`) |
| 2563 | "B ⊂ ℝ^m a closed parameter ball" | `B = Metric.closedBall c r` in the statement of every field (Euclidean ball, FR-PA-4) |
| 2563-2565 | "F is smooth on a neighbourhood of K × B, takes values in ℝ^q" | `smooth : ∃ U, IsOpen U ∧ K ×ˢ Metric.closedBall c r ⊆ U ∧ ContDiffOn ℝ ∞ F U`; values in `ℝ^q` by the type of `F` |
| 2565 | "has derivative of rank q … at every zero in that product" | `rank : ∀ z ∈ K ×ˢ Metric.closedBall c r, F z = 0 → finrank ℝ (fderiv ℝ F z).range = q` (FR-PA-2) |
| 2565 | "rank q > d" | `dim_lt : d < q` |

### Conclusion: `ParameterAvoidanceData : Prop`; the bad set is `zeroParams K (Metric.closedBall c r) F = {a | a ∈ B ∧ ∃ t ∈ K, F (t, a) = 0}`

| tex | printed clause | field |
|---|---|---|
| 2566-2567 | "The parameters a for which F(t,a) = 0 for some t ∈ K form a closed set" | `isClosed : ∀ d m q K c r F, ParameterAvoidanceHyp d m q K c r F → IsClosed (zeroParams K (closedBall c r) F)` |
| 2567 | "with empty interior" | `interior_eq_empty : … → interior (zeroParams K (closedBall c r) F) = ∅` |
| 2567-2568 | "The same assertion holds simultaneously for a finite collection of such maps" | `finite_collection : ∀ (ι : Type) [Finite ι] (d q : ι → ℕ) m K c r F, (∀ i, ParameterAvoidanceHyp (d i) m (q i) (K i) c r (F i)) → IsClosed (⋃ i, zeroParams …) ∧ interior (⋃ i, zeroParams …) = ∅` (FR-PA-5: dimensions may vary with `i`, the ball is shared) |

Row theorem: `SM.fd_parameter_avoidance : ParameterAvoidanceData` (file line 467), assembled from
`ParameterAvoidanceHyp.isClosed_zeroParams`, `ParameterAvoidanceHyp.interior_zeroParams_eq_empty`,
`isClosed_iUnion_of_finite`, `ParameterAvoidance.interior_iUnion_eq_empty_of_isClosed`.

## 2. The route (all proved)

General core, namespace `SM.ParameterAvoidance`, for finite-dimensional real normed spaces
`E`, `P`, `Q` (`E` the coordinate space, `P` the parameter space, `Q` the target); only `C¹` of `F`
is needed there.

| step (tex) | declaration | Mathlib used |
|---|---|---|
| definitions | `zeroSet K B F = (K ×ˢ B) ∩ F⁻¹'{0}`, `zeroParams K B F`, `zeroParams_eq_image : zeroParams = Prod.snd '' zeroSet` | — |
| 2572 "The zero set is compact, so its parameter projection is closed" | `isCompact_zeroSet`, `isClosed_zeroParams` | `ContinuousOn.preimage_isClosed_of_isClosed`, `IsCompact.of_isClosed_subset`, `IsCompact.image`, `IsCompact.isClosed` |
| 2573-2574 "the inverse function theorem express[es] the local zero set as a smooth graph of e = d+m−q variables" | `contDiffAt_uncurry_implicitFunction` (the uncurried `HasStrictFDerivAt.implicitFunction : Q → ker f' → E × P` is `C^n` at `(F z₀, 0)`); `exists_isOpen_dimH_le` (an open `s ∋ z₀` with `dimH (Prod.snd '' (zeroSet ∩ s)) ≤ finrank (ker f')`) | `ContDiffAt.hasStrictFDerivAt`, `HasStrictFDerivAt.implicitFunctionDataOfComplemented`, `ImplicitFunctionData.contDiffAt_implicitFunction`, `ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range`, `HasStrictFDerivAt.implicitToOpenPartialHomeomorph` (`_fst`, `_self`, `mem_…_source`, `isOpen_inter_preimage`), `HasStrictFDerivAt.eq_implicitFunction`, `ContDiffAt.eventually`, `eventually_nhds_iff`, `ContDiffAt.differentiableAt`, `DifferentiableOn.dimH_image_le`, `dimH_mono`, `Real.dimH_univ_eq_finrank` |
| 2574 "e = d + m − q" | `finrank_ker_add_of_range_eq_top`, `finrank_ker_fderiv_add` (`dim ker + dim Q = dim E + dim P`) | `LinearMap.finrank_range_add_finrank_ker`, `finrank_top`, `Module.finrank_prod` |
| 2575-2576, 2582 "Finitely many such charts … cover the zero set … A finite union of the chart images has the same estimate" | `dimH_zeroParams_le` (`dimH (zeroParams) ≤ N` if every kernel has dimension `≤ N`), `dimH_zeroParams_le_sub` (`≤ dim E + dim P − dim Q`) | `IsCompact.elim_finite_subcover_image`, `dimH_bUnion`, `iSup₂_le` |
| 2577-2583 the volume estimate, "This proves empty interior" | `zeroParams_eq_empty_or_dimH_lt` (no zero at all, or `dimH < dim P`), `dense_compl_zeroParams`, `interior_zeroParams_eq_empty` | `dense_compl_of_dimH_lt_finrank`, `interior_eq_empty_iff_dense_compl` |
| 2582-2583 finite collection | `interior_iUnion_eq_empty_of_isClosed` (countable union of closed sets with empty interior, Baire space) | `dense_iInter_of_isOpen` (Baire), `BaireSpace.of_completelyPseudoMetrizable` for `ℝ^m` |
| unprinted export | `measure_zeroParams_eq_zero` (null for every additive Haar measure on `P`) | `hausdorffMeasure_of_dimH_lt`, `isAddHaarMeasure_hausdorffMeasure` (instance), `Measure.isAddLeftInvariant_eq_smul`, `Measure.smul_apply` |

Printed level, namespace `SM`, on `ℝ^d × ℝ^m → ℝ^q` with `Metric.closedBall c r`:
`rank_eq_iff_range_eq_top` (FR-PA-2), `ParameterAvoidanceHyp.range_eq_top`,
`ParameterAvoidanceHyp.isClosed_zeroParams`, `ParameterAvoidanceHyp.dimH_zeroParams_le`
(`dimH ≤ d + m − q`), `ParameterAvoidanceHyp.interior_zeroParams_eq_empty`,
`fd_parameter_avoidance` (the row), `ParameterAvoidanceHyp.volume_zeroParams_eq_zero`,
`volume_iUnion_zeroParams_eq_zero` (Lebesgue-null, unprinted), `exists_param_avoiding` (consumer
corollary, unprinted: for `0 < r` and any `ε > 0` there is `a ∈ closedBall c r` with `dist a c < ε`
avoiding every bad set of a finite collection — the form used at sm-3:2653-2654 and 2711-2712).

The printed proof's box-counting argument ("Subdividing an e-cube into O(n^e) pieces … total volume
O(n^{e−m}) … tends to zero") is replaced by its Hausdorff-dimension form: a differentiable image of
a set of dimension `e` has `dimH ≤ e`, and a set of `dimH < m` in `ℝ^m` has dense complement.  The
mathematical content is identical (the Hausdorff dimension bound is exactly the vanishing of the
`m`-dimensional box-counting volume); Sard's theorem is not used, as printed.

## 3. Readings and fidelity risks

* **FR-PA-1 (chart reading of "coordinate manifold").**  Printed: "a compact subset of a smooth
  d-dimensional coordinate manifold".  The paper does not define the phrase elsewhere (the only
  occurrence in reference/SM/*.tex is this statement) and its proof works in coordinates.  Lean:
  `K` is a compact subset of the coordinate space `ℝ^d`.  Reduction of the manifold statement to
  this one: a compact subset of a `d`-manifold is a finite union of compact pieces each inside one
  chart; pulling `F` back through each chart gives finitely many maps on `ℝ^d × ℝ^m` with the same
  zero parameters, and `finite_collection` applies.  The consumers (sm-3:2653 with `d = 1` on `S¹`;
  sm-3:2711 with `(d,q) = (2,3), (3,4)` on compact subsets of `(S¹)²`, `(S¹)³`) lift through the
  periodic covering `ℝ^d → (S¹)^d`, which preserves compactness of the preimage in `[0,1]^d` and
  the zero-parameter set exactly.  A statement over Mathlib's `IsManifold` was judged not worth the
  cost (chart transfer of `mfderiv` ranks); this is the main fidelity risk of the row.
* **FR-PA-2 (rank).**  "derivative of rank q" is `finrank ℝ (fderiv ℝ F z).range = q`; for values in
  `ℝ^q` this is equivalent to the derivative being onto (`rank_eq_iff_range_eq_top`), which is what
  the proof uses.
* **FR-PA-3 (empty interior via Hausdorff dimension).**  The conclusion is the printed one.  The
  proof route is dimension-theoretic rather than the printed cube subdivision; the intermediate
  bound `dimH ≤ d + m − q` and the Lebesgue-null strengthening are exported as theorems, not as
  bundle fields.
* **FR-PA-4 (the ball).**  `B = Metric.closedBall c r` in `EuclideanSpace ℝ (Fin m)` (Euclidean
  norm), any real radius; only its compactness is used.  The empty or one-point ball is allowed and
  makes the statement trivial.
* **FR-PA-5 (finite collection).**  "Simultaneously" is read as: the union of the bad sets is
  closed with empty interior, so a single parameter avoids all of them (`exists_param_avoiding`).
  The maps may have different `(d i, q i)` and share `m`, `c`, `r`.
* **Smoothness.**  The hypothesis keeps the printed `C^∞` (`ContDiffOn ℝ ∞ F U`); the proof uses
  only `C¹` (`hF.of_le`), so the general core is stated for `ContDiffOn ℝ 1`.

## 4. Open items

1. Port to `work/lean/SM/ParameterAvoidance.lean` (Mathlib-only imports; the port header per the
   accepted modules' convention).  No project module depends on it yet; the consumers are the
   later fd rows (86-88, generic front), not yet drafted.
2. A genuine-manifold statement (Mathlib `IsManifold (𝓡 d)`) remains unformalised (FR-PA-1).  If
   the fd consumers are eventually formalised on `S¹`-domains, the periodic-lift reduction described
   under FR-PA-1 should be proved once as a wrapper (`Function.Periodic` maps on `ℝ^d`).
3. `interior_iUnion_eq_empty_of_isClosed` uses the Baire category theorem (`dense_iInter_of_isOpen`)
   for what is a finite union; a Baire-free finite induction would remove the dependency on
   `Mathlib.Topology.Baire.*` if desired.  Not a correctness issue.
4. Mathlib API notes for the porter: this Mathlib pin names the implicit-function homeomorphism
   `HasStrictFDerivAt.implicitToOpenPartialHomeomorph`; `ContDiffAt.differentiableAt` and
   `ContDiffAt.hasStrictFDerivAt` take `n ≠ 0`; `ContDiffOn.dimH_image_le` is deprecated in favour of
   `DifferentiableOn.dimH_image_le` (used).  `LinearMap.range`/`LinearMap.ker` of a continuous
   linear map must be written with dot notation (`f'.range`, `f'.ker`) for the coercion to resolve.
