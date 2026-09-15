import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # SM fd:parameter-avoidance — compact parameter avoidance (row 85)

Source: reference/SM/sm-3-statesum.tex:2561-2570 (statement), 2571-2584 (proof).  Drafted 2026-09-14
in work/drafts/fd/ (the fd block 84-88, scheduled after the certificate rows, AUTHOR_NOTES
"deferrals" 2026-09-14; row 85 first as the most tractable).  Pure analysis: no dependency on the
project's diagram layer, Mathlib only.  Intended home: `work/lean/SM/ParameterAvoidance.lean`.
Main declaration: `SM.fd_parameter_avoidance : ParameterAvoidanceData`.
Check: `cd work/lean && lake env lean ../drafts/fd/ParameterAvoidance.lean`.

## The printed statement (sm-3:2561-2568, verbatim)

"Let K be a compact subset of a smooth d-dimensional coordinate manifold and B ⊂ ℝ^m a closed
parameter ball. Suppose that F is smooth on a neighbourhood of K × B, takes values in ℝ^q, and has
derivative of rank q > d at every zero in that product. The parameters a for which F(t,a) = 0 for
some t ∈ K form a closed set with empty interior. The same assertion holds simultaneously for a
finite collection of such maps."

Printed proof (sm-3:2571-2584): the zero set is compact, so its parameter projection is closed; at
each zero the inverse function theorem writes the local zero set as a smooth graph of
`e = d + m − q < m` variables; finitely many charts cover the zero set; the parameter projections are
Lipschitz images of `e`-cubes, of `m`-volume `O(n^{e−m}) → 0`, so no open `m`-box is covered; a
finite union has the same estimate — "without Sard's theorem".

## Printed notion → Lean

| printed | Lean |
|---|---|
| "a smooth d-dimensional coordinate manifold", `K` compact in it (2562-2563) | the coordinate space `ℝ^d = EuclideanSpace ℝ (Fin d)`; `K : Set (ℝ^d)`, `compact : IsCompact K` (chart reading, FR-PA-1) |
| "B ⊂ ℝ^m a closed parameter ball" (2563) | `Metric.closedBall c r` in `ℝ^m = EuclideanSpace ℝ (Fin m)` (Euclidean ball; centre `c`, radius `r`) |
| "F is smooth on a neighbourhood of K × B, takes values in ℝ^q" (2563-2565) | `F : ℝ^d × ℝ^m → ℝ^q`, `smooth : ∃ U, IsOpen U ∧ K ×ˢ closedBall c r ⊆ U ∧ ContDiffOn ℝ ∞ F U` |
| "has derivative of rank q … at every zero in that product" (2565) | `rank : ∀ z ∈ K ×ˢ closedBall c r, F z = 0 → finrank ℝ (LinearMap.range (fderiv ℝ F z)) = q` (equivalently the derivative is onto `ℝ^q`, `ParameterAvoidanceHyp.range_eq_top`; FR-PA-2) |
| "rank q > d" (2565) | `dim_lt : d < q` |
| "The parameters a for which F(t,a) = 0 for some t ∈ K" (2566) | `zeroParams K B F = {a | a ∈ B ∧ ∃ t ∈ K, F (t, a) = 0}` = `Prod.snd '' zeroSet K B F` |
| "form a closed set" (2566-2567) | field `isClosed` |
| "with empty interior" (2567) | field `interior_eq_empty` (route: Hausdorff dimension `≤ d + m − q < m`, FR-PA-3) |
| "The same assertion holds simultaneously for a finite collection of such maps" (2567-2568) | field `finite_collection`: for `ι` finite and maps `F i : ℝ^(d i) × ℝ^m → ℝ^(q i)` (the dimensions `d i`, `q i` may vary, as in the consumer sm-3:2711 with `(d,q) = (2,3)` and `(3,4)`), the union of the bad sets is closed with empty interior |

## Route (§1, general finite-dimensional real normed spaces `E`, `P`, `Q`)

* `isClosed_zeroParams`: `zeroSet = (K ×ˢ B) ∩ F⁻¹{0}` is compact (`ContinuousOn.preimage_isClosed_of_isClosed`
  inside the compact `K ×ˢ B`), its projection `Prod.snd '' zeroSet` is compact, hence closed (sm-3:2572).
* `contDiffAt_uncurry_implicitFunction`: Mathlib's finite-dimensional implicit function
  `HasStrictFDerivAt.implicitFunction : Q → ker f' → E × P` is `C^n` near `(F z₀, 0)` when `F` is
  (from `ImplicitFunctionData.contDiffAt_implicitFunction`).
* `exists_isOpen_dimH_le` (sm-3:2573-2574): near a zero `z₀` with onto derivative `f'`, every zero
  `x` is `implicitFunction 0 ((φ x).2)` (`HasStrictFDerivAt.eq_implicitFunction`), so the local
  parameter projection is the image of an open subset of `ker f'` under the differentiable map
  `y ↦ (implicitFunction 0 y).2`; `DifferentiableOn.dimH_image_le` and `Real.dimH_univ_eq_finrank`
  give `dimH ≤ finrank (ker f') = d + m − q`.
* `dimH_zeroParams_le` (sm-3:2575-2576, 2582): finitely many such open sets cover the compact zero
  set (`IsCompact.elim_finite_subcover_image`); `dimH_bUnion` bounds the finite union.
* `zeroParams_eq_empty_or_dimH_lt`, `dense_compl_zeroParams`, `interior_zeroParams_eq_empty`
  (sm-3:2577-2583): either there is no zero at all, or `dimH < m = finrank P`, which gives a dense
  complement (`dense_compl_of_dimH_lt_finrank`), i.e. empty interior.  This replaces the printed
  box-counting estimate by its Hausdorff-dimension form; no Sard theorem is used.
* `measure_zeroParams_eq_zero` (unprinted export, the measure form of sm-3:2577-2582): `dimH < m`
  makes the bad set `μH[m]`-null (`hausdorffMeasure_of_dimH_lt`) and every additive Haar measure is
  a multiple of `μH[m]` (`Measure.isAddLeftInvariant_eq_smul`); on `ℝ^m` this is Lebesgue-null
  (`ParameterAvoidanceHyp.volume_zeroParams_eq_zero`, `volume_iUnion_zeroParams_eq_zero`).
* `interior_iUnion_eq_empty_of_isClosed`: a countable (here finite) union of closed sets with empty
  interior has empty interior (`dense_iInter_of_isOpen`, `ℝ^m` is a Baire space).

## Fidelity readings recorded

* **FR-PA-1 (chart reading of "coordinate manifold").** The printed proof works in coordinates and
  the paper does not define "coordinate manifold" elsewhere.  Lean: `K` is a compact subset of the
  coordinate space `ℝ^d`.  A compact subset of a genuine `d`-manifold is a finite union of compact
  pieces each inside one chart, and the finite-collection clause (`finite_collection`) then gives the
  manifold statement chart by chart (the consumers sm-3:2653, 2711 apply the lemma to `S¹`, `(S¹)²`,
  `(S¹)³`, whose maps lift to periodic maps on `ℝ^d`).  A statement over Mathlib's `IsManifold`
  would cost a chart-transfer of `mfderiv` ranks and is not attempted here.
* **FR-PA-2 (rank).** "derivative of rank q" is rendered as `finrank ℝ (range (fderiv ℝ F z)) = q`,
  which for values in `ℝ^q` is equivalent to the derivative being onto (`rank_eq_iff_range_eq_top`).
* **FR-PA-3 (empty interior via Hausdorff dimension).** The conclusion is the printed one (closed,
  empty interior; fields `isClosed`, `interior_eq_empty`, `finite_collection`).  The proof bounds
  the Hausdorff dimension of the bad set by `d + m − q < m` (exported as `dimH_zeroParams_le_sub`,
  `ParameterAvoidanceHyp.dimH_zeroParams_le`), the modern form of the printed volume estimate; the
  Lebesgue-null strengthening is exported as well (`ParameterAvoidanceHyp.volume_zeroParams_eq_zero`)
  but is not a bundle field, since the printed conclusion is only "empty interior".
* **FR-PA-5 (the finite collection).** "Simultaneously for a finite collection" is read as: the
  union of the bad sets is closed with empty interior (equivalently its complement is open and
  dense, so one parameter avoids every bad set at once: `exists_param_avoiding`).  The maps of the
  collection may have different `d i`, `q i` (the consumer sm-3:2711 uses `(2,3)` and `(3,4)`
  together) but share the parameter ball.  Only `C¹` of `F` is used in the proof; the hypothesis
  keeps the printed `C^∞`.
* **FR-PA-4 (the ball).** `B` is the Euclidean closed ball `Metric.closedBall c r` of
  `EuclideanSpace ℝ (Fin m)`; any radius `r : ℝ` is allowed (a nonpositive radius gives a point or the
  empty set, for which the statement is trivial).  Only compactness of `B` is used. -/

namespace SM

open scoped ContDiff Topology
open Set Filter Module

noncomputable section

/-! ## 1. The general core: `E`, `P`, `Q` finite-dimensional real normed spaces -/

namespace ParameterAvoidance

section defs

variable {E P Q : Type*} [Zero Q]

/-- The zeros of `F` in the product `K × B` ("every zero in that product", sm-3:2565). -/
def zeroSet (K : Set E) (B : Set P) (F : E × P → Q) : Set (E × P) :=
  (K ×ˢ B) ∩ F ⁻¹' {0}

/-- "The parameters a for which F(t,a) = 0 for some t ∈ K" (sm-3:2566): the parameters `a ∈ B`
with a zero `(t, a)`, `t ∈ K`. -/
def zeroParams (K : Set E) (B : Set P) (F : E × P → Q) : Set P :=
  {a | a ∈ B ∧ ∃ t ∈ K, F (t, a) = 0}

theorem mem_zeroSet {K : Set E} {B : Set P} {F : E × P → Q} {z : E × P} :
    z ∈ zeroSet K B F ↔ z ∈ K ×ˢ B ∧ F z = 0 := Iff.rfl

theorem mem_zeroParams {K : Set E} {B : Set P} {F : E × P → Q} {a : P} :
    a ∈ zeroParams K B F ↔ a ∈ B ∧ ∃ t ∈ K, F (t, a) = 0 := Iff.rfl

/-- The bad parameters are the parameter projection of the zero set (sm-3:2572). -/
theorem zeroParams_eq_image (K : Set E) (B : Set P) (F : E × P → Q) :
    zeroParams K B F = Prod.snd '' zeroSet K B F := by
  ext a
  rw [mem_zeroParams]
  constructor
  · rintro ⟨haB, t, htK, hF⟩
    exact ⟨(t, a), mem_zeroSet.2 ⟨⟨htK, haB⟩, hF⟩, rfl⟩
  · rintro ⟨⟨t, a'⟩, hz, rfl⟩
    obtain ⟨⟨htK, haB⟩, hF⟩ := mem_zeroSet.1 hz
    exact ⟨haB, t, htK, hF⟩

end defs

section topology

variable {E P Q : Type*} [TopologicalSpace E] [TopologicalSpace P] [TopologicalSpace Q]
  [T2Space E] [T2Space P] [T1Space Q] [Zero Q]

/-- "The zero set is compact" (sm-3:2572). -/
theorem isCompact_zeroSet {K : Set E} {B : Set P} {F : E × P → Q} (hK : IsCompact K)
    (hB : IsCompact B) (hF : ContinuousOn F (K ×ˢ B)) : IsCompact (zeroSet K B F) :=
  (hK.prod hB).of_isClosed_subset
    (hF.preimage_isClosed_of_isClosed (hK.prod hB).isClosed isClosed_singleton) inter_subset_left

/-- "so its parameter projection is closed" (sm-3:2572). -/
theorem isClosed_zeroParams {K : Set E} {B : Set P} {F : E × P → Q} (hK : IsCompact K)
    (hB : IsCompact B) (hF : ContinuousOn F (K ×ˢ B)) : IsClosed (zeroParams K B F) := by
  rw [zeroParams_eq_image]
  exact ((isCompact_zeroSet hK hB hF).image continuous_snd).isClosed

end topology

section implicit

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- Mathlib's finite-dimensional implicit function `HasStrictFDerivAt.implicitFunction`
(`Y → ker f' → X`, uncurried) is `C^n` at `(f a, 0)` when `f` is `C^n` at `a` (the smooth-graph
clause of sm-3:2573-2574).  Transcribes `ImplicitFunctionData.contDiffAt_implicitFunction` to the
complemented-kernel data used by the finite-dimensional theorem. -/
theorem contDiffAt_uncurry_implicitFunction {f : X → Y} {f' : X →L[ℝ] Y} {a : X}
    (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) {n : ℕ∞ω} (hn : n ≠ 0)
    (hcd : ContDiffAt ℝ n f a) :
    ContDiffAt ℝ n (Function.uncurry (hf.implicitFunction f f' hf')) (f a, 0) := by
  have : CompleteSpace Y := FiniteDimensional.complete ℝ Y
  have hr : ContDiffAt ℝ n
      (HasStrictFDerivAt.implicitFunctionDataOfComplemented f f' hf hf'
        f'.ker_closedComplemented_of_finiteDimensional_range).rightFun
      (HasStrictFDerivAt.implicitFunctionDataOfComplemented f f' hf hf'
        f'.ker_closedComplemented_of_finiteDimensional_range).pt := by
    simp only [HasStrictFDerivAt.implicitFunctionDataOfComplemented]
    exact (ContinuousLinearMap.contDiff _).contDiffAt.comp a (contDiffAt_id.sub contDiffAt_const)
  have h := (HasStrictFDerivAt.implicitFunctionDataOfComplemented f f' hf hf'
    f'.ker_closedComplemented_of_finiteDimensional_range).contDiffAt_implicitFunction
    (by simpa using hcd) hr hn
  have hpt : (HasStrictFDerivAt.implicitFunctionDataOfComplemented f f' hf hf'
      f'.ker_closedComplemented_of_finiteDimensional_range).prodFun
      (HasStrictFDerivAt.implicitFunctionDataOfComplemented f f' hf hf'
        f'.ker_closedComplemented_of_finiteDimensional_range).pt = (f a, 0) := by
    simp [HasStrictFDerivAt.implicitFunctionDataOfComplemented, ImplicitFunctionData.prodFun_apply]
  rw [hpt] at h
  exact h

end implicit

section rank

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Rank–nullity for an onto derivative: `dim ker f' + dim Y = dim X`. -/
theorem finrank_ker_add_of_range_eq_top (f' : X →L[ℝ] Y) (hf' : f'.range = ⊤) :
    finrank ℝ f'.ker + finrank ℝ Y = finrank ℝ X := by
  have h := LinearMap.finrank_range_add_finrank_ker (f' : X →ₗ[ℝ] Y)
  rw [hf', finrank_top] at h
  omega

end rank

section analytic

variable {E P Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  {K : Set E} {B : Set P} {F : E × P → Q}

/-- The local chart of the printed proof (sm-3:2573-2574): near a zero `z₀` at which the derivative
is onto, the parameter projection of the zero set has Hausdorff dimension at most
`dim ker (fderiv ℝ F z₀)` (`= d + m − q`).  The local zero set is parametrised by an open subset of
the kernel through Mathlib's implicit function `y ↦ implicitFunction 0 y`, which is differentiable
there, and differentiable maps do not raise Hausdorff dimension. -/
theorem exists_isOpen_dimH_le {z₀ : E × P} (hz₀ : z₀ ∈ zeroSet K B F)
    (hF : ContDiffAt ℝ 1 F z₀) (hrank : (fderiv ℝ F z₀).range = ⊤) :
    ∃ s : Set (E × P), IsOpen s ∧ z₀ ∈ s ∧
      dimH (Prod.snd '' (zeroSet K B F ∩ s)) ≤ (finrank ℝ (fderiv ℝ F z₀).ker : ENNReal) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have : CompleteSpace P := FiniteDimensional.complete ℝ P
  have hF0 : F z₀ = 0 := (mem_zeroSet.1 hz₀).2
  have hf : HasStrictFDerivAt F (fderiv ℝ F z₀) z₀ := hF.hasStrictFDerivAt one_ne_zero
  have hg1 : ContDiffAt ℝ 1 (Function.uncurry (hf.implicitFunction F (fderiv ℝ F z₀) hrank))
      (F z₀, 0) :=
    contDiffAt_uncurry_implicitFunction hf hrank one_ne_zero hF
  obtain ⟨V, hV, hVo, hV0⟩ := eventually_nhds_iff.1 (hg1.eventually (by simp))
  obtain ⟨W, hW, hWo, hW0⟩ := eventually_nhds_iff.1 (hf.eq_implicitFunction hrank)
  set φ := hf.implicitToOpenPartialHomeomorph F (fderiv ℝ F z₀) hrank with hφ
  set g := hf.implicitFunction F (fderiv ℝ F z₀) hrank with hg
  have hφ0 : φ z₀ = (F z₀, 0) := hf.implicitToOpenPartialHomeomorph_self hrank
  have hφ1 : ∀ x, (φ x).1 = F x := fun x => hf.implicitToOpenPartialHomeomorph_fst hrank x
  refine ⟨W ∩ (φ.source ∩ φ ⁻¹' V), hWo.inter (φ.isOpen_inter_preimage hVo),
    ⟨hW0, hf.mem_implicitToOpenPartialHomeomorph_source hrank, ?_⟩, ?_⟩
  · show φ z₀ ∈ V
    rw [hφ0]
    exact hV0
  · set T : Set (fderiv ℝ F z₀).ker := {y | ((0 : Q), y) ∈ V} with hT
    set Ψ : (fderiv ℝ F z₀).ker → P := fun y => (g 0 y).2 with hΨ
    have hΨd : DifferentiableOn ℝ Ψ T := by
      intro y hy
      have h1 : DifferentiableAt ℝ (Function.uncurry g) ((0 : Q), y) :=
        (hV _ hy).differentiableAt one_ne_zero
      have h2 : DifferentiableAt ℝ (fun y : (fderiv ℝ F z₀).ker => ((0 : Q), y)) y :=
        (differentiableAt_const _).prodMk differentiableAt_id
      exact ((h1.comp y h2).snd).differentiableWithinAt
    have hsub : Prod.snd '' (zeroSet K B F ∩ (W ∩ (φ.source ∩ φ ⁻¹' V))) ⊆ Ψ '' T := by
      rintro a ⟨x, ⟨hxZ, hxW, _, hxV⟩, rfl⟩
      have hFx : F x = 0 := (mem_zeroSet.1 hxZ).2
      have hφx1 : (φ x).1 = 0 := by rw [hφ1 x, hFx]
      have hφx : φ x = ((0 : Q), (φ x).2) := Prod.ext hφx1 rfl
      refine ⟨(φ x).2, ?_, ?_⟩
      · have hxV' : φ x ∈ V := hxV
        rw [hφx] at hxV'
        exact hxV'
      · show (g 0 (φ x).2).2 = x.2
        have hx : g (F x) (φ x).2 = x := hW x hxW
        rw [hFx] at hx
        rw [hx]
    calc dimH (Prod.snd '' (zeroSet K B F ∩ (W ∩ (φ.source ∩ φ ⁻¹' V))))
        ≤ dimH (Ψ '' T) := dimH_mono hsub
      _ ≤ dimH T := hΨd.dimH_image_le
      _ ≤ dimH (univ : Set (fderiv ℝ F z₀).ker) := dimH_mono (subset_univ _)
      _ = finrank ℝ (fderiv ℝ F z₀).ker := Real.dimH_univ_eq_finrank _

/-- The finite cover (sm-3:2575-2576, 2582): if every zero in `K × B` has onto derivative with
kernel of dimension at most `N`, the bad parameter set has Hausdorff dimension at most `N`. -/
theorem dimH_zeroParams_le (hK : IsCompact K) (hB : IsCompact B) {U : Set (E × P)}
    (hU : IsOpen U) (hKBU : K ×ˢ B ⊆ U) (hF : ContDiffOn ℝ 1 F U)
    (hrank : ∀ z ∈ zeroSet K B F, (fderiv ℝ F z).range = ⊤) {N : ℕ}
    (hN : ∀ z ∈ zeroSet K B F, finrank ℝ (fderiv ℝ F z).ker ≤ N) :
    dimH (zeroParams K B F) ≤ N := by
  have hZc : IsCompact (zeroSet K B F) := isCompact_zeroSet hK hB (hF.continuousOn.mono hKBU)
  have hloc : ∀ z ∈ zeroSet K B F, ∃ s : Set (E × P), IsOpen s ∧ z ∈ s ∧
      dimH (Prod.snd '' (zeroSet K B F ∩ s)) ≤ (finrank ℝ (fderiv ℝ F z).ker : ENNReal) :=
    fun z hz => exists_isOpen_dimH_le hz
      (hF.contDiffAt (hU.mem_nhds (hKBU (mem_zeroSet.1 hz).1))) (hrank z hz)
  choose! s hs using hloc
  obtain ⟨b, hbZ, hbfin, hcov⟩ := hZc.elim_finite_subcover_image (fun z hz => (hs z hz).1)
    (fun z hz => mem_biUnion hz (hs z hz).2.1)
  have himg : zeroParams K B F ⊆ ⋃ z ∈ b, Prod.snd '' (zeroSet K B F ∩ s z) := by
    rw [zeroParams_eq_image]
    rintro a ⟨x, hxZ, rfl⟩
    obtain ⟨z, hzb, hxs⟩ := mem_iUnion₂.1 (hcov hxZ)
    exact mem_iUnion₂.2 ⟨z, hzb, x, ⟨hxZ, hxs⟩, rfl⟩
  calc dimH (zeroParams K B F) ≤ dimH (⋃ z ∈ b, Prod.snd '' (zeroSet K B F ∩ s z)) :=
        dimH_mono himg
    _ = ⨆ z ∈ b, dimH (Prod.snd '' (zeroSet K B F ∩ s z)) := dimH_bUnion hbfin.countable _
    _ ≤ N := iSup₂_le fun z hz =>
        (hs z (hbZ hz)).2.2.trans (by exact_mod_cast hN z (hbZ hz))

omit [FiniteDimensional ℝ Q] in
/-- At every zero with onto derivative, `dim ker + dim Q = dim E + dim P` (the printed
`e = d + m − q`, sm-3:2574). -/
theorem finrank_ker_fderiv_add {z : E × P} (hrank : (fderiv ℝ F z).range = ⊤) :
    finrank ℝ (fderiv ℝ F z).ker + finrank ℝ Q = finrank ℝ E + finrank ℝ P := by
  have h := finrank_ker_add_of_range_eq_top (fderiv ℝ F z) hrank
  rw [Module.finrank_prod] at h
  exact h

/-- The printed dimension count: the bad set has Hausdorff dimension at most
`dim E + dim P − dim Q` (sm-3:2574, `e = d + m − q`). -/
theorem dimH_zeroParams_le_sub (hK : IsCompact K) (hB : IsCompact B) {U : Set (E × P)}
    (hU : IsOpen U) (hKBU : K ×ˢ B ⊆ U) (hF : ContDiffOn ℝ 1 F U)
    (hrank : ∀ z ∈ zeroSet K B F, (fderiv ℝ F z).range = ⊤) :
    dimH (zeroParams K B F) ≤ ((finrank ℝ E + finrank ℝ P - finrank ℝ Q : ℕ) : ENNReal) :=
  dimH_zeroParams_le hK hB hU hKBU hF hrank fun z hz => by
    have := finrank_ker_fderiv_add (F := F) (hrank z hz)
    omega

/-- The dimension count behind sm-3:2577-2583: either there is no zero at all (the bad set is
empty), or the bad set has Hausdorff dimension `< dim P`. -/
theorem zeroParams_eq_empty_or_dimH_lt (hK : IsCompact K) (hB : IsCompact B) {U : Set (E × P)}
    (hU : IsOpen U) (hKBU : K ×ˢ B ⊆ U) (hF : ContDiffOn ℝ 1 F U)
    (hrank : ∀ z ∈ zeroSet K B F, (fderiv ℝ F z).range = ⊤)
    (hlt : finrank ℝ E < finrank ℝ Q) :
    zeroParams K B F = ∅ ∨ dimH (zeroParams K B F) < (finrank ℝ P : ENNReal) := by
  rcases (zeroSet K B F).eq_empty_or_nonempty with hZ | ⟨z, hz⟩
  · left
    rw [zeroParams_eq_image, hZ, image_empty]
  · right
    have hP : 0 < finrank ℝ P := by
      have := finrank_ker_fderiv_add (F := F) (hrank z hz)
      omega
    calc dimH (zeroParams K B F) ≤ ((finrank ℝ P - 1 : ℕ) : ENNReal) :=
          dimH_zeroParams_le hK hB hU hKBU hF hrank fun z hz => by
            have := finrank_ker_fderiv_add (F := F) (hrank z hz)
            omega
      _ < (finrank ℝ P : ENNReal) := by exact_mod_cast Nat.sub_lt hP one_pos

/-- "This proves empty interior" (sm-3:2577-2583) in its dense-complement form: when
`dim E < dim Q`, the complement of the bad parameter set is dense in `P`. -/
theorem dense_compl_zeroParams (hK : IsCompact K) (hB : IsCompact B) {U : Set (E × P)}
    (hU : IsOpen U) (hKBU : K ×ˢ B ⊆ U) (hF : ContDiffOn ℝ 1 F U)
    (hrank : ∀ z ∈ zeroSet K B F, (fderiv ℝ F z).range = ⊤)
    (hlt : finrank ℝ E < finrank ℝ Q) : Dense (zeroParams K B F)ᶜ := by
  rcases zeroParams_eq_empty_or_dimH_lt hK hB hU hKBU hF hrank hlt with h0 | hlt'
  · rw [h0, compl_empty]
    exact dense_univ
  · exact dense_compl_of_dimH_lt_finrank hlt'

open MeasureTheory in
/-- Unprinted strengthening (the printed proof is a volume estimate, sm-3:2577-2582): the bad
parameter set is null for every additive Haar measure on `P`, because `dimH < dim P` makes it
`μH[dim P]`-null and every additive Haar measure is a multiple of `μH[dim P]`. -/
theorem measure_zeroParams_eq_zero [MeasurableSpace P] [BorelSpace P]
    [SecondCountableTopology P] (μ : Measure P) [μ.IsAddHaarMeasure] (hK : IsCompact K)
    (hB : IsCompact B) {U : Set (E × P)} (hU : IsOpen U) (hKBU : K ×ˢ B ⊆ U)
    (hF : ContDiffOn ℝ 1 F U) (hrank : ∀ z ∈ zeroSet K B F, (fderiv ℝ F z).range = ⊤)
    (hlt : finrank ℝ E < finrank ℝ Q) : μ (zeroParams K B F) = 0 := by
  rcases zeroParams_eq_empty_or_dimH_lt hK hB hU hKBU hF hrank hlt with h0 | hlt'
  · rw [h0, measure_empty]
  · have hH : μH[((finrank ℝ P : NNReal) : ℝ)] (zeroParams K B F) = 0 :=
      hausdorffMeasure_of_dimH_lt (by exact_mod_cast hlt')
    have hH' : μH[(finrank ℝ P : ℝ)] (zeroParams K B F) = 0 := by simpa using hH
    rw [Measure.isAddLeftInvariant_eq_smul μ μH[finrank ℝ P], Measure.smul_apply, hH', smul_zero]

/-- "with empty interior" (sm-3:2567). -/
theorem interior_zeroParams_eq_empty (hK : IsCompact K) (hB : IsCompact B) {U : Set (E × P)}
    (hU : IsOpen U) (hKBU : K ×ˢ B ⊆ U) (hF : ContDiffOn ℝ 1 F U)
    (hrank : ∀ z ∈ zeroSet K B F, (fderiv ℝ F z).range = ⊤)
    (hlt : finrank ℝ E < finrank ℝ Q) : interior (zeroParams K B F) = ∅ :=
  interior_eq_empty_iff_dense_compl.2 (dense_compl_zeroParams hK hB hU hKBU hF hrank hlt)

end analytic

/-- "A finite union of the chart images has the same estimate" (sm-3:2582): a countable (in
particular finite) union of closed sets with empty interior has empty interior, in a Baire space. -/
theorem interior_iUnion_eq_empty_of_isClosed {X : Type*} [TopologicalSpace X] [BaireSpace X]
    {ι : Sort*} [Countable ι] {s : ι → Set X} (hc : ∀ i, IsClosed (s i))
    (hi : ∀ i, interior (s i) = ∅) : interior (⋃ i, s i) = ∅ := by
  rw [interior_eq_empty_iff_dense_compl, compl_iUnion]
  exact dense_iInter_of_isOpen (fun i => (hc i).isOpen_compl)
    (fun i => interior_eq_empty_iff_dense_compl.1 (hi i))

end ParameterAvoidance

/-! ## 2. The printed statement on `ℝ^d`, `ℝ^m`, `ℝ^q` -/

/-- `ℝ^n` is `EuclideanSpace ℝ (Fin n)` (the Euclidean norm, so that "closed ball" is the
Euclidean ball). -/
local notation "ℝ^" n:max => EuclideanSpace ℝ (Fin n)

open ParameterAvoidance

/-- The printed hypotheses of fd:parameter-avoidance on one map (sm-3:2562-2565), one field per
clause.  `K ⊂ ℝ^d` (chart reading, FR-PA-1), `B = closedBall c r ⊂ ℝ^m`, `F : ℝ^d × ℝ^m → ℝ^q`. -/
structure ParameterAvoidanceHyp (d m q : ℕ) (K : Set (ℝ^d)) (c : ℝ^m) (r : ℝ)
    (F : ℝ^d × ℝ^m → ℝ^q) : Prop where
  /-- sm-3:2562-2563 "Let K be a compact subset of a smooth d-dimensional coordinate manifold":
  `K` is a compact subset of the coordinate space `ℝ^d` (FR-PA-1). -/
  compact : IsCompact K
  /-- sm-3:2563-2565 "Suppose that F is smooth on a neighbourhood of K × B, takes values in ℝ^q":
  an open `U ⊇ K × B` on which `F` is `C^∞`; the values lie in `ℝ^q` by the type of `F`. -/
  smooth : ∃ U : Set (ℝ^d × ℝ^m), IsOpen U ∧ K ×ˢ Metric.closedBall c r ⊆ U ∧ ContDiffOn ℝ ∞ F U
  /-- sm-3:2565 "and has derivative of rank q … at every zero in that product" (FR-PA-2). -/
  rank : ∀ z ∈ K ×ˢ Metric.closedBall c r, F z = 0 → finrank ℝ (fderiv ℝ F z).range = q
  /-- sm-3:2565 "rank q > d". -/
  dim_lt : d < q

/-- FR-PA-2: for a linear map into `ℝ^q`, "rank `q`" is "onto". -/
theorem rank_eq_iff_range_eq_top {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {q : ℕ}
    (f' : X →L[ℝ] ℝ^q) : finrank ℝ f'.range = q ↔ f'.range = ⊤ := by
  constructor
  · intro h
    exact Submodule.eq_top_of_finrank_eq (by rw [h, finrank_euclideanSpace_fin])
  · intro h
    rw [h, finrank_top, finrank_euclideanSpace_fin]

theorem ParameterAvoidanceHyp.range_eq_top {d m q : ℕ} {K : Set (ℝ^d)} {c : ℝ^m} {r : ℝ}
    {F : ℝ^d × ℝ^m → ℝ^q} (h : ParameterAvoidanceHyp d m q K c r F) {z : ℝ^d × ℝ^m}
    (hz : z ∈ zeroSet K (Metric.closedBall c r) F) : (fderiv ℝ F z).range = ⊤ :=
  (rank_eq_iff_range_eq_top _).1 (h.rank z (mem_zeroSet.1 hz).1 (mem_zeroSet.1 hz).2)

/-- fd:parameter-avoidance (sm-3:2561-2568), one field per printed clause of the conclusion.  The
hypotheses are `ParameterAvoidanceHyp`; the bad set is
`zeroParams K (closedBall c r) F = {a ∈ B | ∃ t ∈ K, F (t, a) = 0}`. -/
structure ParameterAvoidanceData : Prop where
  /-- sm-3:2566-2567 "The parameters a for which F(t,a) = 0 for some t ∈ K form a closed set". -/
  isClosed : ∀ (d m q : ℕ) (K : Set (ℝ^d)) (c : ℝ^m) (r : ℝ) (F : ℝ^d × ℝ^m → ℝ^q),
    ParameterAvoidanceHyp d m q K c r F → IsClosed (zeroParams K (Metric.closedBall c r) F)
  /-- sm-3:2567 "with empty interior". -/
  interior_eq_empty : ∀ (d m q : ℕ) (K : Set (ℝ^d)) (c : ℝ^m) (r : ℝ) (F : ℝ^d × ℝ^m → ℝ^q),
    ParameterAvoidanceHyp d m q K c r F → interior (zeroParams K (Metric.closedBall c r) F) = ∅
  /-- sm-3:2567-2568 "The same assertion holds simultaneously for a finite collection of such
  maps": for finitely many maps `F i : ℝ^(d i) × ℝ^m → ℝ^(q i)` over the same parameter ball (the
  dimensions may vary with `i`), the union of the bad sets is closed with empty interior. -/
  finite_collection : ∀ (ι : Type) [Finite ι] (d q : ι → ℕ) (m : ℕ) (K : ∀ i, Set (ℝ^(d i)))
    (c : ℝ^m) (r : ℝ) (F : ∀ i, ℝ^(d i) × ℝ^m → ℝ^(q i)),
    (∀ i, ParameterAvoidanceHyp (d i) m (q i) (K i) c r (F i)) →
    IsClosed (⋃ i, zeroParams (K i) (Metric.closedBall c r) (F i)) ∧
      interior (⋃ i, zeroParams (K i) (Metric.closedBall c r) (F i)) = ∅

/-- Closedness for one map, from the hypotheses. -/
theorem ParameterAvoidanceHyp.isClosed_zeroParams {d m q : ℕ} {K : Set (ℝ^d)} {c : ℝ^m} {r : ℝ}
    {F : ℝ^d × ℝ^m → ℝ^q} (h : ParameterAvoidanceHyp d m q K c r F) :
    IsClosed (zeroParams K (Metric.closedBall c r) F) := by
  obtain ⟨U, _, hKBU, hF⟩ := h.smooth
  exact ParameterAvoidance.isClosed_zeroParams h.compact (isCompact_closedBall c r)
    (hF.continuousOn.mono hKBU)

/-- The Hausdorff-dimension count for one map: `dimH ≤ d + m − q` (sm-3:2574). -/
theorem ParameterAvoidanceHyp.dimH_zeroParams_le {d m q : ℕ} {K : Set (ℝ^d)} {c : ℝ^m} {r : ℝ}
    {F : ℝ^d × ℝ^m → ℝ^q} (h : ParameterAvoidanceHyp d m q K c r F) :
    dimH (zeroParams K (Metric.closedBall c r) F) ≤ ((d + m - q : ℕ) : ENNReal) := by
  obtain ⟨U, hU, hKBU, hF⟩ := h.smooth
  have := dimH_zeroParams_le_sub h.compact (isCompact_closedBall c r) hU hKBU (hF.of_le (by simp))
    (fun z hz => h.range_eq_top hz)
  simpa only [finrank_euclideanSpace_fin] using this

/-- Empty interior for one map, from the hypotheses. -/
theorem ParameterAvoidanceHyp.interior_zeroParams_eq_empty {d m q : ℕ} {K : Set (ℝ^d)} {c : ℝ^m}
    {r : ℝ} {F : ℝ^d × ℝ^m → ℝ^q} (h : ParameterAvoidanceHyp d m q K c r F) :
    interior (zeroParams K (Metric.closedBall c r) F) = ∅ := by
  obtain ⟨U, hU, hKBU, hF⟩ := h.smooth
  exact ParameterAvoidance.interior_zeroParams_eq_empty h.compact (isCompact_closedBall c r) hU
    hKBU (hF.of_le (by simp)) (fun z hz => h.range_eq_top hz)
    (by rw [finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]; exact h.dim_lt)

/-- **fd:parameter-avoidance** (sm-3:2561-2568): the row. -/
theorem fd_parameter_avoidance : ParameterAvoidanceData where
  isClosed _ _ _ _ _ _ _ h := h.isClosed_zeroParams
  interior_eq_empty _ _ _ _ _ _ _ h := h.interior_zeroParams_eq_empty
  finite_collection _ _ _ _ _ _ _ _ _ h :=
    ⟨isClosed_iUnion_of_finite fun i => (h i).isClosed_zeroParams,
      interior_iUnion_eq_empty_of_isClosed (fun i => (h i).isClosed_zeroParams)
        (fun i => (h i).interior_zeroParams_eq_empty)⟩

/-- Unprinted strengthening for one map: the bad parameter set is Lebesgue-null in `ℝ^m`
(sm-3:2577-2582 is a volume estimate; the printed conclusion is only "empty interior"). -/
theorem ParameterAvoidanceHyp.volume_zeroParams_eq_zero {d m q : ℕ} {K : Set (ℝ^d)} {c : ℝ^m}
    {r : ℝ} {F : ℝ^d × ℝ^m → ℝ^q} (h : ParameterAvoidanceHyp d m q K c r F) :
    MeasureTheory.volume (zeroParams K (Metric.closedBall c r) F) = 0 := by
  obtain ⟨U, hU, hKBU, hF⟩ := h.smooth
  exact measure_zeroParams_eq_zero MeasureTheory.volume h.compact (isCompact_closedBall c r) hU
    hKBU (hF.of_le (by simp)) (fun z hz => h.range_eq_top hz)
    (by rw [finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]; exact h.dim_lt)

/-- Unprinted strengthening for a finite collection: the union of the bad sets is Lebesgue-null. -/
theorem volume_iUnion_zeroParams_eq_zero {ι : Type} [Finite ι] {d q : ι → ℕ} {m : ℕ}
    {K : ∀ i, Set (ℝ^(d i))} {c : ℝ^m} {r : ℝ} {F : ∀ i, ℝ^(d i) × ℝ^m → ℝ^(q i)}
    (h : ∀ i, ParameterAvoidanceHyp (d i) m (q i) (K i) c r (F i)) :
    MeasureTheory.volume (⋃ i, zeroParams (K i) (Metric.closedBall c r) (F i)) = 0 :=
  MeasureTheory.measure_iUnion_null fun i => (h i).volume_zeroParams_eq_zero

/-! ## 3. Consumer corollary (not a printed clause): "choose a small parameter avoiding all these
zeros" (sm-3:2653-2654), "choose a parameter outside both bad projections" (sm-3:2712). -/

/-- For a finite collection over a ball of positive radius, and any `ε > 0`, there is a parameter
in the ball within `ε` of the centre that is a zero parameter of none of the maps. -/
theorem exists_param_avoiding {ι : Type} [Finite ι] {d q : ι → ℕ} {m : ℕ} {K : ∀ i, Set (ℝ^(d i))}
    {c : ℝ^m} {r : ℝ} {F : ∀ i, ℝ^(d i) × ℝ^m → ℝ^(q i)}
    (h : ∀ i, ParameterAvoidanceHyp (d i) m (q i) (K i) c r (F i)) (hr : 0 < r) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ a ∈ Metric.closedBall c r, dist a c < ε ∧
      ∀ i, a ∉ zeroParams (K i) (Metric.closedBall c r) (F i) := by
  have hd : Dense (⋃ i, zeroParams (K i) (Metric.closedBall c r) (F i))ᶜ :=
    interior_eq_empty_iff_dense_compl.1
      (fd_parameter_avoidance.finite_collection ι d q m K c r F h).2
  have hne : (Metric.ball c (min r ε)).Nonempty := Metric.nonempty_ball.2 (lt_min hr hε)
  obtain ⟨a, ha, hab⟩ := hd.exists_mem_open Metric.isOpen_ball hne
  have hab' : dist a c < min r ε := Metric.mem_ball.1 hab
  refine ⟨a, Metric.mem_closedBall.2 (le_of_lt (lt_of_lt_of_le hab' (min_le_left r ε))),
    lt_of_lt_of_le hab' (min_le_right r ε), fun i hi => ha (mem_iUnion.2 ⟨i, hi⟩)⟩

end

end SM
