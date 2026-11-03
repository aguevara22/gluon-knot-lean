import SourcePrimitiveExtension

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.SourcePrimitiveConsequences
open DirectGLSSW GeometricSmoothingWeights PolygonUniformity Filter Topology

private theorem turnDet_continuous {n : ℕ} (i : Fin n) :
    Continuous (fun q : Fin n → PlanarPoint ℝ => PolygonUniformity.turnDet q i) := by
  unfold PolygonUniformity.turnDet cyclicTangent planarDet
  fun_prop

private theorem eventually_turn_signs {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∀ᶠ r in 𝓝 q, ∀ i : Fin n,
      (0 < PolygonUniformity.turnDet r i ↔ 0 < PolygonUniformity.turnDet q i) ∧
      (PolygonUniformity.turnDet r i < 0 ↔ PolygonUniformity.turnDet q i < 0) := by
  apply Filter.eventually_all.mpr
  intro i
  have hne := PolygonUniformity.turnDet_ne_zero q hq i
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hev : ∀ᶠ r in 𝓝 q, PolygonUniformity.turnDet r i < 0 :=
      ((turnDet_continuous i).continuousAt).eventually (isOpen_Iio.mem_nhds hneg)
    filter_upwards [hev] with r hr
    constructor <;> constructor <;> intro h <;> (try linarith)
  · have hev : ∀ᶠ r in 𝓝 q, 0 < PolygonUniformity.turnDet r i :=
      ((turnDet_continuous i).continuousAt).eventually (isOpen_Ioi.mem_nhds hpos)
    filter_upwards [hev] with r hr
    constructor <;> constructor <;> intro h <;> (try linarith)

private theorem eventually_uniform_iff {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∀ᶠ r in 𝓝 q, PolygonUniform r ↔ PolygonUniform q := by
  filter_upwards [eventually_turn_signs q hq] with r hs
  unfold PolygonUniform
  constructor <;> intro h
  · rcases h with hp | hn
    · exact Or.inl (fun i => (hs i).1.mp (hp i))
    · exact Or.inr (fun i => (hs i).2.mp (hn i))
  · rcases h with hp | hn
    · exact Or.inl (fun i => (hs i).1.mpr (hp i))
    · exact Or.inr (fun i => (hs i).2.mpr (hn i))

private theorem eventually_source_leftCount_eq {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∀ᶠ r in 𝓝 q, SmoothingTurnCount.leftTurnCount r =
      SmoothingTurnCount.leftTurnCount q := by
  simpa only [SmoothingTurnCount.leftTurnCount_eq_literal_filter_card,
    OriginalLeftTurnLocality.leftTurnCount] using
      OriginalLeftTurnLocality.eventually_leftTurnCount_eq q hq

private theorem eventually_prescribedCorner_eq {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∀ᶠ r in 𝓝 q, ∀ hr : CyclicGeneric r,
      GeminiReversalContract.prescribedCorner r hr =
        GeminiReversalContract.prescribedCorner q hq := by
  filter_upwards [HOMFLY.PositivePolygonLocality.eventually_positivePolygon_evaluator_count q hq,
    HOMFLY.PolygonTurnLocality.eventually_positivePolygon_turnInteger q hq]
    with r hEval hTurn
  intro hr
  obtain ⟨hr', hCount, hH⟩ := hEval
  have hp : hr' = hr := Subsingleton.elim _ _
  subst hr'
  simp only [GeminiReversalContract.prescribedCorner, hCount, hH, hTurn hr]

private theorem auxiliary_uniform_value (hRI : GLSSWRootIndependence)
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hAux : auxiliaryGenericity q hq) (hUniform : PolygonUniform q) :
    separatingSmoothingSum q hq hAux =
      (-1 : ℚ) ^ SmoothingTurnCount.leftTurnCount q *
        (GeminiReversalContract.prescribedCorner q hq : ℚ) := by
  have h := HOMFLY.GeminiReversalConsumerPrep.polygon_uniform_identity_of_right_reduction
    hRI GeminiReversal.right_turning_reduction q hq hAux hUniform
  have hs : ((-1 : ℚ) ^ SmoothingTurnCount.leftTurnCount q) *
      ((-1 : ℚ) ^ SmoothingTurnCount.leftTurnCount q) = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    separatingSmoothingSum q hq hAux =
        1 * separatingSmoothingSum q hq hAux := (one_mul _).symm
    _ = (((-1 : ℚ) ^ SmoothingTurnCount.leftTurnCount q) *
        ((-1 : ℚ) ^ SmoothingTurnCount.leftTurnCount q)) *
          separatingSmoothingSum q hq hAux := by rw [hs]
    _ = (-1 : ℚ) ^ SmoothingTurnCount.leftTurnCount q *
        (((-1 : ℚ) ^ SmoothingTurnCount.leftTurnCount q) *
          separatingSmoothingSum q hq hAux) := mul_assoc _ _ _
    _ = (-1 : ℚ) ^ SmoothingTurnCount.leftTurnCount q *
        (GeminiReversalContract.prescribedCorner q hq : ℚ) := by
          rw [h]
          rfl

private theorem extension_eq_of_eventually_auxiliary_value
    {n : ℕ} (Γ : (q : Fin n → PlanarPoint ℝ) → CyclicGeneric q → ℚ)
    (hlocal : ∀ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q),
      ∀ᶠ r in 𝓝 q, ∀ (hr : CyclicGeneric r), Γ r hr = Γ q hq)
    (hagree : ∀ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
      (hAux : auxiliaryGenericity q hq),
      Γ q hq = separatingSmoothingSum q hq hAux)
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (z : ℚ)
    (hEv : ∀ᶠ r in 𝓝 q, ∀ (hr : CyclicGeneric r)
      (hAux : auxiliaryGenericity r hr), separatingSmoothingSum r hr hAux = z) :
    Γ q hq = z := by
  have hBoth : ∀ᶠ r in 𝓝 q, ∀ (hr : CyclicGeneric r)
      (hAux : auxiliaryGenericity r hr), Γ r hr = Γ q hq ∧
        separatingSmoothingSum r hr hAux = z := by
    filter_upwards [hlocal q hq,hEv] with r hΓ hv
    exact fun hr hAux => ⟨hΓ hr,hv hr hAux⟩
  obtain ⟨r,hrBoth,hr,hrAux,_⟩ :=
    ActualAuxiliaryDensity.exists_auxiliaryGenericity_mem_nhds q hq _ hBoth
  calc
    Γ q hq = Γ r hr := (hrBoth hr hrAux).1.symm
    _ = separatingSmoothingSum r hr hrAux := hagree r hr hrAux
    _ = z := (hrBoth hr hrAux).2

/-- Any intrinsic continuation has the source's nonuniform zero value.
This is conditional on the characterization, without defining Γ. -/
theorem any_extension_nonuniform_zero (hRI : GLSSWRootIndependence)
    {n : ℕ} (Γ : (q : Fin n → PlanarPoint ℝ) → CyclicGeneric q → ℚ)
    (hlocal : ∀ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q),
      ∀ᶠ r in 𝓝 q, ∀ (hr : CyclicGeneric r), Γ r hr = Γ q hq)
    (hagree : ∀ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
      (hAux : auxiliaryGenericity q hq),
      Γ q hq = separatingSmoothingSum q hq hAux)
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hnu : ¬ PolygonUniform q) : Γ q hq = 0 := by
  apply extension_eq_of_eventually_auxiliary_value Γ hlocal hagree q hq 0
  filter_upwards [eventually_uniform_iff q hq] with r hUniform
  intro hr hAux
  exact NonuniformPrimitive.separatingSmoothingSum_eq_zero_of_not_uniform
    r hr hAux hRI (fun hur => hnu (hUniform.mp hur))

/-- Any intrinsic continuation has the source's uniform prescribed corner.
This is conditional on the characterization, without defining Γ. -/
theorem any_extension_uniform_corner (hRI : GLSSWRootIndependence)
    {n : ℕ} (Γ : (q : Fin n → PlanarPoint ℝ) → CyclicGeneric q → ℚ)
    (hlocal : ∀ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q),
      ∀ᶠ r in 𝓝 q, ∀ (hr : CyclicGeneric r), Γ r hr = Γ q hq)
    (hagree : ∀ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
      (hAux : auxiliaryGenericity q hq),
      Γ q hq = separatingSmoothingSum q hq hAux)
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hu : PolygonUniform q) :
    Γ q hq = (-1 : ℚ) ^ SmoothingTurnCount.leftTurnCount q *
      (GeminiReversalContract.prescribedCorner q hq : ℚ) := by
  apply extension_eq_of_eventually_auxiliary_value Γ hlocal hagree q hq _
  filter_upwards [eventually_uniform_iff q hq,
    eventually_source_leftCount_eq q hq,
    eventually_prescribedCorner_eq q hq] with r hUniform hLeft hCorner
  intro hr hAux
  rw [auxiliary_uniform_value hRI r hr hAux (hUniform.mpr hu)]
  simp only [hLeft,hCorner hr]



end DirectGLSSW.SourcePrimitiveConsequences
