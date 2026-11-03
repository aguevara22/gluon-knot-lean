import ActualAuxiliaryDensityTransport
import ReversalConsumerPrep
import GeminiReversal.Solution
import PositivePolygonEvaluatorLocality
import PolygonTurnLocality
import OriginalLeftTurnLocality
import NonuniformPrimitive
import PolygonGermStability

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.SourcePrimitiveExtension
open DirectGLSSW GeometricSmoothingWeights PolygonUniformity
open Filter Topology

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

theorem auxiliaryPrimitive_local_patch (hRI : GLSSWRootIndependence)
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∃ U : Set (Fin n → PlanarPoint ℝ), IsOpen U ∧ q ∈ U ∧
      ∃ z : ℚ, ∀ r ∈ U, ∀ (hr : CyclicGeneric r)
        (hAux : auxiliaryGenericity r hr), separatingSmoothingSum r hr hAux = z := by
  have hEv : ∃ z : ℚ, ∀ᶠ r in 𝓝 q, ∀ (hr : CyclicGeneric r)
      (hAux : auxiliaryGenericity r hr), separatingSmoothingSum r hr hAux = z := by
    by_cases hu : PolygonUniform q
    · let z : ℚ := (-1 : ℚ) ^ SmoothingTurnCount.leftTurnCount q *
          (GeminiReversalContract.prescribedCorner q hq : ℚ)
      refine ⟨z, ?_⟩
      filter_upwards [eventually_uniform_iff q hq,
        eventually_source_leftCount_eq q hq,
        eventually_prescribedCorner_eq q hq] with r hUniform hLeft hCorner
      intro hr hAux
      have hur : PolygonUniform r := hUniform.mpr hu
      rw [auxiliary_uniform_value hRI r hr hAux hur]
      simp only [z, hLeft, hCorner hr]
    · refine ⟨0, ?_⟩
      filter_upwards [eventually_uniform_iff q hq] with r hUniform
      intro hr hAux
      exact NonuniformPrimitive.separatingSmoothingSum_eq_zero_of_not_uniform
        r hr hAux hRI (fun hur => hu (hUniform.mp hur))
  obtain ⟨z,hz⟩ := hEv
  rcases mem_nhds_iff.mp hz with ⟨U,hUsub,hUopen,hqU⟩
  exact ⟨U,hUopen,hqU,z,fun r hrU hr hAux => hUsub hrU hr hAux⟩

theorem existsUnique_fullPrimitive_extension (hRI : GLSSWRootIndependence)
    (n : ℕ) :
    ∃! Γ : (q : Fin n → PlanarPoint ℝ) → CyclicGeneric q → ℚ,
      (∀ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q),
        ∀ᶠ r in 𝓝 q, ∀ (hr : CyclicGeneric r), Γ r hr = Γ q hq) ∧
      (∀ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
        (hAux : auxiliaryGenericity q hq),
        Γ q hq = separatingSmoothingSum q hq hAux) := by
  classical
  let U (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
      Set (Fin n → PlanarPoint ℝ) :=
    Classical.choose (auxiliaryPrimitive_local_patch hRI q hq)
  have hU (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
      IsOpen (U q hq) ∧ q ∈ U q hq ∧
        ∃ z : ℚ, ∀ r ∈ U q hq, ∀ (hr : CyclicGeneric r)
          (hAux : auxiliaryGenericity r hr), separatingSmoothingSum r hr hAux = z :=
    Classical.choose_spec (auxiliaryPrimitive_local_patch hRI q hq)
  let Γ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) : ℚ :=
    Classical.choose (hU q hq).2.2
  have hΓ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
      (r : Fin n → PlanarPoint ℝ) (hrU : r ∈ U q hq)
      (hr : CyclicGeneric r) (hAux : auxiliaryGenericity r hr) :
      separatingSmoothingSum r hr hAux = Γ q hq :=
    Classical.choose_spec (hU q hq).2.2 r hrU hr hAux
  have hagree (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
      (hAux : auxiliaryGenericity q hq) :
      Γ q hq = separatingSmoothingSum q hq hAux :=
    (hΓ q hq q (hU q hq).2.1 hq hAux).symm
  have hlocal (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
      ∀ᶠ r in 𝓝 q, ∀ (hr : CyclicGeneric r), Γ r hr = Γ q hq := by
    filter_upwards [((hU q hq).1.mem_nhds (hU q hq).2.1)] with r hrU
    intro hr
    have hInter : U q hq ∩ U r hr ∈ 𝓝 r :=
      (((hU q hq).1.inter (hU r hr).1).mem_nhds ⟨hrU,(hU r hr).2.1⟩)
    obtain ⟨s,hs,hsg,hsAux,_⟩ :=
      ActualAuxiliaryDensity.exists_auxiliaryGenericity_mem_nhds r hr _ hInter
    have hqeq := hΓ q hq s hs.1 hsg hsAux
    have hreq := hΓ r hr s hs.2 hsg hsAux
    exact hreq.symm.trans hqeq
  refine ⟨Γ, ⟨hlocal,hagree⟩, ?_⟩
  intro F hF
  funext q hq
  have hEv : ∀ᶠ r in 𝓝 q, ∀ (hr : CyclicGeneric r),
      F r hr = F q hq ∧ Γ r hr = Γ q hq := by
    filter_upwards [hF.1 q hq,hlocal q hq] with r hFr hGr
    exact fun hr => ⟨hFr hr,hGr hr⟩
  obtain ⟨r,hrS,hr,hrAux,_⟩ :=
    ActualAuxiliaryDensity.exists_auxiliaryGenericity_mem_nhds q hq _ hEv
  calc
    F q hq = F r hr := (hrS hr).1.symm
    _ = separatingSmoothingSum r hr hrAux := hF.2 r hr hrAux
    _ = Γ r hr := (hagree r hr hrAux).symm
    _ = Γ q hq := (hrS hr).2




end DirectGLSSW.SourcePrimitiveExtension
