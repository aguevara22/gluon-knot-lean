import ExtendedReturnCapInverse
import DirectGLSSW.MixedEdgeCutInverse

set_option autoImplicit false

namespace DirectGLSSW.MixedCapChainAlgebra
open scoped BigOperators
open OrderedCapEvents ExtendedReturnArcGeometry CapCriticalTimes CapCriticalEventGeometry

/-- Separate the empty-cut term without changing the finite cut-set domain. -/
theorem weightedCutSum_eq_empty_add_nonempty (w : ℕ → ℚ) (b : IntervalArray) (i j : ℕ) :
    weightedCutSum w b i j = b i j + weightedCutSumNonempty w b i j := by
  classical
  unfold weightedCutSum
  have hempty : (∅ : Finset ℕ) ∈ (Finset.Ioo i j).powerset := by simp
  rw [← Finset.add_sum_erase _ _ hempty]
  change (∏ l ∈ (∅ : Finset ℕ), w l) * branchProduct b (cutVertices i j ∅) +
    weightedCutSumNonempty w b i j = _
  simp [branchProduct, cutVertices]

/-- The signs after moving the direct entry to the other side are (-1)^(|S|+1). -/
theorem entry_eq_signed_nonempty_cuts_of_inverse_zero {m : ℕ}
    (X : Matrix (Fin m) (Fin m) ℚ) (hX : StrictUpper X)
    (u v : Fin m) (huv : u < v) (hzero : finiteInverse X m u v = 0) :
    X u v = ∑ S ∈ ((Finset.Ioo u.val v.val).powerset).erase ∅,
      (-1 : ℚ) ^ (S.card+1) *
        branchProduct (finiteMatrixIntervalArray X) (cutVertices u.val v.val S) := by
  classical
  have hfull := finiteInverse_entry_eq_negative_weightedCutSum X hX u v huv
  rw [hzero, weightedCutSum_eq_empty_add_nonempty] at hfull
  have hentry : finiteMatrixIntervalArray X u.val v.val = X u v := by
    simp [finiteMatrixIntervalArray, u.isLt, v.isLt]
  rw [hentry] at hfull
  have heq : X u v = -weightedCutSumNonempty (fun _ : ℕ => -1)
      (finiteMatrixIntervalArray X) u.val v.val := by linarith
  rw [heq, weightedCutSumNonempty, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [Finset.prod_const]
  rw [pow_succ]
  ring

/-- Source endpoint inverse expansion, still before cap/support identification.
All auxiliary geometric hypotheses used by the inverse theorem remain explicit. -/
theorem exists_amplitude_eq_event_cut_sum (hRI : GLSSWRootIndependence)
    {n : ℕ} (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
    (hU : (P (zeroIndex hn)).2 = 0) (hV : (P (lastIndex hn)).2 = 0)
    (hleft : (P (zeroIndex hn)).1 < (P (lastIndex hn)).1)
    (hturn : planarDet (cyclicTangent P (lastIndex hn)) (cyclicTangent P (zeroIndex hn)) *
      planarDet (cyclicTangent P (penultimateIndex hn)) (cyclicTangent P (lastIndex hn)) < 0)
    (ε : ℝ) (hε : 0 < ε) (hbound : ε < geometricRadius hn P)
    (hroots : Set.InjOn (criticalRoot (extendedArc hn P ε))
      ↑(criticalPairs (extendedArc hn P ε) n)) :
    ∃ cU cV : EventIndex (extendedArc hn P ε) n,
      eventTime (extendedArc hn P ε) n cU = 0 ∧
      eventTime (extendedArc hn P ε) n cV = (P (lastIndex hn)).1 - (P (zeroIndex hn)).1 ∧
      cU < cV ∧
      polygonAmplitude P hP =
        ∑ S ∈ ((Finset.Ioo cU.val cV.val).powerset).erase ∅,
          (-1 : ℚ) ^ (S.card+1) *
            branchProduct (eventIntervalArray (extendedArc hn P ε) n)
              (cutVertices cU.val cV.val S) := by
  obtain ⟨cU,cV,hTU,hTV,hlt,hentry,hzero⟩ :=
    ExtendedReturnCapInverse.exists_endpoint_matrix_and_inverse
      hRI hn P hP hU hV hleft hturn ε hε hbound hroots
  refine ⟨cU,cV,hTU,hTV,hlt,?_⟩
  rw [← hentry]
  exact entry_eq_signed_nonempty_cuts_of_inverse_zero
    (eventMatrix (extendedArc hn P ε) n) (eventMatrix_strictUpper _ _) cU cV hlt hzero




end DirectGLSSW.MixedCapChainAlgebra
