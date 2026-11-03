import PolygonRotationSum
import SharpDaughterTurnContinuity

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonTurnLocality
open PrincipalTurning PolygonDrawingBridge Filter Topology
open scoped BigOperators

private theorem edgeVector_ne_zero {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (i : Fin n) : polygonEdgeVector q i ≠ 0 := by
  intro h
  apply cyclicTangent_ne_zero hq.size_ge_three q hq.g1 i
  apply Prod.ext
  · exact congrArg Complex.re h
  · exact congrArg Complex.im h

private theorem continuous_edgeVector {n : ℕ} (i : Fin n) :
    Continuous (fun q : Fin n → PlanarPoint ℝ => polygonEdgeVector q i) :=
  Complex.equivRealProdCLM.symm.continuous.comp
    ((continuous_apply (cyclicSuccessor i)).sub (continuous_apply i))

private theorem corner_ratio_slitPlane {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (i : Fin n) :
    polygonEdgeVector q i / polygonEdgeVector q ((cyclicSuccessorPerm n).symm i)
      ∈ Complex.slitPlane := by
  let j := (cyclicSuccessorPerm n).symm i
  have hs : cyclicSuccessor j = i := (cyclicSuccessorPerm n).apply_symm_apply i
  have hd : planarDet (cyclicTangent q j) (cyclicTangent q i) ≠ 0 := by
    simpa only [hs] using cyclic_turn_det_ne_zero hq.size_ge_three q hq.g1 j
  have him : (polygonEdgeVector q i / polygonEdgeVector q j).im ≠ 0 := by
    rw [Complex.div_im, ← sub_div]
    apply div_ne_zero
    · simpa only [polygonEdgeVector, planarDet, mul_comm] using hd
    · exact mt Complex.normSq_eq_zero.mp (edgeVector_ne_zero q hq j)
  apply Complex.mem_slitPlane_iff_arg.mpr
  constructor
  · intro hp
    exact him (Complex.arg_eq_pi_iff.mp hp).2
  · exact div_ne_zero (edgeVector_ne_zero q hq i) (edgeVector_ne_zero q hq j)

/-- The literal original corner sum is continuous at every G1–G2 polygon.
G1 excludes the argument branch cut separately at each original corner. -/
theorem continuousAt_originalCornerTotalTurn {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ContinuousAt originalCornerTotalTurn q := by
  have hterm (i : Fin n) : ContinuousAt
      (fun r : Fin n → PlanarPoint ℝ => originalCornerTurn r i) q := by
    exact ContinuousAt.comp
      (f := fun r : Fin n → PlanarPoint ℝ =>
        polygonEdgeVector r i / polygonEdgeVector r ((cyclicSuccessorPerm n).symm i))
      (x := q) (Complex.continuousAt_arg (corner_ratio_slitPlane q hq i))
      ((continuous_edgeVector i).continuousAt.div
        (continuous_edgeVector _).continuousAt (edgeVector_ne_zero q hq _))
  have hs (t : Finset (Fin n)) : ContinuousAt
      (fun r : Fin n → PlanarPoint ℝ => ∑ i ∈ t, originalCornerTurn r i) q := by
    classical
    induction t using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using
        (continuousAt_const : ContinuousAt (fun _ : Fin n → PlanarPoint ℝ => (0 : ℝ)) q)
    | @insert i t hi ih => simpa only [Finset.sum_insert hi] using (hterm i).add ih
  exact hs Finset.univ

/-- The existing rotation integer of the actual positive polygon diagram is
locally constant. The nearby genericity certificate is arbitrary; no event
transport, rotation equality, or extra orientation premise is supplied. -/
theorem eventually_positivePolygon_turnInteger {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∀ᶠ r in 𝓝 q, ∀ hr : CyclicGeneric r,
      turnInteger (positivePolygonEventDiagram r hr) =
        turnInteger (positivePolygonEventDiagram q hq) := by
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have he : ∀ᶠ r in 𝓝 q,
      |originalCornerTotalTurn r - originalCornerTotalTurn q| < 2 * Real.pi :=
    (((continuousAt_originalCornerTotalTurn q hq).sub continuousAt_const).abs).eventually
      (isOpen_Iio.mem_nhds (by simpa using hp))
  have hF (r : Fin n → PlanarPoint ℝ) (hr : CyclicGeneric r) :
      originalCornerTotalTurn r =
        (turnInteger (positivePolygonEventDiagram r hr) : ℝ) * (2 * Real.pi) :=
    (positivePolygonEventDiagram_totalTurn r hr).symm.trans
      (totalTurn_eq_turnInteger (positivePolygonEventDiagram r hr))
  filter_upwards [he] with r hnear
  intro hr
  rw [hF r hr, hF q hq, ← sub_mul, abs_mul, abs_of_pos hp] at hnear
  have hsmall : |(turnInteger (positivePolygonEventDiagram r hr) : ℝ) -
      (turnInteger (positivePolygonEventDiagram q hq) : ℝ)| < 1 := by
    apply (mul_lt_mul_right hp).mp
    simpa only [one_mul] using hnear
  have hi : |turnInteger (positivePolygonEventDiagram r hr) -
      turnInteger (positivePolygonEventDiagram q hq)| < (1 : ℤ) := by
    exact_mod_cast hsmall
  have hi' := abs_lt.mp hi
  omega

end DirectGLSSW.HOMFLY.PolygonTurnLocality
