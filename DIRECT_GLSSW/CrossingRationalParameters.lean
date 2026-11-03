import DirectGLSSW.PolygonCrossings
import DirectGLSSW.PolygonLocalMotion

set_option autoImplicit false
namespace DirectGLSSW.CrossingRationalParameters
noncomputable section
abbrev Point := PlanarPoint ℝ
abbrev Configuration (n : ℕ) := Fin n → Point

def edgeIntersection {n : ℕ} (Q : Configuration n) (e f : Fin n) : Prop :=
  ∃ x : Point, edgeInterior Q e x ∧ edgeInterior Q f x

def denominator {n : ℕ} (Q : Configuration n) (e f : Fin n) : ℝ :=
  planarDet (cyclicTangent Q e) (cyclicTangent Q f)
def leftParameter {n : ℕ} (Q : Configuration n) (e f : Fin n) : ℝ :=
  planarDet (Q f-Q e) (cyclicTangent Q f) / denominator Q e f
def rightParameter {n : ℕ} (Q : Configuration n) (e f : Fin n) : ℝ :=
  planarDet (Q f-Q e) (cyclicTangent Q e) / denominator Q e f

theorem rational_intersection {n : ℕ} (Q : Configuration n) (e f : Fin n)
    (hD : denominator Q e f ≠ 0) :
    affinePoint (Q e) (Q (cyclicSuccessor e)) (leftParameter Q e f) =
      affinePoint (Q f) (Q (cyclicSuccessor f)) (rightParameter Q e f) := by
  apply Prod.ext
  all_goals
    dsimp [affinePoint,leftParameter,rightParameter]
    field_simp [hD]
    dsimp [denominator,cyclicTangent,planarDet]
    ring

theorem crossingParameters_eq {n : ℕ} (Q : Configuration n) (c : PolygonCrossing Q)
    (hD : denominator Q c.val.1 c.val.2 ≠ 0) :
    crossingParameterLeft Q c = leftParameter Q c.val.1 c.val.2 ∧
    crossingParameterRight Q c = rightParameter Q c.val.1 c.val.2 := by
  have hu := affinePoint_intersection_parameters_unique
    (Q c.val.1) (Q (cyclicSuccessor c.val.1))
    (Q c.val.2) (Q (cyclicSuccessor c.val.2))
    (crossingParameterLeft Q c) (crossingParameterRight Q c)
    (leftParameter Q c.val.1 c.val.2) (rightParameter Q c.val.1 c.val.2) hD
    ((crossingParameterLeft_spec Q c).2.2.symm.trans (crossingParameterRight_spec Q c).2.2)
    (rational_intersection Q c.val.1 c.val.2 hD)
  exact hu

theorem crossingParameters_eq_of_g1 {n : ℕ} (hn : 3 ≤ n)
    (Q : Configuration n) (hQ : cyclicNoncollinear Q) (c : PolygonCrossing Q) :
    crossingParameterLeft Q c = leftParameter Q c.val.1 c.val.2 ∧
    crossingParameterRight Q c = rightParameter Q c.val.1 c.val.2 :=
  crossingParameters_eq Q c (crossing_transverse hn Q hQ c)

theorem crossingPoint_eq {n : ℕ} (Q : Configuration n) (c : PolygonCrossing Q)
    (hD : denominator Q c.val.1 c.val.2 ≠ 0) :
    crossingPoint Q c = affinePoint (Q c.val.1) (Q (cyclicSuccessor c.val.1))
      (leftParameter Q c.val.1 c.val.2) := by
  rw [← (crossingParameters_eq Q c hD).1]
  exact (crossingParameterLeft_spec Q c).2.2

theorem edgeIntersection_iff_parameters {n : ℕ} (Q : Configuration n) (e f : Fin n)
    (hD : denominator Q e f ≠ 0) :
    edgeIntersection Q e f ↔
      0 < leftParameter Q e f ∧ leftParameter Q e f < 1 ∧
      0 < rightParameter Q e f ∧ rightParameter Q e f < 1 := by
  constructor
  · rintro ⟨x,⟨s,hs0,hs1,hxs⟩,⟨t,ht0,ht1,hxt⟩⟩
    have hu := affinePoint_intersection_parameters_unique
      (Q e) (Q (cyclicSuccessor e)) (Q f) (Q (cyclicSuccessor f))
      s t (leftParameter Q e f) (rightParameter Q e f) hD
      (hxs.symm.trans hxt) (rational_intersection Q e f hD)
    exact ⟨hu.1 ▸ hs0,hu.1 ▸ hs1,hu.2 ▸ ht0,hu.2 ▸ ht1⟩
  · rintro ⟨hs0,hs1,ht0,ht1⟩
    refine ⟨affinePoint (Q e) (Q (cyclicSuccessor e)) (leftParameter Q e f),
      ⟨leftParameter Q e f,hs0,hs1,rfl⟩,
      ⟨rightParameter Q e f,ht0,ht1,rational_intersection Q e f hD⟩⟩

theorem continuous_denominator {n : ℕ} (e f : Fin n) :
    Continuous (fun Q : Configuration n => denominator Q e f) := by
  dsimp [denominator,cyclicTangent,planarDet]
  fun_prop

theorem continuousAt_leftParameter {n : ℕ} (P : Configuration n) (e f : Fin n)
    (hD : denominator P e f ≠ 0) :
    ContinuousAt (fun Q : Configuration n => leftParameter Q e f) P := by
  unfold leftParameter
  apply ContinuousAt.div _ ((continuous_denominator e f).continuousAt) hD
  dsimp [cyclicTangent,planarDet]
  fun_prop

theorem continuousAt_rightParameter {n : ℕ} (P : Configuration n) (e f : Fin n)
    (hD : denominator P e f ≠ 0) :
    ContinuousAt (fun Q : Configuration n => rightParameter Q e f) P := by
  unfold rightParameter
  apply ContinuousAt.div _ ((continuous_denominator e f).continuousAt) hD
  dsimp [cyclicTangent,planarDet]
  fun_prop

theorem continuousAt_intersectionPoint {n : ℕ} (P : Configuration n) (e f : Fin n)
    (hD : denominator P e f ≠ 0) :
    ContinuousAt (fun Q : Configuration n =>
      affinePoint (Q e) (Q (cyclicSuccessor e)) (leftParameter Q e f)) P := by
  have hL := continuousAt_leftParameter P e f hD
  have he : ContinuousAt (fun Q : Configuration n => Q e) P := (continuous_apply e).continuousAt
  have hs : ContinuousAt (fun Q : Configuration n => Q (cyclicSuccessor e)) P :=
    (continuous_apply (cyclicSuccessor e)).continuousAt
  exact (he.fst.add (hL.mul (hs.fst.sub he.fst))).prodMk
    (he.snd.add (hL.mul (hs.snd.sub he.snd)))














end
end DirectGLSSW.CrossingRationalParameters
