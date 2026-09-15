import SM.ScalarBoxes
import SM.CentralLegCollision
import SM.RegularPerturbation

/-! The local cubes required by thm:relgp in the actual regular and generic
loci. Central legs inherit containment from their two actual waypoint values. -/

namespace SM

open Set

noncomputable section

variable {κ σ : Type*} {n : ℕ}

theorem CoordinateWaypointLeg.endpoint_mem_box (leg : CoordinateWaypointLeg κ σ)
    (W : κ × σ → ℝ) (center : σ → ℝ) (radius : ℝ)
    (hleft : (fun z => W (leg.left, z)) ∈ scalarOpenBox center radius)
    (hright : (fun z => W (leg.right, z)) ∈ scalarOpenBox center radius)
    (b : Bool) : leg.endpoint b W ∈ scalarOpenBox center radius := by
  classical
  apply scalarOpenBox_mem_of_coordinates center (fun z => W (leg.left, z))
    (fun z => W (leg.right, z)) _ radius hleft hright
  intro z
  cases b
  · by_cases hz : z ∈ leg.switched
    · right
      simp [endpoint, waypointHybrid, waypointSelection, beforeTag, hz]
    · left
      simp [endpoint, waypointHybrid, waypointSelection, beforeTag, hz]
  · by_cases hz : z = leg.moving
    · right
      simp [endpoint, waypointHybrid, waypointSelection, afterTag, hz]
    · by_cases hs : z ∈ leg.switched
      · right
        simp [endpoint, waypointHybrid, waypointSelection, afterTag, beforeTag, hz, hs]
      · left
        simp [endpoint, waypointHybrid, waypointSelection, afterTag, beforeTag, hz, hs]

theorem CoordinateWaypointLeg.assignment_mem_box (leg : CoordinateWaypointLeg κ σ)
    (W : κ × σ → ℝ) (center : σ → ℝ) (radius : ℝ)
    (hleft : (fun z => W (leg.left, z)) ∈ scalarOpenBox center radius)
    (hright : (fun z => W (leg.right, z)) ∈ scalarOpenBox center radius)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    leg.assignment W t ∈ scalarOpenBox center radius := by
  rw [leg.assignment_eq_line]
  exact scalarAssignmentLine_mem_box center _ _ radius t
    (leg.endpoint_mem_box W center radius hleft hright false)
    (leg.endpoint_mem_box W center radius hleft hright true) ht

theorem CoordinateWaypointLeg.tuple_assignment_mem_box
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (P : LabelledTuple n) (radius : ℝ)
    (hleft : tupleOfScalarCoordinates (fun z => W (leg.left, z)) ∈ tupleScalarBox P radius)
    (hright : tupleOfScalarCoordinates (fun z => W (leg.right, z)) ∈ tupleScalarBox P radius)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    tupleOfScalarCoordinates (leg.assignment W t) ∈ tupleScalarBox P radius := by
  simp only [tupleScalarBox, mem_preimage, scalarCoordinates_tupleOf] at hleft hright ⊢
  exact leg.assignment_mem_box W (scalarCoordinates P) radius hleft hright t ht

theorem exists_regular_tupleScalarBox [NeZero n]
    (P : LabelledTuple n) (hP : Regular P) (δ : ℝ) (hδ : 0 < δ) :
    ∃ radius > 0, P ∈ tupleScalarBox P radius ∧ IsOpen (tupleScalarBox P radius) ∧
      closure (tupleScalarBox P radius) ⊆ {Q | Regular Q} ∧
      Metric.diam (tupleCoordinates '' tupleScalarBox P radius) < δ ∧
      ∀ Q ∈ tupleScalarBox P radius, ∀ R ∈ tupleScalarBox P radius,
        dist (tupleCoordinates Q) (tupleCoordinates R) < δ := by
  obtain ⟨radius, hr, hc, hd, hp⟩ := exists_tupleScalarBox_closure_diameter
    {Q | Regular Q} isOpen_Regular P hP δ hδ
  exact ⟨radius, hr, tupleScalarBox_self P radius hr, isOpen_tupleScalarBox P radius,
    hc, hd, hp⟩

theorem exists_generic_tupleScalarBox (hn : 3 ≤ n)
    (P : LabelledTuple n) (hP : Generic P) (δ : ℝ) (hδ : 0 < δ) :
    ∃ radius > 0, P ∈ tupleScalarBox P radius ∧ IsOpen (tupleScalarBox P radius) ∧
      closure (tupleScalarBox P radius) ⊆ {Q | Regular Q ∧ Generic Q} ∧
      Metric.diam (tupleCoordinates '' tupleScalarBox P radius) < δ ∧
      ∀ Q ∈ tupleScalarBox P radius, ∀ R ∈ tupleScalarBox P radius,
        dist (tupleCoordinates Q) (tupleCoordinates R) < δ := by
  haveI : NeZero n := ⟨by omega⟩
  have hopen : IsOpen {Q : LabelledTuple n | Regular Q ∧ Generic Q} :=
    isOpen_Regular.inter (isOpen_Generic hn)
  obtain ⟨radius, hr, hc, hd, hp⟩ := exists_tupleScalarBox_closure_diameter
    {Q | Regular Q ∧ Generic Q} hopen P ⟨generic_regular hn hP, hP⟩ δ hδ
  exact ⟨radius, hr, tupleScalarBox_self P radius hr, isOpen_tupleScalarBox P radius,
    hc, hd, hp⟩

end

end SM
