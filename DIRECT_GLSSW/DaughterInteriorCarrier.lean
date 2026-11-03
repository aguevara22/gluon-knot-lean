import DaughterClosedContainment
import Mathlib.Tactic.Linarith
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DaughterClosedContainment
open DaughterFirstReturn
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (root : PolygonEvent q)
    (hroot : retainedCorner q S root)

include hroot in
/-- Strict interior points stay strict on the original carrier, including
truncated endpoint edges. No daughter genericity is required. -/
theorem daughter_interior_on_parent
    (i : Fin (Fintype.card (CornerCoord q hq.g2 S root))) (x : PlanarPoint ℝ)
    (hx : edgeInterior (daughterVertex q hq.g2 S root) i x) :
    edgeInterior q (daughterCarrier q hq.g2 S root i) x := by
  obtain ⟨s,t,hs0,hst,ht1,hs,ht⟩ :=
    daughterSide_endpoint_parameters q hq.g2 S hq.size_ge_three root hroot i
  obtain ⟨r,hr0,hr1,hx⟩ := hx
  refine ⟨(1-r)*s+r*t,?_,?_,?_⟩
  · have hp := mul_pos hr0 (sub_pos.mpr hst)
    nlinarith
  · have hp := mul_pos (sub_pos.mpr hr1) (sub_pos.mpr hst)
    nlinarith
  · rw [hx,hs,ht]
    ext <;> simp [affinePoint] <;> ring

include hroot in
/-- The two actual daughter carriers produce an actual original crossing;
the carrier order may reverse after choosing a daughter root. -/
theorem daughter_crossing_original_pair
    (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)
    (d : PolygonCrossing (daughterVertex q hq.g2 S root)) :
    ∃ c : PolygonCrossing q,
      ((c.val.1 = daughterCarrier q hq.g2 S root d.val.1 ∧
        c.val.2 = daughterCarrier q hq.g2 S root d.val.2) ∨
       (c.val.1 = daughterCarrier q hq.g2 S root d.val.2 ∧
        c.val.2 = daughterCarrier q hq.g2 S root d.val.1)) ∧
      crossingPoint q c = crossingPoint (daughterVertex q hq.g2 S root) d := by
  let a := daughterCarrier q hq.g2 S root d.val.1
  let b := daughterCarrier q hq.g2 S root d.val.2
  let x := crossingPoint (daughterVertex q hq.g2 S root) d
  have ha : edgeInterior q a x := daughter_interior_on_parent q hq S root hroot _ _
    (crossingPoint_mem_left _ d)
  have hb : edgeInterior q b x := daughter_interior_on_parent q hq S root hroot _ _
    (crossingPoint_mem_right _ d)
  have hab : a ≠ b := fun he => (ne_of_lt d.property.1)
    (daughterCarrier_injective q hq.g2 S hq.size_ge_three hNA root he)
  rcases lt_or_gt_of_ne hab with hab | hba
  · let c : PolygonCrossing q := ⟨(a,b),hab,x,ha,hb⟩
    refine ⟨c,Or.inl ⟨rfl,rfl⟩,?_⟩
    exact (crossingPoint_eq_of_mem hq.size_ge_three q hq.g1 c x ha hb).symm
  · let c : PolygonCrossing q := ⟨(b,a),hba,x,hb,ha⟩
    refine ⟨c,Or.inr ⟨rfl,rfl⟩,?_⟩
    exact (crossingPoint_eq_of_mem hq.size_ge_three q hq.g1 c x hb ha).symm
end DirectGLSSW.DaughterClosedContainment
