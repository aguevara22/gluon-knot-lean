import DaughterKeptEvents

set_option autoImplicit false
namespace DirectGLSSW.DaughterLiftParameters
open DaughterFirstReturn DaughterEventLift DaughterG2Inheritance PolygonNonalternation
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
variable (root : PolygonEvent P) (hroot : retainedCorner P S root)

/-- Exact positive affine parameter change on the actual carrier subsegment. -/
theorem eventLift_parameter (x : PolygonEvent (daughterVertex P hP.g2 S root)) :
    polygonEventParameter P (eventLift P hP S hS root hroot x) =
      polygonEventParameter P (orbitEventAt P hP.g2 S root
        (cornerEnumeration P hP.g2 S root (polygonEventEdge (daughterVertex P hP.g2 S root) x)).val) +
      polygonEventParameter (daughterVertex P hP.g2 S root) x *
        daughterSideScale P hP.g2 S root
          (cornerEnumeration P hP.g2 S root (polygonEventEdge (daughterVertex P hP.g2 S root) x)) := by
  let i := polygonEventEdge (daughterVertex P hP.g2 S root) x
  let e := daughterCarrier P hP.g2 S root i
  let a := orbitEventAt P hP.g2 S root (cornerEnumeration P hP.g2 S root i).val
  have hne : P e ≠ P (cyclicSuccessor e) := by
    intro h
    exact cyclicTangent_ne_zero hP.size_ge_three P hP.g1 e (sub_eq_zero.mpr h.symm)
  have ha := polygonEventPoint_eq_affine P a
  obtain ⟨_,hab⟩ := daughterSide_positive_multiple P hP.g2 S hP.size_ge_three root hroot i
  apply affinePoint_injective (P e) (P (cyclicSuccessor e)) hne
  calc
    affinePoint (P e) (P (cyclicSuccessor e)) (polygonEventParameter P (eventLift P hP S hS root hroot x)) =
        polygonEventPoint P (eventLift P hP S hS root hroot x) := by
      simpa only [eventLift_carrier] using (polygonEventPoint_eq_affine P (eventLift P hP S hS root hroot x)).symm
    _ = polygonEventPoint (daughterVertex P hP.g2 S root) x := eventLift_point P hP S hS root hroot x
    _ = affinePoint (daughterVertex P hP.g2 S root i)
        (daughterVertex P hP.g2 S root (cyclicSuccessor i))
        (polygonEventParameter (daughterVertex P hP.g2 S root) x) := polygonEventPoint_eq_affine _ x
    _ = _ := affinePoint_subsegment _ _ _ _ _ _ _ ha hab

/-- Same-carrier event order is preserved by its derived positive scale. -/
theorem eventLift_parameter_lt_iff
    (x y : PolygonEvent (daughterVertex P hP.g2 S root))
    (he : polygonEventEdge (daughterVertex P hP.g2 S root) x =
      polygonEventEdge (daughterVertex P hP.g2 S root) y) :
    polygonEventParameter P (eventLift P hP S hS root hroot x) <
        polygonEventParameter P (eventLift P hP S hS root hroot y) ↔
      polygonEventParameter (daughterVertex P hP.g2 S root) x <
        polygonEventParameter (daughterVertex P hP.g2 S root) y := by
  rw [eventLift_parameter,eventLift_parameter,← he]
  have hd := (daughterSide_positive_multiple P hP.g2 S hP.size_ge_three root hroot
    (polygonEventEdge (daughterVertex P hP.g2 S root) x)).1
  exact (add_lt_add_iff_left _).trans (mul_lt_mul_right hd)

theorem eventLift_sameEdge_order_iff
    (x y : PolygonEvent (daughterVertex P hP.g2 S root))
    (he : polygonEventEdge (daughterVertex P hP.g2 S root) x =
      polygonEventEdge (daughterVertex P hP.g2 S root) y) :
    (polygonEventOrder P hP.g2).lt (eventLift P hP S hS root hroot x) (eventLift P hP S hS root hroot y) ↔
      (polygonEventOrder (daughterVertex P hP.g2 S root)
        (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root)).lt x y := by
  have he' : polygonEventEdge P (eventLift P hP S hS root hroot x) =
      polygonEventEdge P (eventLift P hP S hS root hroot y) := by
    rw [eventLift_carrier,eventLift_carrier,he]
  rw [polygonEvent_sameEdge_lt_iff P hP.g2 _ _ he',
    polygonEvent_sameEdge_lt_iff _ _ x y he]
  exact eventLift_parameter_lt_iff P hP S hS root hroot x y he




end
end DirectGLSSW.DaughterLiftParameters
