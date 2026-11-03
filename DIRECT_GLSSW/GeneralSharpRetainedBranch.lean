import GeneralSharpRetainedCrossings
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.GeneralSharpRetained
open DirectGLSSW PermutationOrbits PolygonDrawingBridge DaughterFirstReturn
  DaughterParentCrossing DaughterVisitLift DaughterEventLift
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
  (S : Finset (PolygonCrossing q)) (root : PolygonEvent q)
  (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)
  (hroot : retainedCorner q S root)

theorem branchPermutation_tangent
    (d : PolygonCrossing (daughterVertex q hq.g2 S root)) (i : Fin 2) :
    ∃ a : ℝ, 0 < a ∧
      cyclicTangent (daughterVertex q hq.g2 S root)
        (polygonEventEdge _ (PolygonDrawing.visit _ d (branchPermutation q hq S root d i))) =
      a • cyclicTangent q
        (polygonEventEdge q (PolygonDrawing.visit q (parentCrossing q hq S hNA root hroot d) i)) := by
  let j := polygonEventEdge _ (PolygonDrawing.visit _ d (branchPermutation q hq S root d i))
  have hh := daughterSide_positive_multiple q hq.g2 S hq.size_ge_three root hroot j
  refine ⟨_,hh.1,?_⟩
  have hv : cyclicTangent (daughterVertex q hq.g2 S root) j =
      _ • cyclicTangent q (daughterCarrier q hq.g2 S root j) := hh.2
  rw [branchPermutation_carrier q hq S root hNA hroot] at hv
  exact hv

variable (hP : CyclicGeneric (daughterVertex q hq.g2 S root))
theorem branchPermutation_over
    (d : PolygonCrossing (daughterVertex q hq.g2 S root)) :
    branchPermutation q hq S root d
      ((positivePolygonEventDiagram q hq).overBranch
        (crossingFin q (parentCrossing q hq S hNA root hroot d))) =
    (positivePolygonEventDiagram (daughterVertex q hq.g2 S root) hP).overBranch
      (crossingFin (daughterVertex q hq.g2 S root) d) := by
  let Q := daughterVertex q hq.g2 S root
  let z := parentCrossing q hq S hNA root hroot d
  let β := branchPermutation q hq S root d
  have hne := crossing_transverse hq.size_ge_three q hq.g1 z
  obtain ⟨a,ha,h0⟩ := branchPermutation_tangent q hq S root hNA hroot d 0
  obtain ⟨b,hb,h1⟩ := branchPermutation_tangent q hq S root hNA hroot d 1
  change β ((positivePolygonEventDiagram q hq).overBranch (crossingFin q z)) =
    (positivePolygonEventDiagram Q _).overBranch (crossingFin Q d)
  rw [positivePolygonEventDiagram_overBranch,positivePolygonEventDiagram_overBranch]
  by_cases halign : daughterCarrier q hq.g2 S root d.val.1 < daughterCarrier q hq.g2 S root d.val.2
  · have hβ : β=Equiv.refl _ := by unfold β branchPermutation;rw [if_pos halign]
    have hh0 : cyclicTangent Q d.val.1 = a • cyclicTangent q z.val.1 := by
      simpa only [←show β=branchPermutation q hq S root d from rfl,hβ,
        Equiv.refl_apply,PolygonDrawing.visit,ite_true,polygonEventEdge,crossingVisitEdge,Bool.false_eq_true,ite_false] using h0
    have hh1 : cyclicTangent Q d.val.2 = b • cyclicTangent q z.val.2 := by
      simpa [←show β=branchPermutation q hq S root d from rfl,hβ,
        PolygonDrawing.visit,polygonEventEdge,crossingVisitEdge] using h1
    have hdet : planarDet (cyclicTangent Q d.val.1) (cyclicTangent Q d.val.2) =
        (a*b)*planarDet (cyclicTangent q z.val.1) (cyclicTangent q z.val.2) := by
      rw [hh0,hh1];simp [planarDet];ring
    have hiff : 0<(a*b)*planarDet (cyclicTangent q z.val.1) (cyclicTangent q z.val.2) ↔
        0<planarDet (cyclicTangent q z.val.1) (cyclicTangent q z.val.2) :=
      mul_pos_iff_of_pos_left (mul_pos ha hb)
    have hiffQ : 0<planarDet (cyclicTangent Q d.val.1) (cyclicTangent Q d.val.2) ↔
        0<planarDet (cyclicTangent q z.val.1) (cyclicTangent q z.val.2) := by rw [hdet];exact hiff
    by_cases hp : 0<planarDet (cyclicTangent q z.val.1) (cyclicTangent q z.val.2)
    · simp only [hβ,if_pos hp,if_pos (hiffQ.mpr hp),Equiv.refl_apply]
    · simp only [hβ,if_neg hp,if_neg (fun hh => hp (hiffQ.mp hh)),Equiv.refl_apply]
  · have hβ : β=Equiv.swap 0 1 := by unfold β branchPermutation;rw [if_neg halign]
    have hh0 : cyclicTangent Q d.val.2 = a • cyclicTangent q z.val.1 := by
      simpa [←show β=branchPermutation q hq S root d from rfl,hβ,
        PolygonDrawing.visit,polygonEventEdge,crossingVisitEdge] using h0
    have hh1 : cyclicTangent Q d.val.1 = b • cyclicTangent q z.val.2 := by
      simpa [←show β=branchPermutation q hq S root d from rfl,hβ,
        PolygonDrawing.visit,polygonEventEdge,crossingVisitEdge] using h1
    have hdet : planarDet (cyclicTangent Q d.val.1) (cyclicTangent Q d.val.2) =
        -(a*b)*planarDet (cyclicTangent q z.val.1) (cyclicTangent q z.val.2) := by
      rw [hh0,hh1];simp [planarDet];ring
    have hab : 0<a*b := mul_pos ha hb
    by_cases hp : 0<planarDet (cyclicTangent q z.val.1) (cyclicTangent q z.val.2)
    · have hnp : ¬0<planarDet (cyclicTangent Q d.val.1) (cyclicTangent Q d.val.2) := by rw [hdet];nlinarith
      simp [hβ,hp,hnp]
    · have hneg : planarDet (cyclicTangent q z.val.1) (cyclicTangent q z.val.2)<0 := lt_of_le_of_ne (le_of_not_gt hp) hne
      have hpos : 0<planarDet (cyclicTangent Q d.val.1) (cyclicTangent Q d.val.2) := by rw [hdet];nlinarith
      simp [hβ,hp,hpos]



end DirectGLSSW.HOMFLY.GeneralSharpRetained
