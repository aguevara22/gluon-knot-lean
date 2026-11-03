import SplitTraceProjection
import TriangleDiskGeometry
import DescendingRankHeights

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial
open HOMFLY

theorem actual_spatial_complete_representation (D : PLLinkDiagram) :
    ∀ (e : Fin D.nArc) (H : ℝ),
      (∀ z : ℂ, z ∈ Prod.fst '' splitSpatialTrace D e H ↔
        ∃ k : Fin (componentArcLength D e), ∃ u : unitInterval,
          Complex.equivRealProd.symm
            (affinePoint (D.vertexPoint (D.arcSource ((D.continuation ^ k.val) e)))
              (D.vertexPoint (D.arcTarget ((D.continuation ^ k.val) e))) u.val) = z) ∧
      Continuous (descendingMain D e H) ∧ Function.Injective (descendingMain D e H) ∧
      Continuous (ascendingClosure D e H) ∧ Function.Injective (ascendingClosure D e H) ∧
      descendingMain D e H 0 = (Complex.equivRealProd.symm (splitBaseA D e),H+1) ∧
      descendingMain D e H 1 = (Complex.equivRealProd.symm (splitBaseB D e),H) ∧
      ascendingClosure D e H 0 = (Complex.equivRealProd.symm (splitBaseB D e),H) ∧
      ascendingClosure D e H 1 = (Complex.equivRealProd.symm (splitBaseA D e),H+1) ∧
      Set.range (descendingMain D e H) ∩ Set.range (ascendingClosure D e H) =
        {(Complex.equivRealProd.symm (splitBaseA D e),H+1),
         (Complex.equivRealProd.symm (splitBaseB D e),H)} := by
  intro e H
  refine ⟨splitSpatialTrace_projection_iff D e H,descendingMain_continuous D e H,
    descendingMain_injective D e H,ascendingClosure_continuous D e H,
    ascendingClosure_injective D e H,?_,?_,?_,?_,actual_spatial_arcs_intersection D e H⟩
  · simp [descendingMain_apply,splitMainComplex_apply,
      (splitMainPlanar_endpoints D e).1,sub_zero]
  · simp [descendingMain_apply,splitMainComplex_apply,
      (splitMainPlanar_endpoints D e).2,add_sub_cancel_right]
  · simp [ascendingClosure_apply,affinePoint_zero,add_zero]
  · simp [ascendingClosure_apply,affinePoint_one]

/-- The literal filled disks for all actual component indices are pairwise disjoint. -/
theorem actual_target_triangle_disks (D : PLLinkDiagram) :
    Pairwise (fun i j : Fin (diagramComponentCount D) =>
      Disjoint
        ((fun p : ℝ × ℝ => (((p.1/4:ℝ):ℂ),
          3*((diagramComponentCount D:ℝ)-1-i.val)+p.1/2+p.2)) ''
          {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1+p.2 ≤ 1})
        ((fun p : ℝ × ℝ => (((p.1/4:ℝ):ℂ),
          3*((diagramComponentCount D:ℝ)-1-j.val)+p.1/2+p.2)) ''
          {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1+p.2 ≤ 1})) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · apply Disjoint.symm
    apply triangle_disks_disjoint
    have hi : (i.val:ℝ)+1 ≤ j.val := by exact_mod_cast h
    linarith
  · apply triangle_disks_disjoint
    have hi : (j.val:ℝ)+1 ≤ i.val := by exact_mod_cast h
    linarith

end DirectGLSSW.DescendingSpatial


