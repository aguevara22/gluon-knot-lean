import FiniteActualTriangles
import ActualDescendingCrossingRepresentation
import TriangleDiskGeometry

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial
open HOMFLY PermutationOrbits

/-- A descending actual diagram has its actual crossing-height representation
and a single ambient straightening to disjoint, nondegenerate triangular
component traces. Polynomial normalization is a separate evaluator consequence. -/
theorem exists_descending_actual_split_triangle_realization {D : PLLinkDiagram}
    (T : BasedTraversal D) (hbad : badCrossings T = ∅) :
    ∃ Φ : unitInterval → ((ℂ × ℝ) ≃ₜ (ℂ × ℝ)),
      Φ 0 = Homeomorph.refl (ℂ × ℝ) ∧
      Continuous (fun p : unitInterval × (ℂ × ℝ) => Φ p.1 p.2) ∧
      Continuous (fun p : unitInterval × (ℂ × ℝ) => (Φ p.1).symm p.2) ∧
      (∀ s x, (Φ s x).2 = x.2) ∧
      (∀ i : Fin (diagramComponentCount D),
        let H : ℝ := 3*((diagramComponentCount D:ℝ)-1-i.val)
        Φ 1 '' splitSpatialTrace D (T.baseArc (T.componentIndex.symm i)).val H =
          (Set.range (fun u : unitInterval => (((u.val/4:ℝ):ℂ),H+1-u.val/2)) ∪
           Set.range (fun u : unitInterval => ((((1-u.val)/4:ℝ):ℂ),H+1/2-u.val/2))) ∪
           Set.range (fun u : unitInterval => ((0:ℂ),H+u.val))) ∧
      (∀ c : Fin D.nCrossing,
    let e := D.incoming c (D.overBranch c)
    let f := D.incoming c (otherBranch (D.overBranch c))
    let He : ℝ := 3*((diagramComponentCount D:ℝ)-1-(T.componentIndex (componentOf D.continuation e)).val)
    let Hf : ℝ := 3*((diagramComponentCount D:ℝ)-1-(T.componentIndex (componentOf D.continuation f)).val)
    ∃ t u : unitInterval,
      descendingMain D (T.baseArc (componentOf D.continuation e)).val He t =
        (Complex.equivRealProd.symm (D.vertexPoint (D.crossingVertex c)),He+1-t.val) ∧
      descendingMain D (T.baseArc (componentOf D.continuation f)).val Hf u =
        (Complex.equivRealProd.symm (D.vertexPoint (D.crossingVertex c)),Hf+1-u.val) ∧
      Hf+1-u.val < He+1-t.val) := by
  obtain ⟨Φ,h0,hc,hi,hh,ht⟩ := exists_finite_actual_triangles T
  exact ⟨Φ,h0,hc,hi,hh,ht,fun c => actual_descending_crossing_representation T hbad c⟩

end DirectGLSSW.DescendingSpatial

