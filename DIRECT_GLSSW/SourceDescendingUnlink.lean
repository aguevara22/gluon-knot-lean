import DescendingSplitTriangleRealization
import SourceDescendingNormalization
import ActualSpatialCompleteness

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial
open HOMFLY PermutationOrbits

/-- The actual descending diagram admits the explicit split-triangle ambient
realization, and its already constructed normalized HOMFLY evaluator has the
k-component unlink value (one in the knot case). -/
theorem descending_actual_split_triangles_and_normalization
    (D : PLLinkDiagram) (hD : 0 < D.nArc)
    (T : BasedTraversal D) (hbad : badCrossings T = ∅) :
    Gemini.candidateEvaluator D hD =
      Coefficients.unlinkFactor ^ (diagramComponentCount D - 1) ∧
    (diagramComponentCount D = 1 → Gemini.candidateEvaluator D hD = 1) ∧
    (∀ (e : Fin D.nArc) (H : ℝ),
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
         (Complex.equivRealProd.symm (splitBaseB D e),H)}) ∧
    (Pairwise (fun i j : Fin (diagramComponentCount D) =>
      Disjoint
        ((fun p : ℝ × ℝ => (((p.1/4:ℝ):ℂ),
          3*((diagramComponentCount D:ℝ)-1-i.val)+p.1/2+p.2)) ''
          {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1+p.2 ≤ 1})
        ((fun p : ℝ × ℝ => (((p.1/4:ℝ):ℂ),
          3*((diagramComponentCount D:ℝ)-1-j.val)+p.1/2+p.2)) ''
          {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1+p.2 ≤ 1}))) ∧
    (∀ H : ℝ, Function.Injective (fun p : ℝ × ℝ => (((p.1/4:ℝ):ℂ),H+p.1/2+p.2)) ∧
      Continuous (fun p : ℝ × ℝ => (((p.1/4:ℝ):ℂ),H+p.1/2+p.2))) ∧
    (∀ (H : ℝ) (u : unitInterval),
    (((u.val/4:ℝ):ℂ),H+u.val/2+(1-u.val)) =
      (((u.val/4:ℝ):ℂ),H+1-u.val/2) ∧
    ((((1-u.val)/4:ℝ):ℂ),H+(1-u.val)/2+0) =
      ((((1-u.val)/4:ℝ):ℂ),H+1/2-u.val/2) ∧
    (((0/4:ℝ):ℂ),H+0/2+u.val) = ((0:ℂ),H+u.val)) ∧
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
  refine ⟨DescendingSpatialNormalization.candidateEvaluator_descending_value D hD T hbad,
    DescendingSpatialNormalization.candidateEvaluator_descending_knot_one D hD T hbad,
    actual_spatial_complete_representation D,actual_target_triangle_disks D,
    fun H => ⟨triangle_plane_injective H,triangle_plane_continuous H⟩,
    triangle_plane_boundary,?_⟩
  exact exists_descending_actual_split_triangle_realization T hbad

end DirectGLSSW.DescendingSpatial

