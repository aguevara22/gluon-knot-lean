import ActualBasepointSideTransport
import FiniteContinuousIndex

set_option autoImplicit false
noncomputable section
open DirectGLSSW
open scoped BigOperators
namespace DirectGLSSW.HOMFLY.PLWinding
open PositionalIndex

/-- Complete original-coordinate meaning of the basepoint and its normal probes. -/
theorem actual_normal_parameter_eq_coordinates {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) (τ ε : ℝ) :
    let e := (T.baseArc C).val
    normalAtEdgeParameter (actualComponentWord T C)
      ⟨0,componentArcLength_pos D e⟩ τ ε =
      Complex.equivRealProd.symm (affinePoint (D.vertexPoint (D.arcSource e))
        (D.vertexPoint (D.arcTarget e)) τ) +
      (ε : ℂ) * Complex.I * PrincipalTurning.arcVector D e := by
  intro e
  rw [normalAtEdgeParameter_eq_literal,actualComponentWord_successor,
    actualComponentWord_zero]
  simp only [pow_zero,Equiv.Perm.one_apply]
  apply Complex.ext <;>
    simp [Complex.equivRealProd_symm_apply,affinePoint,PrincipalTurning.arcVector] <;> ring

/-- Finite literal edge avoidance excludes the image of the actual continuous loop. -/
theorem complexPLLoop_avoids_of_actual_word_avoids {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) (z : ℂ)
    (h : AvoidsPolygonEdges (actualComponentWord T C) z) :
    ∀ u : unitInterval, complexPLLoop D (T.baseArc C).val u ≠ z := by
  intro u hu
  let e := (T.baseArc C).val
  have hmem : componentPLLoop D e u ∈ Set.range (componentPLLoop D e) := ⟨u,rfl⟩
  obtain ⟨f,hf,tf,htf⟩ := (componentPLLoop_trace D e _).mp hmem
  let E := PermutationOrbits.orbitEnumeration D.continuation e
  let i := E.symm ⟨f,hf⟩
  have hi : (D.continuation ^ i.val) e = f := by
    have hx := congrArg Subtype.val (E.apply_symm_apply ⟨f,hf⟩)
    simpa only [E,i,PermutationOrbits.orbitEnumeration_apply_val] using hx
  have hs : actualComponentWord T C i =
      Complex.equivRealProd.symm (D.vertexPoint (D.arcSource f)) := by
    change Complex.equivRealProd.symm (D.vertexPoint (D.arcSource ((D.continuation ^ i.val) e))) = _
    rw [hi]
  have ht : actualComponentWord T C (cyclicSuccessorPerm (componentArcLength D e) i) =
      Complex.equivRealProd.symm (D.vertexPoint (D.arcTarget f)) := by
    rw [actualComponentWord_successor]
    change Complex.equivRealProd.symm (D.vertexPoint (D.arcTarget ((D.continuation ^ i.val) e))) = _
    rw [hi]
  apply h i tf.val tf.property.1 tf.property.2
  rw [hs,ht,←hu]
  change Complex.equivRealProd.symm (componentPLLoop D e u) = _
  rw [←htf,diagramArcPath_apply]
  apply Complex.ext <;> simp [Complex.equivRealProd_symm_apply,affinePoint]

/-- The same actual component's continuous positional indices at every
interior basepoint satisfy Whitney in the source determinant convention. -/
theorem actualComponent_whitney_at_arbitrary_basepoint {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    let e := (T.baseArc C).val
    let q := actualComponentWord T C
    let i₀ : Fin (componentArcLength D e) := ⟨0,componentArcLength_pos D e⟩
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ hpos : ∀ u : unitInterval, complexPLLoop D e u ≠ normalAtEdgeParameter q i₀ τ ε,
      ∃ hneg : ∀ u : unitInterval, complexPLLoop D e u ≠ normalAtEdgeParameter q i₀ τ (-ε),
        unitPositionalIndex (complexPLLoop D e) (complexPLLoop_endpoint_eq D e).symm
          (normalAtEdgeParameter q i₀ τ ε) hpos = (actualBaseSideIndexPair T C).1 ∧
        unitPositionalIndex (complexPLLoop D e) (complexPLLoop_endpoint_eq D e).symm
          (normalAtEdgeParameter q i₀ τ (-ε)) hneg = (actualBaseSideIndexPair T C).2 ∧
        (∑ c ∈ PrincipalTurning.actualComponentSelfCrossings T C,
          if 0 < PrincipalTurning.complexDet
            (PrincipalTurning.crossingVector D c (firstVisitedBranch T c))
            (PrincipalTurning.crossingVector D c (otherBranch (firstVisitedBranch T c)))
          then (1 : ℝ) else -1) =
          ((unitPositionalIndex (complexPLLoop D e) (complexPLLoop_endpoint_eq D e).symm
              (normalAtEdgeParameter q i₀ τ ε) hpos +
            unitPositionalIndex (complexPLLoop D e) (complexPLLoop_endpoint_eq D e).symm
              (normalAtEdgeParameter q i₀ τ (-ε)) hneg : ℤ) : ℝ) -
            (PrincipalTurning.componentTurnInteger D C : ℝ) := by
  intro e q i₀
  obtain ⟨δ,hδ,hp,hn⟩ := actual_base_side_indices_at_parameter T C τ hτ0 hτ1
  refine ⟨δ,hδ,?_⟩
  intro ε hε hεδ
  obtain ⟨hpa,hpv⟩ := hp ε ⟨hε,hεδ⟩
  obtain ⟨hna,hnv⟩ := hn (-ε) ⟨by linarith,by linarith⟩
  have hpos := complexPLLoop_avoids_of_actual_word_avoids T C _ hpa
  have hneg := complexPLLoop_avoids_of_actual_word_avoids T C _ hna
  obtain ⟨_,hpi⟩ := complexPLLoop_index_eq_actualComponentWord_windingIndex D T C _ hpos
  obtain ⟨_,hni⟩ := complexPLLoop_index_eq_actualComponentWord_windingIndex D T C _ hneg
  have hpidx := hpi.trans hpv
  have hnidx := hni.trans hnv
  refine ⟨hpos,hneg,hpidx,hnidx,?_⟩
  rw [hpidx,hnidx]
  have hw := actualComponent_whitney_general T C
  dsimp only at hw
  linarith

end DirectGLSSW.HOMFLY.PLWinding




