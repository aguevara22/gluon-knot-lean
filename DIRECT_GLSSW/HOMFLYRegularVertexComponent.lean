import LowestRowContract.Contract
import DirectGLSSW.HOMFLY.HOMFYSmoothingDiagram

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
open DirectGLSSW.PermutationOrbits

/-- The two incident oriented arcs at a regular vertex have one actual component. -/
theorem regular_vertex_component (D : PLLinkDiagram) (v : Fin D.nVertex)
    (hv : ∀ c : Fin D.nCrossing, D.crossingVertex c ≠ v)
    (e f : Fin D.nArc)
    (he : D.arcSource e = v ∨ D.arcTarget e = v)
    (hf : D.arcSource f = v ∨ D.arcTarget f = v) :
    componentOf D.continuation e = componentOf D.continuation f := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (D.regular_degree_one v hv).2
  have hout : ∀ x : Fin D.nArc, D.arcSource x = v → x = a := by
    intro x hx
    have hm : x ∈ outgoingArcs D.arcSource v := by simp [outgoingArcs, hx]
    rw [ha] at hm
    exact Finset.mem_singleton.mp hm
  have hcomponent : ∀ x : Fin D.nArc,
      D.arcSource x = v ∨ D.arcTarget x = v →
      componentOf D.continuation x = componentOf D.continuation a := by
    intro x hx
    rcases hx with hx | hx
    · rw [hout x hx]
    · have hnext : D.continuation x = a :=
        hout _ ((D.continuation_incidence x).symm.trans hx)
      rw [← hnext, componentOf_apply]
  exact (hcomponent e he).trans (hcomponent f hf).symm

/-- A regular endpoint of an excluded actual arc is not a vertex of that component. -/
theorem regular_vertex_not_componentVertex (D : PLLinkDiagram)
    (C : diagramComponent D) (v : Fin D.nVertex)
    (hv : ∀ c : Fin D.nCrossing, D.crossingVertex c ≠ v)
    (e : Fin D.nArc) (he : D.arcSource e = v ∨ D.arcTarget e = v)
    (hne : componentOf D.continuation e ≠ C) :
    ¬ ∃ a : LowestRowContract.ComponentArc D C, D.arcSource a.val = v := by
  rintro ⟨a, ha⟩
  exact hne ((regular_vertex_component D v hv e a.val he (Or.inl ha)).trans a.property)

/-- Actual smoothing connector source vertices are regular, including the reused old label. -/
theorem smooth_connector_source_regular (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (i : Fin 2) :
    ∀ d : Fin (smoothCrossing D c).nCrossing,
      (smoothCrossing D c).crossingVertex d ≠
        (smoothCrossing D c).arcSource (smoothArcEquiv D (Sum.inr i)) := by
  intro d h
  have h' := (smoothVertexEquiv D c).injective h
  change Sum.inl (D.crossingVertex ((smoothCrossingEquiv D c).symm d).val) =
    smoothArcSourceCode D c ((smoothArcEquiv D).symm (smoothArcEquiv D (Sum.inr i))) at h'
  simp only [Equiv.symm_apply_apply] at h'
  have hne : D.crossingVertex ((smoothCrossingEquiv D c).symm d).val ≠ D.crossingVertex c :=
    fun h => ((smoothCrossingEquiv D c).symm d).property (D.crossingVertex_injective h)
  fin_cases i <;> simp [smoothArcSourceCode, smoothLeftCutCode, hne] at h'

/-- Actual smoothing connector target vertices are regular. -/
theorem smooth_connector_target_regular (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (i : Fin 2) :
    ∀ d : Fin (smoothCrossing D c).nCrossing,
      (smoothCrossing D c).crossingVertex d ≠
        (smoothCrossing D c).arcTarget (smoothArcEquiv D (Sum.inr i)) := by
  intro d h
  have h' := (smoothVertexEquiv D c).injective h
  change Sum.inl (D.crossingVertex ((smoothCrossingEquiv D c).symm d).val) =
    smoothArcTargetGeometryCode D c ((smoothArcEquiv D).symm (smoothArcEquiv D (Sum.inr i))) at h'
  simp only [Equiv.symm_apply_apply, smoothArcTargetGeometryCode] at h'
  simp only [smoothRightCutCode] at h'
  split_ifs at h' <;> contradiction

end DirectGLSSW.HOMFLY
