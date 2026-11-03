import DirectGLSSW.ShortEdgeCyclicRelabel
import ExposedEdgeGeometry
import PolygonPositiveDiagram

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.PolygonRebase
open ExposedOpenPrimitive
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (ρ : Fin n ≃ Fin n)
    (hρ : ∀ e, ρ (cyclicSuccessor e) = cyclicSuccessor (ρ e))

include hρ in
theorem tangent_relabel (e : Fin n) :
    cyclicTangent (q ∘ ρ) e = cyclicTangent q (ρ e) := by
  simp only [cyclicTangent,Function.comp_apply,hρ]

include hρ in
theorem strictLeft_relabel
    (hleft : ∀ e, 0 < planarDet (cyclicTangent q e)
      (cyclicTangent q (cyclicSuccessor e))) :
    ∀ e, 0 < planarDet (cyclicTangent (q ∘ ρ) e)
      (cyclicTangent (q ∘ ρ) (cyclicSuccessor e)) := by
  intro e
  rw [tangent_relabel q ρ hρ,tangent_relabel q ρ hρ,hρ]
  exact hleft (ρ e)

include hρ in
theorem leftExposed_relabel (e : Fin n) (he : LeftExposed q (ρ e)) :
    LeftExposed (q ∘ ρ) e := by
  intro i hie his
  rw [tangent_relabel q ρ hρ]
  apply he (ρ i)
  · exact ρ.injective.ne hie
  · rw [← hρ]
    exact ρ.injective.ne his

include hρ in
theorem symm_commutes_successor (e : Fin n) :
    ρ.symm (cyclicSuccessor e) = cyclicSuccessor (ρ.symm e) := by
  apply ρ.injective
  rw [Equiv.apply_symm_apply,hρ,Equiv.apply_symm_apply]

include hρ in
theorem leftExposed_relabel_iff (e : Fin n) :
    LeftExposed (q ∘ ρ) e ↔ LeftExposed q (ρ e) := by
  refine ⟨?_,leftExposed_relabel q ρ hρ e⟩
  intro he i hie his
  have hp := he (ρ.symm i)
  have hi0 : ρ.symm i ≠ e := by intro h;exact hie (by simpa using congrArg ρ h)
  have hi1 : ρ.symm i ≠ cyclicSuccessor e := by
    intro h
    exact his (by simpa only [Equiv.apply_symm_apply,hρ] using congrArg ρ h)
  have hz := hp hi0 hi1
  simpa only [tangent_relabel q ρ hρ,Function.comp_apply,Equiv.apply_symm_apply] using hz

/-- The actual cyclic relabelling whose vertex0 is the selected edge's start. -/
def atEdge (e : Fin n) : Fin n ≃ Fin n :=
  cyclicVertexEquiv ((cyclicSuccessorPerm n).symm e)

theorem atEdge_commutes_successor (e i : Fin n) :
    atEdge e (cyclicSuccessor i) = cyclicSuccessor (atEdge e i) :=
  cyclicVertexEquiv_commutes_successor _ _

theorem atEdge_zero (e : Fin n) (hn : 0 < n) :
    atEdge e ⟨0,hn⟩ = e := by
  change cyclicSuccessor ((cyclicSuccessorPerm n).symm e) = e
  exact (cyclicSuccessorPerm n).apply_symm_apply e

theorem atEdge_symm_edge (e : Fin n) (hn : 0 < n) :
    (atEdge e).symm e = ⟨0,hn⟩ := by
  apply (atEdge e).injective
  rw [Equiv.apply_symm_apply,atEdge_zero e hn]

/-- The exact geometric restart at edge0; no evaluator or AUX invariance is assumed. -/
theorem exposed_zero_restart (hq : CyclicGeneric q) (e : Fin n)
    (he : LeftExposed q e)
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i)
      (cyclicTangent q (cyclicSuccessor i))) :
    CyclicGeneric (q ∘ atEdge e) ∧
      (∀ i, 0 < planarDet (cyclicTangent (q ∘ atEdge e) i)
        (cyclicTangent (q ∘ atEdge e) (cyclicSuccessor i))) ∧
      LeftExposed (q ∘ atEdge e) ⟨0,by have := hq.size_ge_three;omega⟩ ∧
      (q ∘ atEdge e) ⟨0,by have := hq.size_ge_three;omega⟩ = q e := by
  refine ⟨cyclicGeneric_relabel q (atEdge e) (atEdge_commutes_successor e) hq,
    strictLeft_relabel q (atEdge e) (atEdge_commutes_successor e) hleft,?_,?_⟩
  · apply leftExposed_relabel q (atEdge e) (atEdge_commutes_successor e)
    simpa only [atEdge_zero] using he
  · simp only [Function.comp_apply,atEdge_zero]

end DirectGLSSW.PolygonRebase
