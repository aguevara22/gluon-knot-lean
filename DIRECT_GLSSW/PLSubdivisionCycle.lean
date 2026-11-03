import PLArcSubdivisionContraction
import HOMFLYArcContractionComponents

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.ArcSubdivision
open DirectGLSSW.PermutationOrbits

/-- Physical subdivision preserves the full-cycle property because its actual
arc contraction induces an equivalence of continuation components. -/
theorem subdivideArc_isCycleOn (D : PLLinkDiagram) (e : Fin D.nArc)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hp : D.continuation.IsCycleOn Set.univ) :
    (subdivideArc D e t ht0 ht1).continuation.IsCycleOn Set.univ := by
  let R := subdivideArc_contraction D e t ht0 ht1
  let p := (subdivideArc D e t ht0 ht1).continuation
  refine ⟨p.bijOn (fun _ => Iff.rfl), ?_⟩
  intro x _ y _
  apply (componentOf_eq_iff p x y).mp
  apply R.componentEquiv.injective
  rw [R.componentEquiv_map, R.componentEquiv_map]
  apply (componentOf_eq_iff D.continuation _ _).mpr
  exact hp.2 (Set.mem_univ _) (Set.mem_univ _)

end DirectGLSSW.HOMFLY.ArcSubdivision
