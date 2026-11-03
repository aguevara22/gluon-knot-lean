import HoleStarNeighbourConverse

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open Equiv PermutationOrbits

/-- The actual secant spanning one uniform polygon vertex is the positive
cone combination of its two actual consecutive arc vectors. -/
theorem basedUniformSecant_one_corner {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (k : ℤ) (s t : ℝ)
    (hs : s ∈ Set.Icc ((k : ℝ)-1/2) ((k : ℝ)+1/2))
    (ht : t ∈ Set.Icc ((k : ℝ)+1/2) ((k : ℝ)+3/2)) :
    basedUniformSecant T C s t =
      (((k : ℝ)+1/2-s : ℝ) : ℂ) * arcVector D ((D.continuation ^ k) (T.baseArc C).val) +
      ((t-(k : ℝ)-1/2 : ℝ) : ℂ) * arcVector D (D.continuation ((D.continuation ^ k) (T.baseArc C).val)) := by
  have hsarc := uniformPLCurve_arc_cell D (T.baseArc C).val k (s+1/2-(k : ℝ))
    (by constructor <;> linarith [hs.1,hs.2])
  have hstime : (k : ℝ)+(s+1/2-(k : ℝ))=s+1/2 := by ring
  rw [hstime] at hsarc
  have htarc := uniformPLCurve_arc_cell D (T.baseArc C).val (k+1) (t+1/2-((k+1 : ℤ) : ℝ))
    (by push_cast; constructor <;> linarith [ht.1,ht.2])
  have httime : ((k+1 : ℤ) : ℝ)+(t+1/2-((k+1 : ℤ) : ℝ))=t+1/2 := by ring
  rw [httime] at htarc
  have hp : (D.continuation ^ (k+1)) (T.baseArc C).val =
      D.continuation ((D.continuation ^ k) (T.baseArc C).val) := by
    rw [add_comm k 1,zpow_add,Equiv.Perm.mul_apply,zpow_one]
  rw [hp] at htarc
  have hinc := congrArg D.vertexPoint (D.continuation_incidence ((D.continuation ^ k) (T.baseArc C).val))
  apply Complex.equivRealProd.injective
  simp only [basedUniformSecant,Equiv.apply_symm_apply]
  change uniformPLCurve D (T.baseArc C).val (t+1/2) -
    uniformPLCurve D (T.baseArc C).val (s+1/2) = _
  rw [htarc,hsarc]
  simp only [arcVector]
  rw [←hinc]
  apply Prod.ext <;>
    simp [Complex.equivRealProd_apply,affinePoint] <;> ring

end DirectGLSSW.HOMFLY.PrincipalTurning

