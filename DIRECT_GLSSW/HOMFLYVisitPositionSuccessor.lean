import HOMFLYPrefixVisitPosition
import DirectGLSSW.OrbitNormalization
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits
attribute [local instance] Classical.propDecidable

/-- A continuation step that does not wrap to the actual fixed root increases position by one. -/
theorem visitPosition_continuation_of_ne_root (D : PLLinkDiagram) (T : BasedTraversal D)
    (x : Fin D.nArc)
    (hne : D.continuation x ≠ (T.baseArc (componentOf D.continuation x)).val) :
    visitPosition T (D.continuation x) = visitPosition T x + 1 := by
  let p := D.continuation
  let r := (T.baseArc (componentOf p x)).val
  have hcomp : componentOf p r = componentOf p x := (T.baseArc (componentOf p x)).property
  let N := Fintype.card (Fibre p (componentOf p r))
  let j : Fin N := (orbitEnumeration p r).symm ⟨x,hcomp.symm⟩
  have hj : (orbitEnumeration p r j).val = x :=
    congrArg Subtype.val ((orbitEnumeration p r).apply_symm_apply ⟨x,hcomp.symm⟩)
  have hroot : (T.baseArc (componentOf p r)).val = r := by rw [hcomp]
  have hpos : visitPosition T x = j.val := by
    have hh := visitPosition_orbitEnumeration T r hroot j
    rw [hj] at hh
    exact hh
  have hstep : (orbitEnumeration p r (cyclicSuccessorPerm N j)).val = p x := by
    rw [orbitEnumeration_successor]
    change p (orbitEnumeration p r j).val = p x
    rw [hj]
  have hlt : j.val+1 < N := by
    by_contra hh
    have he : j.val+1=N := by have := j.isLt;omega
    have hz : cyclicSuccessorPerm N j = 0 := by
      apply Fin.ext
      change (j.val+1+0)%N = 0
      rw [Nat.add_zero,he,Nat.mod_self]
    have heq : p x = r := by
      rw [← hstep,hz,orbitEnumeration_zero]
    exact hne heq
  have hh := visitPosition_orbitEnumeration T r hroot (cyclicSuccessorPerm N j)
  rw [hstep] at hh
  change visitPosition T (p x) = (j.val+1+0)%N at hh
  rw [Nat.add_zero,Nat.mod_eq_of_lt hlt] at hh
  exact hh.trans (congrArg (fun n:ℕ=>n+1) hpos.symm)

end DirectGLSSW.HOMFLY
