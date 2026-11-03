import MarkedSuffixOrigin
import MarkedRootOrigin
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits
attribute [local instance] Classical.propDecidable

/-- The suffix includes every actual arc at or beyond a, not just a chosen chain. -/
theorem markedSuffixArc_range (t : MarkedParentState) (a e : Fin t.1.nArc) :
    (∃ i, markedSuffixArc t a i = e) ↔ visitPosition t.2.1 a ≤ visitPosition t.2.1 e := by
  constructor
  · rintro ⟨i,rfl⟩
    rw [markedSuffixArc_visitPosition]
    omega
  · intro hle
    have he : componentOf t.1.continuation e = componentOf t.1.continuation (markedOrbitRoot t a) :=
      ((componentOf_eq_iff _ _ _).mpr (t.2.2.connected e a)).trans
        (t.2.1.baseArc (componentOf t.1.continuation a)).property.symm
    let j := (orbitEnumeration t.1.continuation (markedOrbitRoot t a)).symm ⟨e,he⟩
    have hj : markedOrbitArc t a j = e :=
      congrArg Subtype.val ((orbitEnumeration t.1.continuation (markedOrbitRoot t a)).apply_symm_apply ⟨e,he⟩)
    have hp : visitPosition t.2.1 e = j.val := by
      rw [← hj,markedOrbitArc_visitPosition]
    let i : Fin (markedSuffixSize t a) := ⟨j.val-visitPosition t.2.1 a,by
      have hjlt : j.val < markedOrbitSize t a := j.isLt
      change j.val-visitPosition t.2.1 a < markedOrbitSize t a-visitPosition t.2.1 a
      omega⟩
    refine ⟨i,?_⟩
    change markedOrbitArc t a _ = e
    convert hj using 1
    congr 1
    apply Fin.ext
    change visitPosition t.2.1 a + (j.val-visitPosition t.2.1 a) = j.val
    omega

end DirectGLSSW.HOMFLY
