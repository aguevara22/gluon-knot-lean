import DirectGLSSW.LocalCoordinates
import HOMFLYOrbitEmbedding
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.LocalCoordinates
open PermutationOrbits

/-- Actual rooted coordinates transport under a proved cycle embedding,
including a named component fibre rather than only the root's quotient label. -/
theorem rootedEnumeration_position_embedding
    {α β : Type*} [Fintype α] [Fintype β]
    (p : Equiv.Perm α) (q : Equiv.Perm β)
    (e : α → β) (hinj : Function.Injective e) (he : ∀x, e (p x)=q (e x))
    (A : Component p) (root x : Fibre p A) :
    ((orbitEnumeration q (e root.val)).symm
      (orbitFibreEquivOfEmbedding p q e hinj he root.val
        ⟨x.val,x.property.trans root.property.symm⟩)).val =
    ((rootedEnumeration p root).symm x).val := by
  rcases root with ⟨r,hr⟩
  subst A
  simpa [rootedEnumeration] using orbitPosition_embedding p q e hinj he r x
end DirectGLSSW.LocalCoordinates
