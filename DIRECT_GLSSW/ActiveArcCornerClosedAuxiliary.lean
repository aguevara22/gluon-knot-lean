import ActiveArcCornerClosedWords
import DirectGLSSW.DaughterRootAmplitude

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open Primitive RetainedWords PermutationOrbits
attribute [local instance] Classical.propDecidable
variable {b : ℕ} (q : Fin (1+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (hfree : ∀ d : Crossing q, d.val.1 ≠ 0)
include hfree

/-- Closed genericity passes from the actual suffix to the original arc. -/
theorem corner_closedAuxiliary_from_suffix
    (hAux : ClosedAuxiliary (suffix q) (regular_suffix q hR)) : ClosedAuxiliary q hR := by
  intro V
  obtain ⟨T,rfl⟩ := (firstEdgeFreeSupportEquiv q hfree hR).surjective V
  intro C hC
  let E := cornerClosedComponentEquiv q hR hfree T
  let D := E.symm ⟨C,hC⟩
  have hg := hAux T D.val D.property
  have hrot := corner_closed_word_isRotated q hR hfree T D
  have he : E D=⟨C,hC⟩ := E.apply_symm_apply ⟨C,hC⟩
  change List.ofFn (ClosedVertex (suffix q) (regular_suffix q hR) T D.val D.property) ~r
    List.ofFn (ClosedVertex q hR (firstEdgeFreeSupportEquiv q hfree hR T)
      (E D).val (E D).property) at hrot
  rw [he] at hrot
  exact DaughterRootAmplitude.cyclicGeneric_ofFn_isRotated hrot hg

/-- The original closed auxiliary domain supplies the actual suffix domain. -/
theorem corner_closedAuxiliary_suffix
    (hAux : ClosedAuxiliary q hR) : ClosedAuxiliary (suffix q) (regular_suffix q hR) := by
  intro T D hD
  let C := cornerClosedComponentEquiv q hR hfree T ⟨D,hD⟩
  have hg := hAux (firstEdgeFreeSupportEquiv q hfree hR T) C.val C.property
  have hrot := corner_closed_word_isRotated q hR hfree T ⟨D,hD⟩
  exact DaughterRootAmplitude.cyclicGeneric_ofFn_isRotated hrot.symm hg

theorem corner_closedAuxiliary_iff :
    ClosedAuxiliary q hR ↔ ClosedAuxiliary (suffix q) (regular_suffix q hR) :=
  ⟨corner_closedAuxiliary_suffix q hR hfree,corner_closedAuxiliary_from_suffix q hR hfree⟩

end DirectGLSSW.ActiveArc.Split
