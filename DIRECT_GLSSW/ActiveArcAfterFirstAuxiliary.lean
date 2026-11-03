import ActiveArcAfterFirstClosedComponents
import DirectGLSSW.DaughterRootAmplitude

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor.Surviving
open DirectGLSSW ActiveArc PermutationOrbits
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c)
variable (t : ℝ) (hct : leftParameter q c < t) (htb : t < afterBound q c)
variable (hAux : Primitive.ClosedAuxiliary q hR)
include hAux

/-- Every actual closed word of a transported unselected support is generic,
using only the original closed auxiliary package and the proved rotation. -/
theorem after_first_closed_cyclicGeneric
    (U : {U : Primitive.Support q hR // c ∉ U.val}) :
    let ht0 : 0 ≤ t := (lt_trans (leftParameter_spec q c).1 hct).le
    let hM : Regular (moveStart q t) :=
      (regular_first_window_iff q hR c hc t ht0 htb).mpr (ne_of_gt hct)
    let V := (afterFirstSupportEquiv q hR c hc t hct htb).symm U
    ∀ C : Primitive.Components (moveStart q t) hM V,
      ∀ hC : C ≠ openComponent (moveStart q t) hM.noTriple V.val,
        CyclicGeneric (Primitive.ClosedVertex (moveStart q t) hM V C hC) := by
  dsimp only
  intro C hC
  let D := afterFirstClosedComponentEquiv q hR c hc t hct htb U.val.val U.property ⟨C,hC⟩
  have hg := hAux U.val D.val D.property
  exact DaughterRootAmplitude.cyclicGeneric_ofFn_isRotated
    (after_first_closed_word_isRotated q hR c hc t hct htb U.val.val U.property ⟨C,hC⟩) hg

/-- The actual moving arc's entire closed auxiliary condition follows from
the original one: all moving supports are exhausted by the proved support equivalence. -/
theorem after_first_closedAuxiliary :
    let ht0 : 0 ≤ t := (lt_trans (leftParameter_spec q c).1 hct).le
    let hM : Regular (moveStart q t) :=
      (regular_first_window_iff q hR c hc t ht0 htb).mpr (ne_of_gt hct)
    Primitive.ClosedAuxiliary (moveStart q t) hM := by
  dsimp only
  intro V
  obtain ⟨U,hU⟩ := (afterFirstSupportEquiv q hR c hc t hct htb).symm.surjective V
  subst V
  exact after_first_closed_cyclicGeneric q hR c hc t hct htb hAux U

end DirectGLSSW.ActiveArc.Cursor.Surviving
