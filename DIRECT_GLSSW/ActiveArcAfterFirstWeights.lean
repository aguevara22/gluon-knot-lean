import ActiveArcAfterFirstAuxiliary

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor.Surviving
open DirectGLSSW ActiveArc PermutationOrbits
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c)
variable (t : ℝ) (hct : leftParameter q c < t) (htb : t < afterBound q c)
variable (hRI : GLSSWRootIndependence) (hAux : Primitive.ClosedAuxiliary q hR)
include hRI

/-- Each actual closed amplitude is preserved under the derived physical
component matching. The moving auxiliary proof is constructed internally. -/
theorem after_first_closedWeight_eq
    (U : Primitive.Support q hR) (hu : c ∉ U.val) :
    let ht0 : 0 ≤ t := (lt_trans (leftParameter_spec q c).1 hct).le
    let hM : Regular (moveStart q t) :=
      (regular_first_window_iff q hR c hc t ht0 htb).mpr (ne_of_gt hct)
    let V := (afterFirstSupportEquiv q hR c hc t hct htb).symm ⟨U,hu⟩
    ∀ C : {C : Primitive.Components (moveStart q t) hM V //
      C ≠ openComponent (moveStart q t) hM.noTriple V.val},
      let D := afterFirstClosedComponentEquiv q hR c hc t hct htb U.val hu C
      Primitive.closedWeight q hR hAux U D.val =
        Primitive.closedWeight (moveStart q t) hM
          (after_first_closedAuxiliary q hR c hc t hct htb hAux) V C.val := by
  dsimp only
  intro C
  let D := afterFirstClosedComponentEquiv q hR c hc t hct htb U.val hu C
  have hD : D.val ≠ openComponent q hR.noTriple U.val := D.property
  rw [Primitive.closedWeight,dif_pos hD,Primitive.closedWeight,dif_pos C.property]
  exact DaughterRootAmplitude.polygonAmplitude_ofFn_isRotated hRI
    (hAux U D.val D.property)
    (after_first_closed_word_isRotated q hR c hc t hct htb U.val hu C)

/-- The full erased-open closed-factor product is preserved, reindexed by
an actual bijection of all closed components. -/
theorem after_first_closedWeight_product_eq
    (U : Primitive.Support q hR) (hu : c ∉ U.val) :
    let ht0 : 0 ≤ t := (lt_trans (leftParameter_spec q c).1 hct).le
    let hM : Regular (moveStart q t) :=
      (regular_first_window_iff q hR c hc t ht0 htb).mpr (ne_of_gt hct)
    let V := (afterFirstSupportEquiv q hR c hc t hct htb).symm ⟨U,hu⟩
    (∏ D ∈ Finset.univ.erase (openComponent q hR.noTriple U.val),
      Primitive.closedWeight q hR hAux U D) =
    (∏ C ∈ Finset.univ.erase (openComponent (moveStart q t) hM.noTriple V.val),
      Primitive.closedWeight (moveStart q t) hM
        (after_first_closedAuxiliary q hR c hc t hct htb hAux) V C) := by
  intro ht0 hM V
  let E := afterFirstClosedComponentEquiv q hR c hc t hct htb U.val hu
  rw [Finset.prod_subtype (p := fun D => D ≠ openComponent q hR.noTriple U.val)
    (Finset.univ.erase (openComponent q hR.noTriple U.val)) (fun D => by simp)]
  rw [Finset.prod_subtype (p := fun C => C ≠ openComponent (moveStart q t) hM.noTriple V.val)
    (Finset.univ.erase (openComponent (moveStart q t) hM.noTriple V.val)) (fun C => by simp)]
  symm
  apply Fintype.prod_equiv E
  intro C
  exact (after_first_closedWeight_eq q hR c hc t hct htb hRI hAux U hu C).symm

end DirectGLSSW.ActiveArc.Cursor.Surviving
