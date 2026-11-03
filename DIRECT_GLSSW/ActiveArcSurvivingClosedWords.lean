import ActiveArcSurvivingClosedComponents

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor.Surviving
open DirectGLSSW ActiveArc PermutationOrbits CompatibleWords
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
variable (S : Finset (Crossing q)) (hS : ∀ d∈S, Survives q t d)
variable (hM : Regular (moveStart q t))

/-- Canonical words on corresponding actual closed components differ only
by cyclic root choice. Literal matching-root equality supplies the geometry. -/
theorem closed_word_isRotated
    (C : {C : Component (incoming (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S)) //
      C ≠ openComponent (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S)}) :
    let D := closedComponentEquiv q hR t ht0 ht1 S hS hM C
    List.ofFn (RetainedWords.vertex q hR S (closedRoot q hR.noTriple S D.val D.property)) ~r
      List.ofFn (RetainedWords.vertex (moveStart q t) hM (movingSelection q t ht0 ht1 S)
        (closedRoot (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S) C.val C.property)) := by
  let r : {x : Event (moveStart q t) // retained (moveStart q t) (movingSelection q t ht0 ht1 S) x} :=
    ⟨closedRoot (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S) C.val C.property,
      (closedRoot_spec (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S) C.val C.property).2⟩
  let D := closedComponentEquiv q hR t ht0 ht1 S hS hM C
  have hr : componentOf (incoming (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S)) r.val = C.val :=
    (closedRoot_spec (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S) C.val C.property).1
  have hm : componentOf (incoming q hR.noTriple S) (eventMap q t ht0 ht1 r.val) = D.val := rfl
  have hs := (closedRoot_spec q hR.noTriple S D.val D.property).1
  have hrot := retainedWord_isRotated_of_sameCycle q hR S
    (closedRoot q hR.noTriple S D.val D.property) (eventMap q t ht0 ht1 r.val)
    ((componentOf_eq_iff _ _ _).mp (hs.trans hm.symm))
  rw [← closed_root_word q hR t ht0 ht1 S hS hM r (by rw [hr];exact C.property)] at hrot
  exact hrot

end DirectGLSSW.ActiveArc.Cursor.Surviving
