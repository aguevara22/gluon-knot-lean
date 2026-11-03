import ActiveArcAfterFirstSupports
import ActiveArcSurvivingClosedWords

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor.Surviving
open DirectGLSSW ActiveArc PermutationOrbits
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c)
variable (t : ℝ) (hct : leftParameter q c < t) (htb : t < afterBound q c)
variable (S : Finset (Crossing q)) (hu : c ∉ S)

/-- The actual post-crossing closed-component bijection. All geometric window
conditions and survival are derived internally from the unselected crossing. -/
def afterFirstClosedComponentEquiv :
    let ht0 : 0 ≤ t := (lt_trans (leftParameter_spec q c).1 hct).le
    let ht1 : t < 1 := lt_of_lt_of_le htb (afterBound_le_one q c)
    let hM : Regular (moveStart q t) :=
      (regular_first_window_iff q hR c hc t ht0 htb).mpr (ne_of_gt hct)
    {C : Component (incoming (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S)) //
      C ≠ openComponent (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S)} ≃
    {D : Component (incoming q hR.noTriple S) // D ≠ openComponent q hR.noTriple S} := by
  dsimp only
  refine closedComponentEquiv q hR t _ _ S ?_ ?_
  · intro d hd
    exact (survives_after_first_iff q hR c hc t hct htb d).mpr (fun he => hu (he ▸ hd))
  · exact (regular_first_window_iff q hR c hc t
      (lt_trans (leftParameter_spec q c).1 hct).le htb).mpr (ne_of_gt hct)

/-- Source-facing closed factor geometry after the first crossing: the
canonical retained words on matched closed components agree up to rotation. -/
theorem after_first_closed_word_isRotated :
    let ht0 : 0 ≤ t := (lt_trans (leftParameter_spec q c).1 hct).le
    let ht1 : t < 1 := lt_of_lt_of_le htb (afterBound_le_one q c)
    let hM : Regular (moveStart q t) :=
      (regular_first_window_iff q hR c hc t ht0 htb).mpr (ne_of_gt hct)
    ∀ C : {C : Component (incoming (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S)) //
      C ≠ openComponent (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S)},
      let D := afterFirstClosedComponentEquiv q hR c hc t hct htb S hu C
      List.ofFn (RetainedWords.vertex q hR S (closedRoot q hR.noTriple S D.val D.property)) ~r
        List.ofFn (RetainedWords.vertex (moveStart q t) hM (movingSelection q t ht0 ht1 S)
          (closedRoot (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S) C.val C.property)) := by
  dsimp only
  intro C
  have hS : ∀ d∈S, Survives q t d := by
    intro d hd
    exact (survives_after_first_iff q hR c hc t hct htb d).mpr (fun he => hu (he ▸ hd))
  exact closed_word_isRotated q hR t _ _ S hS _ C

end DirectGLSSW.ActiveArc.Cursor.Surviving
