import ActiveArcSurvivingWords

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor.Surviving
open DirectGLSSW ActiveArc PermutationOrbits RetainedWords
attribute [local instance] Classical.propDecidable

/-- Source-facing post-crossing transport. The removed crossing is unselected,
so its disappearing visits are absent from the retained word. Moving
regularity and all selected-label survival are proved from the actual window. -/
theorem after_first_open_word
    {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c)
    (t : ℝ) (hct : leftParameter q c < t) (htb : t < afterBound q c)
    (S : Finset (Crossing q)) (hu : c ∉ S) :
    let ht0 : 0 ≤ t := (lt_trans (leftParameter_spec q c).1 hct).le
    let ht1 : t < 1 := lt_of_lt_of_le htb (afterBound_le_one q c)
    let hM : Regular (moveStart q t) :=
      (regular_first_window_iff q hR c hc t ht0 htb).mpr (ne_of_gt hct)
    List.ofFn (vertex (moveStart q t) hM (movingSelection q t ht0 ht1 S) (start (moveStart q t))) =
      affinePoint (q 0) (q 1) t :: (List.ofFn (vertex q hR S (start q))).tail := by
  dsimp only
  apply open_word q hR t _ _ S
  intro d hd
  exact (survives_after_first_iff q hR c hc t hct htb d).mpr (fun he => hu (he ▸ hd))

/-- The same physical post-crossing window preserves every closed retained
word at corresponding retained roots. Canonical roots differ only by the
existing cyclic-rotation normalization. -/
theorem after_first_closed_root_word
    {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c)
    (t : ℝ) (hct : leftParameter q c < t) (htb : t < afterBound q c)
    (S : Finset (Crossing q)) (hu : c ∉ S) :
    let ht0 : 0 ≤ t := (lt_trans (leftParameter_spec q c).1 hct).le
    let ht1 : t < 1 := lt_of_lt_of_le htb (afterBound_le_one q c)
    let hM : Regular (moveStart q t) :=
      (regular_first_window_iff q hR c hc t ht0 htb).mpr (ne_of_gt hct)
    ∀ root : {x : Event (moveStart q t) // retained (moveStart q t) (movingSelection q t ht0 ht1 S) x},
      componentOf (incoming (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S)) root.val ≠
        openComponent (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S) →
      List.ofFn (vertex (moveStart q t) hM (movingSelection q t ht0 ht1 S) root.val) =
        List.ofFn (vertex q hR S (eventMap q t ht0 ht1 root.val)) := by
  dsimp only
  intro root hclosed
  apply closed_root_word q hR t _ _ S _ _ root hclosed
  intro d hd
  exact (survives_after_first_iff q hR c hc t hct htb d).mpr (fun he => hu (he ▸ hd))

end DirectGLSSW.ActiveArc.Cursor.Surviving
