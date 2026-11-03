import ActiveArcUnsmoothingSwap

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open DirectGLSSW PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
variable (T : Finset (Crossing (parent q c hcut)))

/-- The selected cut's left visit belongs to the actual open parent orbit. -/
theorem selected_left_visit_open :
    componentOf (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)))
      (Sum.inr (c,false)) = openComponent q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)) := by
  have hh := componentOf_apply (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))) (start q)
  simpa only [incoming_start_first q hR c hc,openComponent] using hh

/-- The selected cut's right visit is the actual closed child root at its
physical anchor c, not an extra or fictitious closing event. -/
theorem selected_right_visit_closed :
    componentOf (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)))
      (Sum.inr (c,true)) ≠ openComponent q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)) := by
  have hh := child_root_closed q hR c hc hcut S T ⟨Sum.inl 0,by trivial⟩
  simpa only [childEventMap_zero] using hh

theorem selected_cut_visits_separated :
    ¬(incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))).SameCycle
      (Sum.inr (c,false)) (Sum.inr (c,true)) := by
  intro hh
  have he := (componentOf_eq_iff _ _ _).mpr hh
  exact selected_right_visit_closed q hR c hc hcut S T
    (he.symm.trans (selected_left_visit_open q hR c hc hcut S T))

/-- Undoing the selected cut joins its child and parent cycles: both actual
cut visits lie in the unselected support's open component. -/
theorem unselected_cut_visits_open :
    componentOf (incoming q hR.noTriple (pieceSelections q hR c hc hcut S T))
        (Sum.inr (c,false)) = openComponent q hR.noTriple (pieceSelections q hR c hc hcut S T) ∧
    componentOf (incoming q hR.noTriple (pieceSelections q hR c hc hcut S T))
        (Sum.inr (c,true)) = openComponent q hR.noTriple (pieceSelections q hR c hc hcut S T) := by
  let U := pieceSelections q hR c hc hcut S T
  have hu : c∉U := by
    intro hh
    exact ((pieceSelections_range q hR c hc hcut U).mp ⟨S,T,rfl⟩ c hh).1 rfl
  let p := incoming q hR.noTriple (insert c U)
  have hab : ¬p.SameCycle (Sum.inr (c,false)) (Sum.inr (c,true)) :=
    selected_cut_visits_separated q hR c hc hcut S T
  have ha : p.SameCycle (Sum.inr (c,false)) (start q) :=
    (componentOf_eq_iff _ _ _).mp (selected_left_visit_open q hR c hc hcut S T)
  have hjoin := sameCycle_mul_swap_of_not_sameCycle p hab
  have hroot := (sameCycle_join_iff p hab (start q)).mpr (Or.inl ha)
  change componentOf (incoming q hR.noTriple U) _ = openComponent q hR.noTriple U ∧
    componentOf (incoming q hR.noTriple U) _ = openComponent q hR.noTriple U
  constructor
  · apply (componentOf_eq_iff _ _ _).mpr
    rw [incoming_unselected_eq_swap q hR c U hu]
    exact hroot
  · apply (componentOf_eq_iff _ _ _).mpr
    rw [incoming_unselected_eq_swap q hR c U hu]
    exact hjoin.symm.trans hroot

/-- The distinguished selected child point word is rooted exactly at the
right cut visit and equals the full actual child daughter at anchor zero. -/
theorem selected_child_word_at_cut :
    List.ofFn (RetainedWords.vertex q hR (insert c (pieceSelections q hR c hc hcut S T))
      (Sum.inr (c,true))) =
    DaughterFirstReturn.daughterPointList (child q hR c hc.1 hcut)
      (child_noTriple q hR c hc.1 hcut) S (Sum.inl 0) := by
  have hh := child_root_word q hR c hc hcut S T ⟨Sum.inl 0,by trivial⟩
  simpa only [childEventMap_zero,smoothingPairing_apply,smoothingPairingMap] using hh

/-- The distinguished child list starts at the geometric crossing point. -/
theorem selected_child_word_head :
    (DaughterFirstReturn.daughterPointList (child q hR c hc.1 hcut)
      (child_noTriple q hR c hc.1 hcut) S (Sum.inl 0)).head? = some (crossingPoint q c) := by
  have hh := DaughterFirstReturn.daughterPointList_head (child q hR c hc.1 hcut)
    (child_noTriple q hR c hc.1 hcut) S (Sum.inl 0) (by trivial)
  simpa only [polygonEventPoint,child_zero] using hh

end DirectGLSSW.ActiveArc.CompatibleWords
