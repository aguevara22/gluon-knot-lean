import ActiveArcCompatibleWordSplice
import OrbitJoinSpectatorComponents

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open DirectGLSSW PermutationOrbits SingletonWords Split Cursor
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
variable (T : Finset (Crossing (parent q c hcut)))

/-- Every actual selected spectator has exactly the same complete incoming
orbit after removing the cut. -/
theorem unselected_spectator_orbitWord_eq (x : Event q)
    (ha : ¬(incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))).SameCycle x (Sum.inr (c,false)))
    (hb : ¬(incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))).SameCycle x (Sum.inr (c,true))) :
    orbitWord (incoming q hR.noTriple (pieceSelections q hR c hc hcut S T)) x =
      orbitWord (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))) x := by
  classical
  let U := pieceSelections q hR c hc hcut S T
  have hu : c∉U := by
    intro hh
    exact ((pieceSelections_range q hR c hc hcut U).mp ⟨S,T,rfl⟩ c hh).1 rfl
  rw [incoming_unselected_eq_swap q hR c U hu]
  apply SpectatorDaughterWords.orbitWord_eq_of_agree_on_component
  intro y hy
  apply mul_swap_apply_of_ne
  · intro he
    subst y
    exact ha ((componentOf_eq_iff _ _ _).mp hy.symm)
  · intro he
    subst y
    exact hb ((componentOf_eq_iff _ _ _).mp hy.symm)

/-- The two removed retained visits are absent from a spectator's orbit,
so its literal rooted retained point word is unchanged. -/
theorem unselected_spectator_pointWord_eq (x : Event q)
    (ha : ¬(incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))).SameCycle x (Sum.inr (c,false)))
    (hb : ¬(incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))).SameCycle x (Sum.inr (c,true))) :
    List.ofFn (RetainedWords.vertex q hR (pieceSelections q hR c hc hcut S T) x) =
      List.ofFn (RetainedWords.vertex q hR (insert c (pieceSelections q hR c hc hcut S T)) x) := by
  let U := pieceSelections q hR c hc hcut S T
  have hu : c∉U := by
    intro hh
    exact ((pieceSelections_range q hR c hc hcut U).mp ⟨S,T,rfl⟩ c hh).1 rfl
  rw [retainedWord_eq_filtered,retainedWord_eq_filtered,
    unselected_spectator_orbitWord_eq q hR c hc hcut S T x ha hb]
  apply congrArg (List.map (eventPoint q))
  apply filter_retained_cut_of_avoids q c U hu
  · exact fun h => ha ((mem_orbitWord_iff _ _ _).mp h)
  · exact fun h => hb ((mem_orbitWord_iff _ _ _).mp h)

end DirectGLSSW.ActiveArc.CompatibleWords
