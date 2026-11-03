import ActiveArcCompatibleCutOrbits

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open DirectGLSSW PermutationOrbits
attribute [local instance] Classical.propDecidable

/-- Away from the two physical cut visits, selecting or unselecting the cut
has exactly the same retention predicate on a literal event list. -/
theorem filter_retained_cut_of_avoids {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (c : Crossing q) (U : Finset (Crossing q)) (hu : c∉U) (L : List (Event q))
    (h0 : (Sum.inr (c,false) : Event q) ∉ L) (h1 : (Sum.inr (c,true) : Event q) ∉ L) :
    L.filter (fun x => decide (retained q U x)) =
      L.filter (fun x => decide (retained q (insert c U) x)) := by
  apply List.filter_congr
  intro x hx
  have hx0 : x ≠ Sum.inr (c,false) := fun he => h0 (he ▸ hx)
  have hx1 : x ≠ Sum.inr (c,true) := fun he => h1 (he ▸ hx)
  have hp : retained q U x ↔ retained q (insert c U) x := by
    constructor
    · intro h
      exact ((retained_unselected_iff q c U hu x).mp h).1
    · intro h
      exact (retained_unselected_iff q c U hu x).mpr ⟨h,hx0,hx1⟩
  exact congrArg (fun P : Prop => decide P) (propext hp)

end DirectGLSSW.ActiveArc.CompatibleWords
