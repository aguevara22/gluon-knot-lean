import ActiveArcSurvivingWords
import ActiveArcRetainedOrbitComponents

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

include hS in
/-- Actual incoming components correspond on retained physical labels,
although the full event sets differ by deleted unselected visits. -/
theorem mapped_sameCycle_iff
    (x y : {x : Event (moveStart q t) // retained (moveStart q t) (movingSelection q t ht0 ht1 S) x}) :
    (incoming q hR.noTriple S).SameCycle (eventMap q t ht0 ht1 x.val) (eventMap q t ht0 ht1 y.val) ↔
      (incoming (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S)).SameCycle x.val y.val := by
  letI := eventOrder q hR.noTriple
  letI := eventOrder (moveStart q t) hM.noTriple
  let E := retainedOrderIso q hR t ht0 ht1 S hS hM
  have ho := retained_sameCycle_iff_reduced q hR S (E x) (E y)
  have hn := retained_sameCycle_iff_reduced (moveStart q t) hM (movingSelection q t ht0 ht1 S) x y
  refine ho.trans (Iff.trans ?_ hn.symm)
  rw [← mem_orbitWord_iff,← mem_orbitWord_iff]
  change E y ∈ orbitWord (orderedCyclicSuccessor _ * physicalRetainedPairing q S) (E x) ↔ _
  rw [retainedOrderIso_orbitWord q hR t ht0 ht1 S hS hM]
  constructor
  · intro hh
    obtain ⟨z,hz,he⟩ := List.mem_map.mp hh
    have he' : z=y := E.injective he
    exact he' ▸ hz
  · intro hy
    exact List.mem_map.mpr ⟨y,hy,rfl⟩

include hS in
theorem mapped_open_iff
    (x : {x : Event (moveStart q t) // retained (moveStart q t) (movingSelection q t ht0 ht1 S) x}) :
    componentOf (incoming q hR.noTriple S) (eventMap q t ht0 ht1 x.val) = openComponent q hR.noTriple S ↔
      componentOf (incoming (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S)) x.val =
        openComponent (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S) := by
  simp only [openComponent,componentOf_eq_iff]
  exact mapped_sameCycle_iff q hR t ht0 ht1 S hS hM x
    ⟨start (moveStart q t),(endpoints_retained _ _).1⟩

end DirectGLSSW.ActiveArc.Cursor.Surviving
