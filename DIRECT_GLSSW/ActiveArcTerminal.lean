import ActiveArcOrbits
import DirectGLSSW.OpenMarkedCurrent

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc
open PermutationOrbits

/-- Endpoint-clamped extension of the actual LINE word, used only for its finite interval. -/
def rawWord {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (k : ℕ) : PlanarPoint ℝ :=
  q ⟨min k (n+1),lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)⟩

def rawCurrent {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) : ℚ :=
  OpenMarkedCurrent.entry (polygonSignArray (rawWord q)) 0 (n+1)

instance singleEdgeCrossingEmpty (q : Fin 2 → PlanarPoint ℝ) : IsEmpty (Crossing q) :=
  ⟨fun c => (ne_of_lt c.property.1) (Fin.ext (by have := c.val.1.isLt;have := c.val.2.isLt;omega))⟩

theorem singleEdge_support_empty (q : Fin 2 → PlanarPoint ℝ) (S : Finset (Crossing q)) : S=∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro c
  exact isEmptyElim c

theorem singleEdge_noTriple (q : Fin 2 → PlanarPoint ℝ) : NoTriple q := by
  intro e f g x hef
  exact False.elim (hef (Fin.ext (by have := e.isLt;have := f.isLt;omega)))

theorem singleEdge_event_endpoints (q : Fin 2 → PlanarPoint ℝ) (x : Event q) :
    x=start q ∨ x=terminal q := by
  cases x with
  | inl i => fin_cases i <;> simp [start,terminal]
  | inr v => exact isEmptyElim v.1

theorem singleEdge_component_eq_open (q : Fin 2 → PlanarPoint ℝ)
    (h : NoTriple q) (S : Finset (Crossing q)) (C : Component (incoming q h S)) :
    C=openComponent q h S := by
  induction C using Quotient.inductionOn with | h x =>
    rcases singleEdge_event_endpoints q x with hh|hh
    · subst x;rfl
    · subst x;exact component_endpoints_eq q h S

def singleEdgeClosedComponentsEmpty (q : Fin 2 → PlanarPoint ℝ)
    (h : NoTriple q) (S : Finset (Crossing q)) :
    IsEmpty {C : Component (incoming q h S) // C≠openComponent q h S} :=
  ⟨fun C => C.property (singleEdge_component_eq_open q h S C.val)⟩

theorem singleEdge_current_eq_one (q : Fin 2 → PlanarPoint ℝ) : rawCurrent q=1 := by
  exact OpenMarkedCurrent.entry_adjacent_eq_one (polygonSignArray (rawWord q)) 0



theorem singleEdge_all_retained (q : Fin 2 → PlanarPoint ℝ)
    (S : Finset (Crossing q)) (x : Event q) : retained q S x := by
  rcases singleEdge_event_endpoints q x with hh|hh
  · rw [hh];exact (endpoints_retained q S).1
  · rw [hh];exact (endpoints_retained q S).2

theorem singleEdge_openOrbit_card (q : Fin 2 → PlanarPoint ℝ)
    (h : NoTriple q) (S : Finset (Crossing q)) :
    Fintype.card (Fibre (incoming q h S) (openComponent q h S))=2 := by
  classical
  let e : Fibre (incoming q h S) (openComponent q h S) ≃ Event q :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x,singleEdge_component_eq_open q h S _⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    _ = Fintype.card (Event q) := Fintype.card_congr e
    _ = 2 := by simp [Event,Visit,Fintype.card_sum,Fintype.card_prod]

theorem singleEdge_openEventWord_length (q : Fin 2 → PlanarPoint ℝ)
    (h : NoTriple q) (S : Finset (Crossing q)) :
    (openEventWord q h S).length=2 :=
  (orbitWord_length (incoming q h S) (start q)).trans (singleEdge_openOrbit_card q h S)

end DirectGLSSW.ActiveArc
