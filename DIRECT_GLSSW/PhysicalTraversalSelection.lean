import PhysicalCursorG1
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.TraversalClosure
open DirectGLSSW ActiveArc Cursor Split Primitive
attribute [local instance] Classical.propDecidable

/-- Positivity at every remaining original corner; endpoints have no cyclic turn. -/
def RemainingLeft {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) : Prop :=
  ∀ i : Fin n, 0<planarDet
    (q i.castSucc.succ-q i.castSucc.castSucc) (q i.succ.succ-q i.castSucc.succ)

lemma remainingLeft_moveStart {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hleft : RemainingLeft q) (t : ℝ) (ht : t<1) : RemainingLeft (moveStart q t) := by
  intro i
  exact cursor_turn_pos q t ht i.castSucc i.succ (hleft i)

lemma remainingLeft_suffix {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ)
    (hleft : RemainingLeft q) : RemainingLeft (suffix q) := by
  intro i
  change 0<planarDet
    (suffix q i.castSucc.succ-suffix q i.castSucc.castSucc)
    (suffix q i.succ.succ-suffix q i.succ.castSucc)
  rw [suffix_tangent,suffix_tangent]
  let j : Fin (a+b) := ⟨a+i.val,by omega⟩
  have he₀ : edge (a:=a) i.castSucc=j.castSucc := Fin.ext rfl
  have he₁ : edge (a:=a) i.succ=j.succ := Fin.ext (by simp [edge,j,Nat.add_assoc])
  rw [he₀,he₁]
  exact hleft j

lemma suffix_G1 {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ)
    (hG : cyclicNoncollinear q) : cyclicNoncollinear (suffix q) := by
  intro i j k hij hjk hik
  exact hG (vertex i) (vertex j) (vertex k)
    (fun hh => hij (vertex_injective hh)) (fun hh => hjk (vertex_injective hh))
    (fun hh => hik (vertex_injective hh))

/-- Corner deletion propagates every required state invariant. No corner far
condition is needed by geometry/AUX closure itself. -/
theorem corner_suffix_state_closure {b : ℕ} (q : Fin (1+b+2) → PlanarPoint ℝ)
    (hR : Regular q) (hG : cyclicNoncollinear q) (hAux : ClosedAuxiliary q hR)
    (hleft : RemainingLeft q) (hfree : ∀ c : Crossing q,c.val.1≠0) :
    cyclicNoncollinear (suffix q) ∧
      ClosedAuxiliary (suffix q) (regular_suffix q hR) ∧ RemainingLeft (suffix q) :=
  ⟨suffix_G1 q hG,corner_closedAuxiliary_suffix q hR hfree hAux,remainingLeft_suffix q hleft⟩

/-- A parent inherits actual regularity, closed AUX, and all remaining turns.
All-triple G1 at its newly introduced root is a separate determinant obligation. -/
theorem parent_basic_state_closure {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ)
    (hR : Regular q) (hAux : ClosedAuxiliary q hR) (hleft : RemainingLeft q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a) :
    ClosedAuxiliary (parent q c hcut) (regular_parent q hR c hcut) ∧
      RemainingLeft (parent q c hcut) := by
  refine ⟨CompatibleWords.parent_closedAuxiliary q hR c hc hcut hAux,?_⟩
  exact remainingLeft_moveStart (suffix q) (remainingLeft_suffix q hleft)
    (rightParameter q c) (rightParameter_spec q c).2.1

/-- First-event/crossing-free/terminal selection is derived from the actual
finite crossing carrier, with the positive corner supplied by RemainingLeft. -/
theorem actual_first_edge_selection {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hleft : RemainingLeft q) :
    n=0 ∨ (∃ c : Crossing q,FirstCrossing q c) ∨
      (∃ hn : 0<n, (∀ c : Crossing q,c.val.1≠0) ∧
        0<planarDet (q 1-q 0) (q ⟨2,by omega⟩-q 1)) := by
  by_cases hn : n=0
  · exact Or.inl hn
  by_cases hex : ∃ c : Crossing q,c.val.1=0
  · exact Or.inr (Or.inl (exists_firstCrossing q hex))
  · refine Or.inr (Or.inr ⟨Nat.pos_of_ne_zero hn,?_,?_⟩)
    · intro c hc; exact hex ⟨c,hc⟩
    · exact hleft ⟨0,Nat.pos_of_ne_zero hn⟩
end DirectGLSSW.ActiveArc.TraversalClosure
