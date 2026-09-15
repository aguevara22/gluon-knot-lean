import SM.CrossingPair
import SM.ChamberPaths

/-! Canonical transport when actual crossing predicates agree. Crossing
supports and visited edge labels remain unchanged; their geometric parameters
may vary. No arbitrary bijection is supplied. -/

namespace SM

variable {n : ℕ} {P Q : LabelledTuple n}

def crossingTransport (h : ∀ s, IsCrossing P s ↔ IsCrossing Q s) :
    Crossing P ≃ Crossing Q := Equiv.subtypeEquivRight h

theorem crossingTransport_support (h : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (c : Crossing P) : (crossingTransport h c).val = c.val := rfl

def visitTransport (h : ∀ s, IsCrossing P s ↔ IsCrossing Q s) : Visit P ≃ Visit Q where
  toFun v := ⟨crossingTransport h v.1, v.2⟩
  invFun v := ⟨(crossingTransport h).symm v.1, v.2⟩
  left_inv v := by rcases v with ⟨⟨c, hc⟩, i⟩; rfl
  right_inv v := by rcases v with ⟨⟨c, hc⟩, i⟩; rfl

theorem visitTransport_crossing (h : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (v : Visit P) : (visitTransport h v).1 = crossingTransport h v.1 := rfl

theorem visitTransport_edge (h : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (v : Visit P) : (visitTransport h v).2.val = v.2.val := rfl

theorem crossing_support_partner (c : Crossing P) (i : ZMod n) (hi : i ∈ c.val) :
    ∃ j, i ≠ j ∧ c.val = {i, j} := by
  classical
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp (crossing_card_two c)
  rw [hs] at hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact ⟨b, hab, hs⟩
  · exact ⟨a, hab.symm, hs.trans (Finset.pair_comm _ _)⟩

theorem crossingParameter_eq_of_support_pair (hn : 3 ≤ n) (hP : G1 P)
    (c : Crossing P) (i j : ZMod n) (hi : i ∈ c.val) (hs : c.val = {i, j}) :
    crossingParameter c i hi = edgeParameter P i j := by
  rcases c with ⟨s, hc⟩
  change s = {i, j} at hs
  subst s
  exact crossingParameter_eq_edgeParameter hn hP hc

theorem visitParameter_eq_of_support_pair (hn : 3 ≤ n) (hP : G1 P)
    (v : Visit P) (j : ZMod n) (hs : v.1.val = {v.2.val, j}) :
    visitParameter v = edgeParameter P v.2.val j :=
  crossingParameter_eq_of_support_pair hn hP v.1 v.2.val j v.2.property hs

end SM
