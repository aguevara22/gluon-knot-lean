import SM.TripleOrder
import SM.NamedWallPredicates
import SM.TripleSides

/-! The source's three sign changes give the exact three order reversals.
The unordered support characterization explicitly covers all six orderings. -/

namespace SM

variable {n : ℕ} [NeZero n]

theorem opposite_difference_orders {a b c d : ℝ} (h : (a - b) * (c - d) < 0) :
    (a < b ↔ d < c) ∧ (b < a ↔ c < d) := by
  rcases mul_neg_iff.mp h with ⟨hab, hcd⟩ | ⟨hab, hcd⟩
  · exact ⟨iff_of_false (by linarith) (by linarith),
      iff_of_true (by linarith) (by linarith)⟩
  · exact ⟨iff_of_true (by linarith) (by linarith),
      iff_of_false (by linarith) (by linarith)⟩

def TriangleOrderExchanges (P Q : LabelledTuple n) (e f g : ZMod n) : Prop :=
  ((edgeParameter P e f < edgeParameter P e g ↔ edgeParameter Q e g < edgeParameter Q e f) ∧
    (edgeParameter P e g < edgeParameter P e f ↔ edgeParameter Q e f < edgeParameter Q e g)) ∧
  ((edgeParameter P f e < edgeParameter P f g ↔ edgeParameter Q f g < edgeParameter Q f e) ∧
    (edgeParameter P f g < edgeParameter P f e ↔ edgeParameter Q f e < edgeParameter Q f g)) ∧
  ((edgeParameter P g e < edgeParameter P g f ↔ edgeParameter Q g f < edgeParameter Q g e) ∧
    (edgeParameter P g f < edgeParameter P g e ↔ edgeParameter Q g e < edgeParameter Q g f))

theorem triple_support_six_orders {α : Type*} [DecidableEq α] {i j k e f g : α}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hs : ({i, j, k} : Finset α) = {e, f, g}) :
    (i = e ∧ j = f ∧ k = g) ∨ (i = e ∧ j = g ∧ k = f) ∨
    (i = f ∧ j = e ∧ k = g) ∨ (i = f ∧ j = g ∧ k = e) ∨
    (i = g ∧ j = e ∧ k = f) ∨ (i = g ∧ j = f ∧ k = e) := by
  have hi : i ∈ ({e, f, g} : Finset α) := by rw [← hs]; simp
  have hj : j ∈ ({e, f, g} : Finset α) := by rw [← hs]; simp
  have hk : k ∈ ({e, f, g} : Finset α) := by rw [← hs]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
  rcases hi with rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl <;> simp_all

theorem triangleOrderExchanges_all {P Q : LabelledTuple n} {e f g i j k : ZMod n}
    (h : TriangleOrderExchanges P Q e f g) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hs : ({i, j, k} : Finset (ZMod n)) = {e, f, g}) :
    edgeParameter P i j < edgeParameter P i k ↔ edgeParameter Q i k < edgeParameter Q i j := by
  rcases triple_support_six_orders hij hik hjk hs with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact h.1.1
  · exact h.1.2
  · exact h.2.1.1
  · exact h.2.1.2
  · exact h.2.2.1
  · exact h.2.2.2

namespace WallGerm

theorem triple_order_exchanges_local (g : WallGerm n) {e f k : ZMod n}
    (h : g.TripleAt e f k) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.SideParameter, t.val < δ →
      TriangleOrderExchanges (g.sideTuple true t).val (g.sideTuple false t).val e f k := by
  obtain ⟨δe, hδe, hδer, he⟩ := h.2.2.1
  obtain ⟨δf, hδf, _, hf⟩ := h.2.2.2.1
  obtain ⟨δk, hδk, _, hk⟩ := h.2.2.2.2
  let δ := min δe (min δf δk)
  have hde : δ ≤ δe := min_le_left _ _
  have hdf : δ ≤ δf := (min_le_right _ _).trans (min_le_left _ _)
  have hdk : δ ≤ δk := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, lt_min hδe (lt_min hδf hδk), hde.trans hδer, ?_⟩
  intro t ht
  exact ⟨opposite_difference_orders (he t (lt_of_lt_of_le ht hde)),
    opposite_difference_orders (hf t (lt_of_lt_of_le ht hdf)),
    opposite_difference_orders (hk t (lt_of_lt_of_le ht hdk))⟩

end WallGerm
end SM
