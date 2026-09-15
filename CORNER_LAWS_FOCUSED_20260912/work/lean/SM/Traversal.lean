import SM.CrossingEquiv
import Mathlib.Order.Circular

/-! The actual half-open edge-parameter traversal set of source def:gauss.
A real coordinate chooses a cut at label zero. Its circularization closes
that cut; the resulting ternary cyclic order is not a linear order on a circle. -/

namespace SM

variable {n : ℕ}

abbrev TraversalPoint (n : ℕ) := ZMod n × Set.Ico (0 : ℝ) 1

def traversalEvaluation (P : LabelledTuple n) (p : TraversalPoint n) : Plane :=
  edgePoint P p.1 p.2.val

noncomputable def traversalKey (p : TraversalPoint n) : ℝ := p.1.val + p.2.val

theorem traversalKey_lt_of_edge_lt {p q : TraversalPoint n}
    (h : p.1.val < q.1.val) : traversalKey p < traversalKey q := by
  have hi : (p.1.val : ℝ) + 1 ≤ q.1.val := by exact_mod_cast h
  have hp := p.2.property.2
  have hq := q.2.property.1
  dsimp [traversalKey]
  linarith

theorem traversalKey_same_edge (i : ZMod n) (s t : Set.Ico (0 : ℝ) 1) :
    traversalKey (i, s) < traversalKey (i, t) ↔ s.val < t.val := by
  exact add_lt_add_iff_left _

theorem traversalKey_injective [NeZero n] :
    Function.Injective (traversalKey (n := n)) := by
  intro p q heq
  have hi : p.1.val = q.1.val := by
    rcases lt_trichotomy p.1.val q.1.val with h | h | h
    · exact (ne_of_lt (traversalKey_lt_of_edge_lt h) heq).elim
    · exact h
    · exact (ne_of_lt (traversalKey_lt_of_edge_lt h) heq.symm).elim
  have hi' := ZMod.val_injective n hi
  apply Prod.ext hi'
  apply Subtype.ext
  dsimp [traversalKey] at heq
  rw [hi] at heq
  exact add_left_cancel heq

theorem traversalKey_lt_iff [NeZero n] (p q : TraversalPoint n) :
    traversalKey p < traversalKey q ↔
      p.1.val < q.1.val ∨ p.1 = q.1 ∧ p.2.val < q.2.val := by
  constructor
  · intro h
    rcases lt_trichotomy p.1.val q.1.val with hi | hi | hi
    · exact Or.inl hi
    · right
      refine ⟨ZMod.val_injective n hi, ?_⟩
      dsimp [traversalKey] at h
      rw [hi] at h
      exact (add_lt_add_iff_left _).mp h
    · exact (lt_asymm h (traversalKey_lt_of_edge_lt hi)).elim
  · rintro (hi | ⟨hi, ht⟩)
    · exact traversalKey_lt_of_edge_lt hi
    · dsimp [traversalKey]
      rw [hi]
      exact (add_lt_add_iff_left _).mpr ht

noncomputable def traversalLinearOrder [NeZero n] : LinearOrder (TraversalPoint n) :=
  LinearOrder.lift' traversalKey traversalKey_injective

noncomputable def traversalCircularOrder [NeZero n] : CircularOrder (TraversalPoint n) :=
  @LinearOrder.toCircularOrder (TraversalPoint n) traversalLinearOrder

/-- Strict oriented cyclic order: increasing coordinates, with either possible
wrap across the chosen cut. -/
def traversalBetween (p q r : TraversalPoint n) : Prop :=
  (traversalKey p < traversalKey q ∧ traversalKey q < traversalKey r) ∨
  (traversalKey q < traversalKey r ∧ traversalKey r < traversalKey p) ∨
  (traversalKey r < traversalKey p ∧ traversalKey p < traversalKey q)

theorem traversalBetween_eq_circular [NeZero n] (p q r : TraversalPoint n) :
    traversalBetween p q r ↔ @SBtw.sbtw _ traversalCircularOrder.toSBtw p q r := Iff.rfl

theorem traversalBetween_rotate (p q r : TraversalPoint n) :
    traversalBetween p q r ↔ traversalBetween q r p := by
  unfold traversalBetween
  tauto

def traversalShift (a : ZMod n) (p : TraversalPoint n) : TraversalPoint n :=
  (p.1 - a, p.2)

theorem traversalEvaluation_shift (P : LabelledTuple n) (a : ZMod n)
    (p : TraversalPoint n) :
    traversalEvaluation (shift a P) (traversalShift a p) = traversalEvaluation P p := by
  simp only [traversalEvaluation, traversalShift, edgePoint_shift, sub_add_cancel]

end SM
