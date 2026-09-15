import SM.Chirotope

/-! Source def:shift: traversal reversal is the actual map i -> 2-i. It
fixes vertex 1, conjugates a cyclic shift to the opposite shift, and descends
to the cyclic quotient. It is not identified with a cyclic relabelling. -/

namespace SM

variable {n : ℕ}

def reversal (P : LabelledTuple n) : LabelledTuple n := fun i => P (2 - i)

theorem reversal_apply (P : LabelledTuple n) (i : ZMod n) :
    reversal P i = P (2 - i) := rfl

theorem reversal_fixes_one (P : LabelledTuple n) : reversal P 1 = P 1 := by
  change P (2 - 1) = P 1
  congr 1
  ring

theorem reversal_involutive : Function.Involutive (reversal (n := n)) := by
  intro P
  funext i
  simp [reversal]

theorem reversal_shift (a : ZMod n) (P : LabelledTuple n) :
    reversal (shift a P) = shift (-a) (reversal P) := by
  funext i
  change P (2 - i + a) = P (2 - (i + -a))
  congr 1
  ring

theorem reversal_respects_cyclic {P Q : LabelledTuple n}
    (h : (cyclicSetoid n).r P Q) :
    (cyclicSetoid n).r (reversal P) (reversal Q) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨-a, reversal_shift a P⟩

def polygonReversal (hn : 3 ≤ n) : Polygon n hn → Polygon n hn :=
  Quotient.map reversal (fun _ _ h => reversal_respects_cyclic h)

theorem polygonReversal_mk (hn : 3 ≤ n) (P : LabelledTuple n) :
    polygonReversal hn (Quotient.mk (cyclicSetoid n) P) =
      Quotient.mk (cyclicSetoid n) (reversal P) := rfl

theorem polygonReversal_involutive (hn : 3 ≤ n) :
    Function.Involutive (polygonReversal hn) := by
  intro P
  refine Quotient.inductionOn P (fun Q => ?_)
  change Quotient.mk (cyclicSetoid n) (reversal (reversal Q)) =
    Quotient.mk (cyclicSetoid n) Q
  rw [reversal_involutive Q]

/-- Every reversed edge is the old edge traversed in the opposite direction. -/
theorem edge_reversal (P : LabelledTuple n) (i : ZMod n) :
    edge (reversal P) i = -edge P (1 - i) := by
  have h1 : (2 : ZMod n) - (i + 1) = 1 - i := by ring
  have h2 : (1 : ZMod n) - i + 1 = 2 - i := by ring
  simp [edge, reversal, h1, h2]

theorem turn_reversal (P : LabelledTuple n) (i : ZMod n) :
    turn (reversal P) i = -turn P (2 - i) := by
  have h1 : (2 : ZMod n) - (i - 1) = 2 - i + 1 := by ring
  have h2 : (2 : ZMod n) - (i + 1) = 2 - i - 1 := by ring
  change chi P (2 - (i - 1)) (2 - i) (2 - (i + 1)) =
    -chi P (2 - i - 1) (2 - i) (2 - i + 1)
  rw [h1, h2]
  exact chi_swap_outer P _ _ _

/-- Complete source definition and its assertion of descent to polygons.
The edge and turn identities expose the actual orientation change. -/
theorem reversal_definition (hn : 3 ≤ n) :
    (∀ P : LabelledTuple n, ∀ i, reversal P i = P (2 - i)) ∧
    (∀ P : LabelledTuple n, reversal P 1 = P 1) ∧
    (∀ a : ZMod n, ∀ P : LabelledTuple n,
      reversal (shift a P) = shift (-a) (reversal P)) ∧
    (∀ P : LabelledTuple n,
      polygonReversal hn (Quotient.mk (cyclicSetoid n) P) =
        Quotient.mk (cyclicSetoid n) (reversal P)) ∧
    Function.Involutive (polygonReversal hn) ∧
    (∀ P : LabelledTuple n, ∀ i, edge (reversal P) i = -edge P (1 - i)) ∧
    (∀ P : LabelledTuple n, ∀ i, turn (reversal P) i = -turn P (2 - i)) :=
  ⟨reversal_apply, reversal_fixes_one, reversal_shift, polygonReversal_mk hn,
    polygonReversal_involutive hn, edge_reversal, turn_reversal⟩

end SM
