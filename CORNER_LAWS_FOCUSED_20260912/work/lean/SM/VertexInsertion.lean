import SM.AppendRotation

/-! Insertion at every original edge and every strict interior parameter.
The cyclic cut starts at the chosen edge's next vertex. This retains all old
vertices in traversal order and places the new vertex on the chosen old edge. -/

namespace SM

variable {n : ℕ} [NeZero n]

def insertVertex (P : LabelledTuple n) (i : ZMod n) (t : ℝ) : LabelledTuple (n + 1) :=
  appendVertex (shift (i + 1) P) t

theorem insertVertex_old (P : LabelledTuple n) (i j : ZMod n) (t : ℝ) :
    insertVertex P i t (insertIndex j) = P (j + (i + 1)) := by
  rw [insertVertex, appendVertex_old]
  rfl

theorem insertVertex_new (P : LabelledTuple n) (i : ZMod n) (t : ℝ) :
    insertVertex P i t (insertedIndex n) = edgePoint P i t := by
  rw [insertVertex, appendVertex_new, edgePoint_shift]
  congr 1
  ring

theorem insertVertex_new_mem_edgeInterior (P : LabelledTuple n) (i : ZMod n) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    insertVertex P i t (insertedIndex n) ∈ edgeInterior P i :=
  ⟨t, ht0, ht1, insertVertex_new P i t⟩

theorem regular_insertVertex {P : LabelledTuple n} (h : Regular P) (i : ZMod n) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) : Regular (insertVertex P i t) :=
  regular_appendVertex ((regular_shift (i + 1) P).mpr h) ht0 ht1

theorem rotationNumber_insertVertex {P : LabelledTuple n} (h : Regular P) (i : ZMod n) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) : rotationNumber (insertVertex P i t) = rotationNumber P := by
  rw [insertVertex, rotationNumber_appendVertex ((regular_shift (i + 1) P).mpr h) ht0 ht1,
    rotationNumber_shift]

theorem vertex_insertion {P : LabelledTuple n} (h : Regular P) (i : ZMod n) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    (∀ j : ZMod n, insertVertex P i t (insertIndex j) = P (j + (i + 1))) ∧
    insertVertex P i t (insertedIndex n) = edgePoint P i t ∧
    insertVertex P i t (insertedIndex n) ∈ edgeInterior P i ∧
    Function.Injective (insertIndex (n := n)) ∧
    (∀ j : ZMod n, insertIndex j ≠ insertedIndex n) ∧
    (∀ j : ZMod (n + 1), j = insertedIndex n ∨ ∃ k : ZMod n, j = insertIndex k) ∧
    Regular (insertVertex P i t) ∧ rotationNumber (insertVertex P i t) = rotationNumber P :=
  ⟨fun j => insertVertex_old P i j t, insertVertex_new P i t,
    insertVertex_new_mem_edgeInterior P i ht0 ht1, insertIndex_injective,
    insertIndex_ne_inserted, insertion_indices_exhaust,
    regular_insertVertex h i ht0 ht1, rotationNumber_insertVertex h i ht0 ht1⟩

end SM
