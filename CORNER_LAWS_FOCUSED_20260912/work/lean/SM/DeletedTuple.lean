import SM.DeletionIndices
import SM.InsertedTuple
import SM.StrictBetween
import SM.ContinuousGeometry

/-! Actual deletion of a vertex, retaining every other vertex in its induced
cyclic order. Its closing edge is the fused predecessor-to-successor segment. -/

namespace SM

variable {n : ℕ} [NeZero n]

def deleteVertex (P : LabelledTuple (n + 1)) (j : ZMod (n + 1)) : LabelledTuple n :=
  fun i => P (deletionIndex j i)

theorem deleteVertex_apply (P : LabelledTuple (n + 1)) (j : ZMod (n + 1)) (i : ZMod n) :
    deleteVertex P j i = P (deletionIndex j i) := rfl

theorem deleteVertex_zero (P : LabelledTuple (n + 1)) (j : ZMod (n + 1)) :
    deleteVertex P j 0 = P (j + 1) := by
  rw [deleteVertex_apply, deletionIndex_zero]

theorem deleteVertex_last (P : LabelledTuple (n + 1)) (j : ZMod (n + 1)) :
    deleteVertex P j (-1) = P (j - 1) := by
  rw [deleteVertex_apply, deletionIndex_last]

theorem edge_deleteVertex (P : LabelledTuple (n + 1)) (j : ZMod (n + 1))
    {i : ZMod n} (hi : i ≠ -1) :
    edge (deleteVertex P j) i = edge P (deletionIndex j i) := by
  simp only [edge, deleteVertex_apply, deletionIndex_next j hi]

theorem edge_deleteVertex_last (P : LabelledTuple (n + 1)) (j : ZMod (n + 1)) :
    edge (deleteVertex P j) (-1) = P (j + 1) - P (j - 1) := by
  simp only [edge, neg_add_cancel, deleteVertex_zero, deleteVertex_last]

theorem edgePoint_deleteVertex (P : LabelledTuple (n + 1)) (j : ZMod (n + 1))
    {i : ZMod n} (hi : i ≠ -1) (t : ℝ) :
    edgePoint (deleteVertex P j) i t = edgePoint P (deletionIndex j i) t := by
  simp only [edgePoint, deleteVertex_apply, edge_deleteVertex P j hi]

theorem edgeInterior_deleteVertex (P : LabelledTuple (n + 1)) (j : ZMod (n + 1))
    {i : ZMod n} (hi : i ≠ -1) :
    edgeInterior (deleteVertex P j) i = edgeInterior P (deletionIndex j i) := by
  simp only [edgeInterior, edgePoint_deleteVertex P j hi]

theorem continuous_deleteVertex (j : ZMod (n + 1)) :
    Continuous (fun P : LabelledTuple (n + 1) => deleteVertex P j) := by
  exact continuous_pi (fun i => continuous_apply (deletionIndex j i))

theorem append_deleteVertex (P : LabelledTuple (n + 1)) (j : ZMod (n + 1))
    {t : ℝ} (ht : P j = P (j - 1) + t • (P (j + 1) - P (j - 1))) :
    appendVertex (deleteVertex P j) t = shift (j + 1) P := by
  funext k
  rcases insertion_indices_exhaust k with rfl | ⟨i, rfl⟩
  · rw [appendVertex_new]
    simp only [edgePoint, deleteVertex_last, edge_deleteVertex_last, shift,
      insertedIndex_eq_neg_one]
    have hj : (-1 : ZMod (n + 1)) + (j + 1) = j := by ring
    rw [hj]
    exact ht.symm
  · rw [appendVertex_old]
    rfl

theorem strictBetween_append_deleteVertex (P : LabelledTuple (n + 1))
    {j : ZMod (n + 1)} (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1))) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ appendVertex (deleteVertex P j) t = shift (j + 1) P := by
  obtain ⟨_, t, ht0, ht1, ht⟩ := hb
  exact ⟨t, ht0, ht1, append_deleteVertex P j ht⟩

end SM
