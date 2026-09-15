import SM.InsertionIndices
import SM.AngleScaling

/-! A concrete appended vertex at the cyclic cut. Every old vertex keeps its
natural index, and the new vertex is an actual point on the old wrap edge. -/

namespace SM

variable {n : ℕ} [NeZero n]

def appendVertex (P : LabelledTuple n) (t : ℝ) : LabelledTuple (n + 1) :=
  fun j => if j.val < n then P (j.val : ZMod n) else edgePoint P (-1) t

theorem appendVertex_old (P : LabelledTuple n) (t : ℝ) (i : ZMod n) :
    appendVertex P t (insertIndex i) = P i := by
  simp only [appendVertex, insertIndex_val, if_pos i.val_lt, ZMod.natCast_zmod_val]

theorem appendVertex_new (P : LabelledTuple n) (t : ℝ) :
    appendVertex P t (insertedIndex n) = edgePoint P (-1) t := by
  simp only [appendVertex, insertedIndex_val, lt_self_iff_false, if_false]

theorem appendVertex_zero (P : LabelledTuple n) (t : ℝ) : appendVertex P t 0 = P 0 := by
  rw [← insertIndex_zero, appendVertex_old]

theorem appendVertex_new_mem_edgeInterior (P : LabelledTuple n) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    appendVertex P t (insertedIndex n) ∈ edgeInterior P (-1) :=
  ⟨t, ht0, ht1, appendVertex_new P t⟩

theorem edge_appendVertex_old (P : LabelledTuple n) (t : ℝ) {i : ZMod n} (hi : i ≠ -1) :
    edge (appendVertex P t) (insertIndex i) = edge P i := by
  rw [edge, ← insertIndex_next hi, appendVertex_old, appendVertex_old]
  rfl

theorem edge_appendVertex_last (P : LabelledTuple n) (t : ℝ) :
    edge (appendVertex P t) (insertIndex (-1 : ZMod n)) = t • edge P (-1) := by
  rw [edge, insertIndex_last_add_one, appendVertex_new, appendVertex_old, edgePoint]
  abel

theorem edge_appendVertex_new (P : LabelledTuple n) (t : ℝ) :
    edge (appendVertex P t) (insertedIndex n) = (1 - t) • edge P (-1) := by
  rw [edge, insertedIndex_add_one, appendVertex_zero, appendVertex_new, edgePoint]
  have he : edge P (-1) = P 0 - P (-1) := by simp [edge]
  rw [he, sub_smul, one_smul]
  abel

theorem edge_appendVertex_old_scaled (P : LabelledTuple n) (t : ℝ) (i : ZMod n) :
    edge (appendVertex P t) (insertIndex i) = (if i = -1 then t else 1) • edge P i := by
  by_cases hi : i = -1
  · subst i
    simpa using edge_appendVertex_last P t
  · rw [if_neg hi, one_smul, edge_appendVertex_old P t hi]

theorem incoming_appendVertex_old_scaled (P : LabelledTuple n) (t : ℝ) (i : ZMod n) :
    edge (appendVertex P t) (insertIndex i - 1) =
      (if i = 0 then 1 - t else 1) • edge P (i - 1) := by
  by_cases hi : i = 0
  · subst i
    rw [insertIndex_zero_prev, edge_appendVertex_new]
    simp
  · have hp : i - 1 ≠ -1 := by
      intro he
      apply hi
      simpa only [sub_add_cancel, neg_add_cancel] using
        congrArg (fun j : ZMod n => j + 1) he
    rw [insertIndex_prev hi, edge_appendVertex_old P t hp, if_neg hi, one_smul]

end SM
