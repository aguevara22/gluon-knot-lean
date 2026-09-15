import SM.GaussVisits
import SM.TraversalRelabel

namespace SM

variable {n : ℕ}

def visitEdgeShiftEquiv (a : ZMod n) {P : LabelledTuple n} (c : Crossing P) :
    {i // i ∈ c.val} ≃ {j // j ∈ (crossingShift a c).val} where
  toFun i := ⟨i.val - a, mem_crossingShift a c i.val i.property⟩
  invFun j := ⟨j.val + a, by
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp j.property
    have hj : j.val + a = i := by rw [← he]; simp
    simpa only [hj] using hi⟩
  left_inv i := Subtype.ext (sub_add_cancel i.val a)
  right_inv j := Subtype.ext (add_sub_cancel_right j.val a)

def visitShiftEquiv (a : ZMod n) (P : LabelledTuple n) : Visit P ≃ Visit (shift a P) :=
  Equiv.sigmaCongr (crossingShiftEquiv a P) (visitEdgeShiftEquiv a)

theorem visitShiftEquiv_apply (a : ZMod n) (P : LabelledTuple n) (v : Visit P) :
    visitShiftEquiv a P v = visitShift a v := rfl

theorem visitShift_crossing (a : ZMod n) {P : LabelledTuple n} (v : Visit P) :
    (visitShift a v).1 = crossingShiftEquiv a P v.1 := rfl

theorem visitShift_bijective (a : ZMod n) (P : LabelledTuple n) :
    Function.Bijective (visitShift (P := P) a) := (visitShiftEquiv a P).bijective

theorem visitKey_shift (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (a : ZMod n) (v : Visit P) :
    visitKey hn (g1_shift_forward a hP) (visitShift a v) =
      if visitKey hn hP v < (a.val : ℝ) then visitKey hn hP v - (a.val : ℝ) + n
      else visitKey hn hP v - (a.val : ℝ) := by
  haveI : NeZero n := ⟨by omega⟩
  unfold visitKey
  rw [visitPosition_shift, traversalKey_shift]

end SM
