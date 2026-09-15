import SM.GenericReversal
import SM.CrossingEquiv

/-! Reversal on actual unordered crossing supports is exactly i -> 1-i. -/

namespace SM

variable {n : ℕ}

theorem remote_sub_left (a i j : ZMod n) : remote (a - i) (a - j) ↔ remote i j := by
  have he : (a - j) - (a - i) = i - j := by ring
  have hr : remote (a - i) (a - j) ↔ remote j i := by
    simp only [remote, adjacent, he]
  exact hr.trans ⟨remote_symm, remote_symm⟩

def reverseSupport (s : Finset (ZMod n)) : Finset (ZMod n) :=
  s.image (fun i => 1 - i)

theorem reverseSupport_involutive : Function.Involutive (reverseSupport (n := n)) := by
  intro s
  simp [reverseSupport, Finset.image_image]

theorem isCrossing_reverseSupport {P : LabelledTuple n} {s : Finset (ZMod n)}
    (h : IsCrossing P s) : IsCrossing (reversal P) (reverseSupport s) := by
  obtain ⟨i, j, hs, hr, hmeet⟩ := h
  refine ⟨1 - i, 1 - j, ?_, (remote_sub_left 1 i j).mpr hr, ?_⟩
  · simp [reverseSupport, hs]
  · simpa only [edgeSegment_reversal, sub_sub_cancel] using hmeet

theorem isCrossing_reversal_iff (P : LabelledTuple n) (s : Finset (ZMod n)) :
    IsCrossing (reversal P) (reverseSupport s) ↔ IsCrossing P s := by
  constructor
  · intro h
    have hx := isCrossing_reverseSupport h
    simpa only [reversal_involutive P, reverseSupport_involutive s] using hx
  · exact isCrossing_reverseSupport

def crossingReversalEquiv (P : LabelledTuple n) : Crossing P ≃ Crossing (reversal P) where
  toFun c := ⟨reverseSupport c.val, isCrossing_reverseSupport c.property⟩
  invFun d := ⟨reverseSupport d.val, by
    simpa only [reversal_involutive P] using isCrossing_reverseSupport d.property⟩
  left_inv c := Subtype.ext (reverseSupport_involutive c.val)
  right_inv d := Subtype.ext (reverseSupport_involutive d.val)

theorem crossingSet_reversal [NeZero n] (P : LabelledTuple n) :
    crossingSet (reversal P) = (crossingSet P).image reverseSupport := by
  classical
  ext s
  rw [mem_crossingSet, Finset.mem_image]
  constructor
  · intro h
    refine ⟨reverseSupport s, ?_, reverseSupport_involutive s⟩
    rw [mem_crossingSet]
    simpa only [reversal_involutive P] using isCrossing_reverseSupport h
  · rintro ⟨t, ht, rfl⟩
    exact isCrossing_reverseSupport ((mem_crossingSet P t).mp ht)

end SM
