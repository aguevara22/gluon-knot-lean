import SM.NamedWallRelabel
import SM.CuspEmptyDefinition

/-! The newborn support, central case and loop-side choice commute with
cyclic parent relabelling. The empty predicate is transported on actual visits. -/

namespace SM

variable {n : ℕ} [NeZero n]

theorem cuspCase_shift (r : ZMod n) (P : LabelledTuple n) (j : ZMod n) (b : Bool) :
    CuspCase (shift r P) (j - r) b ↔ CuspCase P j b := by
  cases b <;> simp only [CuspCase, Bool.false_eq_true, ↓reduceIte, shift,
    sub_add_cancel, wall_sub_add_cancel_right, wall_sub_sub_cancel_right]

theorem cuspFirst_sub (r j : ZMod n) (b : Bool) :
    cuspFirst b (j - r) = cuspFirst b j - r := by
  cases b <;> simp only [cuspFirst, Bool.false_eq_true, ↓reduceIte] <;> ring

theorem cuspLast_sub (r j : ZMod n) (b : Bool) :
    cuspLast b (j - r) = cuspLast b j - r := by
  simp only [cuspLast, cuspFirst_sub]
  ring

theorem cuspCorner₁_sub (r j : ZMod n) (b : Bool) :
    cuspCorner₁ b (j - r) = cuspCorner₁ b j - r := by
  simp only [cuspCorner₁, cuspFirst_sub]
  ring

theorem cuspCorner₂_sub (r j : ZMod n) (b : Bool) :
    cuspCorner₂ b (j - r) = cuspCorner₂ b j - r := cuspLast_sub r j b

theorem isCrossing_shift_support (r : ZMod n) (P : LabelledTuple n)
    (S : Finset (ZMod n)) :
    IsCrossing (shift r P) (translateSupport (-r) S) ↔ IsCrossing P S := by
  constructor
  · intro h
    have hh := (crossingUnshift r ⟨_, h⟩).property
    change IsCrossing P (translateSupport r (translateSupport (-r) S)) at hh
    simpa only [translateSupport_cancel] using hh
  · intro h
    exact (crossingShift r ⟨S, h⟩).property

theorem isCrossing_shift_pair (r : ZMod n) (P : LabelledTuple n) (i j : ZMod n) :
    IsCrossing (shift r P) {i - r, j - r} ↔ IsCrossing P {i, j} := by
  simpa only [translateSupport, Finset.image_insert, Finset.image_singleton, ← sub_eq_add_neg]
    using isCrossing_shift_support r P {i, j}

theorem visitShift_twoStepFirst (r : ZMod n) {P : LabelledTuple n} {f : ZMod n}
    (h : IsCrossing P {f, f + 2})
    (h' : IsCrossing (shift r P) {f - r, (f - r) + 2}) :
    visitShift r (twoStepFirstVisit h) = twoStepFirstVisit h' := by
  apply visit_ext
  · change translateSupport (-r) {f, f + 2} = {f - r, f - r + 2}
    simp only [translateSupport, Finset.image_insert, Finset.image_singleton, ← sub_eq_add_neg]
    congr 1
    ring
  · rfl

theorem visitShift_twoStepLast (r : ZMod n) {P : LabelledTuple n} {f : ZMod n}
    (h : IsCrossing P {f, f + 2})
    (h' : IsCrossing (shift r P) {f - r, (f - r) + 2}) :
    visitShift r (twoStepLastVisit h) = twoStepLastVisit h' := by
  apply visit_ext
  · change translateSupport (-r) {f, f + 2} = {f - r, f - r + 2}
    simp only [translateSupport, Finset.image_insert, Finset.image_singleton, ← sub_eq_add_neg]
    congr 1
    ring
  · change (f + 2) - r = f - r + 2
    ring

namespace WallGerm

variable (g : WallGerm n)

theorem cuspCase_relabel (r j : ZMod n) (b : Bool) :
    CuspCase (g.relabel r).center (j - r) b ↔ CuspCase g.center j b :=
  cuspCase_shift r g.center j b

theorem cuspLoopSide_relabel (r j : ZMod n) (b : Bool) :
    (g.relabel r).cuspLoopSide b (j - r) = g.cuspLoopSide b j := by
  classical
  unfold cuspLoopSide
  change (if IsCrossing (shift r (g.sideTuple true g.sideBase).val)
      {cuspFirst b (j - r), cuspLast b (j - r)} then true else false) = _
  rw [cuspFirst_sub, cuspLast_sub, isCrossing_shift_pair]

end WallGerm
end SM
