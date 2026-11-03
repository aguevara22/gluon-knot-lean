import DirectGLSSW.DaughterFirstReturn
import DirectGLSSW.PolygonNonalternation

set_option autoImplicit false

namespace DirectGLSSW.FiniteCycleOrder

variable {m : ℕ}

/-- The outgoing half-open interval `[a,b)` used by a singleton dart smoothing. -/
def outgoingIntervalSide (a b : Fin m) : Set (Fin m) :=
  {i | a.val ≤ i.val ∧ i.val < b.val}

/-- The singleton outgoing cut: swap the two labels after taking one successor. -/
noncomputable def outgoingSplitPerm (a b : Fin m) : Equiv.Perm (Fin m) :=
  Equiv.swap a b * DirectGLSSW.cyclicSuccessorPerm m

theorem outgoingIntervalSide_invariant
    (a b : Fin m) (hab : a < b) (i : Fin m) :
    i ∈ outgoingIntervalSide a b ↔
      outgoingSplitPerm a b i ∈ outgoingIntervalSide a b := by
  change (a.val ≤ i.val ∧ i.val < b.val) ↔
    (a.val ≤ (outgoingSplitPerm a b i).val ∧ (outgoingSplitPerm a b i).val < b.val)
  have hab' : a.val < b.val := hab
  have hb := b.isLt
  have hi := i.isLt
  have hside (j : Fin m) :
      j ∈ outgoingIntervalSide a b ↔ Equiv.swap a b j ∈ intervalSide a b := by
    change (a.val ≤ j.val ∧ j.val < b.val) ↔
      (a.val < (Equiv.swap a b j).val ∧ (Equiv.swap a b j).val ≤ b.val)
    by_cases hja : j = a
    · subst j
      simp [Equiv.swap_apply_def]
    by_cases hjb : j = b
    · subst j
      simp [Equiv.swap_apply_def]
    · simp [Equiv.swap_apply_def, hja, hjb]
      omega
  have hstep : Equiv.swap a b (outgoingSplitPerm a b i) =
      splitPerm a b (Equiv.swap a b i) := by
    simp [outgoingSplitPerm, splitPerm, Equiv.Perm.mul_apply]
  calc
    i ∈ outgoingIntervalSide a b ↔ Equiv.swap a b i ∈ intervalSide a b := hside i
    _ ↔ splitPerm a b (Equiv.swap a b i) ∈ intervalSide a b :=
      intervalSide_invariant a b hab (Equiv.swap a b i)
    _ ↔ Equiv.swap a b (outgoingSplitPerm a b i) ∈ intervalSide a b := by
      rw [hstep]
    _ ↔ outgoingSplitPerm a b i ∈ outgoingIntervalSide a b :=
      (hside (outgoingSplitPerm a b i)).symm

end DirectGLSSW.FiniteCycleOrder
