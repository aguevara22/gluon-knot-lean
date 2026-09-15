namespace SM.SoftDuplication

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The source predecessor is cyclic in the core list, including position zero. -/
def cyclicPred (s : Fin n) : Fin n :=
  ⟨((s.val : ZMod n) - 1).val, ZMod.val_lt _⟩

/-- The source successor is cyclic in the core list, including its last position. -/
def cyclicSucc (s : Fin n) : Fin n :=
  ⟨((s.val : ZMod n) + 1).val, ZMod.val_lt _⟩

theorem cyclicPred_cast (s : Fin n) :
    ((cyclicPred s).val : ZMod n) = (s.val : ZMod n) - 1 :=
  ZMod.natCast_zmod_val _

theorem cyclicSucc_cast (s : Fin n) :
    ((cyclicSucc s).val : ZMod n) = (s.val : ZMod n) + 1 :=
  ZMod.natCast_zmod_val _

theorem cyclicPred_val_of_pos (s : Fin n) (hs : 0 < s.val) :
    (cyclicPred s).val = s.val - 1 := by
  have he : (s.val : ZMod n) - 1 = ((s.val - 1 : ℕ) : ZMod n) := by
    rw [Nat.cast_sub (by omega : 1 ≤ s.val), Nat.cast_one]
  change ((s.val : ZMod n) - 1).val = s.val - 1
  rw [he, ZMod.val_natCast_of_lt (by omega : s.val - 1 < n)]

theorem cyclicSucc_val_of_lt (s : Fin n) (hs : s.val + 1 < n) :
    (cyclicSucc s).val = s.val + 1 := by
  have he : (s.val : ZMod n) + 1 = ((s.val + 1 : ℕ) : ZMod n) := by
    rw [Nat.cast_add, Nat.cast_one]
  change ((s.val : ZMod n) + 1).val = s.val + 1
  rw [he, ZMod.val_natCast_of_lt hs]

theorem cyclicPred_val_zero (s : Fin n) (hs : s.val = 0) :
    (cyclicPred s).val = n - 1 := by
  change ((s.val : ZMod n) - 1).val = n - 1
  rw [hs, Nat.cast_zero, zero_sub]
  have hn := SM.last_index_val_succ (n := n)
  omega

theorem cyclicSucc_val_last (s : Fin n) (hs : s.val = n - 1) :
    (cyclicSucc s).val = 0 := by
  have hn : 0 < n := NeZero.pos n
  have he : (s.val : ZMod n) + 1 = (n : ZMod n) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
    congr 1
    omega
  change ((s.val : ZMod n) + 1).val = 0
  rw [he, ZMod.natCast_self, ZMod.val_zero]

/-- Neither cyclic neighbor is the distinguished occurrence on the source domain. -/
theorem cyclic_neighbors_ne (hn : 3 ≤ n) (s : Fin n) :
    cyclicPred s ≠ s ∧ cyclicSucc s ≠ s := by
  constructor
  · intro he
    have hv := congrArg Fin.val he
    by_cases hs : s.val = 0
    · rw [cyclicPred_val_zero s hs] at hv
      omega
    · rw [cyclicPred_val_of_pos s (by omega)] at hv
      omega
  · intro he
    have hv := congrArg Fin.val he
    by_cases hs : s.val + 1 < n
    · rw [cyclicSucc_val_of_lt s hs] at hv
      omega
    · have hlast : s.val = n - 1 := by omega
      rw [cyclicSucc_val_last s hlast] at hv
      omega

/-- A unit collapsed interval starting at A ends at the actual cyclic successor.
The strict endpoint hypotheses themselves exclude successor wrap here. -/
theorem start_unit_endpoint (s : Fin n) (I : BoundaryInterval (n + 1))
    (hl : I.left = A s) (hr : B s < I.right)
    (hu : (collapseInterval s I (not_duplicate_of_right_gt s I hr)).leaves = 1) :
    collapse s I.right = cyclicSucc s := by
  have hlt : s.val < (collapse s I.right).val := (start_collapsed_bounds s I hl hr).2
  change (collapse s I.right).val - (collapse s I.left).val = 1 at hu
  rw [hl, collapse_A] at hu
  have hv : (collapse s I.right).val = s.val + 1 := by omega
  have hb : s.val + 1 < n := by have := (collapse s I.right).isLt; omega
  apply Fin.ext
  rw [hv, cyclicSucc_val_of_lt s hb]

/-- The analogous unit collapsed interval ending at B begins at the actual
cyclic predecessor, whose no-wrap condition follows from strictness. -/
theorem end_unit_endpoint (s : Fin n) (I : BoundaryInterval (n + 1))
    (hl : I.left < A s) (hr : I.right = B s)
    (hu : (collapseInterval s I (not_duplicate_of_left_lt s I hl)).leaves = 1) :
    collapse s I.left = cyclicPred s := by
  have hlt : (collapse s I.left).val < s.val := (end_collapsed_bounds s I hl hr).1
  change (collapse s I.right).val - (collapse s I.left).val = 1 at hu
  rw [hr, collapse_B] at hu
  have hs : 0 < s.val := by omega
  have hv : (collapse s I.left).val = s.val - 1 := by omega
  apply Fin.ext
  rw [hv, cyclicPred_val_of_pos s hs]

/-- The starting table factor vanishes when the collapsed core interval is
one leaf. No value or nonvanishing assumption on b0 is required. -/
theorem ordinaryLift_start_unit_zero (s : Fin n) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (I : BoundaryInterval (n + 1))
    (hl : I.left = A s) (hr : B s < I.right)
    (hu : (collapseInterval s I (not_duplicate_of_right_gt s I hr)).leaves = 1) :
    ordinaryLift s (t (cyclicPred s)) (t (cyclicSucc s)) t b0 I = 0 := by
  rw [ordinaryLift_start s _ _ t b0 I hl hr, start_unit_endpoint s I hl hr hu]
  simp

theorem ordinaryLift_end_unit_zero (s : Fin n) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (I : BoundaryInterval (n + 1))
    (hl : I.left < A s) (hr : I.right = B s)
    (hu : (collapseInterval s I (not_duplicate_of_left_lt s I hl)).leaves = 1) :
    ordinaryLift s (t (cyclicPred s)) (t (cyclicSucc s)) t b0 I = 0 := by
  rw [ordinaryLift_end s _ _ t b0 I hl hr, end_unit_endpoint s I hl hr hu]
  simp

theorem fullInterval_not_duplicate (hn : 3 ≤ n) (s : Fin n) :
    fullBoundaryInterval (by omega : 3 ≤ n + 1) ≠ duplicateInterval s := by
  intro he
  have hl := congrArg (fun J : BoundaryInterval (n + 1) => J.left.val) he
  have hr := congrArg (fun J : BoundaryInterval (n + 1) => J.right.val) he
  simp only [fullBoundaryInterval, duplicateInterval, A_val, B_val] at hl hr
  omega

/-- The entire child word collapses to the entire core word for every placement. -/
theorem collapse_fullInterval (hn : 3 ≤ n) (s : Fin n) :
    collapseInterval s (fullBoundaryInterval (by omega : 3 ≤ n + 1))
      (fullInterval_not_duplicate hn s) = fullBoundaryInterval hn := by
  apply BoundaryInterval.eq_of_endpoints
  · apply Fin.ext
    change (collapse s (⟨0, by omega⟩ : Fin (n + 1))).val = 0
    rw [collapse_val, if_pos (Nat.zero_le _)]
  · apply Fin.ext
    change (collapse s (⟨n + 1 - 1, by omega⟩ : Fin (n + 1))).val = n - 1
    rw [collapse_val]
    change (if n + 1 - 1 ≤ s.val then n + 1 - 1 else (n + 1 - 1) - 1) = n - 1
    rw [if_neg (by have := s.isLt; omega)]
    omega

end
end SM.SoftDuplication

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

theorem boundaryIndex_cyclicPred (g : ZMod n) (s : Fin n) :
    boundaryIndex g (SoftDuplication.cyclicPred s) = boundaryIndex g s - 1 := by
  unfold boundaryIndex
  rw [SoftDuplication.cyclicPred_cast]
  abel

theorem boundaryIndex_cyclicSucc (g : ZMod n) (s : Fin n) :
    boundaryIndex g (SoftDuplication.cyclicSucc s) = boundaryIndex g s + 1 := by
  unfold boundaryIndex
  rw [SoftDuplication.cyclicSucc_cast]
  abel

/-- Literal cyclic core positions coincide with the actual predecessor and
successor labels under every nonsoft-root boundary reading. -/
theorem softRootPosition_cyclic_neighbors (j g : ZMod n) :
    SoftDuplication.cyclicPred (softRootPosition j g) = softRootPosition (j - 1) g ∧
    SoftDuplication.cyclicSucc (softRootPosition j g) = softRootPosition (j + 1) g := by
  constructor
  · apply boundaryIndex_injective g
    rw [boundaryIndex_cyclicPred, softRootPosition_index, softRootPosition_index]
  · apply boundaryIndex_injective g
    rw [boundaryIndex_cyclicSucc, softRootPosition_index, softRootPosition_index]

/-- The formal cyclic eta values are exactly the physical attachment signs. -/
theorem softRootFarData_cyclic_attachments (P : LabelledTuple n) (j g : ZMod n)
    (q : Plane) :
    softRootFarData P j g q (SoftDuplication.cyclicPred (softRootPosition j g)) =
      ((softAttachmentMinus P j q : ℤ) : ℚ) ∧
    softRootFarData P j g q (SoftDuplication.cyclicSucc (softRootPosition j g)) =
      ((softAttachmentPlus P j q : ℤ) : ℚ) := by
  rw [(softRootPosition_cyclic_neighbors j g).1, (softRootPosition_cyclic_neighbors j g).2]
  exact softRootFarData_neighbors P j g q

theorem softRootPosition_root_injective (j : ZMod n) :
    Function.Injective (fun g : ZMod n => softRootPosition j g) := by
  intro g h he
  change softRootPosition j g = softRootPosition j h at he
  have hg := softRootPosition_index j g
  rw [he] at hg
  have hh := softRootPosition_index j h
  have hx := hg.trans hh.symm
  unfold boundaryIndex at hx
  exact add_right_cancel (add_right_cancel hx)

theorem softRootPosition_first_iff (j g : ZMod n) :
    (softRootPosition j g).val = 0 ↔ g = j - 1 := by
  constructor
  · intro hv
    apply softRootPosition_root_injective j
    apply Fin.ext
    exact hv.trans (softRootPosition_incoming j).symm
  · rintro rfl
    exact softRootPosition_incoming j

theorem softRootPosition_last_iff (j g : ZMod n) :
    (softRootPosition j g).val = n - 1 ↔ g = j := by
  constructor
  · intro hv
    apply softRootPosition_root_injective j
    apply Fin.ext
    exact hv.trans (softRootPosition_return j).symm
  · intro hg
    subst g
    exact softRootPosition_return j

theorem softRootPosition_strict_iff (hn : 3 ≤ n) (j g : ZMod n) :
    (0 < (softRootPosition j g).val ∧ (softRootPosition j g).val < n - 1) ↔
      (g ≠ j - 1 ∧ g ≠ j) := by
  have hfirst := softRootPosition_first_iff j g
  have hlast := softRootPosition_last_iff j g
  have hb := (softRootPosition j g).isLt
  constructor
  · rintro ⟨hl, hr⟩
    constructor
    · intro he; have := hfirst.mpr he; omega
    · intro he; have := hlast.mpr he; omega
  · rintro ⟨hl, hr⟩
    have hz : (softRootPosition j g).val ≠ 0 := fun he => hl (hfirst.mp he)
    have hm : (softRootPosition j g).val ≠ n - 1 := fun he => hr (hlast.mp he)
    omega

/-- The actual full child interval has precisely the incoming-first,
return-last, or strictly spanning placement for its corresponding core root. -/
theorem softRoot_fullInterval_cases (hn : 3 ≤ n) (j g : ZMod n) :
    let I := fullBoundaryInterval (by omega : 3 ≤ n + 1)
    let s := softRootPosition j g
    (g = j - 1 ∧ I.left = SoftDuplication.A s ∧ SoftDuplication.B s < I.right) ∨
    (g = j ∧ I.left < SoftDuplication.A s ∧ I.right = SoftDuplication.B s) ∨
    (g ≠ j - 1 ∧ g ≠ j ∧ I.left < SoftDuplication.A s ∧
      SoftDuplication.B s < I.right) := by
  dsimp only
  by_cases hi : g = j - 1
  · left
    have hs := (softRootPosition_first_iff j g).mpr hi
    refine ⟨hi, ?_, ?_⟩
    · apply Fin.ext
      change 0 = (softRootPosition j g).val
      exact hs.symm
    · change (softRootPosition j g).val + 1 < n + 1 - 1
      omega
  · by_cases hr : g = j
    · right; left
      have hs := (softRootPosition_last_iff j g).mpr hr
      refine ⟨hr, ?_, ?_⟩
      · change 0 < (softRootPosition j g).val
        omega
      · apply Fin.ext
        change n + 1 - 1 = (softRootPosition j g).val + 1
        omega
    · right; right
      obtain ⟨hs0, hsm⟩ := (softRootPosition_strict_iff hn j g).mpr ⟨hi, hr⟩
      refine ⟨hi, hr, ?_, ?_⟩
      · change 0 < (softRootPosition j g).val
        exact hs0
      · change (softRootPosition j g).val + 1 < n + 1 - 1
        omega

end
end SM
