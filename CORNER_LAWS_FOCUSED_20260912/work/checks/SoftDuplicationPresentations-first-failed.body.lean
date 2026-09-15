namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- All subsets of the two distinct physical occurrences, including empty. -/
theorem cutSubsetPair_cases (s : Fin n) (Q : Finset (Fin (n + 1)))
    (hQ : Q ⊆ {A s, B s}) :
    Q = ∅ ∨ Q = {A s} ∨ Q = {B s} ∨ Q = {A s, B s} := by
  have hm : ∀ p ∈ Q, p = A s ∨ p = B s := by
    intro p hp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hQ hp
  by_cases ha : A s ∈ Q
  · by_cases hb : B s ∈ Q
    · right; right; right
      apply Finset.Subset.antisymm hQ
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact ha
      · exact hb
    · right; left
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨ha, ?_⟩
      intro p hp
      rcases hm p hp with h | h
      · exact h
      · exact False.elim (hb (h ▸ hp))
  · by_cases hb : B s ∈ Q
    · right; right; left
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hb, ?_⟩
      intro p hp
      rcases hm p hp with h | h
      · exact False.elim (ha (h ▸ hp))
      · exact h
    · left
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      rcases hm p hp with h | h
      · exact ha (h ▸ hp)
      · exact hb (h ▸ hp)

theorem cutFiberCondition_empty (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI)) :
    CutFiberCondition s I hI C ∅ ↔ s ∉ C.cuts := by
  constructor
  · intro h hs
    exact Finset.not_nonempty_empty (h.2.1.mpr hs)
  · intro hs
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p hp
      exact False.elim (Finset.notMem_empty p hp)
    · simp only [Finset.not_nonempty_empty, hs, iff_false, not_false_eq_true]
    · intro hl
      have hm := C.left_mem
      change collapse s I.left ∈ C.cuts at hm
      exact False.elim (hs (hl ▸ hm))
    · intro hr
      have hm := C.right_mem
      change collapse s I.right ∈ C.cuts at hm
      exact False.elim (hs (hr ▸ hm))

/-- Strictly spanning endpoints impose no local endpoint selection. -/
theorem cutFiberCondition_spanning (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (Q : Finset (Fin (n + 1))) :
    CutFiberCondition s I hI C Q ↔ Q ⊆ {A s, B s} ∧ (Q.Nonempty ↔ s ∈ C.cuts) := by
  constructor
  · intro h
    exact ⟨cutFiber_subset_pair s I hI C ⟨Q, h⟩, h.2.1⟩
  · rintro ⟨hq, hn⟩
    refine ⟨?_, hn, ?_, ?_⟩
    · intro p hp
      have hm := hq hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl
      · exact ⟨collapse_A s, hL.le, (lt_trans (A_lt_B s) hR).le⟩
      · exact ⟨collapse_B s, (lt_trans hL (A_lt_B s)).le, hR.le⟩
    · intro he
      rcases (collapse_eq_s_iff s I.left).mp he with he | he
      · exact False.elim ((ne_of_lt hL) he)
      · exact False.elim ((ne_of_lt (lt_trans hL (A_lt_B s))) he)
    · intro he
      rcases (collapse_eq_s_iff s I.right).mp he with he | he
      · exact False.elim ((ne_of_gt (lt_trans (A_lt_B s) hR)) he)
      · exact False.elim ((ne_of_gt hR) he)

/-- A spanning core cut at s has exactly the three nonempty subsets. -/
theorem cutFiberCondition_spanning_cut (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (Q : Finset (Fin (n + 1))) :
    CutFiberCondition s I hI C Q ↔ Q = {A s} ∨ Q = {B s} ∨ Q = {A s, B s} := by
  rw [cutFiberCondition_spanning s I hI C hL hR Q]
  constructor
  · rintro ⟨hq, hn⟩
    rcases cutSubsetPair_cases s Q hq with he | he | he | he
    · exact False.elim ((hn.mpr hs).ne_empty he)
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr he)
  · rintro (rfl | rfl | rfl) <;> simp [hs]

/-- At a left endpoint A, A is mandatory and only the cut at B is optional. -/
theorem cutFiberCondition_start (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (Q : Finset (Fin (n + 1))) :
    CutFiberCondition s I hI C Q ↔ Q = {A s} ∨ Q = {A s, B s} := by
  have hl : collapse s I.left = s := by rw [hL, collapse_A]
  have hs : s ∈ C.cuts := by
    have hm := C.left_mem
    change collapse s I.left ∈ C.cuts at hm
    exact hl ▸ hm
  constructor
  · intro h
    have ha : A s ∈ Q := hL ▸ h.2.2.1 hl
    rcases cutSubsetPair_cases s Q (cutFiber_subset_pair s I hI C ⟨Q, h⟩) with he | he | he | he
    · exact False.elim (by simpa only [he, Finset.notMem_empty] using ha)
    · exact Or.inl he
    · have heq : A s = B s := by simpa only [he, Finset.mem_singleton] using ha
      exact False.elim ((ne_of_lt (A_lt_B s)) heq)
    · exact Or.inr he
  · have build : ∀ Q : Finset (Fin (n + 1)), Q ⊆ {A s, B s} → A s ∈ Q →
        CutFiberCondition s I hI C Q := by
      intro Q hq ha
      refine ⟨?_, ⟨fun _ => hs, fun _ => ⟨A s, ha⟩⟩, ?_, ?_⟩
      · intro p hp
        have hm := hq hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl
        · exact ⟨collapse_A s, hL.le, (lt_trans (A_lt_B s) hR).le⟩
        · exact ⟨collapse_B s, by rw [hL]; exact (A_lt_B s).le, hR.le⟩
      · intro _
        exact hL.symm ▸ ha
      · intro he
        rcases (collapse_eq_s_iff s I.right).mp he with he | he
        · exact False.elim ((ne_of_gt (lt_trans (A_lt_B s) hR)) he)
        · exact False.elim ((ne_of_gt hR) he)
    rintro (rfl | rfl)
    · exact build _ (by simp) (by simp)
    · exact build _ (by simp) (by simp)

/-- At a right endpoint B, B is mandatory and only the cut at A is optional. -/
theorem cutFiberCondition_end (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) (Q : Finset (Fin (n + 1))) :
    CutFiberCondition s I hI C Q ↔ Q = {B s} ∨ Q = {A s, B s} := by
  have hr : collapse s I.right = s := by rw [hR, collapse_B]
  have hs : s ∈ C.cuts := by
    have hm := C.right_mem
    change collapse s I.right ∈ C.cuts at hm
    exact hr ▸ hm
  constructor
  · intro h
    have hb : B s ∈ Q := hR ▸ h.2.2.2 hr
    rcases cutSubsetPair_cases s Q (cutFiber_subset_pair s I hI C ⟨Q, h⟩) with he | he | he | he
    · exact False.elim (by simpa only [he, Finset.notMem_empty] using hb)
    · have heq : B s = A s := by simpa only [he, Finset.mem_singleton] using hb
      exact False.elim ((ne_of_gt (A_lt_B s)) heq)
    · exact Or.inl he
    · exact Or.inr he
  · have build : ∀ Q : Finset (Fin (n + 1)), Q ⊆ {A s, B s} → B s ∈ Q →
        CutFiberCondition s I hI C Q := by
      intro Q hq hb
      refine ⟨?_, ⟨fun _ => hs, fun _ => ⟨B s, hb⟩⟩, ?_, ?_⟩
      · intro p hp
        have hm := hq hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl
        · exact ⟨collapse_A s, hL.le, by rw [hR]; exact (A_lt_B s).le⟩
        · exact ⟨collapse_B s, (lt_trans hL (A_lt_B s)).le, hR.ge⟩
      · intro he
        rcases (collapse_eq_s_iff s I.left).mp he with he | he
        · exact False.elim ((ne_of_lt hL) he)
        · exact False.elim ((ne_of_lt (lt_trans hL (A_lt_B s))) he)
      · intro _
        exact hR.symm ▸ hb
    rintro (rfl | rfl)
    · exact build _ (by simp) (by simp)
    · exact build _ (by simp) (by simp)

def emptyCutFiber (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) : CutFiber s I hI C :=
  ⟨∅, (cutFiberCondition_empty s I hI C).mpr hs⟩

def emptyCutFiberEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) : PUnit ≃ CutFiber s I hI C :=
  Equiv.ofBijective (fun _ => emptyCutFiber s I hI C hs) ⟨by
    intro x y _
    exact Subsingleton.elim x y, by
    intro Q
    exact ⟨PUnit.unit, Subtype.ext ((cutFiber_empty_iff s I hI C Q).mpr hs).symm⟩⟩

/-- Row zero selects A only, row one B only, and row two both. -/
def spanningRows (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    Fin 3 → CutFiber s I hI C :=
  ![⟨{A s}, (cutFiberCondition_spanning_cut s I hI C hL hR hs _).mpr (Or.inl rfl)⟩,
    ⟨{B s}, (cutFiberCondition_spanning_cut s I hI C hL hR hs _).mpr (Or.inr (Or.inl rfl))⟩,
    ⟨{A s, B s}, (cutFiberCondition_spanning_cut s I hI C hL hR hs _).mpr
      (Or.inr (Or.inr rfl))⟩]

def spanningRowsEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    Fin 3 ≃ CutFiber s I hI C :=
  Equiv.ofBijective (spanningRows s I hI C hL hR hs) ⟨by
    intro i j he
    have ha := congrArg (fun Q : CutFiber s I hI C => A s ∈ Q.val) he
    have hb := congrArg (fun Q : CutFiber s I hI C => B s ∈ Q.val) he
    have hab := ne_of_lt (A_lt_B s)
    have hba := ne_of_gt (A_lt_B s)
    fin_cases i <;> fin_cases j <;> simp_all [spanningRows], by
    intro Q
    rcases (cutFiberCondition_spanning_cut s I hI C hL hR hs Q.val).mp Q.property with h | h | h
    · exact ⟨0, Subtype.ext h.symm⟩
    · exact ⟨1, Subtype.ext h.symm⟩
    · exact ⟨2, Subtype.ext h.symm⟩⟩

/-- At A the two rows differ exactly by the optional cut at B. -/
def startingRows (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) : Fin 2 → CutFiber s I hI C :=
  ![⟨{A s}, (cutFiberCondition_start s I hI C hL hR _).mpr (Or.inl rfl)⟩,
    ⟨{A s, B s}, (cutFiberCondition_start s I hI C hL hR _).mpr (Or.inr rfl)⟩]

def startingRowsEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) : Fin 2 ≃ CutFiber s I hI C :=
  Equiv.ofBijective (startingRows s I hI C hL hR) ⟨by
    intro i j he
    have hb := congrArg (fun Q : CutFiber s I hI C => B s ∈ Q.val) he
    have hba := ne_of_gt (A_lt_B s)
    fin_cases i <;> fin_cases j <;> simp_all [startingRows], by
    intro Q
    rcases (cutFiberCondition_start s I hI C hL hR Q.val).mp Q.property with h | h
    · exact ⟨0, Subtype.ext h.symm⟩
    · exact ⟨1, Subtype.ext h.symm⟩⟩

/-- At B the two rows differ exactly by the optional cut at A. -/
def endingRows (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) : Fin 2 → CutFiber s I hI C :=
  ![⟨{B s}, (cutFiberCondition_end s I hI C hL hR _).mpr (Or.inl rfl)⟩,
    ⟨{A s, B s}, (cutFiberCondition_end s I hI C hL hR _).mpr (Or.inr rfl)⟩]

def endingRowsEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) : Fin 2 ≃ CutFiber s I hI C :=
  Equiv.ofBijective (endingRows s I hI C hL hR) ⟨by
    intro i j he
    have ha := congrArg (fun Q : CutFiber s I hI C => A s ∈ Q.val) he
    have hab := ne_of_lt (A_lt_B s)
    fin_cases i <;> fin_cases j <;> simp_all [endingRows], by
    intro Q
    rcases (cutFiberCondition_end s I hI C hL hR Q.val).mp Q.property with h | h
    · exact ⟨0, Subtype.ext h.symm⟩
    · exact ⟨1, Subtype.ext h.symm⟩⟩

theorem sum_emptyCutFiber {R : Type*} [AddCommMonoid R]
    (s : Fin n) (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (C : BoundaryCutSet (collapseInterval s I hI)) (hs : s ∉ C.cuts)
    (f : CutFiber s I hI C → R) :
    (∑ Q, f Q) = f (emptyCutFiber s I hI C hs) := by
  have he := (Fintype.sum_equiv (emptyCutFiberEquiv s I hI C hs)
    (fun _ => f (emptyCutFiber s I hI C hs)) f (fun _ => rfl)).symm
  simpa using he

theorem sum_spanningRows {R : Type*} [AddCommMonoid R]
    (s : Fin n) (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (f : CutFiber s I hI C → R) :
    (∑ Q, f Q) = f (spanningRows s I hI C hL hR hs 0) +
      f (spanningRows s I hI C hL hR hs 1) + f (spanningRows s I hI C hL hR hs 2) := by
  exact (Fintype.sum_equiv (spanningRowsEquiv s I hI C hL hR hs)
    (fun i => f (spanningRows s I hI C hL hR hs i)) f (fun _ => rfl)).symm.trans
      (Fin.sum_univ_three _)

theorem sum_startingRows {R : Type*} [AddCommMonoid R]
    (s : Fin n) (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (f : CutFiber s I hI C → R) :
    (∑ Q, f Q) = f (startingRows s I hI C hL hR 0) + f (startingRows s I hI C hL hR 1) := by
  exact (Fintype.sum_equiv (startingRowsEquiv s I hI C hL hR)
    (fun i => f (startingRows s I hI C hL hR i)) f (fun _ => rfl)).symm.trans
      (Fin.sum_univ_two _)

theorem sum_endingRows {R : Type*} [AddCommMonoid R]
    (s : Fin n) (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) (f : CutFiber s I hI C → R) :
    (∑ Q, f Q) = f (endingRows s I hI C hL hR 0) + f (endingRows s I hI C hL hR 1) := by
  exact (Fintype.sum_equiv (endingRowsEquiv s I hI C hL hR)
    (fun i => f (endingRows s I hI C hL hR i)) f (fun _ => rfl)).symm.trans
      (Fin.sum_univ_two _)

end
end SM.SoftDuplication
