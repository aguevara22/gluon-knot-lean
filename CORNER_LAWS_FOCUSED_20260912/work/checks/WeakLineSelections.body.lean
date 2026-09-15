namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

theorem boundaryIndex_first_of_val (g : ZMod n) (a : Fin n) (ha : a.val = 0) :
    boundaryIndex g a = g + 1 := by simp [boundaryIndex, ha]

theorem boundaryIndex_last_of_val (g : ZMod n) (a : Fin n) (ha : a.val = n - 1) :
    boundaryIndex g a = g := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) a.isLt
  have he : ((n - 1 : ℕ) : ZMod n) + 1 = 0 := by
    calc
      ((n - 1 : ℕ) : ZMod n) + 1 = (((n - 1) + 1 : ℕ) : ZMod n) := by simp
      _ = (n : ZMod n) := congrArg (fun t : ℕ => (t : ZMod n)) (Nat.sub_add_cancel hn)
      _ = 0 := ZMod.natCast_self n
  simp only [boundaryIndex, ha, add_assoc, he, add_zero]

/-- Consecutive physical labels, including the wraparound root labels, cannot
all be on one line in a weak polygon. The successor equations are explicit. -/
theorem weak_not_successive_labels_on_line {P : LabelledTuple n} (hP : WeakGeneric P)
    (a b c : ZMod n) (hab : b = a + 1) (hbc : c = b + 1)
    (p ω : Plane) (x y z : ℝ) (hx : P a = p + x • ω)
    (hy : P b = p + y • ω) (hz : P c = p + z • ω) : False := by
  have ha : b - 1 = a := by rw [hab]; ring
  apply weak_not_three_consecutive_on_line hP b p ω x y z
  · rw [ha]
    exact hx
  · exact hy
  · rw [← hbc]
    exact hz

theorem weak_line_coordinate_injective {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) {k : ℕ} (r : Fin (k + 1) → Fin n) (hr : StrictMono r)
    (p ω : Plane) (t : Fin (k + 1) → ℝ)
    (hline : ∀ l, boundaryWord P g (r l) = p + t l • ω) : Function.Injective t := by
  intro a b he
  apply hr.injective
  apply weak_boundaryWord_injective hP g
  rw [hline a, hline b, he]

/-- Every one-leaf selected gap is an actual edge and contains no other
selected line coordinate. Endpoint indices are included in the quantifier. -/
theorem weak_line_selection_clear {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) {k : ℕ} (r : Fin (k + 1) → Fin n) (hr : StrictMono r)
    (p ω : Plane) (t : Fin (k + 1) → ℝ)
    (hline : ∀ l, boundaryWord P g (r l) = p + t l • ω)
    (j : Fin k) (hj : (r j.succ).val = (r j.castSucc).val + 1) (l : Fin (k + 1)) :
    ¬ (t j.castSucc < t l ∧ t l < t j.succ) ∧
      ¬ (t j.succ < t l ∧ t l < t j.castSucc) := by
  by_cases h0 : l = j.castSucc
  · subst l
    exact ⟨fun h => (lt_irrefl _ h.1), fun h => (lt_irrefl _ h.2)⟩
  by_cases h1 : l = j.succ
  · subst l
    exact ⟨fun h => (lt_irrefl _ h.2), fun h => (lt_irrefl _ h.1)⟩
  have h := weak_boundary_leaf_no_between hP g (r j.castSucc) (r j.succ) (r l) hj
    (fun he => h0 (hr.injective he)) (fun he => h1 (hr.injective he))
    p ω (t j.castSucc) (t j.succ) (t l) (hline _) (hline _) (hline _)
  exact ⟨fun h0 => h (Or.inl h0), fun h1 => h (Or.inr h1)⟩

/-- Two successive selected gaps cannot both be original edges on the line. -/
theorem weak_line_selection_no_successive_leaves {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) {k : ℕ} (r : Fin (k + 1) → Fin n)
    (p ω : Plane) (t : Fin (k + 1) → ℝ)
    (hline : ∀ l, boundaryWord P g (r l) = p + t l • ω)
    (j l : Fin k) (hjl : j.val + 1 = l.val) :
    ¬ ((r j.succ).val = (r j.castSucc).val + 1 ∧
      (r l.succ).val = (r l.castSucc).val + 1) := by
  rintro ⟨hj, hl⟩
  have hm : j.succ = l.castSucc := Fin.ext hjl
  have hnext := boundaryIndex_successive g (r l.castSucc) (r l.succ) hl
  rw [← hm] at hnext
  exact weak_not_successive_labels_on_line hP _ _ _
    (boundaryIndex_successive g _ _ hj) hnext
    p ω (t j.castSucc) (t j.succ) (t l.succ) (hline _) (hline _) (hline _)

/-- With both full-word endpoints selected, the physical root edge cannot
contain any other selected coordinate. This has no arbitrary-interval analogue. -/
theorem weak_line_selection_root_clear {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) {k : ℕ} (r : Fin (k + 1) → Fin n) (hr : StrictMono r)
    (p ω : Plane) (t : Fin (k + 1) → ℝ)
    (hline : ∀ l, boundaryWord P g (r l) = p + t l • ω)
    (hfirst : (r 0).val = 0) (hlast : (r (Fin.last k)).val = n - 1)
    (l : Fin (k + 1)) : ¬ (t 0 < t l ∧ t l < t (Fin.last k)) := by
  by_cases h0 : l = 0
  · subst l
    exact fun h => lt_irrefl _ h.1
  by_cases h1 : l = Fin.last k
  · subst l
    exact fun h => lt_irrefl _ h.2
  have hf := boundaryIndex_first_of_val g (r 0) hfirst
  have hh := boundaryIndex_last_of_val g (r (Fin.last k)) hlast
  have h := weak_line_edge_no_between hP g (boundaryIndex g (r l))
    (fun he => h1 (hr.injective (boundaryIndex_injective g (he.trans hh.symm))))
    (fun he => h0 (hr.injective (boundaryIndex_injective g (he.trans hf.symm))))
    p ω (t (Fin.last k)) (t 0) (t l)
    (by simpa only [boundaryWord, hh] using hline (Fin.last k))
    (by simpa only [boundaryWord, hf] using hline 0) (hline l)
  exact fun ht => h (Or.inr ht)

theorem weak_line_selection_first_not_leaf {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) {k : ℕ} (hk : 0 < k) (r : Fin (k + 1) → Fin n)
    (p ω : Plane) (t : Fin (k + 1) → ℝ)
    (hline : ∀ l, boundaryWord P g (r l) = p + t l • ω)
    (hfirst : (r 0).val = 0) (hlast : (r (Fin.last k)).val = n - 1) :
    ¬ ((r (⟨0, hk⟩ : Fin k).succ).val = (r (⟨0, hk⟩ : Fin k).castSucc).val + 1) := by
  intro hleaf
  let j : Fin k := ⟨0, hk⟩
  have hj0 : j.castSucc = 0 := Fin.ext rfl
  have hf := boundaryIndex_first_of_val g (r 0) hfirst
  have hh := boundaryIndex_last_of_val g (r (Fin.last k)) hlast
  have hclose : boundaryIndex g (r j.castSucc) = boundaryIndex g (r (Fin.last k)) + 1 := by
    rw [hj0, hf, hh]
  exact weak_not_successive_labels_on_line hP _ _ _ hclose
    (boundaryIndex_successive g _ _ hleaf) p ω (t (Fin.last k)) (t j.castSucc) (t j.succ)
    (hline _) (hline _) (hline _)

theorem weak_line_selection_last_not_leaf {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) {k : ℕ} (hk : 0 < k) (r : Fin (k + 1) → Fin n)
    (p ω : Plane) (t : Fin (k + 1) → ℝ)
    (hline : ∀ l, boundaryWord P g (r l) = p + t l • ω)
    (hfirst : (r 0).val = 0) (hlast : (r (Fin.last k)).val = n - 1) :
    ¬ ((r (⟨k - 1, by omega⟩ : Fin k).succ).val =
      (r (⟨k - 1, by omega⟩ : Fin k).castSucc).val + 1) := by
  intro hleaf
  let j : Fin k := ⟨k - 1, by omega⟩
  have hjlast : j.succ = Fin.last k := by apply Fin.ext; change k - 1 + 1 = k; omega
  have hf := boundaryIndex_first_of_val g (r 0) hfirst
  have hh := boundaryIndex_last_of_val g (r (Fin.last k)) hlast
  have hclose : boundaryIndex g (r 0) = boundaryIndex g (r j.succ) + 1 := by
    rw [hjlast, hf, hh]
  exact weak_not_successive_labels_on_line hP _ _ _
    (boundaryIndex_successive g _ _ hleaf) hclose p ω (t j.castSucc) (t j.succ) (t 0)
    (hline _) (hline _) (hline _)

end
end SM
