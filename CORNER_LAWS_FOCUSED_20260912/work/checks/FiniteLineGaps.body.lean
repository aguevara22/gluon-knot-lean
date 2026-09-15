namespace SM.FiniteLineOrder

noncomputable section

/-- An endpoint below a maximum is at least every other selected value if
no selected value lies strictly between those two endpoints. Injectivity
makes each selected value other than the maximum strictly smaller than it. -/
theorem second_max_bound {ι : Type*} (t : ι → ℝ) (hinj : Function.Injective t)
    (a m : ι) (hmax : ∀ l, t l ≤ t m)
    (hclear : ∀ l, ¬ (t a < t l ∧ t l < t m)) :
    ∀ l, l ≠ m → t l ≤ t a := by
  intro l hl
  apply le_of_not_gt
  intro ha
  exact hclear l ⟨ha, lt_of_le_of_ne (hmax l) (hinj.ne hl)⟩

/-- Abstract increasing-gap assertion. The only restrictions on a leaf
gap are absence of any selected coordinate in its open segment and the
prohibition on two successive leaf gaps. The endpoints are merely ordered;
their coordinates need not be normalized to zero and one. -/
theorem exists_increasing_nonleaf_gap (k : ℕ) (hk : 2 ≤ k)
    (t : Fin (k + 1) → ℝ) (hinj : Function.Injective t) (leaf : Fin k → Prop)
    (hend : t 0 < t (Fin.last k))
    (hclear : ∀ j : Fin k, leaf j → ∀ l : Fin (k + 1),
      ¬ (t j.castSucc < t l ∧ t l < t j.succ) ∧
      ¬ (t j.succ < t l ∧ t l < t j.castSucc))
    (hnext : ∀ j l : Fin k, j.val + 1 = l.val → ¬ (leaf j ∧ leaf l)) :
    ∃ j : Fin k, t j.castSucc < t j.succ ∧ ¬ leaf j := by
  classical
  by_contra hn
  have hleaf : ∀ j : Fin k, t j.castSucc < t j.succ → leaf j := by
    intro j hj
    by_contra hnot
    exact hn ⟨j, hj, hnot⟩
  obtain ⟨m, hmax⟩ := Finite.exists_max t
  have hm0 : 0 < m.val := by
    by_contra h
    have he : m = 0 := by
      apply Fin.ext
      change m.val = 0
      omega
    have h := hmax (Fin.last k)
    rw [he] at h
    exact (not_le_of_gt hend) h
  let j : Fin k := ⟨m.val - 1, by have := m.isLt; omega⟩
  have hjs : j.succ = m := by
    apply Fin.ext
    change m.val - 1 + 1 = m.val
    omega
  have hjm : j.castSucc ≠ m := by
    intro he
    have hv := congrArg Fin.val he
    change m.val - 1 = m.val at hv
    omega
  have hjup : t j.castSucc < t j.succ := by
    rw [hjs]
    exact lt_of_le_of_ne (hmax j.castSucc) (hinj.ne hjm)
  have hjleaf := hleaf j hjup
  have hsecond : ∀ l : Fin (k + 1), l ≠ m → t l ≤ t j.castSucc :=
    second_max_bound t hinj j.castSucc m hmax (by
      intro l
      simpa only [hjs] using (hclear j hjleaf l).1)
  have hm2 : 2 ≤ m.val := by
    by_contra h
    have hm1 : m.val = 1 := by omega
    have hj0 : j.castSucc = (0 : Fin (k + 1)) := by
      apply Fin.ext
      change m.val - 1 = 0
      omega
    have hlast : Fin.last k ≠ m := by
      intro he
      have hv := congrArg Fin.val he
      change k = m.val at hv
      omega
    have h := hsecond (Fin.last k) hlast
    rw [hj0] at h
    exact (not_le_of_gt hend) h
  let i : Fin k := ⟨m.val - 2, by have := m.isLt; omega⟩
  have his : i.succ = j.castSucc := by
    apply Fin.ext
    change m.val - 2 + 1 = m.val - 1
    omega
  have him : i.castSucc ≠ m := by
    intro he
    have hv := congrArg Fin.val he
    change m.val - 2 = m.val at hv
    omega
  have hij : i.castSucc ≠ j.castSucc := by
    intro he
    have hv := congrArg Fin.val he
    change m.val - 2 = m.val - 1 at hv
    omega
  have hiup : t i.castSucc < t i.succ := by
    rw [his]
    exact lt_of_le_of_ne (hsecond i.castSucc him) (hinj.ne hij)
  have hileaf := hleaf i hiup
  have hadj : i.val + 1 = j.val := by
    change m.val - 2 + 1 = m.val - 1
    omega
  exact hnext i j hadj ⟨hileaf, hjleaf⟩

/-- Abstract decreasing-gap assertion for a list closed by its ordered
last-to-first step. The additional hypotheses explicitly state the closing
segment exclusion and the two nonleaf gaps next to that closing step. -/
theorem exists_decreasing_nonleaf_gap (k : ℕ) (hk : 2 ≤ k)
    (t : Fin (k + 1) → ℝ) (hinj : Function.Injective t) (leaf : Fin k → Prop)
    (hend : t 0 < t (Fin.last k))
    (hclear : ∀ j : Fin k, leaf j → ∀ l : Fin (k + 1),
      ¬ (t j.castSucc < t l ∧ t l < t j.succ) ∧
      ¬ (t j.succ < t l ∧ t l < t j.castSucc))
    (hnext : ∀ j l : Fin k, j.val + 1 = l.val → ¬ (leaf j ∧ leaf l))
    (hclose : ∀ l : Fin (k + 1), ¬ (t 0 < t l ∧ t l < t (Fin.last k)))
    (hfirst : ¬ leaf ⟨0, by omega⟩)
    (hlast : ¬ leaf ⟨k - 1, by omega⟩) :
    ∃ j : Fin k, t j.succ < t j.castSucc ∧ ¬ leaf j := by
  classical
  by_contra hn
  have hleaf : ∀ j : Fin k, t j.succ < t j.castSucc → leaf j := by
    intro j hj
    by_contra hnot
    exact hn ⟨j, hj, hnot⟩
  let f : Fin k := ⟨0, by omega⟩
  have hfne : f.castSucc ≠ f.succ := by
    intro he
    have hv := congrArg Fin.val he
    change (0 : ℕ) = 1 at hv
    omega
  have hfup : t f.castSucc < t f.succ := by
    have hnot : ¬ (t f.succ < t f.castSucc) := fun h => hfirst (hleaf f h)
    exact lt_of_le_of_ne (le_of_not_gt hnot) (hinj.ne hfne)
  have hfup0 : t 0 < t f.succ := hfup
  have hfl : f.succ ≠ Fin.last k := by
    intro he
    have hv := congrArg Fin.val he
    change 1 = k at hv
    omega
  have hlastbelow : t (Fin.last k) < t f.succ := by
    have hnot : ¬ (t f.succ < t (Fin.last k)) := fun h => hclose f.succ ⟨hfup0, h⟩
    exact lt_of_le_of_ne (le_of_not_gt hnot) (hinj.ne hfl).symm
  obtain ⟨m, hmax⟩ := Finite.exists_max t
  have hmk : m.val < k := by
    have hmne : m ≠ Fin.last k := by
      intro he
      have h := hmax f.succ
      rw [he] at h
      exact (not_le_of_gt hlastbelow) h
    by_contra h
    apply hmne
    apply Fin.ext
    change m.val = k
    have := m.isLt
    omega
  let j : Fin k := ⟨m.val, hmk⟩
  have hjc : j.castSucc = m := by
    apply Fin.ext
    rfl
  have hjsm : j.succ ≠ m := by
    intro he
    have hv := congrArg Fin.val he
    change m.val + 1 = m.val at hv
    omega
  have hjdown : t j.succ < t j.castSucc := by
    rw [hjc]
    exact lt_of_le_of_ne (hmax j.succ) (hinj.ne hjsm)
  have hjleaf := hleaf j hjdown
  have hsecond : ∀ l : Fin (k + 1), l ≠ m → t l ≤ t j.succ :=
    second_max_bound t hinj j.succ m hmax (by
      intro l
      simpa only [hjc] using (hclear j hjleaf l).2)
  have hmnext : m.val + 1 < k := by
    by_contra h
    have he : j = (⟨k - 1, by omega⟩ : Fin k) := by
      apply Fin.ext
      change m.val = k - 1
      omega
    exact hlast (he ▸ hjleaf)
  let i : Fin k := ⟨m.val + 1, hmnext⟩
  have hic : i.castSucc = j.succ := by
    apply Fin.ext
    rfl
  have hism : i.succ ≠ m := by
    intro he
    have hv := congrArg Fin.val he
    change m.val + 1 + 1 = m.val at hv
    omega
  have hisj : i.succ ≠ j.succ := by
    intro he
    have hv := congrArg Fin.val he
    change m.val + 1 + 1 = m.val + 1 at hv
    omega
  have hidown : t i.succ < t i.castSucc := by
    rw [hic]
    exact lt_of_le_of_ne (hsecond i.succ hism) (hinj.ne hisj)
  have hileaf := hleaf i hidown
  have hadj : j.val + 1 = i.val := rfl
  exact hnext j i hadj ⟨hjleaf, hileaf⟩

end
end SM.FiniteLineOrder
