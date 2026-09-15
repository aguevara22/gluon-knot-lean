import SM.Farout
import SM.EuclideanPlane
import SM.WeakGeometry
import Mathlib.Tactic

namespace SM

noncomputable section
variable {n : ℕ}

/-- Weak genericity already separates every pair of actual vertices, even
when selected triples are collinear. No G1 assumption is used. -/
theorem weak_vertices_injective {P : LabelledTuple n} (hP : WeakGeneric P) :
    Function.Injective P := by
  intro i j he
  by_contra hij
  by_cases hn : i = j + 1
  · apply hP.1 j
    unfold edge
    rw [← hn, he, sub_self]
  · apply hP.2.2.1 i j ((nonincident_iff i j).mpr ⟨hij, hn⟩)
    rw [he]
    exact ⟨0, le_rfl, by norm_num, (edgePoint_zero P j).symm⟩

theorem weak_boundaryWord_injective [NeZero n] {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) : Function.Injective (boundaryWord P g) :=
  (weak_vertices_injective hP).comp (boundaryIndex_injective g)

/-- Exact affine interpolation before any geometric nondegeneracy premise. -/
theorem line_coordinate_interpolation (p ω : Plane) (x y z : ℝ) (hxy : x ≠ y) :
    p + z • ω = (p + x • ω) + ((z - x) / (y - x)) •
      ((p + y • ω) - (p + x • ω)) := by
  ext <;> dsimp <;> field_simp [sub_ne_zero.mpr hxy.symm] <;> ring

/-- A scalar strictly between either ordered pair gives an interior affine
parameter for that exact oriented edge. Both orientations are retained. -/
theorem line_coordinate_between_parameter (x y z : ℝ)
    (h : (x < z ∧ z < y) ∨ (y < z ∧ z < x)) :
    x ≠ y ∧ 0 < (z - x) / (y - x) ∧ (z - x) / (y - x) < 1 := by
  rcases h with h | h
  · have hd : 0 < y - x := by linarith
    exact ⟨by linarith, div_pos (by linarith) hd, (div_lt_one hd).mpr (by linarith)⟩
  · have hd : y - x < 0 := by linarith
    exact ⟨by linarith, div_pos_of_neg_of_neg (by linarith) hd,
      (div_lt_one_of_neg hd).mpr (by linarith)⟩

/-- An original edge of a weak polygon cannot skip another selected point
on the same line. Its two orientations have the same exclusion. -/
theorem weak_line_edge_no_between {P : LabelledTuple n} (hP : WeakGeneric P)
    (i k : ZMod n) (hk0 : k ≠ i) (hk1 : k ≠ i + 1)
    (p ω : Plane) (x y z : ℝ)
    (hx : P i = p + x • ω) (hy : P (i + 1) = p + y • ω)
    (hz : P k = p + z • ω) :
    ¬ ((x < z ∧ z < y) ∨ (y < z ∧ z < x)) := by
  intro h
  obtain ⟨hxy, ht0, ht1⟩ := line_coordinate_between_parameter x y z h
  apply hP.2.2.1 k i ((nonincident_iff k i).mpr ⟨hk0, hk1⟩)
  refine ⟨(z - x) / (y - x), ht0.le, ht1.le, ?_⟩
  change P k = P i + ((z - x) / (y - x)) • (P (i + 1) - P i)
  rw [hx, hy, hz]
  exact line_coordinate_interpolation p ω x y z hxy

/-- Three consecutive original vertices on one affine line contradict the
actual nonzero turn in WeakGeneric, without assuming point-triple G1. -/
theorem weak_not_three_consecutive_on_line {P : LabelledTuple n} (hP : WeakGeneric P)
    (i : ZMod n) (p ω : Plane) (x y z : ℝ)
    (hx : P (i - 1) = p + x • ω) (hy : P i = p + y • ω)
    (hz : P (i + 1) = p + z • ω) : False := by
  apply hP.2.1 i
  have hd : det (P i - P (i - 1)) (P (i + 1) - P (i - 1)) = 0 := by
    rw [hx, hy, hz]
    dsimp [det]
    ring
  simp only [turn, chi, hd, sign_zero]

theorem boundaryIndex_successive [NeZero n] (g : ZMod n) (a b : Fin n)
    (hab : b.val = a.val + 1) : boundaryIndex g b = boundaryIndex g a + 1 := by
  unfold boundaryIndex
  rw [hab, Nat.cast_add, Nat.cast_one]
  ring

/-- A leaf gap in an actual boundary word is precisely an original oriented
edge, so all selected line points other than its endpoints are excluded. -/
theorem weak_boundary_leaf_no_between [NeZero n] {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) (a b c : Fin n) (hab : b.val = a.val + 1)
    (hca : c ≠ a) (hcb : c ≠ b) (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g a = p + x • ω)
    (hy : boundaryWord P g b = p + y • ω)
    (hz : boundaryWord P g c = p + z • ω) :
    ¬ ((x < z ∧ z < y) ∨ (y < z ∧ z < x)) := by
  have hb := boundaryIndex_successive g a b hab
  apply weak_line_edge_no_between hP (boundaryIndex g a) (boundaryIndex g c)
    (fun h => hca (boundaryIndex_injective g h))
    (fun h => hcb (boundaryIndex_injective g (h.trans hb.symm))) p ω x y z hx
  · rw [← hb]
    exact hy
  · exact hz

end
end SM

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

namespace SM

noncomputable section
variable {k : ℕ}

/-- The printed gap ratio uses the ordered endpoints of the whole selected list. -/
def lineGapEpsilon (t : Fin (k + 1) → ℝ) (j : Fin k) : SignType :=
  SignType.sign ((t j.succ - t j.castSucc) / (t (Fin.last k) - t 0))

def normalizedLineCoordinate (t : Fin (k + 1) → ℝ) (l : Fin (k + 1)) : ℝ :=
  (t l - t 0) / (t (Fin.last k) - t 0)

theorem selected_endpoint_difference_nonzero (hk : 0 < k)
    (t : Fin (k + 1) → ℝ) (hinj : Function.Injective t) : t (Fin.last k) - t 0 ≠ 0 := by
  apply sub_ne_zero.mpr
  intro he
  have hi := congrArg Fin.val (hinj he)
  change k = 0 at hi
  omega

theorem normalizedLineCoordinate_first (t : Fin (k + 1) → ℝ) :
    normalizedLineCoordinate t 0 = 0 := by simp [normalizedLineCoordinate]

theorem normalizedLineCoordinate_last (t : Fin (k + 1) → ℝ)
    (hd : t (Fin.last k) - t 0 ≠ 0) :
    normalizedLineCoordinate t (Fin.last k) = 1 := by
  exact div_self hd

theorem normalizedLineCoordinate_injective (t : Fin (k + 1) → ℝ)
    (hinj : Function.Injective t) (hd : t (Fin.last k) - t 0 ≠ 0) :
    Function.Injective (normalizedLineCoordinate t) := by
  intro a b he
  apply hinj
  have hc := congrArg (fun x : ℝ => x * (t (Fin.last k) - t 0)) he
  have hsub : t a - t 0 = t b - t 0 := by
    simpa only [normalizedLineCoordinate, div_mul_cancel₀ _ hd] using hc
  linarith

/-- Normalization changes neither the selected points nor their line, even
when the original endpoint difference is negative. -/
theorem normalizedLineCoordinate_representation (p ω : Plane) (t : Fin (k + 1) → ℝ)
    (hd : t (Fin.last k) - t 0 ≠ 0) (l : Fin (k + 1)) :
    p + t l • ω = (p + t 0 • ω) + normalizedLineCoordinate t l •
      ((t (Fin.last k) - t 0) • ω) := by
  rw [smul_smul]
  simp only [normalizedLineCoordinate, div_mul_cancel₀ _ hd]
  ext <;> dsimp <;> ring

theorem normalizedLineCoordinate_gap (t : Fin (k + 1) → ℝ) (j : Fin k) :
    normalizedLineCoordinate t j.succ - normalizedLineCoordinate t j.castSucc =
      (t j.succ - t j.castSucc) / (t (Fin.last k) - t 0) := by
  unfold normalizedLineCoordinate
  rw [← sub_div]
  congr 1
  ring

theorem lineGapEpsilon_positive (t : Fin (k + 1) → ℝ) (j : Fin k) :
    lineGapEpsilon t j = 1 ↔
      normalizedLineCoordinate t j.castSucc < normalizedLineCoordinate t j.succ := by
  unfold lineGapEpsilon
  rw [sign_eq_one_iff, ← normalizedLineCoordinate_gap, sub_pos]

theorem lineGapEpsilon_negative (t : Fin (k + 1) → ℝ) (j : Fin k) :
    lineGapEpsilon t j = -1 ↔
      normalizedLineCoordinate t j.succ < normalizedLineCoordinate t j.castSucc := by
  unfold lineGapEpsilon
  rw [sign_eq_neg_one_iff, ← normalizedLineCoordinate_gap, sub_neg]

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {k : ℕ}

/-- The actual dot-product coordinate on the line from the first selected
point to the last. Its endpoints will be proved to have coordinates0 and1. -/
def selectedLineCoordinate (P : LabelledTuple n) (g : ZMod n)
    (r : Fin (k + 1) → Fin n) (l : Fin (k + 1)) : ℝ :=
  let ω := boundaryWord P g (r (Fin.last k)) - boundaryWord P g (r 0)
  planeDot ω (boundaryWord P g (r l) - boundaryWord P g (r 0)) / planeDot ω ω

/-- Zero actual determinants on the selected line supply all affine data
and distinct coordinates; no separate collinearity or injectivity oracle is
assumed. This uses only WeakGeneric, even with arbitrarily many silent zeros. -/
theorem weak_selected_line_coordinates {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) (hk : 0 < k) (r : Fin (k + 1) → Fin n) (hr : StrictMono r)
    (hcol : ∀ l, det (boundaryWord P g (r l) - boundaryWord P g (r 0))
      (boundaryWord P g (r (Fin.last k)) - boundaryWord P g (r 0)) = 0) :
    (boundaryWord P g (r (Fin.last k)) - boundaryWord P g (r 0) ≠ 0) ∧
    (∀ l, boundaryWord P g (r l) = boundaryWord P g (r 0) +
      selectedLineCoordinate P g r l •
        (boundaryWord P g (r (Fin.last k)) - boundaryWord P g (r 0))) ∧
    Function.Injective (selectedLineCoordinate P g r) ∧
    selectedLineCoordinate P g r 0 = 0 ∧
    selectedLineCoordinate P g r (Fin.last k) = 1 := by
  let p := boundaryWord P g (r 0)
  let ω := boundaryWord P g (r (Fin.last k)) - p
  have hω : ω ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have hi := hr.injective (weak_boundaryWord_injective hP g he)
    have hv := congrArg Fin.val hi
    change k = 0 at hv
    omega
  have hline : ∀ l, boundaryWord P g (r l) = p + selectedLineCoordinate P g r l • ω := by
    intro l
    have hd : det ω (boundaryWord P g (r l) - p) = 0 := by
      rw [det_swap]
      change -det (boundaryWord P g (r l) - boundaryWord P g (r 0))
        (boundaryWord P g (r (Fin.last k)) - boundaryWord P g (r 0)) = 0
      rw [hcol l, neg_zero]
    have hs := scalar_of_det_zero hω hd
    change boundaryWord P g (r l) - p = selectedLineCoordinate P g r l • ω at hs
    calc
      _ = p + (boundaryWord P g (r l) - p) := by abel
      _ = _ := by rw [hs]
  refine ⟨hω, hline, weak_line_coordinate_injective hP g r hr p ω _ hline, ?_, ?_⟩
  · simp [selectedLineCoordinate, planeDot]
  · exact div_self (ne_of_gt (planeDot_self_pos hω))

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Both assertions of source pf:line-gap for every actual selected collinear
list in a weak polygon, using its exact endpoint-normalized sign ratios.
The negative assertion requires both endpoints of the physical root word. -/
theorem silent_line_gap (hn : 3 ≤ n) {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) (k : ℕ) (hk : 2 ≤ k) (r : Fin (k + 1) → Fin n) (hr : StrictMono r)
    (p ω : Plane) (t : Fin (k + 1) → ℝ)
    (hline : ∀ l, boundaryWord P g (r l) = p + t l • ω) :
    (∃ j : Fin k, lineGapEpsilon t j = 1 ∧
      2 ≤ (r j.succ).val - (r j.castSucc).val) ∧
    ((r 0).val = 0 → (r (Fin.last k)).val = n - 1 →
      ∃ j : Fin k, lineGapEpsilon t j = -1 ∧
        2 ≤ (r j.succ).val - (r j.castSucc).val) := by
  have hinj := weak_line_coordinate_injective hP g r hr p ω t hline
  have hd := selected_endpoint_difference_nonzero (by omega : 0 < k) t hinj
  let u := normalizedLineCoordinate t
  let p' := p + t 0 • ω
  let ω' := (t (Fin.last k) - t 0) • ω
  have hu : ∀ l, boundaryWord P g (r l) = p' + u l • ω' := by
    intro l
    exact (hline l).trans (normalizedLineCoordinate_representation p ω t hd l)
  have hui : Function.Injective u := normalizedLineCoordinate_injective t hinj hd
  have hend : u 0 < u (Fin.last k) := by
    change normalizedLineCoordinate t 0 < normalizedLineCoordinate t (Fin.last k)
    rw [normalizedLineCoordinate_first, normalizedLineCoordinate_last t hd]
    norm_num
  let leaf : Fin k → Prop := fun j => (r j.succ).val = (r j.castSucc).val + 1
  have hclear : ∀ j : Fin k, leaf j → ∀ l : Fin (k + 1),
      ¬ (u j.castSucc < u l ∧ u l < u j.succ) ∧
      ¬ (u j.succ < u l ∧ u l < u j.castSucc) :=
    fun j hj l => weak_line_selection_clear hP g r hr p' ω' u hu j hj l
  have hnext : ∀ j l : Fin k, j.val + 1 = l.val → ¬ (leaf j ∧ leaf l) :=
    fun j l hjl => weak_line_selection_no_successive_leaves hP g r p' ω' u hu j l hjl
  have hlength (j : Fin k) (hj : ¬ leaf j) :
      2 ≤ (r j.succ).val - (r j.castSucc).val := by
    have hpos : r j.castSucc < r j.succ := hr Fin.castSucc_lt_succ
    change (r j.castSucc).val < (r j.succ).val at hpos
    change ¬ ((r j.succ).val = (r j.castSucc).val + 1) at hj
    omega
  constructor
  · obtain ⟨j, hj, hl⟩ := FiniteLineOrder.exists_increasing_nonleaf_gap
      k hk u hui leaf hend hclear hnext
    exact ⟨j, (lineGapEpsilon_positive t j).mpr hj, hlength j hl⟩
  · intro hfirst hlast
    have hclose : ∀ l, ¬ (u 0 < u l ∧ u l < u (Fin.last k)) :=
      weak_line_selection_root_clear hP g r hr p' ω' u hu hfirst hlast
    have hf : ¬ leaf ⟨0, by omega⟩ :=
      weak_line_selection_first_not_leaf hP g (by omega) r p' ω' u hu hfirst hlast
    have hh : ¬ leaf ⟨k - 1, by omega⟩ :=
      weak_line_selection_last_not_leaf hP g (by omega) r p' ω' u hu hfirst hlast
    obtain ⟨j, hj, hl⟩ := FiniteLineOrder.exists_decreasing_nonleaf_gap
      k hk u hui leaf hend hclear hnext hclose hf hh
    exact ⟨j, (lineGapEpsilon_negative t j).mpr hj, hlength j hl⟩

/-- The source lemma applied directly to vanishing actual determinants.
The printed distinct line coordinates are constructed from the selected
points themselves; no affine-data oracle is required of the caller. -/
theorem silent_line_gap_of_collinear (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) (k : ℕ) (hk : 2 ≤ k)
    (r : Fin (k + 1) → Fin n) (hr : StrictMono r)
    (hcol : ∀ l, det (boundaryWord P g (r l) - boundaryWord P g (r 0))
      (boundaryWord P g (r (Fin.last k)) - boundaryWord P g (r 0)) = 0) :
    Function.Injective (selectedLineCoordinate P g r) ∧
    selectedLineCoordinate P g r 0 = 0 ∧
    selectedLineCoordinate P g r (Fin.last k) = 1 ∧
    (∃ j : Fin k, lineGapEpsilon (selectedLineCoordinate P g r) j = 1 ∧
      2 ≤ (r j.succ).val - (r j.castSucc).val) ∧
    ((r 0).val = 0 → (r (Fin.last k)).val = n - 1 →
      ∃ j : Fin k, lineGapEpsilon (selectedLineCoordinate P g r) j = -1 ∧
        2 ≤ (r j.succ).val - (r j.castSucc).val) := by
  have hdata := weak_selected_line_coordinates hP g (by omega : 0 < k) r hr hcol
  exact ⟨hdata.2.2.1, hdata.2.2.2.1, hdata.2.2.2.2,
    silent_line_gap hn hP g k hk r hr (boundaryWord P g (r 0))
      (boundaryWord P g (r (Fin.last k)) - boundaryWord P g (r 0))
      (selectedLineCoordinate P g r) hdata.2.1⟩

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- A zero rational geometric far entry is exactly collinearity. The
change from reversed far orientation to the endpoint-line determinant
only negates that determinant and does not change its zero set. -/
theorem rational_geometric_far_zero_iff (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) :
    geometricBoundaryArray (R := ℚ) P g t = 0 ↔
      det (boundaryWord P g t.middle - boundaryWord P g t.lower)
        (boundaryWord P g t.upper - boundaryWord P g t.lower) = 0 := by
  have hs (s : SignType) : ((s : ℤ) : ℚ) = 0 ↔ s = 0 := by
    cases s <;> norm_num
  unfold geometricBoundaryArray
  rw [hs, chi, sign_eq_zero_iff]
  change det (boundaryWord P g t.middle - boundaryWord P g t.upper)
      (boundaryWord P g t.lower - boundaryWord P g t.upper) = 0 ↔ _
  have hd : det (boundaryWord P g t.middle - boundaryWord P g t.upper)
      (boundaryWord P g t.lower - boundaryWord P g t.upper) =
      -det (boundaryWord P g t.middle - boundaryWord P g t.lower)
        (boundaryWord P g t.upper - boundaryWord P g t.lower) := by
    dsimp [det]
    ring
  rw [hd, neg_eq_zero]

/-- If every selected top cut is silent, every point in the actual
composition cut list lies on its endpoint line. Endpoints are included
explicitly, and no independence of determinant differentials is used. -/
theorem silent_composition_cuts_collinear (P : LabelledTuple n) (g : ZMod n)
    {I : BoundaryInterval n} (π : IntervalComposition I)
    (hzero : ∀ j : Fin (π.parts - 1), geometricBoundaryArray (R := ℚ) P g (π.farTriple j) = 0) :
    ∀ l, det (boundaryWord P g (π.cut l) - boundaryWord P g (π.cut 0))
      (boundaryWord P g (π.cut (Fin.last π.parts)) - boundaryWord P g (π.cut 0)) = 0 := by
  intro l
  by_cases hfirst : l = 0
  · subst l
    simp [det]
  by_cases hlast : l = Fin.last π.parts
  · subst l
    simp [det, mul_comm]
  have hlo : 0 < l.val := by
    by_contra h
    apply hfirst
    apply Fin.ext
    change l.val = 0
    omega
  have hhi : l.val < π.parts := by
    have hv := l.isLt
    by_contra h
    apply hlast
    apply Fin.ext
    change l.val = π.parts
    omega
  let j : Fin (π.parts - 1) := ⟨l.val - 1, by omega⟩
  have hm : π.interiorPosition j = π.cut l := by
    unfold IntervalComposition.interiorPosition
    congr 1
    apply Fin.ext
    change (l.val - 1) + 1 = l.val
    omega
  have hd := (rational_geometric_far_zero_iff P g (π.farTriple j)).mp (hzero j)
  change det (boundaryWord P g (π.interiorPosition j) - boundaryWord P g I.left)
    (boundaryWord P g I.right - boundaryWord P g I.left) = 0 at hd
  rw [hm] at hd
  rw [π.first, π.last]
  exact hd

/-- Every nonempty silent selection has a positive gap of at least two
leaves in the actual composition, ready for its zero inverse-coordinate
factor. The rational zero array supplies the collinearity premise. -/
theorem silent_composition_positive_gap (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) {I : BoundaryInterval n}
    (π : IntervalComposition I) (hparts : 2 ≤ π.parts)
    (hzero : ∀ j : Fin (π.parts - 1), geometricBoundaryArray (R := ℚ) P g (π.farTriple j) = 0) :
    ∃ j : Fin π.parts, lineGapEpsilon (selectedLineCoordinate P g π.cut) j = 1 ∧
      2 ≤ (π.part j).leaves := by
  have h := silent_line_gap_of_collinear hn hP g π.parts hparts π.cut π.strict
    (silent_composition_cuts_collinear P g π hzero)
  exact h.2.2.2.1

/-- The negative gap assertion is used only on the full physical root
interval; the source's endpoint condition is discharged by π.first/last. -/
theorem silent_composition_full_negative_gap (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) (π : IntervalComposition (fullBoundaryInterval hn))
    (hparts : 2 ≤ π.parts)
    (hzero : ∀ j : Fin (π.parts - 1), geometricBoundaryArray (R := ℚ) P g (π.farTriple j) = 0) :
    ∃ j : Fin π.parts, lineGapEpsilon (selectedLineCoordinate P g π.cut) j = -1 ∧
      2 ≤ (π.part j).leaves := by
  have h := silent_line_gap_of_collinear hn hP g π.parts hparts π.cut π.strict
    (silent_composition_cuts_collinear P g π hzero)
  apply h.2.2.2.2
  · rw [π.first]
    rfl
  · rw [π.last]
    rfl

end
end SM

#print axioms SM.rational_geometric_far_zero_iff
#print axioms SM.silent_composition_cuts_collinear
#print axioms SM.silent_composition_positive_gap
#print axioms SM.silent_composition_full_negative_gap
