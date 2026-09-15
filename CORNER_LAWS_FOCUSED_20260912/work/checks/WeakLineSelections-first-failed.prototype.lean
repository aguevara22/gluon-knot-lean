import SM.WeakGeometry
import SM.RootBoundary
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
    rw [← Nat.cast_one, ← Nat.cast_add, Nat.sub_add_cancel hn, ZMod.natCast_self]
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

#check SM.boundaryIndex_first_of_val
#print axioms SM.boundaryIndex_first_of_val
#check SM.boundaryIndex_last_of_val
#print axioms SM.boundaryIndex_last_of_val
#check SM.weak_not_successive_labels_on_line
#print axioms SM.weak_not_successive_labels_on_line
#check SM.weak_line_coordinate_injective
#print axioms SM.weak_line_coordinate_injective
#check SM.weak_line_selection_clear
#print axioms SM.weak_line_selection_clear
#check SM.weak_line_selection_no_successive_leaves
#print axioms SM.weak_line_selection_no_successive_leaves
#check SM.weak_line_selection_root_clear
#print axioms SM.weak_line_selection_root_clear
#check SM.weak_line_selection_first_not_leaf
#print axioms SM.weak_line_selection_first_not_leaf
#check SM.weak_line_selection_last_not_leaf
#print axioms SM.weak_line_selection_last_not_leaf
