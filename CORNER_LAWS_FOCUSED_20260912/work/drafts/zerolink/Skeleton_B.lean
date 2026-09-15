import SM.LinkDiagram

/-! Skeleton B for mp:zero-link (reference/SM/sm-3-statesum.tex:1538-1580).  Route: the printed
fan-triangle argument from a generic auxiliary point `o`, with the single geometric core reduced to
a one-dimensional statement about three affine functions (`affine_triple_jump`).  Plan:
work/drafts/zerolink/PLAN_B.md.  Status (2026-09-13): the whole chain is stated; the fan assembly
(L1, L4, L5, L6), the triangle side algebra (L3a-L3d) and the diagram layer (L7-L9, the three fields
of `ZeroLinkData`, `zero_link`) are proved; `sorry` remains only in the one-dimensional core L2
(`affine_triple_jump` and its six sub-lemmas L2a-L2d') and in the segment-versus-triangle jump L3
(`segment_triangle_jump`).  Checked with `lake env lean` (only `sorry` warnings). -/

namespace SM

namespace ZeroLink

open SM.Link Classical

noncomputable section

/-! ## 1. Segments, the interior-crossing predicate and the signed crossing indicator -/

/-- The closed segment from `b` to `b + v`, parametrised exactly as `edgeSegment`. -/
def closedSeg (b v : Plane) : Set Plane := {x | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ x = b + s • v}

theorem edgeSegment_eq_closedSeg {n : ℕ} (P : LabelledTuple n) (i : ZMod n) :
    edgeSegment P i = closedSeg (P i) (edge P i) := rfl

/-- Two segments `[a, a+u]`, `[b, b+v]` meet at interior points of both. -/
def Meets (a u b v : Plane) : Prop :=
  ∃ t s : ℝ, 0 < t ∧ t < 1 ∧ 0 < s ∧ s < 1 ∧ a + t • u = b + s • v

/-- Signed crossing indicator of `[a,a+u]` (first) against `[b,b+v]` (second): `sgn det(u,v)` when
they meet at interior points, `0` otherwise. -/
def chi (a u b v : Plane) : ℤ :=
  if Meets a u b v then ((SignType.sign (det u v) : SignType) : ℤ) else 0

/-- `Meets` is symmetric under reversing the second segment (`s ↦ 1 - s`). -/
theorem meets_reverse_iff (a u b v : Plane) : Meets a u (b + v) (-v) ↔ Meets a u b v := by
  constructor
  · rintro ⟨t, s, ht0, ht1, hs0, hs1, h⟩
    refine ⟨t, 1 - s, ht0, ht1, by linarith, by linarith, ?_⟩
    rw [h, sub_smul, one_smul, smul_neg]
    abel
  · rintro ⟨t, s, ht0, ht1, hs0, hs1, h⟩
    refine ⟨t, 1 - s, ht0, ht1, by linarith, by linarith, ?_⟩
    rw [h, sub_smul, one_smul, smul_neg]
    abel

/-- L1. Reversing the second segment negates the signed crossing indicator. -/
theorem chi_reverse (a u b v : Plane) : chi a u (b + v) (-v) = - chi a u b v := by
  have hd : det u (-v) = - det u v := by
    simp only [det, Prod.fst_neg, Prod.snd_neg]
    ring
  unfold chi
  by_cases h : Meets a u b v
  · rw [ite_eq_left ((meets_reverse_iff a u b v).mpr h), ite_eq_left h, hd, Left.sign_neg]
    simp
  · rw [ite_eq_right (fun h' => h ((meets_reverse_iff a u b v).mp h')), ite_eq_right h, neg_zero]

/-- L1'. The reversal lemma for the segment from `b` to `c`. -/
theorem chi_reverse' (a u b c : Plane) : chi a u c (b - c) = - chi a u b (c - b) := by
  have h := chi_reverse a u b (c - b)
  have e1 : b + (c - b) = c := by abel
  have e2 : -(c - b) = b - c := by abel
  rw [e1, e2] at h
  exact h

/-- The closed segment does not depend on the direction of traversal. -/
theorem closedSeg_reverse (b c : Plane) : closedSeg c (b - c) = closedSeg b (c - b) := by
  ext x
  constructor <;> rintro ⟨s, h0, h1, rfl⟩ <;> refine ⟨1 - s, by linarith, by linarith, ?_⟩ <;>
    simp only [sub_smul, one_smul, smul_sub] <;> abel

/-- A point `x` with `det v (x - b) ≠ 0` is not on the closed segment `[b, b+v]`. -/
theorem not_mem_closedSeg_of_det_ne_zero {b v x : Plane} (h : det v (x - b) ≠ 0) :
    x ∉ closedSeg b v := by
  rintro ⟨s, -, -, rfl⟩
  apply h
  rw [add_sub_cancel_left, det_smul_self]

/-- The vertex `a` is off the radial segment `[o, b]` when `o` is off the line `ab`. -/
theorem not_mem_closedSeg_radial {a b o : Plane} (h : det (b - a) (o - a) ≠ 0) :
    a ∉ closedSeg o (b - o) := by
  rintro ⟨s, -, -, ha⟩
  apply h
  subst ha
  simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  ring

/-- The vertex `a` is off the radial segment `[b, o]` when `o` is off the line `ab`. -/
theorem not_mem_closedSeg_radial' {a b o : Plane} (h : det (b - a) (o - a) ≠ 0) :
    a ∉ closedSeg b (o - b) := by
  rintro ⟨s, -, -, ha⟩
  apply h
  subst ha
  simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  ring

/-! ## 2. The one-dimensional core: three affine functions on `[0,1]` -/

/-- Integer indicator of a proposition. -/
def ind (p : Prop) : ℤ := if p then 1 else 0

/-- The crossing predicate of the `k`-th constraint at parameter `t`: `g k` vanishes at an interior
parameter where the other two constraints are strictly satisfied. -/
def Cross (α β : Fin 3 → ℝ) (k : Fin 3) (t : ℝ) : Prop :=
  0 < t ∧ t < 1 ∧ α k + β k * t = 0 ∧ ∀ j, j ≠ k → 0 < α j + β j * t

/-- L2 (the core).  For three affine functions `g k t = α k + β k * t` such that the endpoints
`t = 0, 1` are not on the "closed boundary" (all `g ≥ 0` with one `= 0`) and no two vanish at a
common `t ∈ [0,1]`, the change of the indicator of `∀ k, 0 < g k t` from `t = 0` to `t = 1` is the
sum over `k` of `sgn (β k)` at the crossings of the `k`-th constraint. -/
theorem affine_triple_jump (α β : Fin 3 → ℝ)
    (hend : ∀ t : ℝ, (t = 0 ∨ t = 1) →
      (∀ k, 0 < α k + β k * t) ∨ ∃ k, α k + β k * t < 0)
    (hvert : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ k k' : Fin 3, k ≠ k' →
      α k + β k * t = 0 → α k' + β k' * t ≠ 0) :
    ind (∀ k, 0 < α k + β k * 1) - ind (∀ k, 0 < α k + β k * 0) =
      ∑ k : Fin 3, if (∃ t : ℝ, Cross α β k t)
        then ((SignType.sign (β k) : SignType) : ℤ) else 0 := by
  sorry

/-! ### Sub-lemmas of L2 (all one-dimensional) -/

/-- L2a. A crossing of positive slope is approached from the inside on the right: for every
`ε > 0` there is `t' ∈ (t, t + ε)` with all constraints strictly satisfied. -/
theorem cross_pos_exists_inside_after (α β : Fin 3 → ℝ) {k : Fin 3} {t : ℝ}
    (hc : Cross α β k t) (hβ : 0 < β k) (ε : ℝ) (hε : 0 < ε) :
    ∃ t' : ℝ, t < t' ∧ t' < t + ε ∧ ∀ j, 0 < α j + β j * t' := by
  sorry

/-- L2a'. Mirror image for negative slope. -/
theorem cross_neg_exists_inside_before (α β : Fin 3 → ℝ) {k : Fin 3} {t : ℝ}
    (hc : Cross α β k t) (hβ : β k < 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ t' : ℝ, t - ε < t' ∧ t' < t ∧ ∀ j, 0 < α j + β j * t' := by
  sorry

/-- L2b. Two crossings whose slopes have the same nonzero sign coincide. -/
theorem cross_same_sign_unique (α β : Fin 3 → ℝ) {k k' : Fin 3} {t t' : ℝ}
    (hc : Cross α β k t) (hc' : Cross α β k' t') (hβ : β k ≠ 0)
    (hs : SignType.sign (β k) = SignType.sign (β k')) : k = k' ∧ t = t' := by
  sorry

/-- L2c. An entry (positive slope) precedes every exit (negative slope). -/
theorem cross_pos_lt_cross_neg (α β : Fin 3 → ℝ) {k k' : Fin 3} {t t' : ℝ}
    (hc : Cross α β k t) (hc' : Cross α β k' t') (hβ : 0 < β k) (hβ' : β k' < 0) : t < t' := by
  sorry

/-- L2d (IVT).  Inside at `s`, not inside at `s' ∈ (s, 1]`: an exit crossing lies in `(s, s')`
(or at `s'` when `s' < 1`); with `hend` the endpoint `s' = 1` is excluded. -/
theorem exists_cross_neg_of_inside_not_inside (α β : Fin 3 → ℝ)
    (hend : ∀ t : ℝ, (t = 0 ∨ t = 1) →
      (∀ k, 0 < α k + β k * t) ∨ ∃ k, α k + β k * t < 0)
    (hvert : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ k k' : Fin 3, k ≠ k' →
      α k + β k * t = 0 → α k' + β k' * t ≠ 0)
    {s s' : ℝ} (hs0 : 0 ≤ s) (hss' : s < s') (hs'1 : s' ≤ 1)
    (hin : ∀ j, 0 < α j + β j * s) (hout : ¬ ∀ j, 0 < α j + β j * s') :
    ∃ k t, Cross α β k t ∧ β k < 0 ∧ s < t ∧ t ≤ s' := by
  sorry

/-- L2d'. Mirror image: not inside at `s`, inside at `s'`: an entry crossing in `[s, s')`. -/
theorem exists_cross_pos_of_not_inside_inside (α β : Fin 3 → ℝ)
    (hend : ∀ t : ℝ, (t = 0 ∨ t = 1) →
      (∀ k, 0 < α k + β k * t) ∨ ∃ k, α k + β k * t < 0)
    (hvert : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ k k' : Fin 3, k ≠ k' →
      α k + β k * t = 0 → α k' + β k' * t ≠ 0)
    {s s' : ℝ} (hs0 : 0 ≤ s) (hss' : s < s') (hs'1 : s' ≤ 1)
    (hout : ¬ ∀ j, 0 < α j + β j * s) (hin : ∀ j, 0 < α j + β j * s') :
    ∃ k t, Cross α β k t ∧ 0 < β k ∧ s ≤ t ∧ t < s' := by
  sorry

/-! ## 3. Triangles: the segment-versus-triangle jump lemma -/

/-- The open triangle with vertices `c₀ c₁ c₂` (positively oriented): strictly left of each side. -/
def InTri (c₀ c₁ c₂ x : Plane) : Prop :=
  0 < det (c₁ - c₀) (x - c₀) ∧ 0 < det (c₂ - c₁) (x - c₁) ∧ 0 < det (c₀ - c₂) (x - c₂)

/-- The boundary of the triangle: the union of its three closed sides. -/
def triBoundary (c₀ c₁ c₂ : Plane) : Set Plane :=
  closedSeg c₀ (c₁ - c₀) ∪ closedSeg c₁ (c₂ - c₁) ∪ closedSeg c₂ (c₀ - c₂)

/-- The signed crossing count of `[a, a+u]` against the three sides of the triangle. -/
def triChi (a u c₀ c₁ c₂ : Plane) : ℤ :=
  chi a u c₀ (c₁ - c₀) + chi a u c₁ (c₂ - c₁) + chi a u c₂ (c₀ - c₂)

/-- The boundary of the triangle does not depend on its orientation. -/
theorem triBoundary_swap (c₀ c₁ c₂ : Plane) : triBoundary c₀ c₂ c₁ = triBoundary c₀ c₁ c₂ := by
  unfold triBoundary
  rw [closedSeg_reverse c₂ c₀, closedSeg_reverse c₁ c₂, closedSeg_reverse c₀ c₁]
  ext x
  simp only [Set.mem_union]
  tauto

/-- The side vector of a nondegenerate triangle is nonzero. -/
theorem side_ne_zero_of_det {b c d : Plane} (hD : det (c - b) (d - b) ≠ 0) : c - b ≠ 0 := by
  intro h
  apply hD
  rw [h]
  simp [det]

/-- Cyclic invariance of the orientation determinant (accepted `area_cyclic`). -/
theorem det_tri_cyclic (c₀ c₁ c₂ : Plane) :
    det (c₂ - c₁) (c₀ - c₁) = det (c₁ - c₀) (c₂ - c₀) := area_cyclic c₀ c₁ c₂

/-- L3c'. Two side lines of a nondegenerate triangle `(b, c, d)` meet only at the common vertex
`c`. -/
theorem line_meet_vertex (b c d x : Plane) (hD : det (c - b) (d - b) ≠ 0)
    (h1 : det (c - b) (x - b) = 0) (h2 : det (d - c) (x - c) = 0) : x = c := by
  have hcb : c - b ≠ 0 := side_ne_zero_of_det hD
  obtain ⟨r, hxr⟩ : ∃ r : ℝ, x - b = r • (c - b) := ⟨_, scalar_of_det_zero hcb h1⟩
  have hxc : x - c = (r - 1) • (c - b) := by
    have e : x - c = (x - b) - (c - b) := by abel
    rw [e, hxr, sub_smul, one_smul]
  have hdet : det (d - c) (c - b) ≠ 0 := by
    intro h
    apply hD
    have e : det (c - b) (d - b) = - det (d - c) (c - b) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub]
      ring
    rw [e, h, neg_zero]
  rw [hxc, det_smul_right] at h2
  rcases mul_eq_zero.mp h2 with h | h
  · have : x - c = 0 := by rw [hxc, h, zero_smul]
    exact sub_eq_zero.mp this
  · exact absurd h hdet

/-- L3a. A point of the line of side `[c₀,c₁]` at parameter `s` has the other two side functions
equal to `(1 - s) D` and `s D`, `D = det (c₁ - c₀) (c₂ - c₀)`. -/
theorem side_line_values (c₀ c₁ c₂ : Plane) (s : ℝ) :
    det (c₂ - c₁) (c₀ + s • (c₁ - c₀) - c₁) = (1 - s) * det (c₁ - c₀) (c₂ - c₀) ∧
    det (c₀ - c₂) (c₀ + s • (c₁ - c₀) - c₂) = s * det (c₁ - c₀) (c₂ - c₀) := by
  constructor <;>
  · simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    ring

/-- L3b'. A point on the line of side `[b, c]` of a positively oriented triangle `(b, c, d)` with the
other two side functions `≥ 0` lies on the closed side. -/
theorem mem_closedSeg_of_side (b c d x : Plane) (hD : 0 < det (c - b) (d - b))
    (h0 : det (c - b) (x - b) = 0) (h1 : 0 ≤ det (d - c) (x - c)) (h2 : 0 ≤ det (b - d) (x - d)) :
    x ∈ closedSeg b (c - b) := by
  have hcb : c - b ≠ 0 := side_ne_zero_of_det hD.ne'
  have hx := scalar_of_det_zero hcb h0
  obtain ⟨s, hxs⟩ : ∃ s : ℝ, x = b + s • (c - b) := ⟨_, by rw [← hx]; abel⟩
  obtain ⟨e1, e2⟩ := side_line_values b c d s
  rw [hxs, e1] at h1
  rw [hxs, e2] at h2
  refine ⟨s, ?_, ?_, hxs⟩
  · nlinarith
  · nlinarith

/-- L3b. On a nondegenerate triangle, the closed triangle minus the open triangle is the boundary:
all side functions `≥ 0` with one `= 0` forces the point onto a closed side. -/
theorem mem_triBoundary_of_ge_of_eq (c₀ c₁ c₂ x : Plane) (hD : 0 < det (c₁ - c₀) (c₂ - c₀))
    (h0 : 0 ≤ det (c₁ - c₀) (x - c₀)) (h1 : 0 ≤ det (c₂ - c₁) (x - c₁))
    (h2 : 0 ≤ det (c₀ - c₂) (x - c₂))
    (hz : det (c₁ - c₀) (x - c₀) = 0 ∨ det (c₂ - c₁) (x - c₁) = 0 ∨ det (c₀ - c₂) (x - c₂) = 0) :
    x ∈ triBoundary c₀ c₁ c₂ := by
  have hD1 : 0 < det (c₂ - c₁) (c₀ - c₁) := by rw [det_tri_cyclic]; exact hD
  have hD2 : 0 < det (c₀ - c₂) (c₁ - c₂) := by rw [det_tri_cyclic]; exact hD1
  rcases hz with h | h | h
  · exact Or.inl (Or.inl (mem_closedSeg_of_side c₀ c₁ c₂ x hD h h1 h2))
  · exact Or.inl (Or.inr (mem_closedSeg_of_side c₁ c₂ c₀ x hD1 h h2 h0))
  · exact Or.inr (mem_closedSeg_of_side c₂ c₀ c₁ x hD2 h h0 h1)

/-- L3c. Two side lines of a nondegenerate triangle meet only at their common vertex. -/
theorem vertex_of_two_sides_zero (c₀ c₁ c₂ x : Plane) (hD : det (c₁ - c₀) (c₂ - c₀) ≠ 0) :
    (det (c₁ - c₀) (x - c₀) = 0 → det (c₂ - c₁) (x - c₁) = 0 → x = c₁) ∧
    (det (c₂ - c₁) (x - c₁) = 0 → det (c₀ - c₂) (x - c₂) = 0 → x = c₂) ∧
    (det (c₀ - c₂) (x - c₂) = 0 → det (c₁ - c₀) (x - c₀) = 0 → x = c₀) := by
  have hD1 : det (c₂ - c₁) (c₀ - c₁) ≠ 0 := by rw [det_tri_cyclic]; exact hD
  have hD2 : det (c₀ - c₂) (c₁ - c₂) ≠ 0 := by rw [det_tri_cyclic]; exact hD1
  exact ⟨line_meet_vertex c₀ c₁ c₂ x hD, line_meet_vertex c₁ c₂ c₀ x hD1,
    line_meet_vertex c₂ c₀ c₁ x hD2⟩

/-- L3d. `Meets` with a side is exactly the one-dimensional crossing predicate of that side's
affine function (`α = det σ (a - c)`, `β = det σ u`) with the other two functions positive. -/
theorem meets_side_iff (c₀ c₁ c₂ a u : Plane) (hD : 0 < det (c₁ - c₀) (c₂ - c₀)) (t : ℝ) :
    (∃ s : ℝ, 0 < s ∧ s < 1 ∧ a + t • u = c₀ + s • (c₁ - c₀)) ↔
      det (c₁ - c₀) (a + t • u - c₀) = 0 ∧ 0 < det (c₂ - c₁) (a + t • u - c₁) ∧
        0 < det (c₀ - c₂) (a + t • u - c₂) := by
  constructor
  · rintro ⟨s, hs0, hs1, hxs⟩
    rw [hxs]
    obtain ⟨e1, e2⟩ := side_line_values c₀ c₁ c₂ s
    rw [e1, e2, add_sub_cancel_left, det_smul_self]
    exact ⟨rfl, mul_pos (by linarith) hD, mul_pos hs0 hD⟩
  · rintro ⟨h0, h1, h2⟩
    have hcb : c₁ - c₀ ≠ 0 := side_ne_zero_of_det hD.ne'
    have hx := scalar_of_det_zero hcb h0
    obtain ⟨s, hxs⟩ : ∃ s : ℝ, a + t • u = c₀ + s • (c₁ - c₀) := ⟨_, by rw [← hx]; abel⟩
    obtain ⟨e1, e2⟩ := side_line_values c₀ c₁ c₂ s
    rw [hxs, e1] at h1
    rw [hxs, e2] at h2
    refine ⟨s, ?_, ?_, hxs⟩
    · nlinarith
    · nlinarith

/-- L3 (segment-versus-triangle jump).  For a positively oriented triangle and a segment whose
endpoints avoid the closed boundary and which avoids the three vertices, the change of the interior
indicator along the segment equals minus the signed crossing count with the three sides. -/
theorem segment_triangle_jump (c₀ c₁ c₂ a u : Plane) (hD : 0 < det (c₁ - c₀) (c₂ - c₀))
    (ha : a ∉ triBoundary c₀ c₁ c₂) (ha' : a + u ∉ triBoundary c₀ c₁ c₂)
    (hc₀ : c₀ ∉ closedSeg a u) (hc₁ : c₁ ∉ closedSeg a u) (hc₂ : c₂ ∉ closedSeg a u) :
    ind (InTri c₀ c₁ c₂ (a + u)) - ind (InTri c₀ c₁ c₂ a) = - triChi a u c₀ c₁ c₂ := by
  sorry

/-- L4a. Reversing the orientation of the triangle negates the signed crossing count. -/
theorem triChi_swap (a u c₀ c₁ c₂ : Plane) : triChi a u c₀ c₂ c₁ = - triChi a u c₀ c₁ c₂ := by
  unfold triChi
  rw [chi_reverse' a u c₂ c₀, chi_reverse' a u c₁ c₂, chi_reverse' a u c₀ c₁]
  ring

/-- L4b. Telescoping over a cyclic index set. -/
theorem sum_shift_sub {m : ℕ} [NeZero m] (f : ZMod m → ℤ) :
    ∑ p : ZMod m, (f (p + 1) - f p) = 0 := by
  have hs : (∑ p : ZMod m, f (p + 1)) = ∑ p : ZMod m, f p :=
    Equiv.sum_comp (Equiv.addRight (1 : ZMod m)) f
  rw [Finset.sum_sub_distrib, hs, sub_self]

/-- L4 (closed polygon versus triangle).  A closed polygon whose vertices avoid the boundary of a
nondegenerate triangle and whose edges avoid its vertices has signed crossing count `0` with the
triangle boundary. -/
theorem closed_polygon_triangle_sum {m : ℕ} [NeZero m] (P : LabelledTuple m) (c₀ c₁ c₂ : Plane)
    (hD : det (c₁ - c₀) (c₂ - c₀) ≠ 0)
    (hP : ∀ p, P p ∉ triBoundary c₀ c₁ c₂)
    (hc : ∀ p, c₀ ∉ edgeSegment P p ∧ c₁ ∉ edgeSegment P p ∧ c₂ ∉ edgeSegment P p) :
    ∑ p : ZMod m, triChi (P p) (edge P p) c₀ c₁ c₂ = 0 := by
  have hnext : ∀ p : ZMod m, P p + edge P p = P (p + 1) := by
    intro p
    simp [edge]
  have hc' : ∀ p, c₀ ∉ closedSeg (P p) (edge P p) ∧ c₁ ∉ closedSeg (P p) (edge P p) ∧
      c₂ ∉ closedSeg (P p) (edge P p) := hc
  rcases lt_or_gt_of_ne hD with hneg | hpos
  · have hpos' : 0 < det (c₂ - c₀) (c₁ - c₀) := by rw [det_swap]; linarith
    have hP' : ∀ p, P p ∉ triBoundary c₀ c₂ c₁ := by
      intro p
      rw [triBoundary_swap]
      exact hP p
    have key : ∀ p, triChi (P p) (edge P p) c₀ c₁ c₂ =
        ind (InTri c₀ c₂ c₁ (P (p + 1))) - ind (InTri c₀ c₂ c₁ (P p)) := by
      intro p
      have h := segment_triangle_jump c₀ c₂ c₁ (P p) (edge P p) hpos' (hP' p)
        (by rw [hnext]; exact hP' (p + 1)) (hc' p).1 (hc' p).2.2 (hc' p).2.1
      rw [hnext, triChi_swap] at h
      linarith
    calc ∑ p : ZMod m, triChi (P p) (edge P p) c₀ c₁ c₂
        = ∑ p : ZMod m, (ind (InTri c₀ c₂ c₁ (P (p + 1))) - ind (InTri c₀ c₂ c₁ (P p))) :=
          Finset.sum_congr rfl (fun p _ => key p)
      _ = 0 := sum_shift_sub (fun p => ind (InTri c₀ c₂ c₁ (P p)))
  · have key : ∀ p, triChi (P p) (edge P p) c₀ c₁ c₂ =
        -(ind (InTri c₀ c₁ c₂ (P (p + 1))) - ind (InTri c₀ c₁ c₂ (P p))) := by
      intro p
      have h := segment_triangle_jump c₀ c₁ c₂ (P p) (edge P p) hpos (hP p)
        (by rw [hnext]; exact hP (p + 1)) (hc' p).1 (hc' p).2.1 (hc' p).2.2
      rw [hnext] at h
      linarith
    calc ∑ p : ZMod m, triChi (P p) (edge P p) c₀ c₁ c₂
        = ∑ p : ZMod m, -(ind (InTri c₀ c₁ c₂ (P (p + 1))) - ind (InTri c₀ c₁ c₂ (P p))) :=
          Finset.sum_congr rfl (fun p _ => key p)
      _ = -∑ p : ZMod m, (ind (InTri c₀ c₁ c₂ (P (p + 1))) - ind (InTri c₀ c₁ c₂ (P p))) :=
          Finset.sum_neg_distrib _
      _ = 0 := by rw [sum_shift_sub (fun p => ind (InTri c₀ c₁ c₂ (P p))), neg_zero]

/-! ## 4. The generic auxiliary point -/

/-- L5. Finitely many lines `{x | det (v l) (x - c l) = 0}` (with `v l ≠ 0`) do not cover the
plane.  Proof: choose an abscissa `X` different from those of the vertical lines, then an ordinate
`Y` different from the finitely many values the non-vertical lines take at `X`. -/
theorem exists_point_off_lines {ι : Type*} [Fintype ι] (c v : ι → Plane) (hv : ∀ l, v l ≠ 0) :
    ∃ o : Plane, ∀ l, det (v l) (o - c l) ≠ 0 := by
  classical
  obtain ⟨X, hX⟩ := Infinite.exists_notMem_finset (Finset.univ.image (fun l => (c l).1))
  obtain ⟨Y, hY⟩ := Infinite.exists_notMem_finset
    (Finset.univ.image (fun l => (c l).2 + (v l).2 * (X - (c l).1) / (v l).1))
  refine ⟨(X, Y), fun l => ?_⟩
  have hX' : X ≠ (c l).1 := fun h => hX (Finset.mem_image.mpr ⟨l, Finset.mem_univ _, h.symm⟩)
  have hY' : Y ≠ (c l).2 + (v l).2 * (X - (c l).1) / (v l).1 :=
    fun h => hY (Finset.mem_image.mpr ⟨l, Finset.mem_univ _, h.symm⟩)
  show (v l).1 * ((X, Y) - c l).2 - (v l).2 * ((X, Y) - c l).1 ≠ 0
  simp only [Prod.fst_sub, Prod.snd_sub]
  by_cases h1 : (v l).1 = 0
  · have h2 : (v l).2 ≠ 0 := by
      intro h2
      exact hv l (Prod.ext h1 h2)
    rw [h1, zero_mul, zero_sub, neg_ne_zero]
    exact mul_ne_zero h2 (sub_ne_zero.mpr hX')
  · have key : (v l).1 * (Y - ((c l).2 + (v l).2 * (X - (c l).1) / (v l).1)) =
        (v l).1 * (Y - (c l).2) - (v l).2 * (X - (c l).1) := by
      field_simp
      ring
    intro h
    apply hY'
    have h' := key.trans h
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' h1
    · exact sub_eq_zero.mp h''

/-- L5a. Nondegeneracy of the fan triangle `(o, b, b')` from `o` off the line `b b'`. -/
theorem det_fan_of_off_line (o b b' : Plane) (h : det (b' - b) (o - b) ≠ 0) :
    det (b - o) (b' - o) ≠ 0 := by
  have e : det (b - o) (b' - o) = det (b' - b) (o - b) := by
    simp only [det, Prod.fst_sub, Prod.snd_sub]
    ring
  rw [e]
  exact h

/-! ## 5. The fan: two closed polygons -/

/-- L6a. Radial cancellation: the radial sides `[o, B q]` and `[B (q+1), o]` of consecutive fan
triangles are traversed once in each orientation. -/
theorem radial_cancel {m n : ℕ} [NeZero m] [NeZero n] (A : LabelledTuple m) (B : LabelledTuple n)
    (o : Plane) :
    ∑ q : ZMod n, ∑ p : ZMod m,
      (chi (A p) (edge A p) o (B q - o) + chi (A p) (edge A p) (B (q + 1)) (o - B (q + 1))) = 0 := by
  have h : ∀ q : ZMod n, ∑ p : ZMod m,
      (chi (A p) (edge A p) o (B q - o) + chi (A p) (edge A p) (B (q + 1)) (o - B (q + 1))) =
      (∑ p : ZMod m, chi (A p) (edge A p) o (B q - o)) -
        ∑ p : ZMod m, chi (A p) (edge A p) o (B (q + 1) - o) := by
    intro q
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [chi_reverse' (A p) (edge A p) o (B (q + 1))]
    ring
  rw [Finset.sum_congr rfl (fun q _ => h q)]
  have hs := sum_shift_sub (fun q : ZMod n => ∑ p : ZMod m, chi (A p) (edge A p) o (B q - o))
  calc ∑ q : ZMod n, ((∑ p : ZMod m, chi (A p) (edge A p) o (B q - o)) -
          ∑ p : ZMod m, chi (A p) (edge A p) o (B (q + 1) - o))
      = ∑ q : ZMod n, -((∑ p : ZMod m, chi (A p) (edge A p) o (B (q + 1) - o)) -
          ∑ p : ZMod m, chi (A p) (edge A p) o (B q - o)) :=
        Finset.sum_congr rfl (fun q _ => by ring)
    _ = -∑ q : ZMod n, ((∑ p : ZMod m, chi (A p) (edge A p) o (B (q + 1) - o)) -
          ∑ p : ZMod m, chi (A p) (edge A p) o (B q - o)) := Finset.sum_neg_distrib _
    _ = 0 := by rw [hs, neg_zero]

/-- L6 (the fan). For two closed polygons with nonzero edges, no vertex of either on an edge of the
other, the fixed-order signed crossing sum is zero. -/
theorem fan_sum_zero {m n : ℕ} [NeZero m] [NeZero n] (A : LabelledTuple m) (B : LabelledTuple n)
    (hA : ∀ p, edge A p ≠ 0) (hB : ∀ q, edge B q ≠ 0)
    (hAB : ∀ p q, A p ∉ edgeSegment B q) (hBA : ∀ p q, B q ∉ edgeSegment A p) :
    ∑ p : ZMod m, ∑ q : ZMod n, chi (A p) (edge A p) (B q) (edge B q) = 0 := by
  -- the generic auxiliary point `o`: off the lines `A p B q`, off the edge lines of `A`, off the
  -- edge lines of `B`
  have hAB' : ∀ p q, B q - A p ≠ 0 := by
    intro p q h
    apply hAB p q
    have e : A p = B q := (sub_eq_zero.mp h).symm
    rw [e]
    exact ⟨0, le_rfl, zero_le_one, by simp [edgePoint]⟩
  obtain ⟨o, ho⟩ := exists_point_off_lines
    (ι := (ZMod m × ZMod n) ⊕ (ZMod m ⊕ ZMod n))
    (Sum.elim (fun pq => A pq.1) (Sum.elim A B))
    (Sum.elim (fun pq => B pq.2 - A pq.1) (Sum.elim (edge A) (edge B)))
    (by
      rintro (⟨p, q⟩ | p | q)
      · exact hAB' p q
      · exact hA p
      · exact hB q)
  have hoAB : ∀ p q, det (B q - A p) (o - A p) ≠ 0 := fun p q => ho (Sum.inl (p, q))
  have hoA : ∀ p, det (edge A p) (o - A p) ≠ 0 := fun p => ho (Sum.inr (Sum.inl p))
  have hoB : ∀ q, det (edge B q) (o - B q) ≠ 0 := fun q => ho (Sum.inr (Sum.inr q))
  -- each fan triangle has signed crossing count zero with `A`
  have hT : ∀ q : ZMod n, ∑ p : ZMod m, triChi (A p) (edge A p) o (B q) (B (q + 1)) = 0 := by
    intro q
    apply closed_polygon_triangle_sum A o (B q) (B (q + 1))
    · exact det_fan_of_off_line o (B q) (B (q + 1)) (hoB q)
    · intro p hmem
      rcases hmem with (h1 | h2) | h3
      · exact not_mem_closedSeg_radial (hoAB p q) h1
      · exact hAB p q h2
      · exact not_mem_closedSeg_radial' (hoAB p (q + 1)) h3
    · intro p
      exact ⟨not_mem_closedSeg_of_det_ne_zero (hoA p), hBA p q, hBA p (q + 1)⟩
  have hsum : ∑ q : ZMod n, ∑ p : ZMod m, triChi (A p) (edge A p) o (B q) (B (q + 1)) = 0 :=
    Finset.sum_eq_zero (fun q _ => hT q)
  have hsplit : ∀ q : ZMod n, ∑ p : ZMod m, triChi (A p) (edge A p) o (B q) (B (q + 1)) =
      (∑ p : ZMod m, (chi (A p) (edge A p) o (B q - o) +
        chi (A p) (edge A p) (B (q + 1)) (o - B (q + 1)))) +
      ∑ p : ZMod m, chi (A p) (edge A p) (B q) (edge B q) := by
    intro q
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    unfold triChi
    show _ = _ + chi (A p) (edge A p) (B q) (B (q + 1) - B q)
    ring
  have hrad := radial_cancel A B o
  rw [Finset.sum_comm]
  calc ∑ q : ZMod n, ∑ p : ZMod m, chi (A p) (edge A p) (B q) (edge B q)
      = ∑ q : ZMod n, ∑ p : ZMod m, triChi (A p) (edge A p) o (B q) (B (q + 1)) -
        ∑ q : ZMod n, ∑ p : ZMod m, (chi (A p) (edge A p) o (B q - o) +
          chi (A p) (edge A p) (B (q + 1)) (o - B (q + 1))) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun q _ => by rw [hsplit q]; ring)
    _ = 0 := by rw [hsum, hrad, sub_zero]

end

end ZeroLink

/-! ## 6. The statement (verbatim copy of work/drafts/ZeroLink_statement.lean, lines 17-45) -/

open SM.Link Classical

namespace Link.Shadow

/-- The ordered strand pairs `(s, t)` with `s` on component `i`, `t` on component `j`, forming a
crossing: the transverse intersections of the two components in the fixed order `(i, j)`. -/
def MixedPair (Γ : Shadow) (i j : Fin Γ.c) (s t : Γ.Strand) : Prop :=
  s.1 = i ∧ t.1 = j ∧ Γ.IsCrossing {s, t}

end Link.Shadow

/-- The sum of the decorated signs over the mixed crossings between components `i` and `j`. -/
noncomputable def mixedSignSum (D : Diagram) (i j : Fin D.Γ.c) : ℤ :=
  ∑ s : D.Γ.Strand, ∑ t : D.Γ.Strand,
    if h : D.Γ.MixedPair i j s t then ((D.sign ⟨{s, t}, h.2.2⟩ : SignType) : ℤ) else 0

/-- mp:zero-link as printed. -/
structure ZeroLinkData : Prop where
  /-- "For two distinct components of an actual generic oriented plane diagram, the sum of
  `sgn det(u₁, u₂)` over their transverse intersections, in this fixed component order, is zero." -/
  fixed_order_sum : ∀ (D : Diagram) (i j : Fin D.Γ.c), i ≠ j →
    (∑ s : D.Γ.Strand, ∑ t : D.Γ.Strand,
      if D.Γ.MixedPair i j s t then ((SignType.sign (det (D.Γ.dir s) (D.Γ.dir t)) : SignType) : ℤ)
      else 0) = 0
  /-- "Consequently the half-sum of decorated crossing signs is an integer". -/
  half_sum_integer : ∀ (D : Diagram) (i j : Fin D.Γ.c), i ≠ j → ∃ k : ℤ, mixedSignSum D i j = 2 * k
  /-- "and it is zero if one component is always over the other." -/
  over_constant : ∀ (D : Diagram) (i j : Fin D.Γ.c), i ≠ j →
    ((∀ (s t : D.Γ.Strand) (h : D.Γ.MixedPair i j s t), D.overStrand ⟨{s, t}, h.2.2⟩ = s) ∨
     (∀ (s t : D.Γ.Strand) (h : D.Γ.MixedPair i j s t), D.overStrand ⟨{s, t}, h.2.2⟩ = t)) →
    mixedSignSum D i j = 0

/-! ## 7. From the fan to the diagram statement -/

namespace ZeroLink

noncomputable section

variable (D : Diagram)

/-- The fixed-order summand of `ZeroLinkData.fixed_order_sum`. -/
def fixedSummand (i j : Fin D.Γ.c) (s t : D.Γ.Strand) : ℤ :=
  if D.Γ.MixedPair i j s t then ((SignType.sign (det (D.Γ.dir s) (D.Γ.dir t)) : SignType) : ℤ)
  else 0

/-- The decorated summand of `mixedSignSum`. -/
def signSummand (i j : Fin D.Γ.c) (s t : D.Γ.Strand) : ℤ :=
  if h : D.Γ.MixedPair i j s t then ((D.sign ⟨{s, t}, h.2.2⟩ : SignType) : ℤ) else 0

theorem mixedSignSum_eq_sum_signSummand (i j : Fin D.Γ.c) :
    mixedSignSum D i j = ∑ s : D.Γ.Strand, ∑ t : D.Γ.Strand, signSummand D i j s t := rfl

/-! ### Genericity consequences used by the fan -/

/-- Every edge of every component is a nonzero vector (`Generic.regular`). -/
theorem edge_ne_zero (i : Fin D.Γ.c) (p : ZMod (D.Γ.comp i).k) : edge (D.Γ.comp i).P p ≠ 0 :=
  ((regular_iff_edges _).mp (D.generic.regular i) p).1

/-- A vertex of component `i` is on no closed edge of a different component `j` (`Generic.tail_off`;
strands on different components are never incident). -/
theorem vertex_not_mem_other_seg {i j : Fin D.Γ.c} (hij : i ≠ j) (p : ZMod (D.Γ.comp i).k)
    (q : ZMod (D.Γ.comp j).k) : (D.Γ.comp i).P p ∉ edgeSegment (D.Γ.comp j).P q :=
  D.generic.tail_off ⟨i, p⟩ ⟨j, q⟩ (fun h => hij h.fst_eq)

/-- Strands on distinct components are distinct. -/
theorem ne_of_mixedPair {i j : Fin D.Γ.c} (hij : i ≠ j) {s t : D.Γ.Strand}
    (h : D.Γ.MixedPair i j s t) : s ≠ t := by
  intro hst
  apply hij
  rw [← h.1, ← h.2.1, hst]

/-- L7. For `i ≠ j`, the mixed-pair predicate on `(⟨i,p⟩, ⟨j,q⟩)` is the interior meeting of the two
edges: strands on different components are never adjacent, and by `tail_off` any common point of
the closed edges has both parameters in `(0,1)`. -/
theorem mixedPair_iff_meets {i j : Fin D.Γ.c} (hij : i ≠ j) (p : ZMod (D.Γ.comp i).k)
    (q : ZMod (D.Γ.comp j).k) :
    D.Γ.MixedPair i j ⟨i, p⟩ ⟨j, q⟩ ↔
      Meets ((D.Γ.comp i).P p) (edge (D.Γ.comp i).P p) ((D.Γ.comp j).P q) (edge (D.Γ.comp j).P q) := by
  have hne : (⟨i, p⟩ : D.Γ.Strand) ≠ ⟨j, q⟩ := by
    intro h
    exact hij (congrArg Sigma.fst h)
  have hna : ¬ D.Γ.Adjacent ⟨i, p⟩ ⟨j, q⟩ := fun h => hij h.fst_eq
  constructor
  · intro h
    obtain ⟨-, x, ⟨τ, hτ0, hτ1, hx1⟩, ⟨σ, hσ0, hσ1, hx2⟩⟩ :=
      D.Γ.crossing_pair_spec ⟨{⟨i, p⟩, ⟨j, q⟩}, h.2.2⟩ (by simp) (by simp) hne
    have hτ0' : τ ≠ 0 := by
      rintro rfl
      apply vertex_not_mem_other_seg D hij p q
      rw [edgePoint_zero] at hx1
      rw [hx1] at hx2
      exact ⟨σ, hσ0, hσ1, hx2⟩
    have hτ1' : τ ≠ 1 := by
      rintro rfl
      apply vertex_not_mem_other_seg D hij (p + 1) q
      rw [edgePoint_one] at hx1
      rw [hx1] at hx2
      exact ⟨σ, hσ0, hσ1, hx2⟩
    have hσ0' : σ ≠ 0 := by
      rintro rfl
      apply vertex_not_mem_other_seg D hij.symm q p
      rw [edgePoint_zero] at hx2
      rw [hx2] at hx1
      exact ⟨τ, hτ0, hτ1, hx1⟩
    have hσ1' : σ ≠ 1 := by
      rintro rfl
      apply vertex_not_mem_other_seg D hij.symm (q + 1) p
      rw [edgePoint_one] at hx2
      rw [hx2] at hx1
      exact ⟨τ, hτ0, hτ1, hx1⟩
    exact ⟨τ, σ, lt_of_le_of_ne hτ0 hτ0'.symm, lt_of_le_of_ne hτ1 hτ1',
      lt_of_le_of_ne hσ0 hσ0'.symm, lt_of_le_of_ne hσ1 hσ1', hx1.symm.trans hx2⟩
  · rintro ⟨τ, σ, hτ0, hτ1, hσ0, hσ1, heq⟩
    refine ⟨rfl, rfl, D.Γ.isCrossing_pair hna ?_⟩
    exact ⟨(D.Γ.comp i).P p + τ • edge (D.Γ.comp i).P p, ⟨τ, hτ0.le, hτ1.le, rfl⟩,
      ⟨σ, hσ0.le, hσ1.le, heq⟩⟩

theorem fixedSummand_eq_chi {i j : Fin D.Γ.c} (hij : i ≠ j) (p : ZMod (D.Γ.comp i).k)
    (q : ZMod (D.Γ.comp j).k) :
    fixedSummand D i j ⟨i, p⟩ ⟨j, q⟩ =
      chi ((D.Γ.comp i).P p) (edge (D.Γ.comp i).P p) ((D.Γ.comp j).P q) (edge (D.Γ.comp j).P q) := by
  unfold fixedSummand chi
  by_cases h : D.Γ.MixedPair i j ⟨i, p⟩ ⟨j, q⟩
  · rw [ite_eq_left h, ite_eq_left ((mixedPair_iff_meets D hij p q).mp h)]
    rfl
  · rw [ite_eq_right h, ite_eq_right (fun hm => h ((mixedPair_iff_meets D hij p q).mpr hm))]

theorem fixedSummand_eq_zero_left {i j : Fin D.Γ.c} {s t : D.Γ.Strand} (hs : s.1 ≠ i) :
    fixedSummand D i j s t = 0 := by
  unfold fixedSummand
  rw [ite_eq_right]
  rintro ⟨h, -, -⟩
  exact hs h

theorem fixedSummand_eq_zero_right {i j : Fin D.Γ.c} {s t : D.Γ.Strand} (ht : t.1 ≠ j) :
    fixedSummand D i j s t = 0 := by
  unfold fixedSummand
  rw [ite_eq_right]
  rintro ⟨-, h, -⟩
  exact ht h

/-- L8. The double sum over all strands collapses to the strands of `i` and of `j`. -/
theorem sum_fixedSummand_eq (i j : Fin D.Γ.c) :
    ∑ s : D.Γ.Strand, ∑ t : D.Γ.Strand, fixedSummand D i j s t =
      ∑ p : ZMod (D.Γ.comp i).k, ∑ q : ZMod (D.Γ.comp j).k, fixedSummand D i j ⟨i, p⟩ ⟨j, q⟩ := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single i]
  · refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Fintype.sum_sigma, Finset.sum_eq_single j]
    · intro j' _ hj'
      exact Finset.sum_eq_zero (fun q _ => fixedSummand_eq_zero_right D hj')
    · intro h
      exact absurd (Finset.mem_univ j) h
  · intro i' _ hi'
    exact Finset.sum_eq_zero (fun p _ => Finset.sum_eq_zero (fun t _ => fixedSummand_eq_zero_left D hi'))
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The first assertion of mp:zero-link, in the form of `ZeroLinkData.fixed_order_sum`. -/
theorem fixed_order_sum_zero {i j : Fin D.Γ.c} (hij : i ≠ j) :
    ∑ s : D.Γ.Strand, ∑ t : D.Γ.Strand, fixedSummand D i j s t = 0 := by
  rw [sum_fixedSummand_eq]
  have h := fan_sum_zero (D.Γ.comp i).P (D.Γ.comp j).P (edge_ne_zero D i) (edge_ne_zero D j)
    (fun p q => vertex_not_mem_other_seg D hij p q)
    (fun p q => vertex_not_mem_other_seg D hij.symm q p)
  rw [← h]
  exact Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => fixedSummand_eq_chi D hij p q))

/-! ### Decorated signs: `D.sign` is the fixed-order sign or its negative -/

theorem over_eq_or {i j : Fin D.Γ.c} {s t : D.Γ.Strand} (h : D.Γ.MixedPair i j s t) :
    D.overStrand ⟨{s, t}, h.2.2⟩ = s ∨ D.overStrand ⟨{s, t}, h.2.2⟩ = t := by
  have hm := D.over_mem ⟨{s, t}, h.2.2⟩
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hm

theorem sign_of_over_left {i j : Fin D.Γ.c} (hij : i ≠ j) {s t : D.Γ.Strand}
    (h : D.Γ.MixedPair i j s t) (ho : D.overStrand ⟨{s, t}, h.2.2⟩ = s) :
    ((D.sign ⟨{s, t}, h.2.2⟩ : SignType) : ℤ) =
      ((SignType.sign (det (D.Γ.dir s) (D.Γ.dir t)) : SignType) : ℤ) := by
  have ht : t ∈ (⟨{s, t}, h.2.2⟩ : D.Γ.Crossing).val := by simp
  have hu : D.underStrand ⟨{s, t}, h.2.2⟩ = t := by
    symm
    apply D.eq_under_of_mem_of_ne _ ht
    rw [ho]
    exact (ne_of_mixedPair D hij h).symm
  unfold Diagram.sign
  rw [ho, hu]

theorem sign_of_over_right {i j : Fin D.Γ.c} (hij : i ≠ j) {s t : D.Γ.Strand}
    (h : D.Γ.MixedPair i j s t) (ho : D.overStrand ⟨{s, t}, h.2.2⟩ = t) :
    ((D.sign ⟨{s, t}, h.2.2⟩ : SignType) : ℤ) =
      -((SignType.sign (det (D.Γ.dir s) (D.Γ.dir t)) : SignType) : ℤ) := by
  have hs : s ∈ (⟨{s, t}, h.2.2⟩ : D.Γ.Crossing).val := by simp
  have hu : D.underStrand ⟨{s, t}, h.2.2⟩ = s := by
    symm
    apply D.eq_under_of_mem_of_ne _ hs
    rw [ho]
    exact ne_of_mixedPair D hij h
  unfold Diagram.sign
  rw [ho, hu, det_swap, Left.sign_neg]
  simp

/-- The correction term: `-σ` at the mixed crossings where the over strand is on `j`, else `0`. -/
def corr (i j : Fin D.Γ.c) (s t : D.Γ.Strand) : ℤ :=
  if h : D.Γ.MixedPair i j s t then
    (if D.overStrand ⟨{s, t}, h.2.2⟩ = t then
      -((SignType.sign (det (D.Γ.dir s) (D.Γ.dir t)) : SignType) : ℤ) else 0)
  else 0

/-- L9. Decorated summand = fixed-order summand + twice the correction. -/
theorem signSummand_eq {i j : Fin D.Γ.c} (hij : i ≠ j) (s t : D.Γ.Strand) :
    signSummand D i j s t = fixedSummand D i j s t + 2 * corr D i j s t := by
  unfold signSummand fixedSummand corr
  by_cases h : D.Γ.MixedPair i j s t
  · rw [dite_eq_left h, ite_eq_left h, dite_eq_left h]
    rcases over_eq_or D h with ho | ho
    · rw [ite_eq_right (by rw [ho]; exact ne_of_mixedPair D hij h), sign_of_over_left D hij h ho]
      ring
    · rw [ite_eq_left ho, sign_of_over_right D hij h ho]
      ring
  · rw [dite_eq_right h, ite_eq_right h, dite_eq_right h]
    ring

theorem mixedSignSum_eq {i j : Fin D.Γ.c} (hij : i ≠ j) :
    mixedSignSum D i j = ∑ s : D.Γ.Strand, ∑ t : D.Γ.Strand, fixedSummand D i j s t +
      2 * ∑ s : D.Γ.Strand, ∑ t : D.Γ.Strand, corr D i j s t := by
  rw [mixedSignSum_eq_sum_signSummand, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun t _ => signSummand_eq D hij s t)

/-- The second assertion: the decorated sum is even. -/
theorem mixedSignSum_eq_two_mul {i j : Fin D.Γ.c} (hij : i ≠ j) :
    mixedSignSum D i j = 2 * ∑ s : D.Γ.Strand, ∑ t : D.Γ.Strand, corr D i j s t := by
  rw [mixedSignSum_eq D hij, fixed_order_sum_zero D hij, zero_add]

theorem corr_eq_zero_of_over_left {i j : Fin D.Γ.c}
    (hL : ∀ (s t : D.Γ.Strand) (h : D.Γ.MixedPair i j s t), D.overStrand ⟨{s, t}, h.2.2⟩ = s)
    (hij : i ≠ j) (s t : D.Γ.Strand) : corr D i j s t = 0 := by
  unfold corr
  by_cases h : D.Γ.MixedPair i j s t
  · rw [dite_eq_left h, ite_eq_right]
    rw [hL s t h]
    exact ne_of_mixedPair D hij h
  · rw [dite_eq_right h]

theorem signSummand_eq_neg_of_over_right {i j : Fin D.Γ.c} (hij : i ≠ j)
    (hR : ∀ (s t : D.Γ.Strand) (h : D.Γ.MixedPair i j s t), D.overStrand ⟨{s, t}, h.2.2⟩ = t)
    (s t : D.Γ.Strand) : signSummand D i j s t = - fixedSummand D i j s t := by
  unfold signSummand fixedSummand
  by_cases h : D.Γ.MixedPair i j s t
  · rw [dite_eq_left h, ite_eq_left h, sign_of_over_right D hij h (hR s t h)]
  · rw [dite_eq_right h, ite_eq_right h, neg_zero]

/-- The third assertion: constant over-component gives decorated sum `0`. -/
theorem mixedSignSum_eq_zero_of_over_constant {i j : Fin D.Γ.c} (hij : i ≠ j)
    (h : (∀ (s t : D.Γ.Strand) (h : D.Γ.MixedPair i j s t), D.overStrand ⟨{s, t}, h.2.2⟩ = s) ∨
      (∀ (s t : D.Γ.Strand) (h : D.Γ.MixedPair i j s t), D.overStrand ⟨{s, t}, h.2.2⟩ = t)) :
    mixedSignSum D i j = 0 := by
  rcases h with hL | hR
  · rw [mixedSignSum_eq D hij, fixed_order_sum_zero D hij, zero_add]
    have : ∑ s : D.Γ.Strand, ∑ t : D.Γ.Strand, corr D i j s t = 0 :=
      Finset.sum_eq_zero (fun s _ => Finset.sum_eq_zero (fun t _ => corr_eq_zero_of_over_left D hL hij s t))
    rw [this, mul_zero]
  · rw [mixedSignSum_eq_sum_signSummand]
    have : ∑ s : D.Γ.Strand, ∑ t : D.Γ.Strand, signSummand D i j s t =
        - ∑ s : D.Γ.Strand, ∑ t : D.Γ.Strand, fixedSummand D i j s t := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun t _ => signSummand_eq_neg_of_over_right D hij hR s t)
    rw [this, fixed_order_sum_zero D hij, neg_zero]

end

end ZeroLink

/-- mp:zero-link, assembled from the chain (sorry-free given the chain lemmas). -/
theorem zero_link : ZeroLinkData where
  fixed_order_sum := fun D _ _ hij => ZeroLink.fixed_order_sum_zero D hij
  half_sum_integer := fun D _ _ hij => ⟨_, ZeroLink.mixedSignSum_eq_two_mul D hij⟩
  over_constant := fun D _ _ hij h => ZeroLink.mixedSignSum_eq_zero_of_over_constant D hij h

end SM
