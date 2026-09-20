import SM.LinkDiagram

/-! Ported 2026-09-13 from work/drafts/zerolink/Skeleton_FINAL.lean (design-panel winner A, fully proved by the designer; judge-merged; checked with `lake env lean`, no placeholder, standard axioms). The statement part (module docstring, `Shadow.MixedPair`, `mixedSignSum`, `ZeroLinkData`, the signature of `zero_link`) is verbatim work/drafts/ZeroLink_statement.lean; plan work/drafts/zerolink/PLAN_FINAL.md; cross-check draft work/drafts/zerolink/Skeleton_B.lean (independent partial design). Row mp:zero-link → `SM.zero_link`. -/

/-! Source mp:zero-link (reference/SM/sm-3-statesum.tex:1538-1545, frame SM15): mixed signed crossings in
a stack. Main declaration: `SM.zero_link`.

Notation (namespace `SM.Link`): "an actual generic oriented plane diagram" is `D : Diagram`; its
components are `Fin D.Γ.c`; a strand `s : D.Γ.Strand` lies on component `s.1` with direction `D.Γ.dir s`
(the oriented edge vector `u`); "the transverse intersections of two distinct components `i ≠ j`, in this
fixed component order" are the crossings `{s, t}` with `s` on `i` and `t` on `j` (`Shadow.MixedPair`; each
mixed crossing between `i` and `j` is exactly one such ordered pair), and `sgn det(u₁, u₂)` is
`SignType.sign (det (D.Γ.dir s) (D.Γ.dir t))`; "the decorated crossing signs" are `D.sign x =
sgn det(u_over, u_under)` (def:positive-lift); "one component is always over the other" is: at every
mixed crossing the over strand lies on `i`, or at every mixed crossing it lies on `j`. -/

namespace SM

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

namespace ZeroLink

/-! ======================= UNIT 1 (OneDim) — assumes nothing beyond Mathlib ======================= -/
/-! ## Part 1. One-dimensional counting for a finite family of affine functions

A convex region cut out by finitely many open half-planes, restricted to a parametrised segment
`t ↦ a + t • u`, `t ∈ [0,1]`, is `{t | ∀ g, 0 < φ g t}` for affine `φ g t = c g + t * d g`.
An *event* is a transverse crossing of the boundary side `g` at a parameter in `(0,1)`: `φ g` has a
zero there with nonzero slope and all other `φ g'` are positive (the crossing point is in the open
side).  The lemma `affine_family_count` says the inside indicator changes by the signed number of
events — the printed "as many entries as exits" for one triangle, in one dimension. -/

section OneDim

variable {ι : Type*}

/-- `φ g t = c g + t * d g`. -/
def affEval (c d : ι → ℝ) (g : ι) (t : ℝ) : ℝ := c g + t * d g

/-- The zero of `φ g` (meaningful when `d g ≠ 0`). -/
noncomputable def zeroAt (c d : ι → ℝ) (g : ι) : ℝ := -c g / d g

/-- A transverse boundary crossing at side `g`, at a parameter strictly inside `(0,1)`, at a point
of the open side (all other half-plane functions positive). -/
def IsEvent (c d : ι → ℝ) (g : ι) : Prop :=
  d g ≠ 0 ∧ 0 < zeroAt c d g ∧ zeroAt c d g < 1 ∧
    ∀ g', g' ≠ g → 0 < affEval c d g' (zeroAt c d g)

/-- Genericity of the family on `[0,1]`: no two functions vanish at a common parameter (the path
misses the vertices of the region) and neither endpoint is an event point (the endpoints are off
the boundary). -/
structure GenericFamily (c d : ι → ℝ) : Prop where
  no_double_zero : ∀ t, 0 ≤ t → t ≤ 1 → ∀ g g', g ≠ g' →
    affEval c d g t = 0 → affEval c d g' t ≠ 0
  start_off : ∀ g, affEval c d g 0 = 0 → ∃ g', g' ≠ g ∧ affEval c d g' 0 ≤ 0
  end_off : ∀ g, affEval c d g 1 = 0 → ∃ g', g' ≠ g ∧ affEval c d g' 1 ≤ 0

variable (c d : ι → ℝ)

theorem affEval_zeroAt {g : ι} (hd : d g ≠ 0) : affEval c d g (zeroAt c d g) = 0 := by
  unfold affEval zeroAt
  field_simp
  ring

theorem affEval_eq_mul {g : ι} (hd : d g ≠ 0) (t : ℝ) :
    affEval c d g t = d g * (t - zeroAt c d g) := by
  unfold affEval zeroAt
  field_simp
  ring

theorem affEval_pos_iff_of_pos {g : ι} (hd : 0 < d g) (t : ℝ) :
    0 < affEval c d g t ↔ zeroAt c d g < t := by
  rw [affEval_eq_mul c d hd.ne']
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have : d g * (t - zeroAt c d g) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hd.le (by linarith)
    linarith
  · intro h
    exact mul_pos hd (by linarith)

theorem affEval_pos_iff_of_neg {g : ι} (hd : d g < 0) (t : ℝ) :
    0 < affEval c d g t ↔ t < zeroAt c d g := by
  rw [affEval_eq_mul c d hd.ne]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have : d g * (t - zeroAt c d g) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hd.le (by linarith)
    linarith
  · intro h
    exact mul_pos_of_neg_of_neg hd (by linarith)

/-- Affine functions: nonnegative at `t₀`, positive at `t₁`, hence positive on `(t₀, t₁]`. -/
theorem affEval_pos_of_between {g : ι} {t₀ t₁ t : ℝ} (h0 : 0 ≤ affEval c d g t₀)
    (h1 : 0 < affEval c d g t₁) (ht : t₀ < t) (ht' : t ≤ t₁) : 0 < affEval c d g t := by
  unfold affEval at *
  have key : (t₁ - t₀) * (c g + t * d g) =
      (t₁ - t) * (c g + t₀ * d g) + (t - t₀) * (c g + t₁ * d g) := by ring
  have hpos : 0 < (t₁ - t) * (c g + t₀ * d g) + (t - t₀) * (c g + t₁ * d g) := by
    have := mul_nonneg (by linarith : (0:ℝ) ≤ t₁ - t) h0
    have := mul_pos (by linarith : (0:ℝ) < t - t₀) h1
    linarith
  rw [← key] at hpos
  exact pos_of_mul_pos_right hpos (by linarith)

/-- Affine functions: positive at `t₀`, nonnegative at `t₁`, hence positive on `[t₀, t₁)`. -/
theorem affEval_pos_of_between' {g : ι} {t₀ t₁ t : ℝ} (h0 : 0 < affEval c d g t₀)
    (h1 : 0 ≤ affEval c d g t₁) (ht : t₀ ≤ t) (ht' : t < t₁) : 0 < affEval c d g t := by
  unfold affEval at *
  have key : (t₁ - t₀) * (c g + t * d g) =
      (t₁ - t) * (c g + t₀ * d g) + (t - t₀) * (c g + t₁ * d g) := by ring
  have hpos : 0 < (t₁ - t) * (c g + t₀ * d g) + (t - t₀) * (c g + t₁ * d g) := by
    have := mul_pos (by linarith : (0:ℝ) < t₁ - t) h0
    have := mul_nonneg (by linarith : (0:ℝ) ≤ t - t₀) h1
    linarith
  rw [← key] at hpos
  exact pos_of_mul_pos_right hpos (by linarith)

/-- Two entries (events with positive slope) coincide: at the earlier one the later function is
still negative, contradicting "all other functions positive". -/
theorem entry_unique {g₁ g₂ : ι} (h₁ : IsEvent c d g₁) (h₂ : IsEvent c d g₂) (hd₁ : 0 < d g₁)
    (hd₂ : 0 < d g₂) : g₁ = g₂ := by
  by_contra hne
  rcases le_total (zeroAt c d g₁) (zeroAt c d g₂) with h | h
  · have hpos := h₁.2.2.2 g₂ (Ne.symm hne)
    rw [affEval_pos_iff_of_pos c d hd₂] at hpos
    linarith
  · have hpos := h₂.2.2.2 g₁ hne
    rw [affEval_pos_iff_of_pos c d hd₁] at hpos
    linarith

/-- Two exits (events with negative slope) coincide. -/
theorem exit_unique {g₁ g₂ : ι} (h₁ : IsEvent c d g₁) (h₂ : IsEvent c d g₂) (hd₁ : d g₁ < 0)
    (hd₂ : d g₂ < 0) : g₁ = g₂ := by
  by_contra hne
  rcases le_total (zeroAt c d g₁) (zeroAt c d g₂) with h | h
  · have hpos := h₂.2.2.2 g₁ hne
    rw [affEval_pos_iff_of_neg c d hd₁] at hpos
    linarith
  · have hpos := h₁.2.2.2 g₂ (Ne.symm hne)
    rw [affEval_pos_iff_of_neg c d hd₂] at hpos
    linarith

/-- The reflected family `t ↦ 1 - t`: `φ' g t = φ g (1 - t)`. -/
def reflC : ι → ℝ := fun g => c g + d g

/-- Slopes of the reflected family. -/
def reflD : ι → ℝ := fun g => -d g

theorem affEval_refl (g : ι) (t : ℝ) : affEval (reflC c d) (reflD d) g t = affEval c d g (1 - t) := by
  unfold affEval reflC reflD
  ring

theorem zeroAt_refl {g : ι} (hd : d g ≠ 0) : zeroAt (reflC c d) (reflD d) g = 1 - zeroAt c d g := by
  unfold zeroAt reflC reflD
  field_simp
  ring

theorem isEvent_refl_iff (g : ι) : IsEvent (reflC c d) (reflD d) g ↔ IsEvent c d g := by
  unfold IsEvent
  constructor
  · rintro ⟨hd, h0, h1, hoth⟩
    have hd' : d g ≠ 0 := by simpa [reflD] using hd
    rw [zeroAt_refl c d hd'] at h0 h1 hoth
    refine ⟨hd', by linarith, by linarith, fun g' hg' => ?_⟩
    have := hoth g' hg'
    rw [affEval_refl] at this
    simpa using this
  · rintro ⟨hd, h0, h1, hoth⟩
    have hd' : reflD d g ≠ 0 := by simpa [reflD] using hd
    refine ⟨hd', ?_, ?_, fun g' hg' => ?_⟩
    · rw [zeroAt_refl c d hd]; linarith
    · rw [zeroAt_refl c d hd]; linarith
    · rw [zeroAt_refl c d hd, affEval_refl]
      simpa using hoth g' hg'

theorem genericFamily_refl (H : GenericFamily c d) : GenericFamily (reflC c d) (reflD d) where
  no_double_zero := by
    intro t ht0 ht1 g g' hgg' h
    rw [affEval_refl] at h ⊢
    exact H.no_double_zero (1 - t) (by linarith) (by linarith) g g' hgg' h
  start_off := by
    intro g h
    rw [affEval_refl, sub_zero] at h
    obtain ⟨g', hg', hle⟩ := H.end_off g h
    exact ⟨g', hg', by rw [affEval_refl, sub_zero]; exact hle⟩
  end_off := by
    intro g h
    rw [affEval_refl, sub_self] at h
    obtain ⟨g', hg', hle⟩ := H.start_off g h
    exact ⟨g', hg', by rw [affEval_refl, sub_self]; exact hle⟩

variable [Fintype ι]

/-- The inside indicator `[∀ g, 0 < φ g t]` as an integer. -/
noncomputable def inside (c d : ι → ℝ) (t : ℝ) : ℤ := if ∀ g, 0 < affEval c d g t then 1 else 0

theorem inside_eq_one_iff (t : ℝ) : inside c d t = 1 ↔ ∀ g, 0 < affEval c d g t := by
  unfold inside
  split_ifs with h
  · simp [h]
  · simp [h]

theorem inside_eq_zero_iff (t : ℝ) : inside c d t = 0 ↔ ∃ g, affEval c d g t ≤ 0 := by
  unfold inside
  split_ifs with h
  · simp only [one_ne_zero, false_iff, not_exists, not_le]
    exact h
  · simp only [true_iff]
    push Not at h
    exact h

theorem inside_eq_zero_or_one (t : ℝ) : inside c d t = 0 ∨ inside c d t = 1 := by
  unfold inside
  split_ifs <;> simp

/-- An entry has `φ g 0 < 0`, so the path starts outside. -/
theorem not_entry_of_inside_zero {g : ι} (h0 : inside c d 0 = 1) (he : IsEvent c d g) : d g < 0 := by
  rcases lt_or_gt_of_ne he.1 with h | h
  · exact h
  · exfalso
    have := (inside_eq_one_iff c d 0).mp h0 g
    rw [affEval_pos_iff_of_pos c d h] at this
    linarith [he.2.1]

/-- An exit has `φ g 1 < 0`, so the path ends outside. -/
theorem not_exit_of_inside_one {g : ι} (h1 : inside c d 1 = 1) (he : IsEvent c d g) : 0 < d g := by
  rcases lt_or_gt_of_ne he.1 with h | h
  · exfalso
    have := (inside_eq_one_iff c d 1).mp h1 g
    rw [affEval_pos_iff_of_neg c d h] at this
    linarith [he.2.2.1]
  · exact h

/-- First-zero argument.  From a parameter `t₀` at which all functions are `≥ 0` and the vanishing
ones are increasing, if the path ends outside there is an exit event after `t₀`: take the function
with `φ g 1 ≤ 0` whose zero comes first; the others are positive there (the later zeros are strictly
later by `no_double_zero`; the never-vanishing ones by affinity), and the zero is `< 1` by
`end_off`. -/
theorem exists_exit_event (H : GenericFamily c d) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (ht₀1 : t₀ < 1)
    (hα : ∀ g, 0 ≤ affEval c d g t₀) (hβ : ∀ g, affEval c d g t₀ = 0 → 0 < d g)
    (hγ : ∃ g, affEval c d g 1 ≤ 0) :
    ∃ g, IsEvent c d g ∧ d g < 0 ∧ t₀ < zeroAt c d g := by
  classical
  set S : Finset ι := Finset.univ.filter fun g => affEval c d g 1 ≤ 0 with hS
  have hSne : S.Nonempty := by
    obtain ⟨g, hg⟩ := hγ
    exact ⟨g, by simp [hS, hg]⟩
  have hmem : ∀ g ∈ S, 0 < affEval c d g t₀ ∧ d g < 0 ∧ t₀ < zeroAt c d g ∧ zeroAt c d g ≤ 1 := by
    intro g hg
    have hg1 : affEval c d g 1 ≤ 0 := by simpa [hS] using hg
    have hlin : affEval c d g 1 = affEval c d g t₀ + (1 - t₀) * d g := by unfold affEval; ring
    have hpos : 0 < affEval c d g t₀ := by
      rcases (hα g).lt_or_eq with h | h
      · exact h
      · exfalso
        have hd := hβ g h.symm
        nlinarith
    have hd : d g < 0 := by
      by_contra hcon
      push Not at hcon
      nlinarith
    refine ⟨hpos, hd, (affEval_pos_iff_of_neg c d hd t₀).mp hpos, ?_⟩
    by_contra hcon
    push Not at hcon
    have := (affEval_pos_iff_of_neg c d hd 1).mpr hcon
    linarith
  obtain ⟨g₀, hg₀S, hmin⟩ := Finset.exists_min_image S (zeroAt c d) hSne
  obtain ⟨hpos₀, hd₀, hz₀, hz₀1⟩ := hmem g₀ hg₀S
  have hothers : ∀ g', g' ≠ g₀ → 0 < affEval c d g' (zeroAt c d g₀) := by
    intro g' hg'
    by_cases hg'S : g' ∈ S
    · obtain ⟨-, hd', -, -⟩ := hmem g' hg'S
      have hle : zeroAt c d g₀ ≤ zeroAt c d g' := hmin g' hg'S
      have hnonneg : 0 ≤ affEval c d g' (zeroAt c d g₀) := by
        rw [affEval_eq_mul c d hd'.ne]
        exact mul_nonneg_of_nonpos_of_nonpos hd'.le (by linarith)
      rcases hnonneg.lt_or_eq with h | h
      · exact h
      · exfalso
        exact H.no_double_zero (zeroAt c d g₀) (by linarith) hz₀1 g₀ g' (Ne.symm hg')
          (affEval_zeroAt c d hd₀.ne) h.symm
    · have hg'1 : 0 < affEval c d g' 1 := by
        by_contra hcon
        push Not at hcon
        exact hg'S (by simp [hS, hcon])
      exact affEval_pos_of_between c d (hα g') hg'1 hz₀ hz₀1
  have hz1 : zeroAt c d g₀ < 1 := by
    rcases hz₀1.lt_or_eq with h | h
    · exact h
    · exfalso
      obtain ⟨g', hg', hle⟩ := H.end_off g₀ (by rw [← h]; exact affEval_zeroAt c d hd₀.ne)
      have := hothers g' hg'
      rw [h] at this
      linarith
  exact ⟨g₀, ⟨hd₀.ne, by linarith, hz1, hothers⟩, hd₀, hz₀⟩

/-- Last-zero argument, obtained from `exists_exit_event` for the reflected family. -/
theorem exists_entry_event (H : GenericFamily c d) {t₁ : ℝ} (ht₁ : 0 < t₁) (ht₁1 : t₁ ≤ 1)
    (hα : ∀ g, 0 ≤ affEval c d g t₁) (hβ : ∀ g, affEval c d g t₁ = 0 → d g < 0)
    (hγ : ∃ g, affEval c d g 0 ≤ 0) :
    ∃ g, IsEvent c d g ∧ 0 < d g ∧ zeroAt c d g < t₁ := by
  have H' := genericFamily_refl c d H
  obtain ⟨g, hev, hd, hz⟩ := exists_exit_event (reflC c d) (reflD d) H' (t₀ := 1 - t₁)
    (by linarith) (by linarith)
    (fun g => by rw [affEval_refl, sub_sub_cancel]; exact hα g)
    (fun g h => by
      rw [affEval_refl, sub_sub_cancel] at h
      have := hβ g h
      simp only [reflD]
      linarith)
    (by
      obtain ⟨g, hg⟩ := hγ
      exact ⟨g, by rw [affEval_refl, sub_self]; exact hg⟩)
  have hd' : 0 < d g := by simpa [reflD] using hd
  rw [zeroAt_refl c d hd'.ne'] at hz
  exact ⟨g, (isEvent_refl_iff c d g).mp hev, hd', by linarith⟩

/-- Starting inside and ending outside forces an exit (`t₀ = 0`). -/
theorem exists_exit_of_one_zero (H : GenericFamily c d) (h0 : inside c d 0 = 1)
    (h1 : inside c d 1 = 0) : ∃ g, IsEvent c d g ∧ d g < 0 := by
  have hall := (inside_eq_one_iff c d 0).mp h0
  obtain ⟨g, hev, hd, -⟩ := exists_exit_event c d H (t₀ := 0) le_rfl zero_lt_one
    (fun g => (hall g).le) (fun g h => absurd h (hall g).ne') ((inside_eq_zero_iff c d 1).mp h1)
  exact ⟨g, hev, hd⟩

/-- Starting outside and ending inside forces an entry (`t₁ = 1`). -/
theorem exists_entry_of_zero_one (H : GenericFamily c d) (h0 : inside c d 0 = 0)
    (h1 : inside c d 1 = 1) : ∃ g, IsEvent c d g ∧ 0 < d g := by
  have hall := (inside_eq_one_iff c d 1).mp h1
  obtain ⟨g, hev, hd, -⟩ := exists_entry_event c d H (t₁ := 1) zero_lt_one le_rfl
    (fun g => (hall g).le) (fun g h => absurd h (hall g).ne') ((inside_eq_zero_iff c d 0).mp h0)
  exact ⟨g, hev, hd⟩

/-- Outside at both ends: an entry forces a later exit (`t₀ = zeroAt c d g⁺`) and an exit forces an
earlier entry (`t₁ = zeroAt c d g⁻`). -/
theorem entry_iff_exit_of_zero_zero (H : GenericFamily c d) (h0 : inside c d 0 = 0)
    (h1 : inside c d 1 = 0) :
    (∃ g, IsEvent c d g ∧ 0 < d g) ↔ (∃ g, IsEvent c d g ∧ d g < 0) := by
  constructor
  · rintro ⟨g, ⟨hd, hz0, hz1, hoth⟩, hdpos⟩
    obtain ⟨g', hev', hd', -⟩ := exists_exit_event c d H (t₀ := zeroAt c d g) hz0.le hz1
      (fun g' => by
        by_cases hg' : g' = g
        · subst hg'; rw [affEval_zeroAt c d hd]
        · exact (hoth g' hg').le)
      (fun g' h => by
        by_cases hg' : g' = g
        · subst hg'; exact hdpos
        · exact absurd h (hoth g' hg').ne')
      ((inside_eq_zero_iff c d 1).mp h1)
    exact ⟨g', hev', hd'⟩
  · rintro ⟨g, ⟨hd, hz0, hz1, hoth⟩, hdneg⟩
    obtain ⟨g', hev', hd', -⟩ := exists_entry_event c d H (t₁ := zeroAt c d g) hz0 hz1.le
      (fun g' => by
        by_cases hg' : g' = g
        · subst hg'; rw [affEval_zeroAt c d hd]
        · exact (hoth g' hg').le)
      (fun g' h => by
        by_cases hg' : g' = g
        · subst hg'; exact hdneg
        · exact absurd h (hoth g' hg').ne')
      ((inside_eq_zero_iff c d 0).mp h0)
    exact ⟨g', hev', hd'⟩

/-- A predicate with at most one witness has indicator sum `[∃ g, P g]`. -/
theorem sum_ite_unique (P : ι → Prop) [DecidablePred P] (hP : ∀ g g', P g → P g' → g = g') :
    (∑ g, if P g then (1 : ℤ) else 0) = if ∃ g, P g then 1 else 0 := by
  split_ifs with h
  · obtain ⟨g₀, hg₀⟩ := h
    rw [Fintype.sum_eq_single g₀]
    · simp [hg₀]
    · intro g hg
      have : ¬ P g := fun hPg => hg (hP g g₀ hPg hg₀)
      simp [this]
  · push Not at h
    exact Finset.sum_eq_zero fun g _ => by simp [h g]

/-- Split the signed event sum into entries minus exits. -/
theorem sum_event_sign_eq :
    (∑ g, if IsEvent c d g then ((SignType.sign (d g) : SignType) : ℤ) else 0) =
      (∑ g, if IsEvent c d g ∧ 0 < d g then (1 : ℤ) else 0) -
      (∑ g, if IsEvent c d g ∧ d g < 0 then (1 : ℤ) else 0) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases he : IsEvent c d g
  · rcases lt_or_gt_of_ne he.1 with h | h
    · simp [he, h, not_lt.mpr h.le, sign_eq_neg_one_iff.mpr h]
    · simp [he, h, not_lt.mpr h.le, sign_eq_one_iff.mpr h]
  · simp [he]

/-- **The one-dimensional count.** The inside indicator of a generic affine family changes from
`t = 0` to `t = 1` by the sum of the event slopes' signs: entries `+1`, exits `-1`. -/
theorem affine_family_count (H : GenericFamily c d) :
    inside c d 1 - inside c d 0 =
      ∑ g, if IsEvent c d g then ((SignType.sign (d g) : SignType) : ℤ) else 0 := by
  rw [sum_event_sign_eq, sum_ite_unique _ (fun g g' h h' => entry_unique c d h.1 h'.1 h.2 h'.2),
    sum_ite_unique _ (fun g g' h h' => exit_unique c d h.1 h'.1 h.2 h'.2)]
  rcases inside_eq_zero_or_one c d 0 with h0 | h0 <;>
    rcases inside_eq_zero_or_one c d 1 with h1 | h1
  · have hiff := entry_iff_exit_of_zero_zero c d H h0 h1
    by_cases hE : ∃ g, IsEvent c d g ∧ 0 < d g
    · simp only [h0, h1, ite_eq_left hE, ite_eq_left (hiff.mp hE)]
      norm_num
    · simp only [h0, h1, ite_eq_right hE, ite_eq_right (fun h => hE (hiff.mpr h))]
  · have hE := exists_entry_of_zero_one c d H h0 h1
    have hX : ¬ ∃ g, IsEvent c d g ∧ d g < 0 := by
      rintro ⟨g, hev, hd⟩
      exact absurd (not_exit_of_inside_one c d h1 hev) (not_lt.mpr hd.le)
    simp only [h0, h1, ite_eq_left hE, ite_eq_right hX]
  · have hX : ¬ ∃ g, IsEvent c d g ∧ 0 < d g := by
      rintro ⟨g, hev, hd⟩
      exact absurd (not_entry_of_inside_zero c d h0 hev) (not_lt.mpr hd.le)
    have hE := exists_exit_of_one_zero c d H h0 h1
    simp only [h0, h1, ite_eq_right hX, ite_eq_left hE]
  · have hX1 : ¬ ∃ g, IsEvent c d g ∧ 0 < d g := by
      rintro ⟨g, hev, hd⟩
      exact absurd (not_entry_of_inside_zero c d h0 hev) (not_lt.mpr hd.le)
    have hX2 : ¬ ∃ g, IsEvent c d g ∧ d g < 0 := by
      rintro ⟨g, hev, hd⟩
      exact absurd (not_exit_of_inside_one c d h1 hev) (not_lt.mpr hd.le)
    simp only [h0, h1, ite_eq_right hX1, ite_eq_right hX2]
    norm_num

end OneDim

/-! ======================= UNIT 2 (Triangle) — assumes Unit 1 ======================= -/
/-! ## Part 2. Segments and fan triangles in the plane -/

section Triangle

/-- The closed segment from `a` to `b`, parametrised as the accepted `edgeSegment`. -/
def Seg (a b : Plane) : Set Plane := {x | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = a + t • (b - a)}

theorem edgeSegment_eq_Seg {n : ℕ} (P : LabelledTuple n) (i : ZMod n) :
    edgeSegment P i = Seg (P i) (P (i + 1)) := rfl

theorem Seg_symm (a b : Plane) : Seg a b = Seg b a := by
  have key : ∀ a b : Plane, Seg a b ⊆ Seg b a := by
    rintro a b x ⟨t, h0, h1, rfl⟩
    refine ⟨1 - t, by linarith, by linarith, ?_⟩
    ext <;> simp <;> ring
  exact Set.Subset.antisymm (key a b) (key b a)

theorem left_mem_Seg (a b : Plane) : a ∈ Seg a b := ⟨0, le_rfl, zero_le_one, by simp⟩

theorem right_mem_Seg (a b : Plane) : b ∈ Seg a b := ⟨1, zero_le_one, le_rfl, by simp⟩

/-- A point off the line of `[a, b]` is off the segment. -/
theorem not_mem_Seg_of_det {a b x : Plane} (h : det (b - a) (x - a) ≠ 0) : x ∉ Seg a b := by
  rintro ⟨t, -, -, rfl⟩
  apply h
  simp only [add_sub_cancel_left]
  exact det_smul_self _ _

/-- Two lines with independent directions through the same point meet only there. -/
theorem eq_of_two_dets {d₁ d₂ p x : Plane} (hd : det d₁ d₂ ≠ 0) (h₁ : det d₁ (x - p) = 0)
    (h₂ : det d₂ (x - p) = 0) : x = p := by
  unfold det at hd h₁ h₂
  simp only [Prod.fst_sub, Prod.snd_sub] at h₁ h₂
  have e1 : (d₁.1 * d₂.2 - d₁.2 * d₂.1) * (x.1 - p.1) = 0 := by
    linear_combination d₂.1 * h₁ - d₁.1 * h₂
  have e2 : (d₁.1 * d₂.2 - d₁.2 * d₂.1) * (x.2 - p.2) = 0 := by
    linear_combination d₂.2 * h₁ - d₁.2 * h₂
  have hx1 := (mul_eq_zero.mp e1).resolve_left hd
  have hx2 := (mul_eq_zero.mp e2).resolve_left hd
  ext <;> linarith

/-- `(sign x)² = 1` for `x ≠ 0`. -/
theorem coe_sign_mul_self {x : ℝ} (hx : x ≠ 0) :
    ((SignType.sign x : SignType) : ℤ) * ((SignType.sign x : SignType) : ℤ) = 1 := by
  rcases lt_or_gt_of_ne hx with h | h
  · rw [sign_eq_neg_one_iff.mpr h]; decide
  · rw [sign_eq_one_iff.mpr h]; decide

theorem coe_sign_mul (x y : ℝ) :
    ((SignType.sign (x * y) : SignType) : ℤ) =
      ((SignType.sign x : SignType) : ℤ) * ((SignType.sign y : SignType) : ℤ) := by
  rw [sign_mul]; simp

theorem coe_sign_det_swap (u w : Plane) :
    ((SignType.sign (det w u) : SignType) : ℤ) = -((SignType.sign (det u w) : SignType) : ℤ) := by
  rw [det_swap, Left.sign_neg, SignType.coe_neg]

variable (o v w : Plane)

/-- Tails of the three oriented sides of the triangle chain `[o, v, w]`: `[o,v]`, `[v,w]`, `[w,o]`. -/
def triTail : Fin 3 → Plane := ![o, v, w]

/-- Heads of the three oriented sides. -/
def triHead : Fin 3 → Plane := ![v, w, o]

/-- Direction vectors of the three oriented sides. -/
def triDir (g : Fin 3) : Plane := triHead o v w g - triTail o v w g

/-- The closed sides. -/
def triSide (g : Fin 3) : Set Plane := Seg (triTail o v w g) (triHead o v w g)

/-- "Its coefficient relative to the usual positive plane orientation is its determinant sign":
the orientation determinant `det(v - o, w - o)` of the triangle. -/
def triD : ℝ := det (v - o) (w - o)

/-- The side-line function of side `g`: `det(dir g, x - tail g)`; positive on the left of the side. -/
def lineFn (g : Fin 3) (x : Plane) : ℝ := det (triDir o v w g) (x - triTail o v w g)

/-- The open-triangle indicator: `x` is on the `triD`-side (left for a positive triangle, right for
a negative one) of all three side lines. -/
noncomputable def triInside (x : Plane) : ℤ :=
  if ∀ g, 0 < triD o v w * lineFn o v w g x then 1 else 0

theorem triHead_eq_triTail_succ (g : Fin 3) : triHead o v w g = triTail o v w (g + 1) := by
  fin_cases g <;> rfl

theorem mem_triSide_iff (g : Fin 3) (x : Plane) :
    x ∈ triSide o v w g ↔ ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ x = triTail o v w g + s • triDir o v w g :=
  Iff.rfl

theorem triSide_zero : triSide o v w 0 = Seg o v := rfl
theorem triSide_one : triSide o v w 1 = Seg v w := rfl
theorem triSide_two : triSide o v w 2 = Seg w o := rfl
theorem triDir_zero : triDir o v w 0 = v - o := rfl
theorem triDir_one : triDir o v w 1 = w - v := rfl
theorem triDir_two : triDir o v w 2 = o - w := rfl

/-- The side-line function is affine along a parametrised segment. -/
theorem lineFn_add_smul (g : Fin 3) (a u : Plane) (t : ℝ) :
    lineFn o v w g (a + t • u) = lineFn o v w g a + t * det (triDir o v w g) u := by
  unfold lineFn
  rw [add_sub_right_comm, det_add_right, det_smul_right]

/-- Barycentric reconstruction (Cramer): every point is `o + α(v-o) + β(w-o)` with
`α = lineFn 2 x / triD`, `β = lineFn 0 x / triD`. -/
theorem tri_reconstruct (hD : triD o v w ≠ 0) (x : Plane) :
    x = o + (lineFn o v w 2 x / triD o v w) • (v - o) + (lineFn o v w 0 x / triD o v w) • (w - o) := by
  have k1 : triD o v w * (x.1 - o.1) =
      lineFn o v w 2 x * (v.1 - o.1) + lineFn o v w 0 x * (w.1 - o.1) := by
    unfold lineFn triDir triHead triTail triD
    simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    unfold det
    simp only [Prod.fst_sub, Prod.snd_sub]
    ring
  have k2 : triD o v w * (x.2 - o.2) =
      lineFn o v w 2 x * (v.2 - o.2) + lineFn o v w 0 x * (w.2 - o.2) := by
    unfold lineFn triDir triHead triTail triD
    simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    unfold det
    simp only [Prod.fst_sub, Prod.snd_sub]
    ring
  ext
  · simp only [Prod.fst_add, Prod.fst_sub, Prod.smul_fst, smul_eq_mul]
    field_simp
    linear_combination k1
  · simp only [Prod.snd_add, Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
    field_simp
    linear_combination k2

/-- The three side-line functions sum to the orientation determinant. -/
theorem lineFn_sum (x : Plane) :
    lineFn o v w 0 x + lineFn o v w 1 x + lineFn o v w 2 x = triD o v w := by
  unfold lineFn triDir triHead triTail triD
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  unfold det
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

theorem div_pos_of_mul_pos' {D L : ℝ} (hD : D ≠ 0) (h : 0 < D * L) : 0 < L / D := by
  rw [← mul_div_mul_left L D hD]
  exact div_pos h (mul_self_pos.mpr hD)

/-- Values of the three side-line functions at a point of side `g` with parameter `s`: zero on its
own line, `(1 - s) * triD` on the next side's line, `s * triD` on the previous side's line. -/
theorem lineFn_openSide_vals (g : Fin 3) (s : ℝ) :
    lineFn o v w g (triTail o v w g + s • triDir o v w g) = 0 ∧
    lineFn o v w (g + 1) (triTail o v w g + s • triDir o v w g) = (1 - s) * triD o v w ∧
    lineFn o v w (g + 2) (triTail o v w g + s • triDir o v w g) = s * triD o v w := by
  fin_cases g <;> refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [lineFn, triDir, triHead, triTail, triD, det, Fin.zero_eta, Fin.isValue, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, zero_add, Fin.reduceAdd, Prod.fst_add, Prod.snd_add,
      Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    try ring

theorem fin3_ne_cases {g g' : Fin 3} (h : g' ≠ g) : g' = g + 1 ∨ g' = g + 2 := by
  fin_cases g <;> fin_cases g' <;> simp_all

/-- Two side lines meet only at the common vertex. -/
theorem vertex_of_two_lineFn (hD : triD o v w ≠ 0) {g g' : Fin 3} (hgg' : g ≠ g') {x : Plane}
    (h : lineFn o v w g x = 0) (h' : lineFn o v w g' x = 0) : ∃ g'', x = triTail o v w g'' := by
  have hx := tri_reconstruct o v w hD x
  have hs := lineFn_sum o v w x
  fin_cases g <;> fin_cases g' <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one,
    Fin.reduceFinMk, ne_eq, Fin.reduceEq, not_true_eq_false, not_false_eq_true] at hgg' h h' ⊢
  · refine ⟨1, hx.trans ?_⟩
    have h2 : lineFn o v w 2 x = triD o v w := by linarith
    rw [h2, h, div_self hD, zero_div, one_smul, zero_smul, add_zero]
    show o + (v - o) = v
    abel
  · refine ⟨0, hx.trans ?_⟩
    rw [h, h', zero_div, zero_smul, zero_smul, add_zero, add_zero]
    rfl
  · refine ⟨1, hx.trans ?_⟩
    have h2 : lineFn o v w 2 x = triD o v w := by linarith
    rw [h2, h', div_self hD, zero_div, one_smul, zero_smul, add_zero]
    show o + (v - o) = v
    abel
  · refine ⟨2, hx.trans ?_⟩
    have h0 : lineFn o v w 0 x = triD o v w := by linarith
    rw [h0, h', div_self hD, zero_div, one_smul, zero_smul, add_zero]
    show o + (w - o) = w
    abel
  · refine ⟨0, hx.trans ?_⟩
    rw [h, h', zero_div, zero_smul, zero_smul, add_zero, add_zero]
    rfl
  · refine ⟨2, hx.trans ?_⟩
    have h0 : lineFn o v w 0 x = triD o v w := by linarith
    rw [h0, h, div_self hD, zero_div, one_smul, zero_smul, add_zero]
    show o + (w - o) = w
    abel

/-- A point of the open side `g` is on its line and strictly on the triangle side of the other two
lines ("the triangle lies consistently on the left of its positive boundary"). -/
theorem lineFn_of_mem_openSide (hD : triD o v w ≠ 0) (g : Fin 3) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    lineFn o v w g (triTail o v w g + s • triDir o v w g) = 0 ∧
      ∀ g', g' ≠ g → 0 < triD o v w * lineFn o v w g' (triTail o v w g + s • triDir o v w g) := by
  obtain ⟨h0, h1, h2⟩ := lineFn_openSide_vals o v w g s
  refine ⟨h0, fun g' hg' => ?_⟩
  have hDD := mul_self_pos.mpr hD
  rcases fin3_ne_cases hg' with rfl | rfl
  · rw [h1]
    nlinarith
  · rw [h2]
    nlinarith

/-- Conversely, a point on the line of side `g` strictly on the triangle side of the other two
lines lies on the open side `g`. -/
theorem mem_openSide_of_lineFn (hD : triD o v w ≠ 0) (g : Fin 3) {x : Plane}
    (h0 : lineFn o v w g x = 0) (hpos : ∀ g', g' ≠ g → 0 < triD o v w * lineFn o v w g' x) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ x = triTail o v w g + s • triDir o v w g := by
  have hx := tri_reconstruct o v w hD x
  have hs := lineFn_sum o v w x
  have hp1 := hpos (g + 1) (by fin_cases g <;> decide)
  have hp2 := hpos (g + 2) (by fin_cases g <;> decide)
  refine ⟨lineFn o v w (g + 2) x / triD o v w, div_pos_of_mul_pos' hD hp2, ?_, ?_⟩
  · have hsum : lineFn o v w (g + 1) x + lineFn o v w (g + 2) x = triD o v w := by
      fin_cases g <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk,
        Fin.reduceAdd, zero_add] at h0 ⊢ <;> linarith
    have : 1 - lineFn o v w (g + 2) x / triD o v w = lineFn o v w (g + 1) x / triD o v w := by
      field_simp
      linarith
    have := div_pos_of_mul_pos' hD hp1
    linarith
  · fin_cases g <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk,
        Fin.reduceAdd, zero_add] at h0 hp1 hp2 ⊢
    · calc x = o + (lineFn o v w 2 x / triD o v w) • (v - o) +
            (lineFn o v w 0 x / triD o v w) • (w - o) := hx
        _ = triTail o v w 0 + (lineFn o v w 2 x / triD o v w) • triDir o v w 0 := by
          rw [h0, zero_div, zero_smul, add_zero]
          rfl
    · have hα : lineFn o v w 2 x / triD o v w = 1 - lineFn o v w 0 x / triD o v w := by
        field_simp
        linarith
      calc x = o + (lineFn o v w 2 x / triD o v w) • (v - o) +
            (lineFn o v w 0 x / triD o v w) • (w - o) := hx
        _ = triTail o v w 1 + (lineFn o v w 0 x / triD o v w) • triDir o v w 1 := by
          rw [hα]
          show _ = v + (lineFn o v w 0 x / triD o v w) • (w - v)
          ext <;> simp <;> ring
    · have hβ : lineFn o v w 1 x / triD o v w = 1 - lineFn o v w 0 x / triD o v w := by
        field_simp
        linarith
      calc x = o + (lineFn o v w 2 x / triD o v w) • (v - o) +
            (lineFn o v w 0 x / triD o v w) • (w - o) := hx
        _ = triTail o v w 2 + (lineFn o v w 1 x / triD o v w) • triDir o v w 2 := by
          rw [hβ, h0, zero_div, zero_smul, add_zero]
          show _ = w + (1 - lineFn o v w 0 x / triD o v w) • (o - w)
          ext <;> simp <;> ring

/-- The affine family of the segment `[a, b]` against the triangle: `c g = triD * lineFn g a`,
`d g = triD * det(dir g, b - a)`. -/
def segC (a _b : Plane) : Fin 3 → ℝ := fun g => triD o v w * lineFn o v w g a

/-- Slopes of the segment family. -/
def segD (a b : Plane) : Fin 3 → ℝ := fun g => triD o v w * det (triDir o v w g) (b - a)

theorem affEval_seg (a b : Plane) (g : Fin 3) (t : ℝ) :
    affEval (segC o v w a b) (segD o v w a b) g t = triD o v w * lineFn o v w g (a + t • (b - a)) := by
  unfold affEval segC segD
  rw [lineFn_add_smul]
  ring

theorem inside_seg_zero (a b : Plane) : inside (segC o v w a b) (segD o v w a b) 0 = triInside o v w a := by
  unfold inside triInside
  simp only [affEval_seg, zero_smul, add_zero]

theorem inside_seg_one (a b : Plane) : inside (segC o v w a b) (segD o v w a b) 1 = triInside o v w b := by
  unfold inside triInside
  simp only [affEval_seg, one_smul, add_sub_cancel]

/-- Genericity of the segment `[a, b]` against the triangle `(o, v, w)`: transverse to every side it
meets, containing no vertex, with both endpoints off the boundary. -/
structure SegGeneric (a b : Plane) : Prop where
  hD : triD o v w ≠ 0
  transverse : ∀ g, (Seg a b ∩ triSide o v w g).Nonempty → det (b - a) (triDir o v w g) ≠ 0
  no_vertex : ∀ g, triTail o v w g ∉ Seg a b
  start_off : ∀ g, a ∉ triSide o v w g
  end_off : ∀ g, b ∉ triSide o v w g

/-- An event of the segment family is exactly a meeting of `[a, b]` with a (closed) side. -/
theorem isEvent_iff_meets {a b : Plane} (hg : SegGeneric o v w a b) (g : Fin 3) :
    IsEvent (segC o v w a b) (segD o v w a b) g ↔ (Seg a b ∩ triSide o v w g).Nonempty := by
  have hD := hg.hD
  constructor
  · rintro ⟨hd, hz0, hz1, hoth⟩
    have h0 : lineFn o v w g (a + zeroAt (segC o v w a b) (segD o v w a b) g • (b - a)) = 0 := by
      have := affEval_zeroAt (segC o v w a b) (segD o v w a b) hd
      rw [affEval_seg] at this
      exact (mul_eq_zero.mp this).resolve_left hD
    have hpos : ∀ g', g' ≠ g →
        0 < triD o v w * lineFn o v w g' (a + zeroAt (segC o v w a b) (segD o v w a b) g • (b - a)) := by
      intro g' hg'
      have := hoth g' hg'
      rwa [affEval_seg] at this
    obtain ⟨s, hs0, hs1, hxs⟩ := mem_openSide_of_lineFn o v w hD g h0 hpos
    exact ⟨_, ⟨_, hz0.le, hz1.le, rfl⟩, (mem_triSide_iff o v w g _).mpr ⟨s, hs0.le, hs1.le, hxs⟩⟩
  · rintro ⟨x, ⟨t, ht0, ht1, rfl⟩, hxg⟩
    obtain ⟨s, hs0, hs1, hxs⟩ := (mem_triSide_iff o v w g _).mp hxg
    have hmeet : (Seg a b ∩ triSide o v w g).Nonempty := ⟨_, ⟨t, ht0, ht1, rfl⟩, hxg⟩
    have hdet := hg.transverse g hmeet
    have hd : segD o v w a b g ≠ 0 := by
      unfold segD
      rw [det_swap]
      exact mul_ne_zero hD (neg_ne_zero.mpr hdet)
    have hs0' : 0 < s := by
      rcases hs0.lt_or_eq with h | h
      · exact h
      · exfalso
        apply hg.no_vertex g
        rw [← h, zero_smul, add_zero] at hxs
        exact ⟨t, ht0, ht1, hxs.symm⟩
    have hs1' : s < 1 := by
      rcases hs1.lt_or_eq with h | h
      · exact h
      · exfalso
        apply hg.no_vertex (g + 1)
        rw [← triHead_eq_triTail_succ]
        rw [h, one_smul] at hxs
        refine ⟨t, ht0, ht1, ?_⟩
        rw [hxs]
        unfold triDir
        abel
    obtain ⟨h0, hpos⟩ := lineFn_of_mem_openSide o v w hD g hs0' hs1'
    rw [← hxs] at h0 hpos
    have ht_eq : t = zeroAt (segC o v w a b) (segD o v w a b) g := by
      have h1 : affEval (segC o v w a b) (segD o v w a b) g t = 0 := by
        rw [affEval_seg, h0, mul_zero]
      rw [affEval_eq_mul _ _ hd] at h1
      have := (mul_eq_zero.mp h1).resolve_left hd
      linarith
    have ht0' : 0 < t := by
      rcases ht0.lt_or_eq with h | h
      · exact h
      · exfalso
        apply hg.start_off g
        rw [← h, zero_smul, add_zero] at hxs
        exact (mem_triSide_iff o v w g _).mpr ⟨s, hs0, hs1, hxs⟩
    have ht1' : t < 1 := by
      rcases ht1.lt_or_eq with h | h
      · exact h
      · exfalso
        apply hg.end_off g
        rw [h, one_smul, add_sub_cancel] at hxs
        exact (mem_triSide_iff o v w g _).mpr ⟨s, hs0, hs1, hxs⟩
    refine ⟨hd, ht_eq ▸ ht0', ht_eq ▸ ht1', fun g' hg' => ?_⟩
    rw [← ht_eq, affEval_seg]
    exact hpos g' hg'

/-- The segment family of a generic segment is a generic affine family. -/
theorem genericFamily_seg {a b : Plane} (hg : SegGeneric o v w a b) :
    GenericFamily (segC o v w a b) (segD o v w a b) where
  no_double_zero := by
    intro t ht0 ht1 g g' hgg' h h'
    rw [affEval_seg] at h h'
    have h0 := (mul_eq_zero.mp h).resolve_left hg.hD
    have h0' := (mul_eq_zero.mp h').resolve_left hg.hD
    obtain ⟨g'', hx⟩ := vertex_of_two_lineFn o v w hg.hD hgg' h0 h0'
    exact hg.no_vertex g'' ⟨t, ht0, ht1, hx.symm⟩
  start_off := by
    intro g h
    by_contra hcon
    push Not at hcon
    rw [affEval_seg, zero_smul, add_zero] at h
    have h0 := (mul_eq_zero.mp h).resolve_left hg.hD
    have hpos : ∀ g', g' ≠ g → 0 < triD o v w * lineFn o v w g' a := by
      intro g' hg'
      have := hcon g' hg'
      rwa [affEval_seg, zero_smul, add_zero] at this
    obtain ⟨s, hs0, hs1, hxs⟩ := mem_openSide_of_lineFn o v w hg.hD g h0 hpos
    exact hg.start_off g ((mem_triSide_iff o v w g _).mpr ⟨s, hs0.le, hs1.le, hxs⟩)
  end_off := by
    intro g h
    by_contra hcon
    push Not at hcon
    rw [affEval_seg, one_smul, add_sub_cancel] at h
    have h0 := (mul_eq_zero.mp h).resolve_left hg.hD
    have hpos : ∀ g', g' ≠ g → 0 < triD o v w * lineFn o v w g' b := by
      intro g' hg'
      have := hcon g' hg'
      rwa [affEval_seg, one_smul, add_sub_cancel] at this
    obtain ⟨s, hs0, hs1, hxs⟩ := mem_openSide_of_lineFn o v w hg.hD g h0 hpos
    exact hg.end_off g ((mem_triSide_iff o v w g _).mpr ⟨s, hs0.le, hs1.le, hxs⟩)

/-- **One edge against one triangle** (printed: "At an entry the ordered tangent pair (path,
triangle boundary) has the opposite determinant sign from an exit").  The signed intersection sum of
the segment `[a, b]` with the oriented boundary of the triangle equals `sgn(triD)` times the drop of
the inside indicator. -/
theorem tri_edge_count {a b : Plane} (hg : SegGeneric o v w a b) :
    (∑ g : Fin 3, if (Seg a b ∩ triSide o v w g).Nonempty then
        ((SignType.sign (det (b - a) (triDir o v w g)) : SignType) : ℤ) else 0) =
      ((SignType.sign (triD o v w) : SignType) : ℤ) * (triInside o v w a - triInside o v w b) := by
  have hcount := affine_family_count (segC o v w a b) (segD o v w a b) (genericFamily_seg o v w hg)
  rw [inside_seg_zero, inside_seg_one] at hcount
  have hD := hg.hD
  set σ : ℤ := ((SignType.sign (triD o v w) : SignType) : ℤ) with hσ
  have hσσ : σ * σ = 1 := coe_sign_mul_self hD
  set S : ℤ := ∑ g : Fin 3, (if (Seg a b ∩ triSide o v w g).Nonempty then
        ((SignType.sign (det (b - a) (triDir o v w g)) : SignType) : ℤ) else 0) with hS
  have hsum : (∑ g, if IsEvent (segC o v w a b) (segD o v w a b) g then
      ((SignType.sign (segD o v w a b g) : SignType) : ℤ) else 0) = -σ * S := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases h : (Seg a b ∩ triSide o v w g).Nonempty
    · rw [ite_eq_left ((isEvent_iff_meets o v w hg g).mpr h), ite_eq_left h]
      unfold segD
      rw [coe_sign_mul, coe_sign_det_swap]
      ring
    · rw [ite_eq_right (fun h' => h ((isEvent_iff_meets o v w hg g).mp h')), ite_eq_right h, mul_zero]
  rw [hsum] at hcount
  linear_combination σ * hcount - S * hσσ

/-- Telescoping around a cyclic index set. -/
theorem zmod_telescope {n : ℕ} [NeZero n] (f : ZMod n → ℤ) : ∑ q : ZMod n, (f q - f (q + 1)) = 0 := by
  rw [Finset.sum_sub_distrib]
  have h := Equiv.sum_comp (Equiv.addRight (1 : ZMod n)) f
  simp only [Equiv.coe_addRight] at h
  rw [h, sub_self]

/-- **One closed polygon against one triangle** (printed: "For one positively oriented triangle, a
closed transverse path has as many entries into its interior as exits, counted with sign ... Thus
its algebraic intersection sum with that boundary is zero. Reversing triangle orientation negates
the sum and still gives zero."). -/
theorem tri_polygon_sum {m : ℕ} [NeZero m] (A : LabelledTuple m)
    (hg : ∀ p, SegGeneric o v w (A p) (A (p + 1))) :
    (∑ p : ZMod m, ∑ g : Fin 3, if (edgeSegment A p ∩ triSide o v w g).Nonempty then
        ((SignType.sign (det (edge A p) (triDir o v w g)) : SignType) : ℤ) else 0) = 0 := by
  have h : ∀ p, (∑ g : Fin 3, if (edgeSegment A p ∩ triSide o v w g).Nonempty then
        ((SignType.sign (det (edge A p) (triDir o v w g)) : SignType) : ℤ) else 0) =
      ((SignType.sign (triD o v w) : SignType) : ℤ) *
        (triInside o v w (A p) - triInside o v w (A (p + 1))) := by
    intro p
    rw [edgeSegment_eq_Seg]
    exact tri_edge_count o v w (hg p)
  rw [Finset.sum_congr rfl fun p _ => h p, ← Finset.mul_sum,
    zmod_telescope (fun p => triInside o v w (A p)), mul_zero]

end Triangle

/-! ======================= UNIT 3 (ApexFan) — assumes Unit 2 ======================= -/
/-! ## Part 3. The auxiliary apex `o`

"Choose an auxiliary point `o` off the finitely many lines and intersections that would make a fan
triangle degenerate or a radial edge nongeneric against component 1. A finite union of proper lines
and points cannot fill the plane, so such `o` exists." -/

section Apex

/-- A finite family of lines `(base, direction)` with nonzero directions misses some point: pick a
slope `μ` with `(1, μ)` parallel to none of them (finitely many forbidden slopes), then on the line
`s ↦ s • (1, μ)` each forbidden line is hit at most once (finitely many forbidden `s`). -/
theorem exists_point_off_finite_lines (L : Finset (Plane × Plane)) (hL : ∀ ℓ ∈ L, ℓ.2 ≠ 0) :
    ∃ o : Plane, ∀ ℓ ∈ L, det ℓ.2 (o - ℓ.1) ≠ 0 := by
  obtain ⟨μ, hμ⟩ := Infinite.exists_notMem_finset (L.image fun ℓ => ℓ.2.2 / ℓ.2.1)
  have hdir : ∀ ℓ ∈ L, det ℓ.2 ((1 : ℝ), μ) ≠ 0 := by
    intro ℓ hℓ h
    unfold det at h
    simp only [mul_one] at h
    by_cases h1 : ℓ.2.1 = 0
    · have h2 : ℓ.2.2 = 0 := by rw [h1] at h; linarith
      exact hL ℓ hℓ (Prod.ext h1 h2)
    · apply hμ
      rw [Finset.mem_image]
      refine ⟨ℓ, hℓ, ?_⟩
      field_simp
      linarith
  obtain ⟨s, hs⟩ := Infinite.exists_notMem_finset
    (L.image fun ℓ => det ℓ.2 ℓ.1 / det ℓ.2 ((1 : ℝ), μ))
  refine ⟨s • ((1 : ℝ), μ), fun ℓ hℓ h => hs ?_⟩
  rw [Finset.mem_image]
  refine ⟨ℓ, hℓ, ?_⟩
  have hd := hdir ℓ hℓ
  rw [sub_eq_add_neg, det_add_right, det_smul_right] at h
  have hneg : det ℓ.2 (-ℓ.1) = -det ℓ.2 ℓ.1 := by unfold det; simp; ring
  rw [hneg] at h
  field_simp
  linarith

/-- The apex for the fan of `B` against `A`: off the lines of the edges of `B` (nondegenerate
triangles), off the lines through the vertices of `B` parallel to the edges of `A` (radial sides
transverse to every edge of `A`), off the lines of the edges of `A` (no radial side hits a vertex of
`A` at `o`), and off the lines through a vertex of `A` and a vertex of `B` (no vertex of `A` on a
radial side). -/
theorem exists_good_apex {m n : ℕ} [NeZero m] [NeZero n] (A : LabelledTuple m) (B : LabelledTuple n)
    (hA : ∀ p, edge A p ≠ 0) (hB : ∀ q, edge B q ≠ 0) (hAB : ∀ p q, A p ∉ edgeSegment B q) :
    ∃ o : Plane, (∀ q, triD o (B q) (B (q + 1)) ≠ 0) ∧ (∀ p q, det (edge A p) (B q - o) ≠ 0) ∧
      (∀ p, o ∉ edgeSegment A p) ∧ (∀ p q, A p ∉ Seg o (B q)) := by
  classical
  let L1 : Finset (Plane × Plane) := Finset.univ.image fun q : ZMod n => (B q, edge B q)
  let L2 : Finset (Plane × Plane) :=
    Finset.univ.image fun pq : ZMod m × ZMod n => (B pq.2, edge A pq.1)
  let L3 : Finset (Plane × Plane) := Finset.univ.image fun p : ZMod m => (A p, edge A p)
  let L4 : Finset (Plane × Plane) :=
    Finset.univ.image fun pq : ZMod m × ZMod n => (A pq.1, B pq.2 - A pq.1)
  have hL : ∀ ℓ ∈ L1 ∪ L2 ∪ L3 ∪ L4, ℓ.2 ≠ 0 := by
    intro ℓ hℓ
    simp only [L1, L2, L3, L4, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hℓ
    rcases hℓ with ((⟨q, rfl⟩ | ⟨pq, rfl⟩) | ⟨p, rfl⟩) | ⟨pq, rfl⟩
    · exact hB q
    · exact hA pq.1
    · exact hA p
    · intro h
      apply hAB pq.1 pq.2
      have hEq : A pq.1 = B pq.2 := (sub_eq_zero.mp h).symm
      rw [hEq]
      exact ⟨0, le_rfl, zero_le_one, by simp [edgePoint]⟩
  obtain ⟨o, ho⟩ := exists_point_off_finite_lines _ hL
  have h1 : ∀ q, det (edge B q) (o - B q) ≠ 0 := fun q =>
    ho (B q, edge B q) (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image_of_mem (fun q : ZMod n => (B q, edge B q)) (Finset.mem_univ q)))))
  have h2 : ∀ p q, det (edge A p) (o - B q) ≠ 0 := fun p q =>
    ho (B q, edge A p) (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun pq : ZMod m × ZMod n => (B pq.2, edge A pq.1))
        (Finset.mem_univ (p, q))))))
  have h3 : ∀ p, det (edge A p) (o - A p) ≠ 0 := fun p =>
    ho (A p, edge A p) (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun p : ZMod m => (A p, edge A p)) (Finset.mem_univ p))))
  have h4 : ∀ p q, det (B q - A p) (o - A p) ≠ 0 := fun p q =>
    ho (A p, B q - A p) (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun pq : ZMod m × ZMod n => (A pq.1, B pq.2 - A pq.1))
        (Finset.mem_univ (p, q))))
  refine ⟨o, fun q => ?_, fun p q => ?_, fun p => ?_, fun p q => ?_⟩
  · have : triD o (B q) (B (q + 1)) = det (edge B q) (o - B q) := by
      unfold triD edge det
      simp only [Prod.fst_sub, Prod.snd_sub]
      ring
    rw [this]
    exact h1 q
  · intro h
    apply h2 p q
    have : det (edge A p) (o - B q) = -det (edge A p) (B q - o) := by
      unfold det
      simp only [Prod.fst_sub, Prod.snd_sub]
      ring
    rw [this, h, neg_zero]
  · rintro ⟨t, -, -, ht⟩
    apply h3 p
    rw [ht]
    unfold edgePoint
    rw [add_sub_cancel_left]
    exact det_smul_self _ _
  · rintro ⟨t, -, -, ht⟩
    apply h4 p q
    rw [ht]
    unfold det
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    ring

end Apex

/-! ## Part 4. The fan: radial cancellation and the boundary chain -/

section Fan

variable {m n : ℕ} [NeZero m] [NeZero n] (A : LabelledTuple m) (B : LabelledTuple n)

omit [NeZero m] [NeZero n] in
/-- Every edge of `A` is generic against every fan triangle `[o, B q, B (q+1)]` of a good apex. -/
theorem segGeneric_fan (o : Plane) (hAB : ∀ p q, A p ∉ edgeSegment B q) (hBA : ∀ p q, B q ∉ edgeSegment A p)
    (htr : ∀ p q, (edgeSegment A p ∩ edgeSegment B q).Nonempty → det (edge A p) (edge B q) ≠ 0)
    (ho₁ : ∀ q, triD o (B q) (B (q + 1)) ≠ 0) (ho₂ : ∀ p q, det (edge A p) (B q - o) ≠ 0)
    (ho₃ : ∀ p, o ∉ edgeSegment A p) (ho₄ : ∀ p q, A p ∉ Seg o (B q)) (p : ZMod m) (q : ZMod n) :
    SegGeneric o (B q) (B (q + 1)) (A p) (A (p + 1)) where
  hD := ho₁ q
  transverse := by
    intro g hmeet
    fin_cases g
    · exact ho₂ p q
    · exact htr p q hmeet
    · intro h
      apply ho₂ p (q + 1)
      have : det (edge A p) (B (q + 1) - o) = -det (edge A p) (o - B (q + 1)) := by
        unfold det
        simp only [Prod.fst_sub, Prod.snd_sub]
        ring
      have h' : det (A (p + 1) - A p) (o - B (q + 1)) = 0 := h
      rw [this]
      show -det (A (p + 1) - A p) (o - B (q + 1)) = 0
      rw [h', neg_zero]
  no_vertex := by
    intro g
    fin_cases g
    · exact ho₃ p
    · exact hBA p q
    · exact hBA p (q + 1)
  start_off := by
    intro g
    fin_cases g
    · exact ho₄ p q
    · exact hAB p q
    · show A p ∉ Seg (B (q + 1)) o
      rw [Seg_symm]
      exact ho₄ p (q + 1)
  end_off := by
    intro g
    fin_cases g
    · exact ho₄ (p + 1) q
    · exact hAB (p + 1) q
    · show A (p + 1) ∉ Seg (B (q + 1)) o
      rw [Seg_symm]
      exact ho₄ (p + 1) (q + 1)

/-- The signed intersection sum of `A` with the radial segment `[o, B q]`. -/
noncomputable def radialSum (o : Plane) (q : ZMod n) : ℤ :=
  ∑ p : ZMod m, if (edgeSegment A p ∩ Seg o (B q)).Nonempty then
    ((SignType.sign (det (edge A p) (B q - o)) : SignType) : ℤ) else 0

omit [NeZero n] in
/-- The three sides of the fan triangle `q`: radial `[o, B q]`, the edge `B q`, and the reversed
radial `[B (q+1), o]` ("each radial edge occurs once in each orientation and cancels"). -/
theorem fan_triangle_sides (o : Plane) (q : ZMod n) :
    (∑ p : ZMod m, ∑ g : Fin 3, if (edgeSegment A p ∩ triSide o (B q) (B (q + 1)) g).Nonempty then
        ((SignType.sign (det (edge A p) (triDir o (B q) (B (q + 1)) g)) : SignType) : ℤ) else 0) =
      radialSum A B o q +
        (∑ p : ZMod m, if (edgeSegment A p ∩ edgeSegment B q).Nonempty then
          ((SignType.sign (det (edge A p) (edge B q)) : SignType) : ℤ) else 0) -
        radialSum A B o (q + 1) := by
  unfold radialSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Fin.sum_univ_three]
  have h0 : (if (edgeSegment A p ∩ triSide o (B q) (B (q + 1)) 0).Nonempty then
        ((SignType.sign (det (edge A p) (triDir o (B q) (B (q + 1)) 0)) : SignType) : ℤ) else 0) =
      (if (edgeSegment A p ∩ Seg o (B q)).Nonempty then
        ((SignType.sign (det (edge A p) (B q - o)) : SignType) : ℤ) else 0) := rfl
  have h1 : (if (edgeSegment A p ∩ triSide o (B q) (B (q + 1)) 1).Nonempty then
        ((SignType.sign (det (edge A p) (triDir o (B q) (B (q + 1)) 1)) : SignType) : ℤ) else 0) =
      (if (edgeSegment A p ∩ edgeSegment B q).Nonempty then
        ((SignType.sign (det (edge A p) (edge B q)) : SignType) : ℤ) else 0) := rfl
  have h2 : (if (edgeSegment A p ∩ triSide o (B q) (B (q + 1)) 2).Nonempty then
        ((SignType.sign (det (edge A p) (triDir o (B q) (B (q + 1)) 2)) : SignType) : ℤ) else 0) =
      -(if (edgeSegment A p ∩ Seg o (B (q + 1))).Nonempty then
        ((SignType.sign (det (edge A p) (B (q + 1) - o)) : SignType) : ℤ) else 0) := by
    rw [triSide_two, triDir_two, Seg_symm]
    have : det (edge A p) (o - B (q + 1)) = -det (edge A p) (B (q + 1) - o) := by
      unfold det
      simp only [Prod.fst_sub, Prod.snd_sub]
      ring
    rw [this, Left.sign_neg, SignType.coe_neg, neg_ite, neg_zero]
  rw [h0, h1, h2]
  ring

/-- **The fan theorem** (printed: "Their boundary chain is exactly component 2. Hence the
intersection sum of components 1 and 2 is zero."). -/
theorem fan_sum_zero (hA : ∀ p, edge A p ≠ 0) (hB : ∀ q, edge B q ≠ 0)
    (hAB : ∀ p q, A p ∉ edgeSegment B q) (hBA : ∀ p q, B q ∉ edgeSegment A p)
    (htr : ∀ p q, (edgeSegment A p ∩ edgeSegment B q).Nonempty → det (edge A p) (edge B q) ≠ 0) :
    (∑ p : ZMod m, ∑ q : ZMod n, if (edgeSegment A p ∩ edgeSegment B q).Nonempty then
        ((SignType.sign (det (edge A p) (edge B q)) : SignType) : ℤ) else 0) = 0 := by
  obtain ⟨o, ho₁, ho₂, ho₃, ho₄⟩ := exists_good_apex A B hA hB hAB
  have hq : ∀ q, (∑ p : ZMod m, if (edgeSegment A p ∩ edgeSegment B q).Nonempty then
          ((SignType.sign (det (edge A p) (edge B q)) : SignType) : ℤ) else 0) =
        radialSum A B o (q + 1) - radialSum A B o q := by
    intro q
    have h1 := fan_triangle_sides A B o q
    have h2 := tri_polygon_sum o (B q) (B (q + 1)) A
      (fun p => segGeneric_fan A B o hAB hBA htr ho₁ ho₂ ho₃ ho₄ p q)
    linarith
  rw [Finset.sum_comm, Finset.sum_congr rfl fun q _ => hq q]
  calc ∑ q : ZMod n, (radialSum A B o (q + 1) - radialSum A B o q)
      = -∑ q : ZMod n, (radialSum A B o q - radialSum A B o (q + 1)) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun q _ => by ring
    _ = 0 := by rw [zmod_telescope, neg_zero]

end Fan

/-! ======================= UNIT 4 (Diagram + assembly) — assumes Unit 3 ======================= -/
/-! ## Part 5. From the diagram to the two polygons, and the sign bookkeeping -/

section Diagram

/-- Strands on different components are never adjacent, so a mixed pair is a crossing exactly when
the closed edges meet. -/
theorem isCrossing_pair_iff_of_fst_ne (Γ : Shadow) {s t : Γ.Strand} (hst : s.1 ≠ t.1) :
    Γ.IsCrossing {s, t} ↔ (Γ.seg s ∩ Γ.seg t).Nonempty := by
  have hna : ¬ Γ.Adjacent s t := fun h => hst h.fst_eq
  constructor
  · rintro ⟨s', t', hx, -, hmeet⟩
    have hne : s ≠ t := fun h => hst (congrArg Sigma.fst h)
    have hs : s ∈ ({s', t'} : Finset Γ.Strand) := by rw [← hx]; simp
    have ht : t ∈ ({s', t'} : Finset Γ.Strand) := by rw [← hx]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact absurd rfl hne
    · exact hmeet
    · rwa [Set.inter_comm]
    · exact absurd rfl hne
  · intro hmeet
    exact Γ.isCrossing_pair hna hmeet

theorem mixedPair_iff (Γ : Shadow) {i j : Fin Γ.c} (hij : i ≠ j) (s t : Γ.Strand) :
    Γ.MixedPair i j s t ↔ s.1 = i ∧ t.1 = j ∧ (Γ.seg s ∩ Γ.seg t).Nonempty := by
  unfold Shadow.MixedPair
  constructor
  · rintro ⟨hs, ht, hx⟩
    exact ⟨hs, ht, (isCrossing_pair_iff_of_fst_ne Γ (by rw [hs, ht]; exact hij)).mp hx⟩
  · rintro ⟨hs, ht, hx⟩
    exact ⟨hs, ht, (isCrossing_pair_iff_of_fst_ne Γ (by rw [hs, ht]; exact hij)).mpr hx⟩

/-- A sum over the strands supported on component `i` is a sum over the edges of component `i`. -/
theorem sum_sigma_fst_eq {c : ℕ} {k : Fin c → ℕ} [∀ i, NeZero (k i)] (i : Fin c)
    (F : (Σ i', ZMod (k i')) → ℤ) (hF : ∀ s, s.1 ≠ i → F s = 0) :
    ∑ s, F s = ∑ p : ZMod (k i), F ⟨i, p⟩ := by
  rw [Fintype.sum_sigma]
  apply Fintype.sum_eq_single i
  intro i' hi'
  exact Finset.sum_eq_zero fun p _ => hF ⟨i', p⟩ hi'

/-- The fixed-order signed intersection sum of the printed statement. -/
noncomputable def fixedOrderSum (D : Diagram) (i j : Fin D.Γ.c) : ℤ :=
  ∑ s : D.Γ.Strand, ∑ t : D.Γ.Strand,
    if D.Γ.MixedPair i j s t then ((SignType.sign (det (D.Γ.dir s) (D.Γ.dir t)) : SignType) : ℤ)
    else 0

/-- The fixed-order sum is the polygon sum of the two components. -/
theorem fixedOrderSum_eq_polygon_sum (D : Diagram) {i j : Fin D.Γ.c} (hij : i ≠ j) :
    fixedOrderSum D i j =
      ∑ p : ZMod (D.Γ.comp i).k, ∑ q : ZMod (D.Γ.comp j).k,
        if (edgeSegment (D.Γ.comp i).P p ∩ edgeSegment (D.Γ.comp j).P q).Nonempty then
          ((SignType.sign (det (edge (D.Γ.comp i).P p) (edge (D.Γ.comp j).P q)) : SignType) : ℤ)
        else 0 := by
  unfold fixedOrderSum
  rw [sum_sigma_fst_eq (k := fun i' => (D.Γ.comp i').k) i]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [sum_sigma_fst_eq (k := fun i' => (D.Γ.comp i').k) j]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [mixedPair_iff D.Γ hij]
      simp only [true_and]
      rfl
    · intro t ht
      rw [ite_eq_right]
      intro h
      exact ht h.2.1
  · intro s hs
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [ite_eq_right]
    intro h
    exact hs h.1

/-- The genericity of the diagram supplies the hypotheses of the fan theorem: regular components
(nonzero edges), `tail_off` across components, transversality across components. -/
theorem fixedOrderSum_eq_zero (D : Diagram) (i j : Fin D.Γ.c) (hij : i ≠ j) :
    fixedOrderSum D i j = 0 := by
  rw [fixedOrderSum_eq_polygon_sum D hij]
  apply fan_sum_zero
  · intro p
    exact ((regular_iff_edges _).mp (D.generic.regular i) p).1
  · intro q
    exact ((regular_iff_edges _).mp (D.generic.regular j) q).1
  · intro p q
    have h := D.generic.tail_off ⟨i, p⟩ ⟨j, q⟩ (fun h => hij h.fst_eq)
    exact h
  · intro p q
    have h := D.generic.tail_off ⟨j, q⟩ ⟨i, p⟩ (fun h => hij h.fst_eq.symm)
    exact h
  · intro p q hmeet
    exact D.generic.transverse ⟨i, p⟩ ⟨j, q⟩ (fun h => hij h.fst_eq) hmeet

/-- "At each mixed crossing the decorated sign is either the fixed-order determinant sign or its
negative, according to which component is over." -/
theorem sign_mixed_eq (D : Diagram) {i j : Fin D.Γ.c} {s t : D.Γ.Strand} (h : D.Γ.MixedPair i j s t) :
    ((D.sign ⟨{s, t}, h.2.2⟩ : SignType) : ℤ) =
      if D.overStrand ⟨{s, t}, h.2.2⟩ = s then
        ((SignType.sign (det (D.Γ.dir s) (D.Γ.dir t)) : SignType) : ℤ)
      else -((SignType.sign (det (D.Γ.dir s) (D.Γ.dir t)) : SignType) : ℤ) := by
  set x : D.Γ.Crossing := ⟨{s, t}, h.2.2⟩ with hx
  have hs : s ∈ x.val := by rw [hx]; simp
  have ht : t ∈ x.val := by rw [hx]; simp
  have hne : s ≠ t := by
    obtain ⟨s', t', hx', hna, -⟩ := h.2.2
    intro hst
    subst hst
    have : ({s, s} : Finset D.Γ.Strand) = {s} := by simp
    rw [this] at hx'
    have hs' : s' ∈ ({s} : Finset _) := by rw [hx']; simp
    have ht' : t' ∈ ({s} : Finset _) := by rw [hx']; simp
    simp only [Finset.mem_singleton] at hs' ht'
    subst hs' ht'
    exact hna (Shadow.Adjacent.refl _ _)
  unfold Diagram.sign
  split_ifs with hover
  · have hunder : D.underStrand x = t :=
      (D.eq_under_of_mem_of_ne x ht (by rw [hover]; exact hne.symm)).symm
    rw [hover, hunder]
  · have hover' : D.overStrand x = t := by
      rcases (D.mem_iff x (D.overStrand x)).mp (D.over_mem x) with h' | h'
      · rcases (D.Γ.mem_iff_eq_or_other x (D.over_mem x) t).mp ht with h'' | h''
        · exact h''.symm
        · rcases (D.Γ.mem_iff_eq_or_other x (D.over_mem x) s).mp hs with h3 | h3
          · exact absurd h3.symm hover
          · exact absurd (h3.trans h''.symm) hne
      · exact absurd h' (D.over_ne_under x)
    have hunder : D.underStrand x = s :=
      (D.eq_under_of_mem_of_ne x hs (by rw [hover']; exact hne)).symm
    rw [hover', hunder, det_swap, Left.sign_neg, SignType.coe_neg]

/-- The correction: minus the fixed-order sign at the mixed crossings where component `j` is over. -/
noncomputable def corrSum (D : Diagram) (i j : Fin D.Γ.c) : ℤ :=
  ∑ s : D.Γ.Strand, ∑ t : D.Γ.Strand,
    if h : D.Γ.MixedPair i j s t then
      (if D.overStrand ⟨{s, t}, h.2.2⟩ = s then 0
        else -((SignType.sign (det (D.Γ.dir s) (D.Γ.dir t)) : SignType) : ℤ))
    else 0

/-- "Their total differs from the zero fixed-order sum by twice an integer." -/
theorem mixedSignSum_eq_fixed_add (D : Diagram) (i j : Fin D.Γ.c) :
    mixedSignSum D i j = fixedOrderSum D i j + 2 * corrSum D i j := by
  unfold mixedSignSum fixedOrderSum corrSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h : D.Γ.MixedPair i j s t
  · rw [dite_eq_left h, dite_eq_left h, ite_eq_left h, sign_mixed_eq D h]
    split_ifs <;> ring
  · rw [dite_eq_right h, dite_eq_right h, ite_eq_right h]
    ring

/-- "If the over-component is constant, all signs use the same one of those two conventions":
component `i` always over. -/
theorem mixedSignSum_eq_fixed_of_over_fst (D : Diagram) (i j : Fin D.Γ.c)
    (h : ∀ (s t : D.Γ.Strand) (h : D.Γ.MixedPair i j s t), D.overStrand ⟨{s, t}, h.2.2⟩ = s) :
    mixedSignSum D i j = fixedOrderSum D i j := by
  unfold mixedSignSum fixedOrderSum
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  by_cases hm : D.Γ.MixedPair i j s t
  · rw [dite_eq_left hm, ite_eq_left hm, sign_mixed_eq D hm, ite_eq_left (h s t hm)]
  · rw [dite_eq_right hm, ite_eq_right hm]

/-- Component `j` always over. -/
theorem mixedSignSum_eq_neg_fixed_of_over_snd (D : Diagram) (i j : Fin D.Γ.c)
    (h : ∀ (s t : D.Γ.Strand) (h : D.Γ.MixedPair i j s t), D.overStrand ⟨{s, t}, h.2.2⟩ = t) :
    mixedSignSum D i j = -fixedOrderSum D i j := by
  unfold mixedSignSum fixedOrderSum
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hm : D.Γ.MixedPair i j s t
  · rw [dite_eq_left hm, ite_eq_left hm, sign_mixed_eq D hm]
    have hne : D.overStrand ⟨{s, t}, hm.2.2⟩ ≠ s := by
      rw [h s t hm]
      intro hts
      obtain ⟨s', t', hx', hna, -⟩ := hm.2.2
      subst hts
      have : ({t, t} : Finset D.Γ.Strand) = {t} := by simp
      rw [this] at hx'
      have hs' : s' ∈ ({t} : Finset _) := by rw [hx']; simp
      have ht' : t' ∈ ({t} : Finset _) := by rw [hx']; simp
      simp only [Finset.mem_singleton] at hs' ht'
      subst hs' ht'
      exact hna (Shadow.Adjacent.refl _ _)
    rw [ite_eq_right hne]
  · rw [dite_eq_right hm, ite_eq_right hm, neg_zero]

end Diagram

end ZeroLink

/-! ## Assembly of mp:zero-link from the chain -/

open ZeroLink in
theorem zero_link : ZeroLinkData where
  fixed_order_sum := fun D i j hij => fixedOrderSum_eq_zero D i j hij
  half_sum_integer := fun D i j hij =>
    ⟨corrSum D i j, by
      rw [mixedSignSum_eq_fixed_add, fixedOrderSum_eq_zero D i j hij, zero_add]⟩
  over_constant := fun D i j hij h => by
    rcases h with h | h
    · rw [mixedSignSum_eq_fixed_of_over_fst D i j h, fixedOrderSum_eq_zero D i j hij]
    · rw [mixedSignSum_eq_neg_fixed_of_over_snd D i j h, fixedOrderSum_eq_zero D i j hij, neg_zero]

end SM
