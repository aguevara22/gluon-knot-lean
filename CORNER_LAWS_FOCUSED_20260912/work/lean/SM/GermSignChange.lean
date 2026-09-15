import SM.GermSides

/-! The source's local opposite-sign condition, with all evaluations kept
inside the germ's own parameter interval. No derivative condition is used. -/

namespace SM.WallGerm

variable {n : ℕ} (g : WallGerm n)

def SignChanges (φ : LabelledTuple n → ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.SideParameter, t.val < δ →
    φ (g.sideTuple true t).val * φ (g.sideTuple false t).val < 0

theorem signChanges_iff_local (φ : LabelledTuple n → ℝ) :
    g.SignChanges φ ↔ ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      φ (g.sideTuple true t).val * φ (g.sideTuple false t).val < 0 := by
  constructor
  · rintro ⟨δ, hδ, _, h⟩
    exact ⟨δ, hδ, h⟩
  · rintro ⟨δ, hδ, h⟩
    exact ⟨min δ g.radius, lt_min hδ g.radius_pos, min_le_right _ _,
      fun t ht => h t (lt_of_lt_of_le ht (min_le_left _ _))⟩

theorem signChanges_iff_real (φ : LabelledTuple n → ℝ) :
    g.SignChanges φ ↔ ∃ δ : ℝ, ∃ hδ : 0 < δ, ∃ hδr : δ ≤ g.radius,
      ∀ t : ℝ, ∀ ht : 0 < t, ∀ htd : t < δ,
      φ (g.curve ⟨t, by constructor <;> linarith [g.radius_pos]⟩) *
        φ (g.curve ⟨-t, by constructor <;> linarith [g.radius_pos]⟩) < 0 := by
  constructor
  · rintro ⟨δ, hδ, hδr, h⟩
    refine ⟨δ, hδ, hδr, ?_⟩
    intro t ht htd
    exact h ⟨t, ht, lt_of_lt_of_le htd hδr⟩ htd
  · rintro ⟨δ, hδ, hδr, h⟩
    exact ⟨δ, hδ, hδr, fun t ht => h t.val t.property.1 ht⟩

/-- Every smaller positive witness radius preserves the exact condition. -/
theorem signChanges_witness_shrink {φ : LabelledTuple n → ℝ} {δ η : ℝ}
    (hδr : δ ≤ g.radius)
    (h : ∀ t : g.SideParameter, t.val < δ →
      φ (g.sideTuple true t).val * φ (g.sideTuple false t).val < 0)
    (hη : 0 < η) (hηδ : η ≤ δ) :
    0 < η ∧ η ≤ g.radius ∧ ∀ t : g.SideParameter, t.val < η →
      φ (g.sideTuple true t).val * φ (g.sideTuple false t).val < 0 :=
  ⟨hη, hηδ.trans hδr, fun t ht => h t (lt_of_lt_of_le ht hηδ)⟩

theorem signChanges_ne_zero {φ : LabelledTuple n → ℝ} (h : g.SignChanges φ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.SideParameter, t.val < δ →
      φ (g.sideTuple true t).val ≠ 0 ∧ φ (g.sideTuple false t).val ≠ 0 := by
  obtain ⟨δ, hδ, hδr, h⟩ := h
  refine ⟨δ, hδ, hδr, ?_⟩
  intro t ht
  have hn := (h t ht).ne
  exact ⟨fun he => hn (by rw [he, zero_mul]), fun he => hn (by rw [he, mul_zero])⟩

end SM.WallGerm
