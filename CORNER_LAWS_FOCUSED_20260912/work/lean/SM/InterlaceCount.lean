import SM.Interlacement

/-! The source's exactly-one clause, for every choice of the first x visit.
Its cardinality counts the actual two geometric visits of y. -/

namespace SM

variable {n : ℕ} {P : LabelledTuple n}

theorem crossing_unique_between_swap (hn : 3 ≤ n) (hP : Generic P)
    {x y : Crossing P} (hxy : x ≠ y) (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁) :
    (∃! j, crossingVisitBetween hn hP.1 x x₀ x₁ y j) ↔
      ∃! j, crossingVisitBetween hn hP.1 x x₁ x₀ y j := by
  rw [← alternating_visits_iff_unique hn hP hxy x₀ x₁ hx,
    ← alternating_visits_iff_unique hn hP hxy x₁ x₀ hx.symm]
  constructor <;> rintro ⟨a, b, hab, ha, hb⟩
  · exact ⟨b, a, hab.symm, hb, ha⟩
  · exact ⟨b, a, hab.symm, hb, ha⟩

theorem interlaces_iff_unique (hn : 3 ≤ n) (hP : Generic P)
    (x y : Crossing P) (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁) :
    Interlaces hn hP x y ↔ x ≠ y ∧
      ∃! j, crossingVisitBetween hn hP.1 x x₀ x₁ y j := by
  constructor
  · rintro ⟨hxy, a, b, c, d, hab, hcd, h₀, h₁⟩
    refine ⟨hxy, ?_⟩
    have hu := (alternating_visits_iff_unique hn hP hxy a b hab).mp
      ⟨c, d, hcd, h₀, h₁⟩
    rcases crossing_visits_exhaust x x₀ x₁ hx a with he | he
    · subst a
      have hb : b = x₁ := by
        rcases crossing_visits_exhaust x x₀ x₁ hx b with hb | hb
        · exact (hab hb.symm).elim
        · exact hb
      simpa only [hb] using hu
    · subst a
      have hb : b = x₀ := by
        rcases crossing_visits_exhaust x x₀ x₁ hx b with hb | hb
        · exact hb
        · exact (hab hb.symm).elim
      rw [hb] at hu
      exact (crossing_unique_between_swap hn hP hxy x₀ x₁ hx).mpr hu
  · rintro ⟨hxy, hu⟩
    obtain ⟨a, b, hab, ha, hb⟩ :=
      (alternating_visits_iff_unique hn hP hxy x₀ x₁ hx).mpr hu
    exact ⟨hxy, x₀, x₁, a, b, hx, hab, ha, hb⟩

noncomputable def crossingVisitsOnArc (hn : 3 ≤ n) (hP : G1 P)
    (x : Crossing P) (x₀ x₁ : {i // i ∈ x.val}) (y : Crossing P) :
    Finset {j // j ∈ y.val} := by
  classical
  exact Finset.univ.filter (crossingVisitBetween hn hP x x₀ x₁ y)

theorem crossingVisitsOnArc_card_one (hn : 3 ≤ n) (hP : G1 P)
    (x : Crossing P) (x₀ x₁ : {i // i ∈ x.val}) (y : Crossing P) :
    (crossingVisitsOnArc hn hP x x₀ x₁ y).card = 1 ↔
      ∃! j, crossingVisitBetween hn hP x x₀ x₁ y j := by
  classical
  simp only [crossingVisitsOnArc, Finset.card_eq_one_iff_existsUnique,
    Finset.mem_filter, Finset.mem_univ, true_and]

theorem interlaces_iff_count (hn : 3 ≤ n) (hP : Generic P)
    (x y : Crossing P) (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁) :
    Interlaces hn hP x y ↔ x ≠ y ∧
      (crossingVisitsOnArc hn hP.1 x x₀ x₁ y).card = 1 := by
  rw [crossingVisitsOnArc_card_one]
  exact interlaces_iff_unique hn hP x y x₀ x₁ hx

end SM
