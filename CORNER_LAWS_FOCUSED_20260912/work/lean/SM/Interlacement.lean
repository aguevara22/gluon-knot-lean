import SM.CrossingPair
import SM.TraversalArcs

/-! Interlacement is alternating visits of actual geometric crossings.
The witnesses are the two edges of each crossing, not external word data. -/

namespace SM

variable {n : ℕ} {P : LabelledTuple n}

def crossingVisitBetween (hn : 3 ≤ n) (hP : G1 P) (x : Crossing P)
    (x₀ x₁ : {i // i ∈ x.val}) (y : Crossing P) (y₀ : {i // i ∈ y.val}) : Prop :=
  traversalBetween (crossingVisitPosition hn hP x x₀)
    (crossingVisitPosition hn hP y y₀) (crossingVisitPosition hn hP x x₁)

def Interlaces (hn : 3 ≤ n) (hP : Generic P) (x y : Crossing P) : Prop :=
  x ≠ y ∧ ∃ x₀ x₁ : {i // i ∈ x.val}, ∃ y₀ y₁ : {i // i ∈ y.val},
    x₀ ≠ x₁ ∧ y₀ ≠ y₁ ∧
    crossingVisitBetween hn hP.1 x x₀ x₁ y y₀ ∧
    crossingVisitBetween hn hP.1 x x₁ x₀ y y₁

theorem interlaces_irrefl (hn : 3 ≤ n) (hP : Generic P) (x : Crossing P) :
    ¬ Interlaces hn hP x x := fun h => h.1 rfl

theorem interlaces_symm (hn : 3 ≤ n) (hP : Generic P) {x y : Crossing P}
    (h : Interlaces hn hP x y) : Interlaces hn hP y x := by
  rcases h with ⟨hxy, x₀, x₁, y₀, y₁, hx, hy, h₀, h₁⟩
  obtain ⟨h₂, h₃⟩ := traversalAlternating_rotate h₀ h₁
  exact ⟨hxy.symm, y₀, y₁, x₁, x₀, hy, hx.symm, h₂, h₃⟩

theorem interlaces_comm (hn : 3 ≤ n) (hP : Generic P) (x y : Crossing P) :
    Interlaces hn hP x y ↔ Interlaces hn hP y x :=
  ⟨interlaces_symm hn hP, interlaces_symm hn hP⟩

theorem crossingVisitBetween_complement (hn : 3 ≤ n) (hP : Generic P)
    {x y : Crossing P} (hxy : x ≠ y) (x₀ x₁ : {i // i ∈ x.val})
    (hx : x₀ ≠ x₁) (j : {i // i ∈ y.val}) :
    crossingVisitBetween hn hP.1 x x₀ x₁ y j ↔
      ¬ crossingVisitBetween hn hP.1 x x₁ x₀ y j := by
  haveI : NeZero n := ⟨by omega⟩
  apply traversalBetween_complement
  · exact crossingVisitPosition_ne hn hP hxy x₀ j
  · exact crossingVisitPosition_ne hn hP hxy.symm j x₁
  · exact fun he => hx.symm (crossingVisitPosition_injective hn hP x he)

/-- The existential alternating-visit definition implies the one-visit clause
for its chosen x endpoints, because the other y visit is on the opposite arc. -/
theorem alternating_visits_iff_unique (hn : 3 ≤ n) (hP : Generic P)
    {x y : Crossing P} (hxy : x ≠ y) (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁) :
    (∃ y₀ y₁ : {i // i ∈ y.val}, y₀ ≠ y₁ ∧
      crossingVisitBetween hn hP.1 x x₀ x₁ y y₀ ∧
      crossingVisitBetween hn hP.1 x x₁ x₀ y y₁) ↔
      ∃! j, crossingVisitBetween hn hP.1 x x₀ x₁ y j := by
  rw [crossing_unique_visit_iff]
  constructor
  · rintro ⟨y₀, y₁, hy, h₀, h₁⟩
    exact ⟨y₀, y₁, hy, h₀,
      (crossingVisitBetween_complement hn hP hxy x₁ x₀ hx.symm y₁).mp h₁⟩
  · rintro ⟨y₀, y₁, hy, h₀, h₁⟩
    exact ⟨y₀, y₁, hy, h₀,
      (crossingVisitBetween_complement hn hP hxy x₁ x₀ hx.symm y₁).mpr h₁⟩

end SM
