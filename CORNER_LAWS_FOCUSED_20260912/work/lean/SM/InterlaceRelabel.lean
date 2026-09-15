import SM.InterlaceCount
import SM.VisitRelabel

/-! Cyclic relabelling transports actual visit fibres and their interlacement. -/

namespace SM

variable {n : ℕ} {P : LabelledTuple n}

theorem crossingVisitPosition_shift (hn : 3 ≤ n) (hP : G1 P) (a : ZMod n)
    (c : Crossing P) (i : {k // k ∈ c.val}) :
    crossingVisitPosition hn (g1_shift_forward a hP) (crossingShift a c)
      (visitEdgeShiftEquiv a c i) = traversalShift a (crossingVisitPosition hn hP c i) :=
  visitPosition_shift hn hP a ⟨c, i⟩

theorem crossingVisitBetween_shift (hn : 3 ≤ n) (hP : Generic P) (a : ZMod n)
    (x : Crossing P) (x₀ x₁ : {i // i ∈ x.val}) (y : Crossing P)
    (j : {i // i ∈ y.val}) :
    crossingVisitBetween hn ((generic_shift a P).mpr hP).1
      (crossingShift a x) (visitEdgeShiftEquiv a x x₀) (visitEdgeShiftEquiv a x x₁)
      (crossingShift a y) (visitEdgeShiftEquiv a y j) ↔
      crossingVisitBetween hn hP.1 x x₀ x₁ y j := by
  haveI : NeZero n := ⟨by omega⟩
  change crossingVisitBetween hn (g1_shift_forward a hP.1)
      (crossingShift a x) (visitEdgeShiftEquiv a x x₀) (visitEdgeShiftEquiv a x x₁)
      (crossingShift a y) (visitEdgeShiftEquiv a y j) ↔ _
  unfold crossingVisitBetween
  rw [crossingVisitPosition_shift, crossingVisitPosition_shift,
    crossingVisitPosition_shift, traversalBetween_shift]

theorem interlaces_shift (hn : 3 ≤ n) (hP : Generic P) (a : ZMod n)
    (x y : Crossing P) :
    Interlaces hn ((generic_shift a P).mpr hP)
      (crossingShiftEquiv a P x) (crossingShiftEquiv a P y) ↔
      Interlaces hn hP x y := by
  constructor
  · rintro ⟨hxy, s₀, s₁, t₀, t₁, hs, ht, h₀, h₁⟩
    obtain ⟨x₀, rfl⟩ := (visitEdgeShiftEquiv a x).surjective s₀
    obtain ⟨x₁, rfl⟩ := (visitEdgeShiftEquiv a x).surjective s₁
    obtain ⟨y₀, rfl⟩ := (visitEdgeShiftEquiv a y).surjective t₀
    obtain ⟨y₁, rfl⟩ := (visitEdgeShiftEquiv a y).surjective t₁
    refine ⟨fun h => hxy (congrArg (crossingShiftEquiv a P) h),
      x₀, x₁, y₀, y₁, fun h => hs (congrArg (visitEdgeShiftEquiv a x) h),
      fun h => ht (congrArg (visitEdgeShiftEquiv a y) h), ?_, ?_⟩
    · exact (crossingVisitBetween_shift hn hP a x x₀ x₁ y y₀).mp h₀
    · exact (crossingVisitBetween_shift hn hP a x x₁ x₀ y y₁).mp h₁
  · rintro ⟨hxy, x₀, x₁, y₀, y₁, hx, hy, h₀, h₁⟩
    refine ⟨fun h => hxy ((crossingShiftEquiv a P).injective h),
      visitEdgeShiftEquiv a x x₀, visitEdgeShiftEquiv a x x₁,
      visitEdgeShiftEquiv a y y₀, visitEdgeShiftEquiv a y y₁,
      fun h => hx ((visitEdgeShiftEquiv a x).injective h),
      fun h => hy ((visitEdgeShiftEquiv a y).injective h), ?_, ?_⟩
    · exact (crossingVisitBetween_shift hn hP a x x₀ x₁ y y₀).mpr h₀
    · exact (crossingVisitBetween_shift hn hP a x x₁ x₀ y y₁).mpr h₁

end SM
