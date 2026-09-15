import SM.LocalPolynomial

/-! Source lc:single-crossing (reference/SM/sm-3-statesum.tex:1345-1352, frame SM15): a single self crossing
has scalar value one. Main declaration: `SM.single_crossing`.

Notation (namespace `SM.Link`): "an actual oriented one-circle diagram" is a `Diagram` with `D.Γ.c = 1`
(one component circle); "just one self crossing" is `∀ y : D.Γ.Crossing, y = x` for a crossing `x` (the
crossing type is a subsingleton with the inhabitant `x`; on one circle every crossing is a self
crossing); "for either crossing sign" is the absence of any hypothesis on `D.IsPositive x`; "local LM
evaluation `P_D`" is `SM.P` (SM/LocalPolynomial.lean, the Gaussian evaluation of the source value of
lp:lm); "a crossing-free one-circle diagram" is `D.IsCrossingFreeCircle`. -/

namespace SM

open SM.Link

/-- lc:single-crossing as printed. -/
structure SingleCrossingData : Prop where
  /-- "An actual oriented one-circle diagram with just one self crossing has local LM evaluation
  `P_D = 1`, for either crossing sign." -/
  one_crossing : ∀ (D : Diagram) (x : D.Γ.Crossing), D.Γ.c = 1 → (∀ y : D.Γ.Crossing, y = x) → P D = 1
  /-- "A crossing-free one-circle diagram also has value one." -/
  crossing_free : ∀ D : Diagram, D.IsCrossingFreeCircle → P D = 1

theorem single_crossing : SingleCrossingData := by
  sorry

end SM
