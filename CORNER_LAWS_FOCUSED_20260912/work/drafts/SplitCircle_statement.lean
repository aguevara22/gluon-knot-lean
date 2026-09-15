import SM.LocalPolynomial
import SM.LinkMoves

/-! Source lp:split-circle (reference/SM/sm-3-statesum.tex:1180-1190, frame SM15): a diagrammatically split
circle. Main declaration: `SM.split_circle`.

Notation (namespace `SM.Link`): "`D'` is the actual diagram formed from `D` by adding one simple
crossing-free component having no crossings with `D`; it may surround some components of `D`; it need not
lie in the unbounded complementary face" is `IsSplitCircleAddition D D'` (some component of `D'` carries
no crossing occurrence and the restriction of `D'` to the other components is a reparametrization of `D`;
nothing is said about nesting); `P` is `SM.P`, `δ` is `R.delta`; "a crossing-free `c`-component diagram"
is a `Diagram` with `IsEmpty D.Γ.Crossing` and `c = D.componentCount`. -/

namespace SM

open SM.Link

/-- lp:split-circle as printed. -/
structure SplitCircleData : Prop where
  /-- eq. lp:split: `P_{D'} = δ P_D`. -/
  split : ∀ D D' : Diagram, IsSplitCircleAddition D D' → P D' = R.delta * P D
  /-- "In particular every crossing-free `c`-component diagram has value `δ^{c−1}`." -/
  crossing_free : ∀ D : Diagram, IsEmpty D.Γ.Crossing → P D = R.delta ^ (D.componentCount - 1)

theorem split_circle : SplitCircleData := by
  sorry

end SM
