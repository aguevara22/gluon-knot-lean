import SM.CornerStateSum
import SM.Chambers

/-! Source prop:C-chamber (reference/SM/sm-4-knotlaws.tex:36-40, frame SM15): chamber constancy of the corner
state sum. Main declaration: `SM.prop_C_chamber`.

Notation (accepted rows def:chamber / prop:chambers, SM/Chambers.lean and SM/ChamberPaths.lean): the space of
generic polygons `𝓤_n / (ℤ/n)` is `GenericPolygon n` (the quotient of `GenericTuple n = {P // Generic P}` by
cyclic relabelling, `polygonProjection`); a chamber is a connected component of it, `chamber (polygonProjection P)`;
"the state sum `C` of def:C" is `cornerStateSum hn hP` (SM/CornerStateSum.lean, accepted row def:C), defined on
labelled generic polygons. "Constant on every chamber": any two generic labelled polygons whose classes lie in one
chamber have the same state sum (in particular `C` is invariant under cyclic relabelling and constant on labelled
chambers). -/

namespace SM

open Link Carrier

/-- prop:C-chamber as printed: "The state sum `C` of Definition def:C is constant on every chamber." -/
structure CChamberData : Prop where
  constant : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P Q : GenericTuple n),
    polygonProjection Q ∈ chamber (polygonProjection P) →
    cornerStateSum hn P.2 = cornerStateSum hn Q.2

theorem prop_C_chamber : CChamberData := by
  sorry

end SM
