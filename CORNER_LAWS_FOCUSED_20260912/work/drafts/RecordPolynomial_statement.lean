import SM.LocalPolynomial
import SM.LinkDiagramRecord

/-! Source rp:record-polynomial (reference/SM/sm-3-statesum.tex:1215-1229, frame SM15): polynomial equality
from a named decorated record. Main declaration: `SM.record_polynomial`.

Notation (namespace `SM.Link`): "two actual nonempty finite generic oriented link diagrams" are
`D D' : Diagram`; "a bijection of their components and crossing occurrences which preserves oriented cyclic
successor, crossing pairing, over/under bits and crossing signs; the component bijection must also include
all components with no crossing occurrences" is a named record isomorphism `RecordIso D.record D'.record`
(def:gauss-record: `e : comps ≃ comps'` on ALL components, `Φ : M ≃ M'` respecting `comp`, `succ`, `pair`,
`isOver`, `sgn`); `F_D(l, m)` is `lmF D` (lp:lm); "any common Laurent-ring substitution of these two source
values" is any ring homomorphism `σ : T →+* A` applied to both, in particular the Gaussian evaluation
`P = SM.P`; "every coefficient of the substituted values" is `coeffAt d k (P D)`. -/

namespace SM

open SM.Link

/-- rp:record-polynomial as printed. -/
structure RecordPolynomialData : Prop where
  /-- "Then `F_D(l, m) = F_{D'}(l, m)`." -/
  lmF_eq : ∀ D D' : Diagram, Nonempty (RecordIso D.record D'.record) → lmF D = lmF D'
  /-- "Consequently any common Laurent-ring substitution of these two source values ... agrees" -/
  subst_eq : ∀ D D' : Diagram, Nonempty (RecordIso D.record D'.record) →
    ∀ {A : Type} [CommRing A] (σ : T →+* A), σ (lmF D) = σ (lmF D')
  /-- in particular the Gaussian evaluation `P` agrees -/
  P_eq : ∀ D D' : Diagram, Nonempty (RecordIso D.record D'.record) → P D = P D'
  /-- "and every coefficient of the substituted values, agrees." -/
  coeff_eq : ∀ D D' : Diagram, Nonempty (RecordIso D.record D'.record) →
    ∀ d k : ℤ, coeffAt d k (P D) = coeffAt d k (P D')

theorem record_polynomial : RecordPolynomialData := by
  sorry

end SM
