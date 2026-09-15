import SM.LocalPolynomial
import SM.CoefficientTransport

/-! Source lp:core (reference/SM/sm-3-statesum.tex:1041-1063, frame SM15): the local campaign polynomial,
algebraic part. Main declaration: `SM.lp_core`.

Notation (namespace `SM.Link`): `R = ℤ[a^{±1}, z^{±1}]` is `R`; "the same source construction" is the
source function `lmF` of lp:lm and its Gaussian evaluation `φ(F_D)` (eq. lp:gaussian, `phi : TG →ₐ RG`,
`φ(l) = i a`, `φ(m) = −i z`); `P_D` is `SM.P D` (SM/LocalPolynomial.lean: the element of `R` whose image in
`R_G` is `φ(F_D)`, field `gaussian`); `δ = (a − a⁻¹) z⁻¹` is `R.delta`; "UNDER-first c-component diagram" is
a diagram `D` with a basing `B` such that `D.UnderFirst B`, `c = D.componentCount`; `H_D` is `homfly`
(lit:homfly); "every skein triple" is `IsSkeinTriple D₊ D₋ D₀`; "this exact diagram domain" is `Diagram`;
`z^{1−c} ℤ[a^{±1}, z²]` is `InSupportM c` (every monomial `a^d z^k` present has `k = 1 − c + 2j`, `j ∈ ℕ`);
"the crossing-free circle" is `Diagram.IsCrossingFreeCircle`; "knot evaluations" are the values on
one-component diagrams; "all local invariances in lp:lm" are invariance under `PlanarIsotopic`, `RI`,
`RII`, `RIII`. -/

namespace SM

open SM.Link

/-- lp:core as printed, one field per printed sentence. -/
structure LpCoreData : Prop where
  /-- "The same source construction has an evaluation `P_D ∈ R`" (eq. lp:gaussian): `P_D` is the element
  of `R` whose image in `R_G` is the Gaussian evaluation `φ(F_D)` of the source value (integral descent). -/
  gaussian : ∀ D : Diagram, R.toRG (P D) = phi (T.toTG (lmF D))
  /-- eq. lp:skein: `a P_{D₊} − a⁻¹ P_{D₋} = z P_{D₀}` on every skein triple. -/
  skein : ∀ Dp Dm D0 : Diagram, IsSkeinTriple Dp Dm D0 → R.a * P Dp - R.aInv * P Dm = R.z * P D0
  /-- "Its value on every UNDER-first `c`-component diagram is `δ^{c−1}`", `δ = (a − a⁻¹) z⁻¹`. -/
  underFirst_init : ∀ (D : Diagram) (B : D.Basing), D.UnderFirst B → P D = R.delta ^ (D.componentCount - 1)
  /-- "It equals `H_D` of Literature input lit:homfly." -/
  eq_homfly : ∀ D : Diagram, P D = homfly D
  /-- "It is also the unique function on this exact diagram domain satisfying this skein and all these
  initialization values." (The uniqueness hypothesis includes the initialization values explicitly.) -/
  unique : ∀ Q : Diagram → R,
    (∀ Dp Dm D0 : Diagram, IsSkeinTriple Dp Dm D0 → R.a * Q Dp - R.aInv * Q Dm = R.z * Q D0) →
    (∀ (D : Diagram) (B : D.Basing), D.UnderFirst B → Q D = R.delta ^ (D.componentCount - 1)) →
    Q = P
  /-- eq. lp:support: "For every `c`-component diagram, `P_D ∈ z^{1−c} ℤ[a^{±1}, z²]`". -/
  support : ∀ D : Diagram, InSupportM D.componentCount (P D)
  /-- eq. lp:support: "`P_D ≠ 0`". -/
  ne_zero : ∀ D : Diagram, P D ≠ 0
  /-- "In particular `P_○ = 1`". -/
  circle : ∀ D : Diagram, D.IsCrossingFreeCircle → P D = 1
  /-- "and knot evaluations are polynomials in `z²`, with no negative `z` exponents": on a one-component
  diagram every monomial `a^d z^k` present has `k = 2j` for some `j : ℕ`. -/
  knot_support : ∀ D : Diagram, D.componentCount = 1 →
    ∀ d k : ℤ, coeffAt d k (P D) ≠ 0 → ∃ j : ℕ, k = 2 * (j : ℤ)
  /-- "All local invariances in Literature input lp:lm are retained": planar isotopy and the three
  Reidemeister moves. -/
  planar : ∀ D D' : Diagram, PlanarIsotopic D D' → P D = P D'
  reidemeister_I : ∀ D D' : Diagram, RI D D' → P D = P D'
  reidemeister_II : ∀ D D' : Diagram, RII D D' → P D = P D'
  reidemeister_III : ∀ D D' : Diagram, RIII D D' → P D = P D'

theorem lp_core : LpCoreData := by
  sorry

end SM
