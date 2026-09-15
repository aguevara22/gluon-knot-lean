import SM.LinkInterfaces

/-! Source lp:coefficient-transport (reference/SM/sm-3-statesum.tex:981-992, frame SM15): Gaussian coefficient
transport of skein uniqueness. Main declaration: `SM.coefficient_transport`.

Notation (Chapter-3 layer, namespace `SM.Link`): `R = ℤ[a^{±1}, z^{±1}]` is `R` (`R.a`, `R.aInv`, `R.z`);
"oriented link diagrams" are `Diagram` (the document's polygonal class, def:positive-lift); "invariant under
planar isotopy and the three Reidemeister moves" is invariance under `PlanarIsotopic`, `RI`, `RII`, `RIII`;
"the crossing-free circle" is every one-component crossing-free diagram (`Diagram.IsCrossingFreeCircle`);
"every skein triple" is `IsSkeinTriple Dp Dm D0`. The hypotheses on a map are bundled in the Prop structure
`RCompetitor` (one field per printed clause); "no restriction on the support or on the coefficients of the maps
is imposed" is the absence of any further hypothesis on `Q`. -/

namespace SM

open SM.Link

/-- The hypotheses of lp:coefficient-transport on a map `D ↦ Q_D ∈ R`: "invariant under planar isotopy and
the three Reidemeister moves, take the value 1 on the crossing-free circle, and satisfy
`a Q_{D₊} − a⁻¹ Q_{D₋} = z Q_{D₀}` on every skein triple". -/
structure RCompetitor (Q : Diagram → R) : Prop where
  /-- "invariant under planar isotopy" -/
  planar : ∀ D D' : Diagram, PlanarIsotopic D D' → Q D = Q D'
  /-- "and the three Reidemeister moves" -/
  reidemeister_I : ∀ D D' : Diagram, RI D D' → Q D = Q D'
  reidemeister_II : ∀ D D' : Diagram, RII D D' → Q D = Q D'
  reidemeister_III : ∀ D D' : Diagram, RIII D D' → Q D = Q D'
  /-- "take the value 1 on the crossing-free circle" -/
  circle : ∀ D : Diagram, D.IsCrossingFreeCircle → Q D = 1
  /-- "satisfy `a Q_{D₊} − a⁻¹ Q_{D₋} = z Q_{D₀}` on every skein triple" -/
  skein : ∀ Dp Dm D0 : Diagram, IsSkeinTriple Dp Dm D0 →
    R.a * Q Dp - R.aInv * Q Dm = R.z * Q D0

/-- lp:coefficient-transport as printed: "Any two maps `D ↦ Q_D ∈ R` on oriented link diagrams that are
invariant under planar isotopy and the three Reidemeister moves, take the value 1 on the crossing-free
circle, and satisfy `a Q_{D₊} − a⁻¹ Q_{D₋} = z Q_{D₀}` on every skein triple coincide. No restriction on
the support or on the coefficients of the maps is imposed." -/
theorem coefficient_transport (Q Q' : Diagram → R) (hQ : RCompetitor Q) (hQ' : RCompetitor Q') :
    Q = Q' := by
  sorry

end SM
